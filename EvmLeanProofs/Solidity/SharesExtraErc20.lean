import EvmLeanProofs.Solidity.Examples.SolmateAssetTransferSpec

/-!
# Solmate `ERC20`: `approve` and `transferFrom` on the storage abstraction

`EvmLeanProofs.Solidity.Erc20` models Solmate's `transfer` on the word-level ERC-20 view
(`Erc20.State`, `Erc20.view`). This file adds the other two state-changing functions, for
every contract inheriting Solmate's `ERC20` (the vault's share token, the asset):

```solidity
function approve(address spender, uint256 amount) public returns (bool) {
    allowance[msg.sender][spender] = amount; …
}
function transferFrom(address from, address to, uint256 amount) public returns (bool) {
    uint256 allowed = allowance[from][msg.sender];
    if (allowed != type(uint256).max) allowance[from][msg.sender] = allowed - amount;
    balanceOf[from] -= amount;
    unchecked { balanceOf[to] += amount; } …
}
```

* `Model.approve`, `Model.spend`, `Model.transferFrom`: the abstract semantics on
  `Erc20.State` (`none` = revert: checked subtractions).
* `approveWorld`, `spendWorld`, `transferFromWorld`: the storage writes the compiled code
  performs, in its order (`transferFromWorld` is `spendWorld` followed by the `transfer`
  writes, `Erc20.transferWorld`, shared with the asset's `transfer` proof).
* `AllowanceSlotOk`: the non-collision hypothesis for one allowance entry (its slot is no
  balance slot and not `totalSupply`), the analogue of `BalanceSlotOk`;
  `view_sstore_allowanceSlot` is the effect of writing it.
* `view_approveWorld`, `view_spendWorld`, `view_transferFromWorld`: the worlds seen through
  the abstraction are the models' states (allowances pointwise, for entries whose slot is
  not a written slot, as for `transfer`; see `EvmLeanProofs.Solidity.Keccak` on why
  nested-mapping frames cannot be stated for all pairs).
-/

namespace EvmLean.Solidity.Erc20

open Interpreter

/-- `type(uint256).max`, the "infinite" allowance (`PUSH0 NOT` in the bytecode). -/
def maxWord : Word := ~~~0#256

/-- `EQ allowed (NOT 0)` (the `allowed != type(uint256).max` test) on a maximal allowance. -/
theorem eq_maxWord_of_eq {a : Word} (h : a = maxWord) : Word.eq a (~~~0#256) = 1#256 := by
  subst h; simp [Word.eq, Word.ofBool, maxWord]

/-- `EQ allowed (NOT 0)` on a non-maximal allowance. -/
theorem eq_maxWord_of_ne {a : Word} (h : a ≠ maxWord) : Word.eq a (~~~0#256) = 0#256 := by
  have h' : (a == ~~~0#256) = false := beq_eq_false_iff_ne.mpr h
  rw [Word.eq, Word.ofBool, h']; rfl

/-- Update one allowance. -/
def State.setAllowance (s : State) (o sp : Address) (v : Word) : State :=
  { s with allowance := fun o' sp' => if o' = o ∧ sp' = sp then v else s.allowance o' sp' }

/-! ## Non-collision for an allowance entry -/

/-- The slot of `allowance[o][sp]` is no balance slot (for any address) and not the
`totalSupply` slot. The first part is freshness of its preimage among the single-level
address-keyed preimages (`2¹⁶¹` candidates, one target; plausible) plus the inner row slot
`keccak(o ‖ allowances)` not being the `balanceOf` base slot. -/
def AllowanceSlotOk (crypto : Crypto) (L : Layout) (o sp : Address) : Prop :=
  KeccakFresh crypto (level1 L)
      (slotPreimage (Word.ofAddress sp) (mappingSlot crypto (Word.ofAddress o) L.allowances)) ∧
    mappingSlot crypto (Word.ofAddress o) L.allowances ≠ L.balances ∧
    allowanceSlot crypto L o sp ≠ L.totalSupply

/-- Under `AllowanceSlotOk`, no balance slot is the allowance slot. -/
theorem balanceSlot_ne_allowanceSlot {crypto : Crypto} {L : Layout} {o sp : Address}
    (h : AllowanceSlotOk crypto L o sp) (a : Address) :
    balanceSlot crypto L a ≠ allowanceSlot crypto L o sp :=
  mappingSlot_ne_of_fresh h.1 ⟨a, L.balances, by simp, rfl⟩ (.inr h.2.1.symm)

/-- `SSTORE` at the slot of `allowance[o][sp]`, seen through the abstraction: `totalSupply`
and every balance are unchanged; an allowance entry changes only if its slot is the written
one. -/
theorem view_sstore_allowanceSlot {crypto : Crypto} {L : Layout} {w : World} {token o sp : Address}
    (h : AllowanceSlotOk crypto L o sp) (v : Word) :
    (view crypto L (w.sstore token (allowanceSlot crypto L o sp) v) token).totalSupply =
        (view crypto L w token).totalSupply ∧
      (view crypto L (w.sstore token (allowanceSlot crypto L o sp) v) token).balanceOf =
        (view crypto L w token).balanceOf ∧
      ∀ o' sp', (view crypto L (w.sstore token (allowanceSlot crypto L o sp) v) token).allowance
          o' sp' =
        if allowanceSlot crypto L o' sp' = allowanceSlot crypto L o sp then v
        else (view crypto L w token).allowance o' sp' := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [view]
    exact World.sload_sstore_ne_key _ _ _ (fun e => h.2.2 e.symm)
  · funext b
    simp only [view]
    exact World.sload_sstore_ne_key _ _ _ (balanceSlot_ne_allowanceSlot h b)
  · intro o' sp'
    simp only [view]
    split
    · rename_i he; rw [he]; simp
    · rename_i he; exact World.sload_sstore_ne_key _ _ _ he

/-! ## The abstract semantics -/

namespace Model

/-- Solmate's `approve(spender, amount)` from `owner`. -/
def approve (s : State) (owner spender : Address) (amount : Word) : State :=
  s.setAllowance owner spender amount

/-- The allowance step of Solmate's `transferFrom` (`spender` spends `owner`'s allowance):
nothing if the allowance is `type(uint256).max`, otherwise a checked subtraction. -/
def spend (s : State) (owner spender : Address) (amount : Word) : Option State :=
  if s.allowance owner spender = maxWord then some s
  else if amount.toNat ≤ (s.allowance owner spender).toNat then
    some (s.setAllowance owner spender (s.allowance owner spender - amount))
  else none

/-- Solmate's `transferFrom(src, dst, amount)` from `spender`. -/
def transferFrom (s : State) (spender src dst : Address) (amount : Word) : Option State :=
  (spend s src spender amount).bind fun s₁ => transfer s₁ src dst amount

end Model

/-! ## The storage writes of the compiled code -/

/-- The storage effect of `transfer` (`balanceOf[src] -= amount; balanceOf[dst] += amount`),
shared by `transfer` and `transferFrom` of every Solmate `ERC20`. -/
abbrev transferWorld (crypto : Crypto) (w : World) (token src dst : Address) (amount : Word) :
    World :=
  Examples.SolmateAssetTransfer.transferWorld crypto w token src dst amount

/-- The storage effect of `approve`: one `SSTORE` to `allowance[owner][spender]`. -/
def approveWorld (crypto : Crypto) (w : World) (token owner spender : Address) (amount : Word) :
    World :=
  w.sstore token (allowanceSlot crypto Layout.solmate owner spender) amount

/-- The storage effect of the allowance step of `transferFrom`: unless the allowance is
`type(uint256).max`, `allowance[owner][spender] -= amount`. -/
def spendWorld (crypto : Crypto) (w : World) (token owner spender : Address) (amount : Word) :
    World :=
  let a := w.sload token (allowanceSlot crypto Layout.solmate owner spender)
  if a = maxWord then w
  else w.sstore token (allowanceSlot crypto Layout.solmate owner spender) (a - amount)

/-- The storage effect of `transferFrom(src, dst, amount)` from `spender`. -/
def transferFromWorld (crypto : Crypto) (w : World) (token spender src dst : Address)
    (amount : Word) : World :=
  transferWorld crypto (spendWorld crypto w token src spender amount) token src dst amount

/-! ## Worlds through the abstraction -/

variable {crypto : Crypto} {w : World} {token : Address}

/-- `approveWorld` through the abstraction: `Model.approve`'s balances and total supply;
allowances of `Model.approve` for every entry that is the written one or has another slot;
other accounts untouched. Needs `AllowanceSlotOk` for the written entry only. -/
theorem view_approveWorld {owner spender : Address} {amount : Word}
    (h : AllowanceSlotOk crypto Layout.solmate owner spender) :
    let s := view crypto Layout.solmate w token
    let s' := view crypto Layout.solmate (approveWorld crypto w token owner spender amount) token
    s'.totalSupply = (Model.approve s owner spender amount).totalSupply ∧
      s'.balanceOf = (Model.approve s owner spender amount).balanceOf ∧
      (∀ o sp, (o = owner ∧ sp = spender) ∨
          allowanceSlot crypto Layout.solmate o sp ≠
            allowanceSlot crypto Layout.solmate owner spender →
        s'.allowance o sp = (Model.approve s owner spender amount).allowance o sp) ∧
      (∀ b k, b ≠ token →
        (approveWorld crypto w token owner spender amount).sload b k = w.sload b k) := by
  obtain ⟨h1, h2, h3⟩ := view_sstore_allowanceSlot (w := w) (token := token) h amount
  refine ⟨h1, h2, ?_, ?_⟩
  · intro o sp hos
    simp only [approveWorld, h3, Model.approve, State.setAllowance]
    rcases hos with ⟨rfl, rfl⟩ | hne
    · simp
    · have : ¬ (o = owner ∧ sp = spender) := by rintro ⟨rfl, rfl⟩; exact hne rfl
      simp [hne, this]
  · intro b k hb
    exact World.sload_sstore_ne_addr _ _ _ _ hb

/-- `spendWorld` through the abstraction, when `Model.spend` succeeds: its balances, total
supply and allowances (for the spent entry and every entry with another slot); other accounts
untouched. -/
theorem view_spendWorld {owner spender : Address} {amount : Word} {s₁ : State}
    (h : AllowanceSlotOk crypto Layout.solmate owner spender)
    (hm : Model.spend (view crypto Layout.solmate w token) owner spender amount = some s₁) :
    let s' := view crypto Layout.solmate (spendWorld crypto w token owner spender amount) token
    s'.totalSupply = s₁.totalSupply ∧ s'.balanceOf = s₁.balanceOf ∧
      (∀ o sp, (o = owner ∧ sp = spender) ∨
          allowanceSlot crypto Layout.solmate o sp ≠
            allowanceSlot crypto Layout.solmate owner spender →
        s'.allowance o sp = s₁.allowance o sp) ∧
      (∀ b k, b ≠ token → (spendWorld crypto w token owner spender amount).sload b k =
        w.sload b k) := by
  unfold Model.spend at hm
  simp only [spendWorld]
  split
  · rename_i hmax
    have hmax' : (view crypto Layout.solmate w token).allowance owner spender = maxWord := hmax
    simp only [hmax', ↓reduceIte, Option.some.injEq] at hm
    subst hm
    exact ⟨rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  · rename_i hmax
    have hmax' : ¬ (view crypto Layout.solmate w token).allowance owner spender = maxWord := hmax
    simp only [hmax', ↓reduceIte] at hm
    split at hm
    · cases hm
      obtain ⟨h1, h2, h3⟩ := view_sstore_allowanceSlot (w := w) (token := token) h
        (w.sload token (allowanceSlot crypto Layout.solmate owner spender) - amount)
      refine ⟨h1, h2, ?_, ?_⟩
      · intro o sp hos
        simp only [h3, State.setAllowance]
        rcases hos with ⟨rfl, rfl⟩ | hne
        · simp; rfl
        · have : ¬ (o = owner ∧ sp = spender) := by rintro ⟨rfl, rfl⟩; exact hne rfl
          simp [hne, this]
      · intro b k hb
        exact World.sload_sstore_ne_addr _ _ _ _ hb
    · cases hm

/-- `transferFromWorld` through the abstraction, when `Model.transferFrom` succeeds with
`s'`: exactly its `totalSupply` and `balanceOf`; its allowance for every entry whose slot is
neither balance slot written and that is the spent entry or has another slot than it; other
accounts untouched. Needs `BalanceSlotOk` for `src` and `dst` and `AllowanceSlotOk` for the
spent entry `allowance[src][spender]`. -/
theorem view_transferFromWorld {spender src dst : Address} {amount : Word} {s' : State}
    (hs : BalanceSlotOk crypto Layout.solmate src) (hd : BalanceSlotOk crypto Layout.solmate dst)
    (ha : AllowanceSlotOk crypto Layout.solmate src spender)
    (hm : Model.transferFrom (view crypto Layout.solmate w token) spender src dst amount =
      some s') :
    let v := view crypto Layout.solmate
      (transferFromWorld crypto w token spender src dst amount) token
    v.totalSupply = s'.totalSupply ∧ v.balanceOf = s'.balanceOf ∧
      (∀ o sp, allowanceSlot crypto Layout.solmate o sp ≠ balanceSlot crypto Layout.solmate src →
        allowanceSlot crypto Layout.solmate o sp ≠ balanceSlot crypto Layout.solmate dst →
        (o = src ∧ sp = spender) ∨
          allowanceSlot crypto Layout.solmate o sp ≠
            allowanceSlot crypto Layout.solmate src spender →
        v.allowance o sp = s'.allowance o sp) ∧
      (∀ b k, b ≠ token →
        (transferFromWorld crypto w token spender src dst amount).sload b k = w.sload b k) := by
  unfold Model.transferFrom at hm
  obtain ⟨s₁, hs₁, ht⟩ := Option.bind_eq_some_iff.1 hm
  obtain ⟨e1, e2, e3, e4⟩ := view_spendWorld (w := w) (token := token) ha hs₁
  -- `Model.transfer` from the view of the intermediate world
  have ht' : Model.transfer (view crypto Layout.solmate
      (spendWorld crypto w token src spender amount) token) src dst amount =
      some { s' with allowance :=
        (view crypto Layout.solmate (spendWorld crypto w token src spender amount) token).allowance } := by
    unfold Model.transfer at ht ⊢
    have hb : (view crypto Layout.solmate (spendWorld crypto w token src spender amount)
        token).balanceOf = s₁.balanceOf := e2
    split at ht
    · rename_i hle
      rw [hb]
      simp only [hle, ↓reduceIte]
      cases ht
      simp only [State.setBalance, Option.some.injEq]
      rw [hb, e1]
    · cases ht
  obtain ⟨f1, f2, f3, f4⟩ := Examples.SolmateAssetTransfer.view_transferWorld (w := spendWorld crypto w token src spender amount)
    (token := token) hs hd ht'
  have hal := Model.transfer_allowance ht
  simp only [transferFromWorld, transferWorld]
  refine ⟨f1, f2, ?_, fun b k hb => by rw [f4 b k hb, e4 b k hb]⟩
  intro o sp h1 h2 h3
  rw [f3 o sp h1 h2, hal, e3 o sp h3]

end EvmLean.Solidity.Erc20
