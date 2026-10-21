import EvmLogic.Solidity.ERC20

/-!
# OpenZeppelin `ERC20` (v5): model and storage writes

OpenZeppelin's `ERC20` keeps `_balances` at slot 0, `_allowances` at 1 and `_totalSupply` at 2
(`Layout.oz`). `Model.oz*` is its word-level semantics: Solmate's `transfer`/`approve`/`spend`
(`ERC20.Model`) behind the zero-address checks (`ERC20InvalidSender`, `ERC20InvalidReceiver`,
`ERC20InvalidApprover`, `ERC20InvalidSpender`), plus `_mint`/`_burn` through `_update`
(checked supply addition, unchecked writes). The `*World` definitions are the compiled code's
`SSTORE`s in order, for any `Layout`; the `view_*World` theorems relate them to the model
through `ERC20.view`, with the same pointwise allowance frames as the Solmate ones. Writing the
supply slot needs `SupplySlotOk` (no balance slot is the supply slot): otherwise the view would
double-count.
-/

section

namespace EvmLogic.Solidity.ERC20
open EvmLean

/-- OpenZeppelin's `ERC20` (v5): `_totalSupply` at 2, `_balances` at 0, `_allowances` at 1. -/
def Layout.oz : Layout := ⟨2, 0, 1⟩

/-! ## Words -/

theorem ofAddress_zero : Word.ofAddress (0 : Address) = 0#256 := rfl

theorem ofAddress_ne_zero {a : Address} (h : a ≠ 0) : Word.ofAddress a ≠ 0#256 :=
  fun e => h (Word.ofAddress_injective (e.trans ofAddress_zero.symm))

/-- solc's checked `x + y` (as `y + x`) does not overflow. -/
theorem gt_add_self_eq_zero {x y : Word} (h : x.toNat + y.toNat < 2 ^ 256) :
    Word.gt x (y + x) = 0#256 := by
  simp only [Word.gt, Word.ofBool, BitVec.ult, decide_eq_true_eq]
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  simp

/-- solc's checked `x + y` (as `y + x`) overflows. -/
theorem gt_add_self_eq_one {x y : Word} (h : 2 ^ 256 ≤ x.toNat + y.toNat) :
    Word.gt x (y + x) = 1#256 := by
  simp only [Word.gt, Word.ofBool, BitVec.ult, decide_eq_true_eq]
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.toNat_add, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [show y.toNat + x.toNat - 2 ^ 256 < x.toNat by omega]
  rfl

/-- `allowance < type(uint256).max` for a finite allowance. -/
theorem lt_maxWord_of_ne {a : Word} (h : a ≠ maxWord) : Word.lt a (~~~0#256) = 1#256 := by
  refine (Word.lt_eq_one_iff _ _).2 ?_
  have hlt : a.toNat < 2 ^ 256 := a.isLt
  have hne : a.toNat ≠ 2 ^ 256 - 1 := fun e => h (BitVec.eq_of_toNat_eq (by
    rw [e]; rfl))
  show a.toNat < (~~~0#256 : Word).toNat
  rw [show (~~~0#256 : Word).toNat = 2 ^ 256 - 1 from rfl]
  omega

/-- `allowance < type(uint256).max` fails for the infinite allowance. -/
theorem lt_maxWord_of_eq {a : Word} (h : a = maxWord) : Word.lt a (~~~0#256) = 0#256 := by
  refine (Word.lt_eq_zero_iff _ _).2 ?_
  rw [h]; exact Nat.le_refl _

/-! ## Non-collision with the supply slot -/

/-- No balance slot is the supply slot (one fixed target against all `2¹⁶⁰` balance rows).
Needed when the code writes `totalSupply` (`_mint`, `_burn`). -/
def SupplySlotOk (crypto : Crypto) (L : Layout) : Prop :=
  KeccakAvoids crypto (AddressKeyed [L.balances]) [L.totalSupply]

theorem SupplySlotOk.balanceSlot_ne {crypto : Crypto} {L : Layout} (h : SupplySlotOk crypto L)
    (a : Address) : balanceSlot crypto L a ≠ L.totalSupply :=
  mappingSlot_ne_of_avoids h ⟨a, L.balances, by simp, rfl⟩ (by simp)

/-! ## The word-level semantics -/

namespace Model

/-- OpenZeppelin's `transfer(to, amount)` from `caller` (`_transfer`): the zero-address checks,
then `_update`, which for nonzero addresses is Solmate's `transfer`. -/
def ozTransfer (s : State) (caller to : Address) (amount : Word) : Option State :=
  if caller = 0 then none else if to = 0 then none else transfer s caller to amount

/-- OpenZeppelin's `_approve(owner, spender, amount)`. -/
def ozApprove (s : State) (owner spender : Address) (amount : Word) : Option State :=
  if owner = 0 then none else if spender = 0 then none else some (approve s owner spender amount)

/-- OpenZeppelin's `_spendAllowance(owner, spender, amount)`: nothing on an infinite allowance,
otherwise a checked subtraction written back through `_approve` (zero-address checks, no
event). -/
def ozSpend (s : State) (owner spender : Address) (amount : Word) : Option State :=
  if s.allowance owner spender = maxWord then some s
  else if amount.toNat ≤ (s.allowance owner spender).toNat then
    ozApprove s owner spender (s.allowance owner spender - amount)
  else none

/-- OpenZeppelin's `transferFrom(src, dst, amount)` from `spender`. -/
def ozTransferFrom (s : State) (spender src dst : Address) (amount : Word) : Option State :=
  (ozSpend s src spender amount).bind fun s₁ => ozTransfer s₁ src dst amount

/-- OpenZeppelin's `_mint(dst, amount)`: `_update(0, dst, amount)` with the checked supply
addition, then an unchecked add to the recipient. -/
def ozMint (s : State) (dst : Address) (amount : Word) : Option State :=
  if dst = 0 then none
  else if s.totalSupply.toNat + amount.toNat < 2 ^ 256 then
    let s₁ := { s with totalSupply := amount + s.totalSupply }
    some (s₁.setBalance dst (amount + s₁.balanceOf dst))
  else none

/-- OpenZeppelin's `_burn(src, amount)`: `_update(src, 0, amount)`, a checked balance
subtraction, then an unchecked supply subtraction. -/
def ozBurn (s : State) (src : Address) (amount : Word) : Option State :=
  if src = 0 then none
  else if amount.toNat ≤ (s.balanceOf src).toNat then
    let s₁ := s.setBalance src (s.balanceOf src - amount)
    some { s₁ with totalSupply := s₁.totalSupply - amount }
  else none

end Model

/-! ## The storage writes of the compiled code -/

/-- `_update(src, dst, amount)` for nonzero `src`, `dst` (possibly equal): the sender's
balance, then the recipient's, re-read after the first write. -/
def moveWorld (crypto : Crypto) (L : Layout) (w : World) (token src dst : Address)
    (amount : Word) : World :=
  let sc := balanceSlot crypto L src
  let st := balanceSlot crypto L dst
  let w₁ := w.sstore token sc (w.sload token sc - amount)
  w₁.sstore token st (amount + w₁.sload token st)

theorem transferWorld_eq_moveWorld (crypto : Crypto) (w : World) (token caller to : Address)
    (amount : Word) :
    transferWorld crypto w token caller to amount =
      moveWorld crypto Layout.solmate w token caller to amount := rfl

/-- One `SSTORE` to `allowance[owner][spender]`. -/
def allowanceWorld (crypto : Crypto) (L : Layout) (w : World) (token owner spender : Address)
    (amount : Word) : World :=
  w.sstore token (allowanceSlot crypto L owner spender) amount

/-- The storage effect of `_spendAllowance` (when it does not revert). -/
def ozSpendWorld (crypto : Crypto) (L : Layout) (w : World) (token owner spender : Address)
    (amount : Word) : World :=
  let a := w.sload token (allowanceSlot crypto L owner spender)
  if a = maxWord then w else allowanceWorld crypto L w token owner spender (a - amount)

/-- The storage effect of `transferFrom(src, dst, amount)` from `spender`. -/
def ozTransferFromWorld (crypto : Crypto) (L : Layout) (w : World)
    (token spender src dst : Address) (amount : Word) : World :=
  moveWorld crypto L (ozSpendWorld crypto L w token src spender amount) token src dst amount

/-- `_mint(dst, amount)`: the supply, then the recipient's balance. -/
def mintWorld (crypto : Crypto) (L : Layout) (w : World) (token dst : Address) (amount : Word) :
    World :=
  let st := balanceSlot crypto L dst
  let w₁ := w.sstore token L.totalSupply (amount + w.sload token L.totalSupply)
  w₁.sstore token st (amount + w₁.sload token st)

/-- `_burn(src, amount)`: the sender's balance, then the supply. -/
def burnWorld (crypto : Crypto) (L : Layout) (w : World) (token src : Address) (amount : Word) :
    World :=
  let sc := balanceSlot crypto L src
  let w₁ := w.sstore token sc (w.sload token sc - amount)
  w₁.sstore token L.totalSupply (w₁.sload token L.totalSupply - amount)

/-! ## Worlds through the abstraction -/

variable {crypto : Crypto} {L : Layout} {w : World} {token : Address}

/-- `moveWorld` through the view is `Model.transfer`, for any layout (allowances pointwise,
for entries whose slot is not written). -/
theorem view_moveWorld {src dst : Address} {amount : Word} (hc : BalanceSlotOk crypto L src)
    (ht : BalanceSlotOk crypto L dst) {s' : State}
    (hm : Model.transfer (view crypto L w token) src dst amount = some s') :
    (view crypto L (moveWorld crypto L w token src dst amount) token).totalSupply =
        s'.totalSupply ∧
      (view crypto L (moveWorld crypto L w token src dst amount) token).balanceOf =
        s'.balanceOf ∧
      (∀ o s, allowanceSlot crypto L o s ≠ balanceSlot crypto L src →
        allowanceSlot crypto L o s ≠ balanceSlot crypto L dst →
        (view crypto L (moveWorld crypto L w token src dst amount) token).allowance o s =
          s'.allowance o s) ∧
      (∀ b k, b ≠ token → (moveWorld crypto L w token src dst amount).sload b k = w.sload b k) := by
  have hal := Model.transfer_allowance hm
  unfold Model.transfer at hm
  split at hm
  · cases hm
    obtain ⟨h1t, h1b, h1a⟩ := view_sstore_balanceSlot (w := w) (token := token) hc
      (w.sload token (balanceSlot crypto L src) - amount)
    obtain ⟨h2t, h2b, h2a⟩ := view_sstore_balanceSlot
      (w := w.sstore token (balanceSlot crypto L src)
        (w.sload token (balanceSlot crypto L src) - amount)) (token := token) ht
      (amount + (w.sstore token (balanceSlot crypto L src)
        (w.sload token (balanceSlot crypto L src) - amount)).sload token
          (balanceSlot crypto L dst))
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [moveWorld]
      rw [h2t, h1t]; rfl
    · simp only [moveWorld]
      rw [h2b]
      funext b
      have hb1 := congrFun h1b dst
      have hb2 := congrFun h1b b
      simp only [State.setBalance] at hb1 hb2 ⊢
      split
      · rename_i hbt
        subst hbt
        have : (w.sstore token (balanceSlot crypto L src)
            (w.sload token (balanceSlot crypto L src) - amount)).sload token
              (balanceSlot crypto L b) =
            (view crypto L (w.sstore token (balanceSlot crypto L src)
              (w.sload token (balanceSlot crypto L src) - amount)) token).balanceOf b := rfl
        rw [this, hb1, BitVec.add_comm]
        rfl
      · exact hb2
    · intro o s hoc hot
      simp only [moveWorld]
      rw [h2a, h1a]
      simp only [hot, hoc, ite_false, hal]
    · intro b k hb
      simp only [moveWorld]
      rw [World.sload_sstore_ne_addr _ _ _ _ hb, World.sload_sstore_ne_addr _ _ _ _ hb]
  · cases hm

/-- `allowanceWorld` through the view is `Model.approve` (allowances pointwise). -/
theorem view_allowanceWorld {owner spender : Address} {amount : Word}
    (h : AllowanceSlotOk crypto L owner spender) :
    let s := view crypto L w token
    let s' := view crypto L (allowanceWorld crypto L w token owner spender amount) token
    s'.totalSupply = (Model.approve s owner spender amount).totalSupply ∧
      s'.balanceOf = (Model.approve s owner spender amount).balanceOf ∧
      (∀ o sp, (o = owner ∧ sp = spender) ∨
          allowanceSlot crypto L o sp ≠ allowanceSlot crypto L owner spender →
        s'.allowance o sp = (Model.approve s owner spender amount).allowance o sp) ∧
      (∀ b k, b ≠ token →
        (allowanceWorld crypto L w token owner spender amount).sload b k = w.sload b k) := by
  obtain ⟨h1, h2, h3⟩ := view_sstore_allowanceSlot (w := w) (token := token) h amount
  refine ⟨h1, h2, ?_, ?_⟩
  · intro o sp hos
    simp only [allowanceWorld, h3, Model.approve, State.setAllowance]
    rcases hos with ⟨rfl, rfl⟩ | hne
    · simp
    · have : ¬ (o = owner ∧ sp = spender) := by rintro ⟨rfl, rfl⟩; exact hne rfl
      simp [hne, this]
  · intro b k hb
    exact World.sload_sstore_ne_addr _ _ _ _ hb

/-- `ozSpendWorld` through the view is `Model.ozSpend` (allowances pointwise). -/
theorem view_ozSpendWorld {owner spender : Address} {amount : Word} {s₁ : State}
    (h : AllowanceSlotOk crypto L owner spender)
    (hm : Model.ozSpend (view crypto L w token) owner spender amount = some s₁) :
    let s' := view crypto L (ozSpendWorld crypto L w token owner spender amount) token
    s'.totalSupply = s₁.totalSupply ∧ s'.balanceOf = s₁.balanceOf ∧
      (∀ o sp, (o = owner ∧ sp = spender) ∨
          allowanceSlot crypto L o sp ≠ allowanceSlot crypto L owner spender →
        s'.allowance o sp = s₁.allowance o sp) ∧
      (∀ b k, b ≠ token →
        (ozSpendWorld crypto L w token owner spender amount).sload b k = w.sload b k) := by
  unfold Model.ozSpend at hm
  simp only [ozSpendWorld]
  split
  · rename_i hmax
    have hmax' : (view crypto L w token).allowance owner spender = maxWord := hmax
    simp only [hmax', ↓reduceIte, Option.some.injEq] at hm
    subst hm
    exact ⟨rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  · rename_i hmax
    have hmax' : ¬ (view crypto L w token).allowance owner spender = maxWord := hmax
    simp only [hmax', ↓reduceIte] at hm
    split at hm
    · unfold Model.ozApprove at hm
      split at hm
      · cases hm
      · split at hm
        · cases hm
        · cases hm
          exact view_allowanceWorld h
    · cases hm

/-- `ozTransferFromWorld` through the view is `Model.ozTransferFrom` (allowances pointwise).
Needs `BalanceSlotOk` for `src`, `dst` and `AllowanceSlotOk` for `allowance[src][spender]`. -/
theorem view_ozTransferFromWorld {spender src dst : Address} {amount : Word} {s' : State}
    (hs : BalanceSlotOk crypto L src) (hd : BalanceSlotOk crypto L dst)
    (ha : AllowanceSlotOk crypto L src spender)
    (hm : Model.ozTransferFrom (view crypto L w token) spender src dst amount = some s') :
    let v := view crypto L (ozTransferFromWorld crypto L w token spender src dst amount) token
    v.totalSupply = s'.totalSupply ∧ v.balanceOf = s'.balanceOf ∧
      (∀ o sp, allowanceSlot crypto L o sp ≠ balanceSlot crypto L src →
        allowanceSlot crypto L o sp ≠ balanceSlot crypto L dst →
        (o = src ∧ sp = spender) ∨
          allowanceSlot crypto L o sp ≠ allowanceSlot crypto L src spender →
        v.allowance o sp = s'.allowance o sp) ∧
      (∀ b k, b ≠ token →
        (ozTransferFromWorld crypto L w token spender src dst amount).sload b k = w.sload b k) := by
  unfold Model.ozTransferFrom at hm
  obtain ⟨s₁, hs₁, ht⟩ := Option.bind_eq_some_iff.1 hm
  obtain ⟨e1, e2, e3, e4⟩ := view_ozSpendWorld (w := w) (token := token) ha hs₁
  unfold Model.ozTransfer at ht
  split at ht
  · cases ht
  split at ht
  · cases ht
  have ht' : Model.transfer (view crypto L (ozSpendWorld crypto L w token src spender amount)
      token) src dst amount =
      some { s' with allowance :=
        (view crypto L (ozSpendWorld crypto L w token src spender amount) token).allowance } := by
    unfold Model.transfer at ht ⊢
    have hb : (view crypto L (ozSpendWorld crypto L w token src spender amount)
        token).balanceOf = s₁.balanceOf := e2
    split at ht
    · rename_i hle
      rw [hb]
      simp only [hle, ↓reduceIte]
      cases ht
      simp only [State.setBalance, Option.some.injEq]
      rw [hb, e1]
    · cases ht
  obtain ⟨f1, f2, f3, f4⟩ := view_moveWorld
    (w := ozSpendWorld crypto L w token src spender amount) (token := token) hs hd ht'
  have hal := Model.transfer_allowance ht
  simp only [ozTransferFromWorld]
  refine ⟨f1, f2, ?_, fun b k hb => by rw [f4 b k hb, e4 b k hb]⟩
  intro o sp h1 h2 h3
  rw [f3 o sp h1 h2, hal, e3 o sp h3]

/-- `mintWorld` through the view is `Model.ozMint` (allowances pointwise, for entries in
neither written slot). Needs `BalanceSlotOk` for `dst` and `SupplySlotOk`. -/
theorem view_mintWorld {dst : Address} {amount : Word} {s' : State}
    (hd : BalanceSlotOk crypto L dst) (hk : SupplySlotOk crypto L)
    (hm : Model.ozMint (view crypto L w token) dst amount = some s') :
    let v := view crypto L (mintWorld crypto L w token dst amount) token
    v.totalSupply = s'.totalSupply ∧ v.balanceOf = s'.balanceOf ∧
      (∀ o sp, allowanceSlot crypto L o sp ≠ L.totalSupply →
        allowanceSlot crypto L o sp ≠ balanceSlot crypto L dst →
        v.allowance o sp = s'.allowance o sp) ∧
      (∀ b k, b ≠ token → (mintWorld crypto L w token dst amount).sload b k = w.sload b k) := by
  unfold Model.ozMint at hm
  split at hm
  · cases hm
  split at hm
  · cases hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (mintWorld crypto L w token dst amount).sload token L.totalSupply = _
      simp only [mintWorld]
      rw [World.sload_sstore_ne_key _ _ _ (fun e => hd.2 e.symm), World.sload_sstore_self]
      rfl
    · funext b
      show (mintWorld crypto L w token dst amount).sload token (balanceSlot crypto L b) = _
      simp only [mintWorld, State.setBalance]
      by_cases hb : b = dst
      · subst hb
        simp only [World.sload_sstore_self, ↓reduceIte]
        rw [World.sload_sstore_ne_key _ _ _ hd.2]
        rfl
      · simp only [hb, ↓reduceIte]
        rw [World.sload_sstore_ne_key _ _ _ (balanceSlot_ne hd hb),
          World.sload_sstore_ne_key _ _ _ (hk.balanceSlot_ne b)]
        rfl
    · intro o sp h1 h2
      show (mintWorld crypto L w token dst amount).sload token (allowanceSlot crypto L o sp) = _
      simp only [mintWorld]
      rw [World.sload_sstore_ne_key _ _ _ h2, World.sload_sstore_ne_key _ _ _ h1]
      rfl
    · intro b k hb
      simp only [mintWorld]
      rw [World.sload_sstore_ne_addr _ _ _ _ hb, World.sload_sstore_ne_addr _ _ _ _ hb]
  · cases hm

/-- `burnWorld` through the view is `Model.ozBurn` (allowances pointwise, for entries in
neither written slot). Needs `BalanceSlotOk` for `src` and `SupplySlotOk`. -/
theorem view_burnWorld {src : Address} {amount : Word} {s' : State}
    (hs : BalanceSlotOk crypto L src) (hk : SupplySlotOk crypto L)
    (hm : Model.ozBurn (view crypto L w token) src amount = some s') :
    let v := view crypto L (burnWorld crypto L w token src amount) token
    v.totalSupply = s'.totalSupply ∧ v.balanceOf = s'.balanceOf ∧
      (∀ o sp, allowanceSlot crypto L o sp ≠ L.totalSupply →
        allowanceSlot crypto L o sp ≠ balanceSlot crypto L src →
        v.allowance o sp = s'.allowance o sp) ∧
      (∀ b k, b ≠ token → (burnWorld crypto L w token src amount).sload b k = w.sload b k) := by
  unfold Model.ozBurn at hm
  split at hm
  · cases hm
  split at hm
  · cases hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (burnWorld crypto L w token src amount).sload token L.totalSupply = _
      simp only [burnWorld, World.sload_sstore_self]
      rw [World.sload_sstore_ne_key _ _ _ (fun e => hs.2 e.symm)]
      rfl
    · funext b
      show (burnWorld crypto L w token src amount).sload token (balanceSlot crypto L b) = _
      simp only [burnWorld, State.setBalance]
      rw [World.sload_sstore_ne_key _ _ _ (hk.balanceSlot_ne b)]
      by_cases hb : b = src
      · subst hb
        simp only [World.sload_sstore_self, ↓reduceIte]
        rfl
      · simp only [hb, ↓reduceIte]
        rw [World.sload_sstore_ne_key _ _ _ (balanceSlot_ne hs hb)]
        rfl
    · intro o sp h1 h2
      show (burnWorld crypto L w token src amount).sload token (allowanceSlot crypto L o sp) = _
      simp only [burnWorld]
      rw [World.sload_sstore_ne_key _ _ _ h1, World.sload_sstore_ne_key _ _ _ h2]
      rfl
    · intro b k hb
      simp only [burnWorld]
      rw [World.sload_sstore_ne_addr _ _ _ _ hb, World.sload_sstore_ne_addr _ _ _ _ hb]
  · cases hm

end EvmLogic.Solidity.ERC20

end
