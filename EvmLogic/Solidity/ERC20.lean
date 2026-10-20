import EvmLogic.Solidity.Keccak

/-!
# ERC-20 storage abstraction

`ERC20.view crypto L w token` reads `totalSupply`, `balanceOf` and `allowance` through a
storage `Layout`; reading needs no hypothesis. Writes need `BalanceSlotOk` / `AllowanceSlotOk`
(the written slot is fresh among address-keyed entries and is not the supply slot); effects on
nested-mapping entries are stated pointwise (see `EvmLogic.Solidity.Keccak`). `Model` is
Solmate's `transfer`/`approve`/`transferFrom`; `*World` are the compiled code's writes.
-/

section

namespace EvmLogic.Solidity.ERC20
open EvmLean

/-! ## Layout -/

/-- The storage slots of an ERC-20's state variables. -/
structure Layout where
  totalSupply : Word
  balances : Word
  allowances : Word

/-- Solmate's `ERC20`: `totalSupply` at 2, `balanceOf` at 3, `allowance` at 4. -/
def Layout.solmate : Layout := ⟨2, 3, 4⟩

/-- The slot of `balanceOf[a]`. -/
def balanceSlot (crypto : Crypto) (L : Layout) (a : Address) : Word :=
  mappingSlot crypto (Word.ofAddress a) L.balances

/-- The slot of `allowance[o][s]`. -/
def allowanceSlot (crypto : Crypto) (L : Layout) (o s : Address) : Word :=
  mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress s) L.allowances

/-! ## Abstract state -/

/-- The typed state of an ERC-20. -/
structure State where
  totalSupply : Word
  balanceOf : Address → Word
  allowance : Address → Address → Word

def State.setBalance (s : State) (a : Address) (v : Word) : State :=
  { s with balanceOf := fun b => if b = a then v else s.balanceOf b }

/-- The ERC-20 state of the contract at `token` in world `w`. -/
def view (crypto : Crypto) (L : Layout) (w : World) (token : Address) : State where
  totalSupply := w.sload token L.totalSupply
  balanceOf a := w.sload token (balanceSlot crypto L a)
  allowance o s := w.sload token (allowanceSlot crypto L o s)

/-! ## Non-collision hypotheses -/

/-- The single-level address-keyed preimages: `pad(a) ‖ balances`, `pad(a) ‖ allowances`. -/
def level1 (L : Layout) : ByteArray → Prop := AddressKeyed [L.balances, L.allowances]

/-- The balance slot of `a` is used by no other balance or allowance row and is not the
`totalSupply` slot (plausible: one target against `2¹⁶¹` candidates). -/
def BalanceSlotOk (crypto : Crypto) (L : Layout) (a : Address) : Prop :=
  KeccakFresh crypto (level1 L) (slotPreimage (Word.ofAddress a) L.balances) ∧
    balanceSlot crypto L a ≠ L.totalSupply

theorem balanceSlot_ne {crypto : Crypto} {L : Layout} {a b : Address}
    (h : BalanceSlotOk crypto L a) (hne : b ≠ a) : balanceSlot crypto L b ≠ balanceSlot crypto L a :=
  mappingSlot_ne_of_fresh_addr h.1 (by simp) (.inl hne)

/-! ## Reading after writing -/

/-- `SSTORE` at `a`'s balance slot through the view: `balanceOf` updated at `a` only; an
allowance entry changes only if its slot is the written one. -/
theorem view_sstore_balanceSlot {crypto : Crypto} {L : Layout} {w : World} {token a : Address}
    (h : BalanceSlotOk crypto L a) (v : Word) :
    (view crypto L (w.sstore token (balanceSlot crypto L a) v) token).totalSupply =
        (view crypto L w token).totalSupply ∧
      (view crypto L (w.sstore token (balanceSlot crypto L a) v) token).balanceOf =
        ((view crypto L w token).setBalance a v).balanceOf ∧
      ∀ o s, (view crypto L (w.sstore token (balanceSlot crypto L a) v) token).allowance o s =
        if allowanceSlot crypto L o s = balanceSlot crypto L a then v
        else (view crypto L w token).allowance o s := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [view]
    exact World.sload_sstore_ne_key _ _ _ (fun e => h.2 e.symm)
  · funext b
    simp only [view, State.setBalance]
    by_cases hb : b = a
    · subst hb; simp
    · simp only [hb, ite_false]
      exact World.sload_sstore_ne_key _ _ _ (balanceSlot_ne h hb)
  · intro o s
    simp only [view]
    split
    · rename_i he; rw [he]; simp
    · rename_i he; exact World.sload_sstore_ne_key _ _ _ he

theorem view_sstore_ne {crypto : Crypto} {L : Layout} {w : World} {token b : Address}
    (hb : token ≠ b) (k v : Word) :
    view crypto L (w.sstore b k v) token = view crypto L w token := by
  simp only [view, World.sload_sstore_ne_addr _ _ _ _ hb]

/-! ## The abstract semantics -/

namespace Model
open EvmLean

/-- Solmate's `transfer` from `caller`: checked subtraction (`none` = revert), then an
unchecked add to the recipient's *updated* balance. -/
def transfer (s : State) (caller to : Address) (amount : Word) : Option State :=
  if amount.toNat ≤ (s.balanceOf caller).toNat then
    let s₁ := s.setBalance caller (s.balanceOf caller - amount)
    some (s₁.setBalance to (s₁.balanceOf to + amount))
  else none

theorem transfer_totalSupply {s s' : State} {caller to : Address} {amount : Word}
    (h : transfer s caller to amount = some s') : s'.totalSupply = s.totalSupply := by
  unfold transfer at h
  split at h
  · cases h; rfl
  · cases h

theorem transfer_allowance {s s' : State} {caller to : Address} {amount : Word}
    (h : transfer s caller to amount = some s') : s'.allowance = s.allowance := by
  unfold transfer at h
  split at h
  · cases h; rfl
  · cases h

theorem transfer_balanceOf {s s' : State} {caller to : Address} {amount : Word}
    (h : transfer s caller to amount = some s') (hne : to ≠ caller) (b : Address) :
    s'.balanceOf b = if b = caller then s.balanceOf caller - amount
      else if b = to then s.balanceOf to + amount else s.balanceOf b := by
  unfold transfer at h
  split at h
  · cases h
    simp only [State.setBalance]
    by_cases hb : b = to
    · subst hb; simp [hne]
    · by_cases hc : b = caller
      · subst hc; simp [hb]
      · simp [hb, hc]
  · cases h

end Model

/-! ## The storage writes of `transfer` -/

/-- The storage writes of a successful `transfer`, in the code's order. -/
def transferWorld (crypto : Crypto) (w : World) (token caller to : Address) (amount : Word) :
    World :=
  let sc := balanceSlot crypto Layout.solmate caller
  let st := balanceSlot crypto Layout.solmate to
  let w₁ := w.sstore token sc (w.sload token sc - amount)
  w₁.sstore token st (amount + w₁.sload token st)

section

variable {w : World} {token caller to : Address} {amount : Word}

/-- `transferWorld` through the view is `Model.transfer` (allowances pointwise, for entries
whose slot is not written). Needs `BalanceSlotOk` for `caller` and `to` only. -/
theorem view_transferWorld {crypto : Crypto} (hc : BalanceSlotOk crypto Layout.solmate caller)
    (ht : BalanceSlotOk crypto Layout.solmate to) {s' : State}
    (hm : Model.transfer (view crypto Layout.solmate w token) caller to amount = some s') :
    (view crypto Layout.solmate (transferWorld crypto w token caller to amount) token).totalSupply =
        s'.totalSupply ∧
      (view crypto Layout.solmate (transferWorld crypto w token caller to amount) token).balanceOf =
        s'.balanceOf ∧
      (∀ o s, allowanceSlot crypto Layout.solmate o s ≠ balanceSlot crypto Layout.solmate caller →
        allowanceSlot crypto Layout.solmate o s ≠ balanceSlot crypto Layout.solmate to →
        (view crypto Layout.solmate (transferWorld crypto w token caller to amount) token).allowance
          o s = s'.allowance o s) ∧
      (∀ b k, b ≠ token → (transferWorld crypto w token caller to amount).sload b k = w.sload b k) := by
  have hts := Model.transfer_totalSupply hm
  have hal := Model.transfer_allowance hm
  unfold Model.transfer at hm
  split at hm
  · cases hm
    obtain ⟨h1t, h1b, h1a⟩ := view_sstore_balanceSlot (w := w) (token := token) hc
      (w.sload token (balanceSlot crypto Layout.solmate caller) - amount)
    obtain ⟨h2t, h2b, h2a⟩ := view_sstore_balanceSlot
      (w := w.sstore token (balanceSlot crypto Layout.solmate caller)
        (w.sload token (balanceSlot crypto Layout.solmate caller) - amount)) (token := token) ht
      (amount + (w.sstore token (balanceSlot crypto Layout.solmate caller)
        (w.sload token (balanceSlot crypto Layout.solmate caller) - amount)).sload token
          (balanceSlot crypto Layout.solmate to))
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [transferWorld]
      rw [h2t, h1t]; rfl
    · simp only [transferWorld]
      rw [h2b]
      funext b
      have hb1 := congrFun h1b to
      have hb2 := congrFun h1b b
      simp only [State.setBalance] at hb1 hb2 ⊢
      split
      · rename_i hbt
        subst hbt
        have : (w.sstore token (balanceSlot crypto Layout.solmate caller)
            (w.sload token (balanceSlot crypto Layout.solmate caller) - amount)).sload token
              (balanceSlot crypto Layout.solmate b) =
            (view crypto Layout.solmate (w.sstore token (balanceSlot crypto Layout.solmate caller)
              (w.sload token (balanceSlot crypto Layout.solmate caller) - amount)) token).balanceOf
                b := rfl
        rw [this, hb1, BitVec.add_comm]
        rfl
      · exact hb2
    · intro o s hoc hot
      simp only [transferWorld]
      rw [h2a, h1a]
      simp only [hot, hoc, ite_false, hal]
    · intro b k hb
      simp only [transferWorld]
      rw [World.sload_sstore_ne_addr _ _ _ _ hb, World.sload_sstore_ne_addr _ _ _ _ hb]
  · cases hm

end

end EvmLogic.Solidity.ERC20

end

section

/-! ## Solmate `ERC20`: `approve` and `transferFrom` -/

namespace EvmLogic.Solidity.ERC20
open EvmLean EvmLean.Interpreter

/-- `type(uint256).max`, the "infinite" allowance (`PUSH0 NOT` in the bytecode). -/
def maxWord : Word := ~~~0#256

theorem eq_maxWord_of_eq {a : Word} (h : a = maxWord) : Word.eq a (~~~0#256) = 1#256 := by
  subst h; simp [Word.eq, Word.ofBool, maxWord]

theorem eq_maxWord_of_ne {a : Word} (h : a ≠ maxWord) : Word.eq a (~~~0#256) = 0#256 := by
  have h' : (a == ~~~0#256) = false := beq_eq_false_iff_ne.mpr h
  rw [Word.eq, Word.ofBool, h']; rfl

def State.setAllowance (s : State) (o sp : Address) (v : Word) : State :=
  { s with allowance := fun o' sp' => if o' = o ∧ sp' = sp then v else s.allowance o' sp' }

/-! ## Non-collision for an allowance entry -/

/-- The slot of `allowance[o][sp]` is no balance slot and not `totalSupply`: freshness among
single-level address-keyed preimages (plausible), and the inner row slot is not `balances`. -/
def AllowanceSlotOk (crypto : Crypto) (L : Layout) (o sp : Address) : Prop :=
  KeccakFresh crypto (level1 L)
      (slotPreimage (Word.ofAddress sp) (mappingSlot crypto (Word.ofAddress o) L.allowances)) ∧
    mappingSlot crypto (Word.ofAddress o) L.allowances ≠ L.balances ∧
    allowanceSlot crypto L o sp ≠ L.totalSupply

theorem balanceSlot_ne_allowanceSlot {crypto : Crypto} {L : Layout} {o sp : Address}
    (h : AllowanceSlotOk crypto L o sp) (a : Address) :
    balanceSlot crypto L a ≠ allowanceSlot crypto L o sp :=
  mappingSlot_ne_of_fresh h.1 ⟨a, L.balances, by simp, rfl⟩ (.inr h.2.1.symm)

/-- `SSTORE` at `allowance[o][sp]` through the view: balances and supply unchanged; an
allowance entry changes only if its slot is the written one. -/
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
open EvmLean

/-- Solmate's `approve(spender, amount)` from `owner`. -/
def approve (s : State) (owner spender : Address) (amount : Word) : State :=
  s.setAllowance owner spender amount

/-- The allowance step of `transferFrom`: nothing on an infinite allowance, otherwise a
checked subtraction. -/
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

/-- The storage effect of `approve`: one `SSTORE` to `allowance[owner][spender]`. -/
def approveWorld (crypto : Crypto) (w : World) (token owner spender : Address) (amount : Word) :
    World :=
  w.sstore token (allowanceSlot crypto Layout.solmate owner spender) amount

/-- The storage effect of the allowance step of `transferFrom`. -/
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

/-- `approveWorld` through the view is `Model.approve` (allowances pointwise). Needs
`AllowanceSlotOk` for the written entry only. -/
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

/-- `spendWorld` through the view is `Model.spend` (allowances pointwise). -/
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

/-- `transferFromWorld` through the view is `Model.transferFrom` (allowances pointwise).
Needs `BalanceSlotOk` for `src`, `dst` and `AllowanceSlotOk` for `allowance[src][spender]`. -/
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
  obtain ⟨f1, f2, f3, f4⟩ := view_transferWorld (w := spendWorld crypto w token src spender amount)
    (token := token) hs hd ht'
  have hal := Model.transfer_allowance ht
  simp only [transferFromWorld]
  refine ⟨f1, f2, ?_, fun b k hb => by rw [f4 b k hb, e4 b k hb]⟩
  intro o sp h1 h2 h3
  rw [f3 o sp h1 h2, hal, e3 o sp h3]

end EvmLogic.Solidity.ERC20

end
