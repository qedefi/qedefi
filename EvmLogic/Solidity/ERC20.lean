import EvmLogic.Solidity.Keccak

/-!
# ERC-20 storage abstraction

The typed view of an ERC-20's storage (`Erc20.State`: `totalSupply`, `balanceOf`,
`allowance`) read through its storage layout (`Erc20.Layout`: the slots of `totalSupply`,
`balanceOf` and `allowance` from `--storage-layout`; `Layout.solmate` for Solmate's `ERC20`,
whose `name`/`symbol` occupy slots 0–1).

`Erc20.view crypto L w token` is total and needs no hypothesis: it just reads slots. What
needs hypotheses is the *effect of writes*: `view_sstore_balanceSlot` says that `SSTORE` at
the balance slot of `a` updates the abstract `balanceOf` pointwise at `a` and keeps
`totalSupply`, provided `BalanceSlotOk` (the slot of `a` is fresh among all address-keyed
entries of `balanceOf` and of the outer `allowance` mapping, and is not the `totalSupply`
slot; plausible, see `EvmLeanProofs.Solidity.Keccak`). Its effect on `allowance` is stated
pointwise and without hypothesis: an entry changes only if its slot *is* the written slot.

`Erc20.Model` is the abstract semantics of Solmate's functions (here `transfer`), the
specification the compiled code is proved against in `Examples/Erc20Transfer`.
-/

namespace EvmLean.Solidity.Erc20

/-! ## Layout -/

/-- The storage slots of an ERC-20's state variables. -/
structure Layout where
  /-- Slot of `uint256 totalSupply`. -/
  totalSupply : Word
  /-- Slot of `mapping(address => uint256) balanceOf`. -/
  balances : Word
  /-- Slot of `mapping(address => mapping(address => uint256)) allowance`. -/
  allowances : Word

/-- Solmate's `ERC20` (and the `Token` example): `totalSupply` at 2, `balanceOf` at 3,
`allowance` at 4. -/
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
  /-- `totalSupply`. -/
  totalSupply : Word
  /-- `balanceOf`. -/
  balanceOf : Address → Word
  /-- `allowance`. -/
  allowance : Address → Address → Word

/-- Update one balance. -/
def State.setBalance (s : State) (a : Address) (v : Word) : State :=
  { s with balanceOf := fun b => if b = a then v else s.balanceOf b }

/-- The ERC-20 state of the contract at `token` in world `w`. -/
def view (crypto : Crypto) (L : Layout) (w : World) (token : Address) : State where
  totalSupply := w.sload token L.totalSupply
  balanceOf a := w.sload token (balanceSlot crypto L a)
  allowance o s := w.sload token (allowanceSlot crypto L o s)

/-! ## Non-collision hypotheses -/

/-- The single-level address-keyed preimages of the layout: `pad(a) ‖ balances` and
`pad(a) ‖ allowances` for every address `a` (`2¹⁶¹` preimages). -/
def level1 (L : Layout) : ByteArray → Prop := AddressKeyed [L.balances, L.allowances]

/-- The balance slot of `a` is used by no other balance or allowance row (for any address)
and is not the `totalSupply` slot. A plausible assumption on the hash (one target against
`2¹⁶¹` candidates). -/
def BalanceSlotOk (crypto : Crypto) (L : Layout) (a : Address) : Prop :=
  KeccakFresh crypto (level1 L) (slotPreimage (Word.ofAddress a) L.balances) ∧
    balanceSlot crypto L a ≠ L.totalSupply

/-- Under `BalanceSlotOk`, distinct addresses have distinct balance slots. -/
theorem balanceSlot_ne {crypto : Crypto} {L : Layout} {a b : Address}
    (h : BalanceSlotOk crypto L a) (hne : b ≠ a) : balanceSlot crypto L b ≠ balanceSlot crypto L a :=
  mappingSlot_ne_of_fresh_addr h.1 (by simp) (.inl hne)

/-! ## Reading after writing -/

/-- `SSTORE` at the balance slot of `a`, seen through the abstraction: `totalSupply` is
unchanged, `balanceOf` is updated at `a` only, and an allowance entry changes only if its slot
is the written one. -/
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

/-- `SSTORE` to another account does not change the view. -/
theorem view_sstore_ne {crypto : Crypto} {L : Layout} {w : World} {token b : Address}
    (hb : token ≠ b) (k v : Word) :
    view crypto L (w.sstore b k v) token = view crypto L w token := by
  simp only [view, World.sload_sstore_ne_addr _ _ _ _ hb]

/-! ## The abstract semantics -/

namespace Model

/-- Solmate's `transfer(to, amount)` from `caller`: revert (`none`) if the balance is
insufficient (checked subtraction), otherwise subtract from the caller, then add to the
recipient's *updated* balance (unchecked; a self-transfer changes nothing). -/
def transfer (s : State) (caller to : Address) (amount : Word) : Option State :=
  if amount.toNat ≤ (s.balanceOf caller).toNat then
    let s₁ := s.setBalance caller (s.balanceOf caller - amount)
    some (s₁.setBalance to (s₁.balanceOf to + amount))
  else none

/-- `transfer` preserves `totalSupply`. -/
theorem transfer_totalSupply {s s' : State} {caller to : Address} {amount : Word}
    (h : transfer s caller to amount = some s') : s'.totalSupply = s.totalSupply := by
  unfold transfer at h
  split at h
  · cases h; rfl
  · cases h

/-- `transfer` preserves allowances. -/
theorem transfer_allowance {s s' : State} {caller to : Address} {amount : Word}
    (h : transfer s caller to amount = some s') : s'.allowance = s.allowance := by
  unfold transfer at h
  split at h
  · cases h; rfl
  · cases h

/-- `transfer` between distinct accounts moves `amount` from `caller` to `to` and changes no
other balance. -/
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

/-- The world after a successful `transfer`: `balanceOf[caller] -= amount`, then
`balanceOf[to] += amount` (reading the updated storage), in the order the code does it. -/
def transferWorld (crypto : Crypto) (w : World) (token caller to : Address) (amount : Word) :
    World :=
  let sc := balanceSlot crypto Layout.solmate caller
  let st := balanceSlot crypto Layout.solmate to
  let w₁ := w.sstore token sc (w.sload token sc - amount)
  w₁.sstore token st (amount + w₁.sload token st)

section

variable {w : World} {token caller to : Address} {amount : Word}

/-- `transferWorld` through the abstraction: exactly `Model.transfer`'s balances and total
supply; allowances unchanged unless their slot is one of the two written slots; other
accounts untouched. Needs `BalanceSlotOk` for `caller` and `to` only. -/
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
    -- the two writes
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

end EvmLean.Solidity.Erc20
