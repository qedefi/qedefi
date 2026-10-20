import EvmLogic.Tactic.EvmStep
import EvmLogic.Step.Basic

/-!
# A verified token transfer

A hand-assembled token with a single `transfer(to, amount)` entry point, verified for every
`Crypto`, context, world and caller, with symbolic arguments, balances, gas and warm sets.
The balance of `a` is in slot `Word.ofAddress a` (no hashing, so no collision hypothesis).
-/

namespace Examples.Basic.Token
open EvmLean EvmLean.Bytes EvmLean.Interpreter EvmLogic

/-- Calldata `to ‖ amount`; reverts if `balance[caller] < amount`, else
`balance[caller] -= amount; balance[to] += amount` (wrapping). -/
def code : ByteArray := ⟨#[
  0x60, 0x20, 0x35, 0x33, 0x54, 0x81, 0x81, 0x10, 0x60, 0x19, 0x57,
  0x03, 0x33, 0x55,
  0x5f, 0x35, 0x80, 0x54, 0x60, 0x20, 0x35, 0x01, 0x90, 0x55, 0x00,
  0x5b, 0x5f, 0x80, 0xfd]⟩

/-- The storage slot holding the balance of `a`. -/
def slot (a : Address) : Word := Word.ofAddress a

/-- The balance of `a` in the token deployed at `token`. -/
def balanceOf (w : World) (token a : Address) : Word := w.sload token (slot a)

/-- Calldata of `transfer(to, amount)`. -/
def calldata (to : Address) (amount : Word) : ByteArray :=
  Bytes.ofWord (Word.ofAddress to) ++ Bytes.ofWord amount

/-- A top-level call of `transfer(to, amount)` on the token at `token`. -/
def transferCall (token caller to : Address) (amount : Word) (gas : Nat)
    (warmAddrs : AddressSet) (warmKeys : StorageKeySet) : Message where
  caller := caller
  target := some token
  currentTarget := token
  gas := gas
  value := 0
  data := calldata to amount
  codeAddress := some token
  code := code
  depth := 0
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := warmAddrs
  accessedStorageKeys := warmKeys

def start (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message) : Machine where
  ctx := ctx
  precompiles := PrecompileImpl.standard ctx
  world := w
  transient := tr
  originalWorld := w
  createdAccounts := ∅
  frame := Frame.init msg (.call 0 0) (w, tr)
  parents := []

theorem delegatedAddress?_code : delegatedAddress? code = none := by decide

theorem processMessageCall_transfer {ctx : Context} {w : World} {tr : TransientStorage}
    {token caller to : Address} {amount : Word} {gas : Nat} {warmAddrs : AddressSet}
    {warmKeys : StorageKeySet} (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (fuel : Nat) :
    processMessageCall fuel ctx w tr (transferCall token caller to amount gas warmAddrs warmKeys) =
      run fuel (start ctx w tr (transferCall token caller to amount gas warmAddrs warmKeys)) :=
  processMessageCall_eq_run hdeleg delegatedAddress?_code
    (initMachine_call rfl rfl hpre rfl rfl) fuel

theorem calldata_to (to : Address) (amount : Word) :
    Bytes.toWord (readBytes (calldata to amount) 0 32) = Word.ofAddress to :=
  toWord_readBytes_ofWord_append_left _ _

theorem calldata_amount (to : Address) (amount : Word) :
    Bytes.toWord (readBytes (calldata to amount) 32 32) = amount :=
  toWord_readBytes_ofWord_append_right _ _

theorem slot_injective {a b : Address} (h : slot a = slot b) : a = b := by
  simp only [slot, Word.ofAddress] at h
  have := congrArg (BitVec.setWidth 160) h
  simpa using this

variable {ctx : Context} {w : World} {tr : TransientStorage} {token caller to : Address}
  {amount : Word} {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

/-- The world after a successful transfer. -/
def transferWorld (w : World) (token caller to : Address) (amount : Word) : World :=
  let w₁ := w.sstore token (slot caller) (balanceOf w token caller - amount)
  w₁.sstore token (slot to) (amount + balanceOf w₁ token to)

theorem transfer_ok (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false)
    (hgas : 50000 ≤ gas) (hbal : amount.toNat ≤ (balanceOf w token caller).toNat) (k : Nat) :
    ∃ r, processMessageCall (k + 22) ctx w tr
        (transferCall token caller to amount gas warmAddrs warmKeys) = .ok r ∧
      r.success = true ∧ r.world = transferWorld w token caller to amount := by
  rw [processMessageCall_transfer hdeleg hpre]
  simp only [start, Frame.init, transferCall]
  evm_steps [calldata_to, calldata_amount]
  have hlt : Word.lt (w.sload token (Word.ofAddress caller)) amount = 0 := by
    simp only [balanceOf, slot] at hbal
    simp only [Word.lt, Word.ofBool, BitVec.ult, decide_eq_true_eq]
    simp [Nat.not_lt.mpr hbal]
  simp only [hlt]
  evm_steps [calldata_to, calldata_amount]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp [ChildResult.success]
  · simp only [topLevelResult_world, transferWorld, balanceOf, slot]

theorem transfer_revert (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false)
    (hgas : 50000 ≤ gas) (hbal : (balanceOf w token caller).toNat < amount.toNat) (k : Nat) :
    ∃ r, processMessageCall (k + 15) ctx w tr
        (transferCall token caller to amount gas warmAddrs warmKeys) = .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  rw [processMessageCall_transfer hdeleg hpre]
  simp only [start, Frame.init, transferCall]
  evm_steps [calldata_to, calldata_amount]
  have hlt : Word.lt (w.sload token (Word.ofAddress caller)) amount = 1 := by
    simp only [balanceOf, slot] at hbal
    simp only [Word.lt, Word.ofBool, BitVec.ult, decide_eq_true_eq]
    simp [hbal]
  simp only [hlt]
  evm_steps [calldata_to, calldata_amount]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp [ChildResult.success]
  · simp
  · simp

/-! ## The balances after a transfer -/

theorem slot_ne {a b : Address} (h : a ≠ b) : slot a ≠ slot b := fun e => h (slot_injective e)

theorem balanceOf_transferWorld (w : World) (token caller to : Address) (amount : Word)
    (a : Address) :
    balanceOf (transferWorld w token caller to amount) token a =
      if a = to then amount + (if to = caller then balanceOf w token caller - amount
        else balanceOf w token to)
      else if a = caller then balanceOf w token caller - amount
      else balanceOf w token a := by
  simp only [transferWorld, balanceOf, World.sload_sstore, true_and]
  by_cases hto : a = to
  · subst hto
    simp only [ite_true]
    by_cases hc : a = caller
    · subst hc; simp
    · simp [slot_ne hc, hc]
  · by_cases hc : a = caller
    · subst hc; simp [slot_ne hto, hto]
    · simp [slot_ne hto, slot_ne hc, hto, hc]

theorem balanceOf_transferWorld_caller {w : World} {token caller to : Address} {amount : Word}
    (hne : to ≠ caller) :
    balanceOf (transferWorld w token caller to amount) token caller =
      balanceOf w token caller - amount := by
  have hne' : caller ≠ to := fun h => hne h.symm
  rw [balanceOf_transferWorld]
  simp only [hne', ite_false, ite_true]

theorem balanceOf_transferWorld_to {w : World} {token caller to : Address} {amount : Word}
    (hne : to ≠ caller) :
    balanceOf (transferWorld w token caller to amount) token to =
      balanceOf w token to + amount := by
  rw [balanceOf_transferWorld]
  simp only [ite_true, hne, ite_false]
  exact BitVec.add_comm _ _

theorem balanceOf_transferWorld_of_ne {w : World} {token caller to a : Address} {amount : Word}
    (hc : a ≠ caller) (ht : a ≠ to) :
    balanceOf (transferWorld w token caller to amount) token a = balanceOf w token a := by
  rw [balanceOf_transferWorld]
  simp [hc, ht]

theorem balanceOf_transferWorld_self {w : World} {token caller : Address} {amount : Word} :
    balanceOf (transferWorld w token caller caller amount) token caller =
      balanceOf w token caller := by
  rw [balanceOf_transferWorld]
  simp only [ite_true]
  bv_omega

theorem sload_transferWorld_of_ne {w : World} {token caller to b : Address} {amount : Word}
    (hb : b ≠ token) (k : Word) :
    (transferWorld w token caller to amount).sload b k = w.sload b k := by
  simp [transferWorld, World.sload_sstore, hb]

theorem balanceOf_add_balanceOf_transferWorld (w : World) (token caller to : Address)
    (amount : Word) :
    balanceOf (transferWorld w token caller to amount) token caller +
        balanceOf (transferWorld w token caller to amount) token to =
      balanceOf w token caller + balanceOf w token to := by
  by_cases hne : to = caller
  · subst hne
    rw [balanceOf_transferWorld_self]
  · rw [balanceOf_transferWorld_caller hne, balanceOf_transferWorld_to hne]
    bv_omega

theorem toNat_balanceOf_transferWorld_caller {w : World} {token caller to : Address}
    {amount : Word} (hne : to ≠ caller)
    (hbal : amount.toNat ≤ (balanceOf w token caller).toNat) :
    (balanceOf (transferWorld w token caller to amount) token caller).toNat =
      (balanceOf w token caller).toNat - amount.toNat := by
  rw [balanceOf_transferWorld_caller hne, BitVec.toNat_sub_of_le]
  exact BitVec.le_def.mpr hbal

/-! ## Specification -/

/-- **`transfer` meets its specification** (for `to ≠ caller`, gas ≥ 50 000): if affordable it
succeeds, moving `amount` from caller to `to` and changing nothing else; otherwise it reverts
and the world is unchanged. -/
theorem transfer_spec (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false)
    (hgas : 50000 ≤ gas) (hne : to ≠ caller) (fuel : Nat) (hfuel : 22 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (transferCall token caller to amount gas warmAddrs warmKeys) = .ok r ∧
      if amount.toNat ≤ (balanceOf w token caller).toNat then
        r.success = true ∧
        (balanceOf r.world token caller).toNat =
          (balanceOf w token caller).toNat - amount.toNat ∧
        balanceOf r.world token caller = balanceOf w token caller - amount ∧
        balanceOf r.world token to = balanceOf w token to + amount ∧
        balanceOf r.world token caller + balanceOf r.world token to =
          balanceOf w token caller + balanceOf w token to ∧
        (∀ a, a ≠ caller → a ≠ to → balanceOf r.world token a = balanceOf w token a) ∧
        (∀ b k, b ≠ token → r.world.sload b k = w.sload b k)
      else
        r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 22 := ⟨fuel - 22, by omega⟩
  split
  · rename_i hbal
    obtain ⟨r, hr, hs, hw⟩ := transfer_ok (tr := tr) (to := to) (warmAddrs := warmAddrs)
      (warmKeys := warmKeys) hdeleg hpre hgas hbal k
    refine ⟨r, hr, hs, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hw]
    · exact toNat_balanceOf_transferWorld_caller hne hbal
    · exact balanceOf_transferWorld_caller hne
    · exact balanceOf_transferWorld_to hne
    · exact balanceOf_add_balanceOf_transferWorld w token caller to amount
    · exact fun a hc ht => balanceOf_transferWorld_of_ne hc ht
    · exact fun b k hb => sload_transferWorld_of_ne hb k
  · rename_i hbal
    obtain ⟨r, hr, h⟩ := transfer_revert (tr := tr) (to := to) (warmAddrs := warmAddrs)
      (warmKeys := warmKeys) hdeleg hpre hgas (Nat.lt_of_not_le hbal) (k + 7)
    exact ⟨r, hr, h⟩

theorem isPrecompile_cancun_of_lt {a : Address} (h : 0x0a < a.toNat) :
    Precompile.isPrecompile .cancun a = false := by
  simp only [Precompile.isPrecompile, Precompile.ofAddress, Precompile.cancunOfNat]
  split <;> first | rfl | omega

/-- `transfer_spec` for a Cancun context and a token deployed above the precompiles. -/
theorem transfer_spec_cancun (hfork : ctx.fork = .cancun) (htoken : 0x0a < token.toNat)
    (hgas : 50000 ≤ gas) (hne : to ≠ caller) (fuel : Nat) (hfuel : 22 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (transferCall token caller to amount gas warmAddrs warmKeys) = .ok r ∧
      if amount.toNat ≤ (balanceOf w token caller).toNat then
        r.success = true ∧
        (balanceOf r.world token caller).toNat =
          (balanceOf w token caller).toNat - amount.toNat ∧
        balanceOf r.world token caller = balanceOf w token caller - amount ∧
        balanceOf r.world token to = balanceOf w token to + amount ∧
        balanceOf r.world token caller + balanceOf r.world token to =
          balanceOf w token caller + balanceOf w token to ∧
        (∀ a, a ≠ caller → a ≠ to → balanceOf r.world token a = balanceOf w token a) ∧
        (∀ b k, b ≠ token → r.world.sload b k = w.sload b k)
      else
        r.success = false ∧ r.reverted = true ∧ r.world = w :=
  transfer_spec (.inl (by rw [hfork]; decide)) (hfork ▸ isPrecompile_cancun_of_lt htoken) hgas
    hne fuel hfuel

end Examples.Basic.Token
