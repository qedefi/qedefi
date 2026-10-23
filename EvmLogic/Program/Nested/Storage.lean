import EvmLogic.Program.Nested.Frame
import EvmLogic.Program.Nested.Gas
import EvmLogic.State

/-!
# Which storage an instruction writes

`exec_slot`: an instruction other than `SSTORE` keeps every slot of every account holding code
(value transfers and nonce increments touch balances and nonces only). `exec_sstore_world`: an
`SSTORE` writes the slot on top of the stack, at the executing account, with the value below it.
Together they let a frame invariant that knows which `SSTORE`s a frame can reach show that a
protected slot is kept.
-/

section

namespace EvmLogic.Program.Nested
open EvmLean EvmLogic.Program EvmLean.Interpreter

/-- Postcondition: slot `κ` of `p` is unchanged, if `p` holds code. -/
abbrev SlotPost (p : Address) (κ : Word) (m : Machine) (_ : Action) (m' : Machine) : Prop :=
  (m.world.code p).size ≠ 0 → m'.world.sload p κ = m.world.sload p κ

theorem Keep.sload' {p : Address} {w w' : World} (h : Keep p w w') (k : Word) :
    w'.sload p k = w.sload p k := by
  unfold World.sload; rw [h.1]

theorem sload_incrementNonce {w : World} {a p : Address} {k : Word} (hp : (w.code p).size ≠ 0) :
    (incrementNonce w a).sload p k = w.sload p k := (keep_incrementNonce hp).sload' k

set_option maxHeartbeats 1000000 in
theorem execCall_slot (k : CallKind) (m : Machine) (p : Address) (κ : Word) :
    Wp (execCall k) (SlotPost p κ m) m := by
  cases k <;> simp [SlotPost, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall]

set_option maxHeartbeats 1000000 in
theorem execCreate_slot (b : Bool) (m : Machine) (p : Address) (κ : Word) :
    Wp (execCreate b) (SlotPost p κ m) m := by
  cases b <;> simp [SlotPost, execCreate, requireNonStatic, memoryExpansion, expandMemory,
    readMemory, setReturnData] <;> intros <;> simp_all [sload_incrementNonce]

set_option maxHeartbeats 4000000 in
/-- **No instruction but `SSTORE` writes the storage of an account holding code.** -/
theorem exec_slot (op : Opcode) (hop : op ≠ .sstore) (m : Machine) (p : Address) (κ : Word) :
    Wp (exec op) (SlotPost p κ m) m := by
  cases op
  case sstore => exact absurd rfl hop
  case create => exact execCreate_slot false m p κ
  case create2 => exact execCreate_slot true m p κ
  case call => exact execCall_slot .call m p κ
  case callcode => exact execCall_slot .callcode m p κ
  case delegatecall => exact execCall_slot .delegatecall m p κ
  case staticcall => exact execCall_slot .staticcall m p κ
  all_goals simp [SlotPost, exec, binOp, unOp, ternOp, pushValue, copyToMemory,
    readOutput, execLog, memoryExpansion, expandMemory, writeMemory, readMemory,
    accessStorageKey, requireNonStatic, execSelfdestruct, wp_popN']
  case dup => intro _; split <;> simp [SlotPost]
  case swap => intro _; split <;> simp [SlotPost]
  case selfdestruct =>
    intro x _ _ _ _
    have hm : ∀ hp : ¬ m.world.code p = ByteArray.empty, Keep p m.world
        (moveEther m.world m.frame.msg.currentTarget (Word.toAddress x)
          (m.world.balance m.frame.msg.currentTarget)) :=
      fun hp => keep_moveEther (size_ne_zero_of_ne_empty hp)
    have hs : ∀ hp : ¬ m.world.code p = ByteArray.empty, Keep p m.world
        (setAccountBalance (moveEther m.world m.frame.msg.currentTarget (Word.toAddress x)
          (m.world.balance m.frame.msg.currentTarget)) m.frame.msg.currentTarget 0) :=
      fun hp => (hm hp).trans (keep_setAccountBalance (by
        rw [(hm hp).code]; exact size_ne_zero_of_ne_empty hp))
    exact ⟨fun _ => ⟨fun _ hp => (hs hp).sload' κ, fun _ hp => (hs hp).sload' κ⟩,
      fun _ => ⟨fun _ hp => (hm hp).sload' κ, fun _ hp => (hm hp).sload' κ⟩⟩

set_option maxHeartbeats 1000000 in
/-- **`SSTORE` writes one slot**: the key on top of the stack, at the executing account. -/
theorem exec_sstore_world (m : Machine) :
    Wp (exec .sstore) (fun _ m' => ∃ k v r, m.frame.stack = k :: v :: r ∧
      m'.world = m.world.sstore m.frame.msg.currentTarget k v) m := by
  simp [exec, execSstore, accessStorageKey, requireNonStatic, setStorage]
  intro k xs hk v r hr _
  subst hr
  exact ⟨fun _ _ _ => ⟨k, v, ⟨r, hk⟩, rfl⟩, fun _ _ _ => ⟨k, v, ⟨r, hk⟩, rfl⟩⟩

end EvmLogic.Program.Nested

end
