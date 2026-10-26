import EvmLogic.Program.Reentrancy.Exec
import EvmLogic.AbsInt.Effect

/-!
# Instructions that change nothing outside the frame

A *pure* instruction is one that writes no storage (`SSTORE`, `TSTORE`), emits no log, starts
no child (`CALL*`, `CREATE*`) and does not self-destruct. `exec_pure`: whatever such an
instruction does, a successful result leaves the world, the transient storage and the logs as
they were, and is no call or creation. Every other effect (stack, memory, pc, gas, return
data, access lists) is the frame's own.
-/

namespace Verified.Common.Malformed
open EvmLean EvmLean.Interpreter EvmLogic.Program.Nested EvmLogic.Program.Reentrancy

/-- The instruction writes no state, emits no log and starts no child. -/
def pureOpB : Opcode → Bool
  | .sstore | .tstore | .log _ | .create | .call | .callcode | .delegatecall | .create2
  | .staticcall | .selfdestruct => false
  | _ => true

/-- What a successful pure instruction does: no call or creation, and the world, transient
storage and logs unchanged. -/
def PurePost (m : Machine) : Action → Machine → Prop
  | .call _, _ => False
  | .create _, _ => False
  | _, m' => m'.world = m.world ∧ m'.transient = m.transient ∧
      m'.frame.sub.logs = m.frame.sub.logs

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **A pure instruction changes nothing outside the frame.** -/
theorem exec_pure (op : Opcode) (hop : pureOpB op = true) (m : Machine) :
    Wp (exec op) (PurePost m) m := by
  cases op <;> simp only [pureOpB, Bool.false_eq_true] at hop <;> clear hop
  all_goals simp [PurePost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, Substate.warmAddr]
  case dup => intro _; split <;> simp [PurePost]
  case swap => intro _; split <;> simp [PurePost]

end Verified.Common.Malformed
