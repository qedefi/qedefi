import EvmLogic.Program.Nested.Gas

/-!
# One instruction does not read the calldata

`setData D m` is the machine `m` with the calldata of its executing frame replaced by `D`.
`exec_setData`: every instruction except `CALLDATALOAD`, `CALLDATASIZE`, `CALLDATACOPY`
(which read the calldata) and `GAS`, `CALL*`, `CREATE*` (left out, as in the gas lockstep:
the codes this is used for have none) commutes with it: if it succeeds from `m`, it succeeds
with the same action from `setData D m`, ending in `setData D m'`.

This is the per-instruction half of the reduction of dirty calldata to clean calldata for
solc 0.4/0.5 tokens (`Verified.WeirdERC20.Common.DataLockstep`): once the dispatcher has
decoded and masked the argument words, the rest of the frame runs the same whatever the
calldata.
-/

namespace Verified.WeirdERC20.Common
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested

/-- The machine `m` with calldata `D` in its executing frame. -/
def setData (D : ByteArray) (m : Machine) : Machine :=
  { m with frame := { m.frame with msg := { m.frame.msg with data := D } } }

@[simp] theorem setData_world (D : ByteArray) (m : Machine) : (setData D m).world = m.world := rfl
@[simp] theorem setData_transient (D : ByteArray) (m : Machine) :
    (setData D m).transient = m.transient := rfl
@[simp] theorem setData_created (D : ByteArray) (m : Machine) :
    (setData D m).createdAccounts = m.createdAccounts := rfl
@[simp] theorem setData_ctx (D : ByteArray) (m : Machine) : (setData D m).ctx = m.ctx := rfl
@[simp] theorem setData_sub (D : ByteArray) (m : Machine) :
    (setData D m).frame.sub = m.frame.sub := rfl
@[simp] theorem setData_parents (D : ByteArray) (m : Machine) :
    (setData D m).parents = m.parents := rfl
@[simp] theorem setData_code (D : ByteArray) (m : Machine) :
    (setData D m).frame.code = m.frame.code := rfl
@[simp] theorem setData_pc (D : ByteArray) (m : Machine) :
    (setData D m).frame.pc = m.frame.pc := rfl
@[simp] theorem setData_jumpDests (D : ByteArray) (m : Machine) :
    (setData D m).frame.jumpDests = m.frame.jumpDests := rfl
@[simp] theorem setData_gasLeft (D : ByteArray) (m : Machine) :
    (setData D m).frame.gasLeft = m.frame.gasLeft := rfl
@[simp] theorem setData_stack (D : ByteArray) (m : Machine) :
    (setData D m).frame.stack = m.frame.stack := rfl
@[simp] theorem setData_data (D : ByteArray) (m : Machine) :
    (setData D m).frame.msg.data = D := rfl

theorem setData_setData (D D' : ByteArray) (m : Machine) :
    setData D (setData D' m) = setData D m := rfl

theorem setData_self (m : Machine) : setData m.frame.msg.data m = m := rfl

/-- The instructions that read the calldata, the gas, or start a child. -/
def ReadsData : Opcode → Prop
  | .calldataload | .calldatasize | .calldatacopy => True
  | .gas | .call | .callcode | .delegatecall | .staticcall | .create | .create2 => True
  | _ => False

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- An instruction that reads no calldata and succeeds from `m` succeeds identically from
`setData D m`. -/
theorem exec_setData_wp (op : Opcode) (hop : ¬ ReadsData op) (m : Machine) (D : ByteArray) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = setData D m') (setData D m)) m := by
  cases op
  case dup n =>
    simp [exec, setData]
    intro _
    split <;> simp <;> intros <;> simp_all
  case swap n =>
    simp [exec, setData]
    intro _
    split <;> simp <;> intros <;> simp_all
  case returndatacopy =>
    simp [exec, memoryExpansion, expandMemory, writeMemory, setData]
    intros
    simp_all
    intro hz
    simp only [hz] at *
    simp_all
  all_goals first
    | (exact absurd trivial hop)
    | skip
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    setData, execSstore, execSelfdestruct]
  all_goals (intros; try simp_all)

/-- **One instruction does not read the calldata**, as run equations. -/
theorem exec_setData (op : Opcode) (hop : ¬ ReadsData op) {m m' : Machine} {a : Action}
    (h : (exec op).run m = .ok (a, m')) (D : ByteArray) :
    (exec op).run (setData D m) = .ok (a, setData D m') := by
  have hw := (exec_setData_wp op hop m D).of_run h
  unfold Twp at hw
  split at hw
  · rename_i a' m'' he
    obtain ⟨rfl, rfl⟩ := hw
    exact he
  · exact hw.elim

end Verified.WeirdERC20.Common
