import EvmLogic.GasMono.Lockstep

/-!
# One instruction does not read its frame's kind

`exec_setKind`: an instruction that succeeds from `m` succeeds with the same action from
`setKind k m` (the frame kind replaced by `k`), ending in `setKind k m'`. The kind of a frame
(call or creation) is read only when the frame ends (`frameResult`); the low-gas argument
(`LowGas.lean`) uses this to compare a frame of any kind with a top-level call frame.
-/

namespace Verified.OpenZeppelin.ERC20.Spec
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested

/-- The machine with its executing frame's kind replaced by `k`. -/
def setKind (k : FrameKind) (m : Machine) : Machine := { m with frame := { m.frame with kind := k } }

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- An instruction that reads no gas and succeeds from `m` succeeds identically from
`setKind k m`. -/
theorem exec_setKind_wp (op : Opcode) (hop : ¬ ReadsGas op) (m : Machine) (k : FrameKind) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = setKind k m') (setKind k m)) m := by
  cases op
  case dup n =>
    simp [exec, setKind]
    intro _
    split <;> simp <;> intros <;> simp_all
  case swap n =>
    simp [exec, setKind]
    intro _
    split <;> simp <;> intros <;> simp_all
  case returndatacopy =>
    simp [exec, memoryExpansion, expandMemory, writeMemory, setKind]
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
    setKind, execSstore, execSelfdestruct]
  all_goals (intros; try simp_all)

/-- **One instruction does not read the frame kind**, as run equations. -/
theorem exec_setKind (op : Opcode) (hop : ¬ ReadsGas op) {m m' : Machine} {a : Action}
    (h : (exec op).run m = .ok (a, m')) (k : FrameKind) :
    (exec op).run (setKind k m) = .ok (a, setKind k m') := by
  have hw := (exec_setKind_wp op hop m k).of_run h
  unfold Twp at hw
  split at hw
  · rename_i a' m'' he
    obtain ⟨rfl, rfl⟩ := hw
    exact he
  · exact hw.elim

end Verified.OpenZeppelin.ERC20.Spec
