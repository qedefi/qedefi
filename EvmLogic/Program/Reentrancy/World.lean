import EvmLogic.Program.Reentrancy.Exec

/-!
# What one instruction does to the world

`exec_world`: a successful instruction leaves the world unchanged, or (only from a non-static
frame, at the executing account `self`) writes a storage slot of `self`, increments the nonce of
`self` (`CREATE*`), or moves all of `self`'s ether to a beneficiary, possibly zeroing `self`'s
balance (`SELFDESTRUCT`). A requested child's value transfer comes from `self`, is affordable,
and moves value out of a static frame only to itself (`CALLCODE`). This is what lets a
simulation invariant talk about ether balances (`EvmLogic.Program.Reentrancy.Ether`), where
`exec_frame` only describes storage and code.
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program.Nested

/-- Close a goal left by `exec_world` on a call, a creation, an `SSTORE`. -/
macro "world_close" : tactic => `(tactic| first
  | assumption
  | (right; exact ⟨‹_›, .inl ⟨_, _, rfl⟩⟩)
  | (right; exact ⟨‹_›, .inr (.inl rfl)⟩)
  | (right; exact ⟨‹_›, .inr (.inr (.inl ⟨_, rfl⟩))⟩)
  | (right; exact ⟨‹_›, .inr (.inr (.inr ⟨_, rfl⟩))⟩)
  | (right; assumption)
  | (right; rfl)
  | (left; rename_i h1 h2 h3 h4 h5 h6; cases hs : (‹Machine›).frame.msg.isStatic <;> simp_all))

/-- The world changes an instruction can make (see the module docstring). -/
def WorldStep (m : Machine) (w' : World) : Prop :=
  w' = m.world ∨
  (m.frame.msg.isStatic = false ∧
    ((∃ k v, w' = m.world.sstore m.frame.msg.currentTarget k v) ∨
     w' = incrementNonce m.world m.frame.msg.currentTarget ∨
     (∃ b, w' = moveEther m.world m.frame.msg.currentTarget b
        (m.world.balance m.frame.msg.currentTarget)) ∨
     (∃ b, w' = setAccountBalance (moveEther m.world m.frame.msg.currentTarget b
        (m.world.balance m.frame.msg.currentTarget)) m.frame.msg.currentTarget 0)))

/-- A requested child's value transfer: from `self`, affordable, and out of a static frame only
to itself. -/
def TransferOk (m : Machine) : Action → Machine → Prop
  | .call req, m' => req.msg.shouldTransferValue = true → req.msg.value ≠ 0 →
      req.msg.caller = m.frame.msg.currentTarget ∧
      req.msg.value.toNat ≤ (m'.world.balance req.msg.caller).toNat ∧
      (m.frame.msg.isStatic = false ∨ req.msg.currentTarget = req.msg.caller)
  | .create msg, m' => msg.caller = m.frame.msg.currentTarget ∧
      msg.value.toNat ≤ (m.world.balance msg.caller).toNat ∧
      m'.world = incrementNonce m.world m.frame.msg.currentTarget
  | _, _ => True

@[simp] theorem transferOk_next {m m' : Machine} : TransferOk m .next m' := trivial
@[simp] theorem transferOk_stop {m m' : Machine} {o} : TransferOk m (.stop o) m' := trivial
@[simp] theorem transferOk_revert {m m' : Machine} {o} : TransferOk m (.revert o) m' := trivial

/-- The postcondition of `exec_world`. -/
abbrev ExecWorld (m : Machine) (a : Action) (m' : Machine) : Prop :=
  WorldStep m m'.world ∧ TransferOk m a m'

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_world` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_world_0 (op : Opcode) (hk : op.ctorIdx ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8]) (m : Machine) : Wp (exec op) (ExecWorld m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecWorld, WorldStep, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecWorld, WorldStep]
  try case swap => intro _; split <;> simp [ExecWorld, WorldStep]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [WorldStep])

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_world` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_world_1 (op : Opcode) (hk : op.ctorIdx ∈ [9, 10, 11, 12, 13, 14, 15, 16, 17, 18]) (m : Machine) : Wp (exec op) (ExecWorld m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecWorld, WorldStep, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecWorld, WorldStep]
  try case swap => intro _; split <;> simp [ExecWorld, WorldStep]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [WorldStep])

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_world` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_world_2 (op : Opcode) (hk : op.ctorIdx ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27]) (m : Machine) : Wp (exec op) (ExecWorld m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecWorld, WorldStep, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecWorld, WorldStep]
  try case swap => intro _; split <;> simp [ExecWorld, WorldStep]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [WorldStep])

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_world` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_world_3 (op : Opcode) (hk : op.ctorIdx ∈ [28, 29, 30, 31, 32, 33, 34, 35, 36, 37]) (m : Machine) : Wp (exec op) (ExecWorld m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecWorld, WorldStep, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecWorld, WorldStep]
  try case swap => intro _; split <;> simp [ExecWorld, WorldStep]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [WorldStep])

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_world` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_world_4 (op : Opcode) (hk : op.ctorIdx ∈ [38, 39, 40, 41, 42, 43, 44, 45, 46]) (m : Machine) : Wp (exec op) (ExecWorld m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecWorld, WorldStep, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecWorld, WorldStep]
  try case swap => intro _; split <;> simp [ExecWorld, WorldStep]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [WorldStep])

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_world` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_world_5 (op : Opcode) (hk : op.ctorIdx ∈ [47, 48, 49, 50, 51, 52, 53, 54, 55, 56]) (m : Machine) : Wp (exec op) (ExecWorld m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecWorld, WorldStep, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecWorld, WorldStep]
  try case swap => intro _; split <;> simp [ExecWorld, WorldStep]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [WorldStep])

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_world` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_world_6 (op : Opcode) (hk : op.ctorIdx ∈ [57, 58, 59, 61, 62, 63, 64, 65, 66]) (m : Machine) : Wp (exec op) (ExecWorld m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecWorld, WorldStep, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecWorld, WorldStep]
  try case swap => intro _; split <;> simp [ExecWorld, WorldStep]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [WorldStep])

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_world` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_world_7 (op : Opcode) (hk : op.ctorIdx ∈ [67, 68, 69, 70, 71, 72, 73, 77, 81, 82]) (m : Machine) : Wp (exec op) (ExecWorld m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [ExecWorld, WorldStep, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [ExecWorld, WorldStep]
  try case swap => intro _; split <;> simp [ExecWorld, WorldStep]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [WorldStep])

/-- `exec_world` for `SSTORE`. -/
theorem execSstore_world (m : Machine) : Wp execSstore (ExecWorld m) m := by
  simp [ExecWorld, WorldStep, execSstore, accessStorageKey, requireNonStatic, setStorage]
  repeat' (first | (intro _) | apply And.intro)
  all_goals (right; exact ⟨‹_›, .inl ⟨_, _, rfl⟩⟩)

/-- `exec_world` for `SELFDESTRUCT`. -/
theorem execSelfdestruct_world (m : Machine) : Wp execSelfdestruct (ExecWorld m) m := by
  simp [ExecWorld, WorldStep, execSelfdestruct, requireNonStatic]
  repeat' (first | (intro _) | apply And.intro)
  all_goals (right; refine ⟨‹_›, ?_⟩; first
    | exact .inr (.inr (.inl ⟨_, by with_reducible rfl⟩))
    | exact .inr (.inr (.inr ⟨_, by with_reducible rfl⟩)))

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_world` for `CREATE`/`CREATE2`. -/
theorem execCreate_world (b : Bool) (m : Machine) : Wp (execCreate b) (ExecWorld m) m := by
  cases b <;> simp [ExecWorld, WorldStep, TransferOk, execCreate, requireNonStatic, memoryExpansion,
    expandMemory, readMemory, setReturnData]
  all_goals (repeat' (first | (intro _) | apply And.intro))
  all_goals world_close

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_world` for `CALL`. -/
theorem execCall_world_call (m : Machine) : Wp (execCall .call) (ExecWorld m) m := by
  simp [ExecWorld, WorldStep, TransferOk, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall]
  all_goals (repeat' (first | (intro _) | apply And.intro))
  all_goals world_close

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_world` for `CALLCODE`. -/
theorem execCall_world_callcode (m : Machine) : Wp (execCall .callcode) (ExecWorld m) m := by
  simp [ExecWorld, WorldStep, TransferOk, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall]
  all_goals (repeat' (first | (intro _) | apply And.intro))
  all_goals world_close
set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_world` for `DELEGATECALL`. -/
theorem execCall_world_delegatecall (m : Machine) : Wp (execCall .delegatecall) (ExecWorld m) m := by
  simp [ExecWorld, WorldStep, TransferOk, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall]
  all_goals (repeat' (first | (intro _) | apply And.intro))
  all_goals world_close
set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_world` for `STATICCALL`. -/
theorem execCall_world_staticcall (m : Machine) : Wp (execCall .staticcall) (ExecWorld m) m := by
  simp [ExecWorld, WorldStep, TransferOk, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall]
  all_goals (repeat' (first | (intro _) | apply And.intro))
  all_goals world_close
set_option maxHeartbeats 4000000 in
/-- **The world effects of every instruction.** -/
theorem exec_world (op : Opcode) (m : Machine) : Wp (exec op) (ExecWorld m) m := by
  cases op
  case sstore => exact execSstore_world m
  case selfdestruct => exact execSelfdestruct_world m
  case create => exact execCreate_world false m
  case create2 => exact execCreate_world true m
  case call => exact execCall_world_call m
  case callcode => exact execCall_world_callcode m
  case delegatecall => exact execCall_world_delegatecall m
  case staticcall => exact execCall_world_staticcall m
  all_goals first
    | exact exec_world_0 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_world_1 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_world_2 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_world_3 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_world_4 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_world_5 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_world_6 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_world_7 _ (by dsimp only [Opcode.ctorIdx]; decide) m
    | fail "exec_world: no group"

end EvmLogic.Program.Reentrancy
