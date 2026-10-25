import EvmLogic.Program.Nested.Frame

/-!
# What one instruction does to code and to the deletion set

`exec_del`: every instruction keeps every code-holding account holding code (no instruction
removes code: `SSTORE` writes storage, `CREATE*` increments a nonce, `SELFDESTRUCT` moves ether and
zeroes a balance, all through `modifyState`, which erases only empty accounts), and adds to the
frame's `accountsToDelete` only accounts in `createdAccounts` (EIP-6780). The step of the
deletion invariant of `EvmLogic.Tx.Delete`.
-/

namespace EvmLogic.Tx
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested

/-- What one instruction does to code-holding accounts and the frame's deletion set. -/
abbrev DelPost (m : Machine) (_ : Action) (m' : Machine) : Prop :=
  (∀ p, (m.world.code p).size ≠ 0 → (m'.world.code p).size ≠ 0) ∧
  (∀ a, a ∈ m'.frame.sub.accountsToDelete →
    a ∈ m.frame.sub.accountsToDelete ∨ a ∈ m.createdAccounts)

theorem eq_empty_of_size {b : ByteArray} (h : b.size = 0) : b = ByteArray.empty := by
  exact Classical.byContradiction fun hne => size_ne_zero_of_ne_empty hne h

/-- `modifyState` with a code-preserving update keeps every account's code (an erased account
was empty, so its code was already empty). -/
theorem code_modifyState {w : World} {a : Address} {f : Account → Account}
    (hf : ∀ acc, (f acc).code = acc.code) (b : Address) :
    (modifyState w a f).code b = w.code b := by
  unfold modifyState World.code
  by_cases hab : a = b
  · subst hab
    dsimp only
    split
    · rename_i he
      simp only [Account.isEmpty, Bool.and_eq_true, decide_eq_true_eq, hf] at he
      have h3 : (World.account (Std.ExtTreeMap.erase w a) a).code = ByteArray.empty := by
        simp [World.account]
      rw [h3, eq_empty_of_size he.2]
    · simp [World.account, hf]
  · dsimp only
    split <;> simp [World.account, Std.ExtTreeMap.getD_erase, Std.ExtTreeMap.getD_insert, hab]

@[simp] theorem code_incrementNonce (w : World) (a b : Address) :
    (incrementNonce w a).code b = w.code b := by
  unfold incrementNonce; exact code_modifyState (by intro; rfl) b

@[simp] theorem code_setAccountBalance (w : World) (a : Address) (v : Word) (b : Address) :
    (setAccountBalance w a v).code b = w.code b := by
  unfold setAccountBalance; exact code_modifyState (by intro; rfl) b

@[simp] theorem code_moveEther (w : World) (src dst : Address) (v : Word) (b : Address) :
    (moveEther w src dst v).code b = w.code b := by
  simp only [moveEther]
  rw [code_modifyState (by intro; rfl), code_modifyState (by intro; rfl)]

@[simp] theorem code_transferValue (w : World) (msg : Message) (b : Address) :
    (transferValue w msg).code b = w.code b := by
  unfold transferValue; split <;> simp

theorem imp_self_or (p q : Prop) : (p → p ∨ q) ↔ True := ⟨fun _ => trivial, fun _ => Or.inl⟩

theorem code_ne_empty_of_keep {w w' : World} {p : Address} (h : Keep p w w')
    (hp : ¬ w.code p = ByteArray.empty) : ¬ w'.code p = ByteArray.empty := by
  rw [h.code]; exact hp

theorem execSstore_del (m : Machine) : Wp execSstore (DelPost m) m := by
  simp [DelPost, execSstore, accessStorageKey, requireNonStatic, setStorage]
  intros
  constructor <;> intros <;> simp_all

/-- Close the goals `simp` leaves for a deletion-set postcondition. -/
macro "del_close" : tactic => `(tactic| (
  repeat' (first | apply And.intro | intro _)
  all_goals first
    | exact Or.inl ‹_›
    | exact Or.inr ‹_›
    | (rename_i h; rcases h with h | h
       · subst h; exact Or.inr ‹_›
       · exact Or.inl h)))

theorem execSelfdestruct_del (m : Machine) : Wp execSelfdestruct (DelPost m) m := by
  simp [DelPost, execSelfdestruct, requireNonStatic, Substate.warmAddr]
  del_close

theorem execCreate_del (b : Bool) (m : Machine) : Wp (execCreate b) (DelPost m) m := by
  cases b <;> simp [DelPost, execCreate, requireNonStatic, memoryExpansion,
    expandMemory, readMemory, setReturnData, Substate.warmAddr] <;> del_close

theorem execCall_del (k : CallKind) (m : Machine) : Wp (execCall k) (DelPost m) m := by
  cases k <;> simp [DelPost, execCall, memoryExpansion, expandMemory, readMemory,
    setReturnData, genericCall, Substate.warmAddr] <;> del_close

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_del` for the opcodes of constructor index in `[0, 1, 2, 3, 4, 5, 6, 7, 8]` (split for parallel elaboration). -/
theorem exec_del_0 (op : Opcode) (hk : op.ctorIdx ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8]) (m : Machine) :
    Wp (exec op) (DelPost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [DelPost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    Substate.warmAddr, imp_self_or]
  try case dup => intro _; split <;> simp [DelPost, imp_self_or]
  try case swap => intro _; split <;> simp [DelPost, imp_self_or]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [DelPost, imp_self_or])

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_del` for the opcodes of constructor index in `[9, 10, 11, 12, 13, 14, 15, 16, 17, 18]` (split for parallel elaboration). -/
theorem exec_del_1 (op : Opcode) (hk : op.ctorIdx ∈ [9, 10, 11, 12, 13, 14, 15, 16, 17, 18]) (m : Machine) :
    Wp (exec op) (DelPost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [DelPost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    Substate.warmAddr, imp_self_or]
  try case dup => intro _; split <;> simp [DelPost, imp_self_or]
  try case swap => intro _; split <;> simp [DelPost, imp_self_or]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [DelPost, imp_self_or])

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_del` for the opcodes of constructor index in `[19, 20, 21, 22, 23, 24, 25, 26, 27]` (split for parallel elaboration). -/
theorem exec_del_2 (op : Opcode) (hk : op.ctorIdx ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27]) (m : Machine) :
    Wp (exec op) (DelPost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [DelPost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    Substate.warmAddr, imp_self_or]
  try case dup => intro _; split <;> simp [DelPost, imp_self_or]
  try case swap => intro _; split <;> simp [DelPost, imp_self_or]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [DelPost, imp_self_or])

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_del` for the opcodes of constructor index in `[28, 29, 30, 31, 32, 33, 34, 35, 36, 37]` (split for parallel elaboration). -/
theorem exec_del_3 (op : Opcode) (hk : op.ctorIdx ∈ [28, 29, 30, 31, 32, 33, 34, 35, 36, 37]) (m : Machine) :
    Wp (exec op) (DelPost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [DelPost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    Substate.warmAddr, imp_self_or]
  try case dup => intro _; split <;> simp [DelPost, imp_self_or]
  try case swap => intro _; split <;> simp [DelPost, imp_self_or]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [DelPost, imp_self_or])

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_del` for the opcodes of constructor index in `[38, 39, 40, 41, 42, 43, 44, 45, 46]` (split for parallel elaboration). -/
theorem exec_del_4 (op : Opcode) (hk : op.ctorIdx ∈ [38, 39, 40, 41, 42, 43, 44, 45, 46]) (m : Machine) :
    Wp (exec op) (DelPost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [DelPost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    Substate.warmAddr, imp_self_or]
  try case dup => intro _; split <;> simp [DelPost, imp_self_or]
  try case swap => intro _; split <;> simp [DelPost, imp_self_or]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [DelPost, imp_self_or])

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_del` for the opcodes of constructor index in `[47, 48, 49, 50, 51, 52, 53, 54, 55, 56]` (split for parallel elaboration). -/
theorem exec_del_5 (op : Opcode) (hk : op.ctorIdx ∈ [47, 48, 49, 50, 51, 52, 53, 54, 55, 56]) (m : Machine) :
    Wp (exec op) (DelPost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [DelPost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    Substate.warmAddr, imp_self_or]
  try case dup => intro _; split <;> simp [DelPost, imp_self_or]
  try case swap => intro _; split <;> simp [DelPost, imp_self_or]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [DelPost, imp_self_or])

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_del` for the opcodes of constructor index in `[57, 58, 59, 61, 62, 63, 64, 65, 66]` (split for parallel elaboration). -/
theorem exec_del_6 (op : Opcode) (hk : op.ctorIdx ∈ [57, 58, 59, 61, 62, 63, 64, 65, 66]) (m : Machine) :
    Wp (exec op) (DelPost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [DelPost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    Substate.warmAddr, imp_self_or]
  try case dup => intro _; split <;> simp [DelPost, imp_self_or]
  try case swap => intro _; split <;> simp [DelPost, imp_self_or]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [DelPost, imp_self_or])

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_del` for the opcodes of constructor index in `[67, 68, 69, 70, 71, 72, 73, 77, 81, 82]` (split for parallel elaboration). -/
theorem exec_del_7 (op : Opcode) (hk : op.ctorIdx ∈ [67, 68, 69, 70, 71, 72, 73, 77, 81, 82]) (m : Machine) :
    Wp (exec op) (DelPost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [DelPost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    Substate.warmAddr, imp_self_or]
  try case dup => intro _; split <;> simp [DelPost, imp_self_or]
  try case swap => intro _; split <;> simp [DelPost, imp_self_or]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [DelPost, imp_self_or])

set_option maxHeartbeats 4000000 in
/-- **Every instruction** keeps the code of code-holding accounts and adds to the frame's deletion
set only accounts created in the transaction. -/
theorem exec_del (op : Opcode) (m : Machine) : Wp (exec op) (DelPost m) m := by
  cases op
  case sstore => exact execSstore_del m
  case selfdestruct => exact execSelfdestruct_del m
  case create => exact execCreate_del false m
  case create2 => exact execCreate_del true m
  case call => exact execCall_del .call m
  case callcode => exact execCall_del .callcode m
  case delegatecall => exact execCall_del .delegatecall m
  case staticcall => exact execCall_del .staticcall m
  all_goals first
    | exact exec_del_0 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_del_1 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_del_2 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_del_3 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_del_4 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_del_5 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_del_6 _ (by dsimp only [Opcode.ctorIdx]; decide) m |
      exact exec_del_7 _ (by dsimp only [Opcode.ctorIdx]; decide) m
    | fail "exec_del: no group"

end EvmLogic.Tx
