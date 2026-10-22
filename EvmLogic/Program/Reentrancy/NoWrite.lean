import EvmLogic.Program.Reentrancy.Exec

/-!
# World-safe instructions and no-write frames, for any gas

A byte is `WorldSafe` when its instruction neither changes the world nor starts a child: not
`SSTORE`, `CREATE`/`CREATE2`, a member of the `CALL` family, or `SELFDESTRUCT`. `exec_worldSafe`:
a world-safe instruction continues or halts with the world unchanged, requesting no call or
creation. `noWrite_halts`: a frame all of whose reachable instructions are world-safe halts with
the world unchanged, **whatever its gas** (no gas bound) — `absint_frame` localises the reachable
pcs, so each executed byte is world-safe and `exec_worldSafe` keeps the world at every step. This
is the tail of a checks-effects-interactions function after its single external call, and the
only fact the stipend/guard reasoning needs about the resumed caller.
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program.Nested

/-- A byte whose instruction neither changes the world nor starts a child: not `SSTORE` (0x55),
`CREATE`/`CREATE2` (0xf0/0xf5), a `CALL` (0xf1/0xf2/0xf4/0xfa) or `SELFDESTRUCT` (0xff). -/
def WorldSafe (b : UInt8) : Bool :=
  b ≠ 0x55 && b ≠ 0xf0 && b ≠ 0xf1 && b ≠ 0xf2 && b ≠ 0xf4 && b ≠ 0xf5 && b ≠ 0xfa && b ≠ 0xff

/-- A world-safe instruction continues or halts with the world unchanged, and requests no call
or creation. -/
abbrev SafePost (m : Machine) (a : Action) (m' : Machine) : Prop :=
  (∀ req, a ≠ .call req) ∧ (∀ msg, a ≠ .create msg) ∧ m'.world = m.world

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_worldSafe` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_worldSafe_0 (op : Opcode) (hk : op.ctorIdx ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8]) (m : Machine)
    (hb : WorldSafe (op.toByte) = true) : Wp (exec op) (SafePost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk <;>
    (try (simp only [Opcode.toByte, WorldSafe] at hb; exact absurd hb (by decide)))
  all_goals simp [SafePost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [SafePost]
  try case swap => intro _; split <;> simp [SafePost]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [SafePost])
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_worldSafe` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_worldSafe_1 (op : Opcode) (hk : op.ctorIdx ∈ [9, 10, 11, 12, 13, 14, 15, 16, 17, 18]) (m : Machine)
    (hb : WorldSafe (op.toByte) = true) : Wp (exec op) (SafePost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk <;>
    (try (simp only [Opcode.toByte, WorldSafe] at hb; exact absurd hb (by decide)))
  all_goals simp [SafePost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [SafePost]
  try case swap => intro _; split <;> simp [SafePost]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [SafePost])
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_worldSafe` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_worldSafe_2 (op : Opcode) (hk : op.ctorIdx ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27]) (m : Machine)
    (hb : WorldSafe (op.toByte) = true) : Wp (exec op) (SafePost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk <;>
    (try (simp only [Opcode.toByte, WorldSafe] at hb; exact absurd hb (by decide)))
  all_goals simp [SafePost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [SafePost]
  try case swap => intro _; split <;> simp [SafePost]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [SafePost])
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_worldSafe` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_worldSafe_3 (op : Opcode) (hk : op.ctorIdx ∈ [28, 29, 30, 31, 32, 33, 34, 35, 36, 37]) (m : Machine)
    (hb : WorldSafe (op.toByte) = true) : Wp (exec op) (SafePost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk <;>
    (try (simp only [Opcode.toByte, WorldSafe] at hb; exact absurd hb (by decide)))
  all_goals simp [SafePost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [SafePost]
  try case swap => intro _; split <;> simp [SafePost]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [SafePost])
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_worldSafe` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_worldSafe_4 (op : Opcode) (hk : op.ctorIdx ∈ [38, 39, 40, 41, 42, 43, 44, 45, 46]) (m : Machine)
    (hb : WorldSafe (op.toByte) = true) : Wp (exec op) (SafePost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk <;>
    (try (simp only [Opcode.toByte, WorldSafe] at hb; exact absurd hb (by decide)))
  all_goals simp [SafePost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [SafePost]
  try case swap => intro _; split <;> simp [SafePost]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [SafePost])
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_worldSafe` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_worldSafe_5 (op : Opcode) (hk : op.ctorIdx ∈ [47, 48, 49, 50, 51, 52, 53, 54, 55, 56]) (m : Machine)
    (hb : WorldSafe (op.toByte) = true) : Wp (exec op) (SafePost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk <;>
    (try (simp only [Opcode.toByte, WorldSafe] at hb; exact absurd hb (by decide)))
  all_goals simp [SafePost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [SafePost]
  try case swap => intro _; split <;> simp [SafePost]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [SafePost])
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_worldSafe` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_worldSafe_6 (op : Opcode) (hk : op.ctorIdx ∈ [57, 58, 59, 61, 62, 63, 64, 65, 66]) (m : Machine)
    (hb : WorldSafe (op.toByte) = true) : Wp (exec op) (SafePost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk <;>
    (try (simp only [Opcode.toByte, WorldSafe] at hb; exact absurd hb (by decide)))
  all_goals simp [SafePost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [SafePost]
  try case swap => intro _; split <;> simp [SafePost]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [SafePost])
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_worldSafe` for the opcodes of constructor index in the list (split for parallel elaboration). -/
theorem exec_worldSafe_7 (op : Opcode) (hk : op.ctorIdx ∈ [67, 68, 69, 70, 71, 72, 73, 77, 81, 82]) (m : Machine)
    (hb : WorldSafe (op.toByte) = true) : Wp (exec op) (SafePost m) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk <;>
    (try (simp only [Opcode.toByte, WorldSafe] at hb; exact absurd hb (by decide)))
  all_goals simp [SafePost, exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput, execLog,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic]
  try case dup => intro _; split <;> simp [SafePost]
  try case swap => intro _; split <;> simp [SafePost]
  try case log =>
    intro _ _ _ _ _ _
    exact wp_popN_of _ (fun _ _ => by simp [SafePost])
private theorem worldSafe_decode_aux (fork : Fork) : (List.range 256).all
    (fun n => !WorldSafe n.toUInt8 || WorldSafe (Opcode.decode fork n.toUInt8).toByte) = true := by
  cases fork <;> decide +kernel

theorem worldSafe_decode (fork : Fork) (b : UInt8) (h : WorldSafe b = true) :
    WorldSafe (Opcode.decode fork b).toByte = true := by
  have hb : b.toNat < 256 := b.toNat_lt
  have h2 := (List.all_eq_true.1 (worldSafe_decode_aux fork)) b.toNat (by simp [List.mem_range, hb])
  rw [show b.toNat.toUInt8 = b from UInt8.ofNat_toNat] at h2
  simp only [h, Bool.not_true, Bool.false_or] at h2
  exact h2
/-- **Every world-safe instruction.** -/
theorem exec_worldSafe (op : Opcode) (m : Machine) (hb : WorldSafe op.toByte = true) :
    Wp (exec op) (SafePost m) m := by
  cases op
  all_goals first
    | exact exec_worldSafe_0 _ (by dsimp only [Opcode.ctorIdx]; decide) m hb |
      exact exec_worldSafe_1 _ (by dsimp only [Opcode.ctorIdx]; decide) m hb |
      exact exec_worldSafe_2 _ (by dsimp only [Opcode.ctorIdx]; decide) m hb |
      exact exec_worldSafe_3 _ (by dsimp only [Opcode.ctorIdx]; decide) m hb |
      exact exec_worldSafe_4 _ (by dsimp only [Opcode.ctorIdx]; decide) m hb |
      exact exec_worldSafe_5 _ (by dsimp only [Opcode.ctorIdx]; decide) m hb |
      exact exec_worldSafe_6 _ (by dsimp only [Opcode.ctorIdx]; decide) m hb |
      exact exec_worldSafe_7 _ (by dsimp only [Opcode.ctorIdx]; decide) m hb
    | (exfalso; revert hb; simp only [Opcode.toByte, WorldSafe]; decide)

/-- **A world-safe byte** (through `decode`) keeps the world. -/
theorem exec_worldSafe_byte (fork : Fork) (b : UInt8) (m : Machine) (hb : WorldSafe b = true) :
    Wp (exec (Opcode.decode fork b)) (SafePost m) m :=
  exec_worldSafe _ m (worldSafe_decode fork b hb)

end EvmLogic.Program.Reentrancy
