import EvmLogic.Program.Nested.Frame

/-!
# Gas monotonicity of a single instruction

`exec_bump`: every instruction except `GAS`, `CALL*` and `CREATE*` (the only ones whose result
depends on the amount of gas, not just its sufficiency) commutes with adding gas: if it succeeds
from `m`, it succeeds with the same action from `bump d x ps m`, ending in `bump d x ps m'`.
This is the per-instruction part of the low-gas argument (`docs/proving.md` §6).
-/

namespace EvmLogic.Program.Nested
open EvmLean EvmLean.Interpreter

/-- Total weakest precondition: `x` succeeds from `m` and its result satisfies `Q`. -/
def Twp {α : Type} (x : M α) (Q : α → Machine → Prop) (m : Machine) : Prop :=
  match x.run m with
  | .ok (a, m') => Q a m'
  | .error _ => False

variable {α β : Type} {Q : α → Machine → Prop} {m : Machine}

@[simp] theorem twp_pure (a : α) : Twp (pure a : M α) Q m ↔ Q a m := Iff.rfl
@[simp] theorem twp_bind (x : M α) (f : α → M β) (Q : β → Machine → Prop) :
    Twp (x >>= f) Q m ↔ Twp x (fun a m' => Twp (f a) Q m') m := by
  unfold Twp
  simp only [StateT.run_bind]
  cases x.run m with
  | error e => simp [bind, Except.bind]
  | ok p => obtain ⟨a, m'⟩ := p; simp [bind, Except.bind]
@[simp] theorem twp_get {Q : Machine → Machine → Prop} : Twp (get : M Machine) Q m ↔ Q m m := Iff.rfl
@[simp] theorem twp_set (m' : Machine) {Q : PUnit → Machine → Prop} :
    Twp (set m' : M PUnit) Q m ↔ Q ⟨⟩ m' := Iff.rfl
@[simp] theorem twp_modify (f : Machine → Machine) {Q : PUnit → Machine → Prop} :
    Twp (modify f : M PUnit) Q m ↔ Q ⟨⟩ (f m) := Iff.rfl
@[simp] theorem twp_modifyGet (f : Machine → α × Machine) :
    Twp (modifyGet f : M α) Q m ↔ Q (f m).1 (f m).2 := Iff.rfl
@[simp] theorem twp_throw (e : ExceptionalHalt) : Twp (throw e : M α) Q m ↔ False := Iff.rfl
@[simp] theorem twp_ite {c : Prop} [Decidable c] (x y : M α) :
    Twp (if c then x else y) Q m ↔ (c ∧ Twp x Q m) ∨ (¬ c ∧ Twp y Q m) := by
  by_cases h : c <;> simp [h]
@[simp] theorem twp_getFrame {Q : Frame → Machine → Prop} : Twp getFrame Q m ↔ Q m.frame m := Iff.rfl
@[simp] theorem twp_modifyFrame (f : Frame → Frame) {Q : Unit → Machine → Prop} :
    Twp (modifyFrame f) Q m ↔ Q () { m with frame := f m.frame } := Iff.rfl
@[simp] theorem twp_modifyWorld (f : World → World) {Q : Unit → Machine → Prop} :
    Twp (modifyWorld f) Q m ↔ Q () { m with world := f m.world } := Iff.rfl
@[simp] theorem twp_modifySub (f : Substate → Substate) {Q : Unit → Machine → Prop} :
    Twp (modifySub f) Q m ↔ Q () { m with frame := { m.frame with sub := f m.frame.sub } } := Iff.rfl
@[simp] theorem twp_map (f : α → β) (x : M α) (Q : β → Machine → Prop) :
    Twp (f <$> x) Q m ↔ Twp x (fun a m' => Q (f a) m') m := by
  rw [map_eq_pure_bind, twp_bind]; rfl
@[simp] theorem twp_pop {Q : Word → Machine → Prop} :
    Twp pop Q m ↔ match m.frame.stack with
      | [] => False
      | x :: xs => Q x { m with frame := { m.frame with stack := xs } } := by
  unfold pop
  rw [twp_bind, twp_getFrame]
  cases h : m.frame.stack with
  | nil => simp
  | cons x xs => rfl
@[simp] theorem twp_push (w : Word) {Q : Unit → Machine → Prop} :
    Twp (push w) Q m ↔ (m.frame.stack.length < Gas.stackLimit ∧
      Q () { m with frame := { m.frame with stack := w :: m.frame.stack } }) := by
  unfold push; simp
@[simp] theorem twp_charge (c : Nat) {Q : Unit → Machine → Prop} :
    Twp (charge c) Q m ↔ (c ≤ m.frame.gasLeft ∧
      Q () { m with frame := { m.frame with gasLeft := m.frame.gasLeft - c } }) := by
  unfold charge; simp
@[simp] theorem twp_advance (n : Nat) {Q : Unit → Machine → Prop} :
    Twp (advance n) Q m ↔ Q () { m with frame := { m.frame with pc := m.frame.pc + n } } := Iff.rfl

/-- The machine `m` with `d` more gas in the executing frame, message gas `x` and parents `ps`
(none of which an instruction reads). -/
def bump (d x : Nat) (ps : List Frame) (m : Machine) : Machine :=
  { m with frame := { m.frame with gasLeft := m.frame.gasLeft + d, msg := { m.frame.msg with gas := x } },
           parents := ps }

@[simp] theorem twp_popNat {Q : Nat → Machine → Prop} :
    Twp popNat Q m ↔ match m.frame.stack with
      | [] => False
      | x :: xs => Q x.toNat { m with frame := { m.frame with stack := xs } } := by
  unfold popNat; simp only [twp_bind, twp_pop, twp_pure]

@[simp] theorem twp_popAddress {Q : Address → Machine → Prop} :
    Twp popAddress Q m ↔ match m.frame.stack with
      | [] => False
      | x :: xs => Q (Word.toAddress x) { m with frame := { m.frame with stack := xs } } := by
  unfold popAddress; simp only [twp_bind, twp_pop, twp_pure]

@[simp] theorem twp_accessAddress (a : Address) {Q : Bool → Machine → Prop} :
    Twp (accessAddress a) Q m ↔ Q (m.frame.sub.accessedAddresses.contains a)
      { m with frame := { m.frame with sub := m.frame.sub.warmAddr a } } := by
  unfold Twp; rw [run_accessAddress]; rfl

@[simp] theorem twp_refundGas (c : Nat) {Q : Unit → Machine → Prop} :
    Twp (refundGas c) Q m ↔ Q () { m with frame := { m.frame with gasLeft := m.frame.gasLeft + c } } :=
  Iff.rfl

@[simp] theorem twp_dite {c : Prop} [Decidable c] (x : c → M α) (y : ¬ c → M α) :
    Twp (dite c x y) Q m ↔ (∃ h : c, Twp (x h) Q m) ∨ (∃ h : ¬ c, Twp (y h) Q m) := by
  by_cases h : c <;> simp [h]

@[simp] theorem wp_popN' (n : Nat) {Q : List Word → Machine → Prop} {m : Machine} :
    Wp (popN n) Q m ↔ (n ≤ m.frame.stack.length →
      Q (m.frame.stack.take n) { m with frame := { m.frame with stack := m.frame.stack.drop n } }) := by
  induction n generalizing Q m with
  | zero => simp [popN]
  | succ n ih =>
    unfold popN
    simp only [wp_bind, wp_pop, wp_pure, ih]
    cases hs : m.frame.stack with
    | nil => simp
    | cons x xs => simp

@[simp] theorem twp_popN (n : Nat) {Q : List Word → Machine → Prop} {m : Machine} :
    Twp (popN n) Q m ↔ (n ≤ m.frame.stack.length ∧
      Q (m.frame.stack.take n) { m with frame := { m.frame with stack := m.frame.stack.drop n } }) := by
  induction n generalizing Q m with
  | zero => simp [popN]
  | succ n ih =>
    unfold popN
    simp only [twp_bind, twp_pop, twp_pure, ih]
    cases hs : m.frame.stack with
    | nil => simp
    | cons x xs => simp


/-- The instructions that read the amount of gas left. -/
def ReadsGas : Opcode → Prop
  | .gas | .call | .callcode | .delegatecall | .staticcall | .create | .create2 => True
  | _ => False

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_bump_wp` for `DUP`, `SWAP`, `LOG` and `RETURNDATACOPY` (split for parallel elaboration). -/
theorem exec_bump_wp_s (op : Opcode) (hk : op.ctorIdx ∈ [42, 71, 72, 73]) (hop : ¬ ReadsGas op) (m : Machine) (d x : Nat)
    (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = bump d x ps m') (bump d x ps m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  case dup n =>
    simp [exec, bump]
    intro _
    split <;> simp <;> intros <;> omega
  case swap n =>
    simp [exec, bump]
    intro _
    split <;> simp <;> intros <;> omega
  case log n =>
    simp [exec, execLog, bump, memoryExpansion, expandMemory, requireNonStatic, readMemory]
    intros
    subst_vars
    simp_all
    omega
  case returndatacopy =>
    simp [exec, memoryExpansion, expandMemory, writeMemory, bump]
    intros
    simp_all
    constructor <;> intro hz <;> (try simp only [hz] at *)
    · exact ⟨by omega, by omega, .inl ⟨by omega, by omega⟩⟩
    · exact ⟨by omega, by omega⟩

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_bump_wp` for the opcodes of constructor index in `[0, 1, 2, 3, 4, 5]` (split for parallel elaboration). -/
theorem exec_bump_wp_0 (op : Opcode) (hk : op.ctorIdx ∈ [0, 1, 2, 3, 4, 5]) (hop : ¬ ReadsGas op) (m : Machine) (d x : Nat)
    (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = bump d x ps m') (bump d x ps m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    bump, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_bump_wp` for the opcodes of constructor index in `[6, 7, 8, 9, 10, 11]` (split for parallel elaboration). -/
theorem exec_bump_wp_1 (op : Opcode) (hk : op.ctorIdx ∈ [6, 7, 8, 9, 10, 11]) (hop : ¬ ReadsGas op) (m : Machine) (d x : Nat)
    (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = bump d x ps m') (bump d x ps m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    bump, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_bump_wp` for the opcodes of constructor index in `[12, 13, 14, 15, 16, 17]` (split for parallel elaboration). -/
theorem exec_bump_wp_2 (op : Opcode) (hk : op.ctorIdx ∈ [12, 13, 14, 15, 16, 17]) (hop : ¬ ReadsGas op) (m : Machine) (d x : Nat)
    (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = bump d x ps m') (bump d x ps m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    bump, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_bump_wp` for the opcodes of constructor index in `[18, 19, 20, 21, 22, 23]` (split for parallel elaboration). -/
theorem exec_bump_wp_3 (op : Opcode) (hk : op.ctorIdx ∈ [18, 19, 20, 21, 22, 23]) (hop : ¬ ReadsGas op) (m : Machine) (d x : Nat)
    (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = bump d x ps m') (bump d x ps m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    bump, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_bump_wp` for the opcodes of constructor index in `[24, 25, 26, 27, 28, 29]` (split for parallel elaboration). -/
theorem exec_bump_wp_4 (op : Opcode) (hk : op.ctorIdx ∈ [24, 25, 26, 27, 28, 29]) (hop : ¬ ReadsGas op) (m : Machine) (d x : Nat)
    (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = bump d x ps m') (bump d x ps m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    bump, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_bump_wp` for the opcodes of constructor index in `[30, 31, 32, 33, 34, 35]` (split for parallel elaboration). -/
theorem exec_bump_wp_5 (op : Opcode) (hk : op.ctorIdx ∈ [30, 31, 32, 33, 34, 35]) (hop : ¬ ReadsGas op) (m : Machine) (d x : Nat)
    (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = bump d x ps m') (bump d x ps m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    bump, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_bump_wp` for the opcodes of constructor index in `[36, 37, 38, 39, 40, 41]` (split for parallel elaboration). -/
theorem exec_bump_wp_6 (op : Opcode) (hk : op.ctorIdx ∈ [36, 37, 38, 39, 40, 41]) (hop : ¬ ReadsGas op) (m : Machine) (d x : Nat)
    (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = bump d x ps m') (bump d x ps m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    bump, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_bump_wp` for the opcodes of constructor index in `[43, 44, 45, 46, 47, 48]` (split for parallel elaboration). -/
theorem exec_bump_wp_7 (op : Opcode) (hk : op.ctorIdx ∈ [43, 44, 45, 46, 47, 48]) (hop : ¬ ReadsGas op) (m : Machine) (d x : Nat)
    (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = bump d x ps m') (bump d x ps m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    bump, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_bump_wp` for the opcodes of constructor index in `[49, 50, 51, 52, 53, 54]` (split for parallel elaboration). -/
theorem exec_bump_wp_8 (op : Opcode) (hk : op.ctorIdx ∈ [49, 50, 51, 52, 53, 54]) (hop : ¬ ReadsGas op) (m : Machine) (d x : Nat)
    (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = bump d x ps m') (bump d x ps m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    bump, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_bump_wp` for the opcodes of constructor index in `[55, 56, 57, 58, 59, 60]` (split for parallel elaboration). -/
theorem exec_bump_wp_9 (op : Opcode) (hk : op.ctorIdx ∈ [55, 56, 57, 58, 59, 60]) (hop : ¬ ReadsGas op) (m : Machine) (d x : Nat)
    (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = bump d x ps m') (bump d x ps m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    bump, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_bump_wp` for the opcodes of constructor index in `[61, 62, 63, 64, 66, 67]` (split for parallel elaboration). -/
theorem exec_bump_wp_10 (op : Opcode) (hk : op.ctorIdx ∈ [61, 62, 63, 64, 66, 67]) (hop : ¬ ReadsGas op) (m : Machine) (d x : Nat)
    (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = bump d x ps m') (bump d x ps m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    bump, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- `exec_bump_wp` for the opcodes of constructor index in `[68, 69, 70, 77, 81, 82, 83]` (split for parallel elaboration). -/
theorem exec_bump_wp_11 (op : Opcode) (hk : op.ctorIdx ∈ [68, 69, 70, 77, 81, 82, 83]) (hop : ¬ ReadsGas op) (m : Machine) (d x : Nat)
    (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = bump d x ps m') (bump d x ps m)) m := by
  cases op <;> (try exact absurd hk (by dsimp only [Opcode.ctorIdx]; decide)) <;> clear hk
  all_goals simp [exec, binOp, unOp, ternOp, pushValue, copyToMemory, readOutput,
    memoryExpansion, expandMemory, writeMemory, readMemory, accessStorageKey, requireNonStatic,
    bump, execSstore, execSelfdestruct] <;> intros <;> (try simp_all) <;> omega

set_option maxHeartbeats 8000000 in
theorem exec_bump_wp (op : Opcode) (hop : ¬ ReadsGas op) (m : Machine) (d x : Nat)
    (ps : List Frame) :
    Wp (exec op) (fun a m' => Twp (exec op)
      (fun a' m'' => a' = a ∧ m'' = bump d x ps m') (bump d x ps m)) m := by
  cases op
  all_goals first
    | (exact absurd trivial hop) |
      exact exec_bump_wp_s _ (by dsimp only [Opcode.ctorIdx]; decide) hop m d x ps |
      exact exec_bump_wp_0 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m d x ps |
      exact exec_bump_wp_1 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m d x ps |
      exact exec_bump_wp_2 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m d x ps |
      exact exec_bump_wp_3 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m d x ps |
      exact exec_bump_wp_4 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m d x ps |
      exact exec_bump_wp_5 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m d x ps |
      exact exec_bump_wp_6 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m d x ps |
      exact exec_bump_wp_7 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m d x ps |
      exact exec_bump_wp_8 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m d x ps |
      exact exec_bump_wp_9 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m d x ps |
      exact exec_bump_wp_10 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m d x ps |
      exact exec_bump_wp_11 _ (by dsimp only [Opcode.ctorIdx]; decide) hop m d x ps
    | fail "exec_bump_wp: no group"

/-- **Gas monotonicity of one instruction**, as run equations. -/
theorem exec_bump (op : Opcode) (hop : ¬ ReadsGas op) {m m' : Machine} {a : Action}
    (h : (exec op).run m = .ok (a, m')) (d x : Nat) (ps : List Frame) :
    (exec op).run (bump d x ps m) = .ok (a, bump d x ps m') := by
  have hw := (exec_bump_wp op hop m d x ps).of_run h
  unfold Twp at hw
  split at hw
  · rename_i a' m'' he
    obtain ⟨rfl, rfl⟩ := hw
    exact he
  · exact hw.elim

end EvmLogic.Program.Nested
