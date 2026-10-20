import EvmLeanProofs.Program.Summary

/-!
# A weakest-precondition calculus for the instruction monad

`Wp x Q m`: if the instruction-monad computation `x` succeeds from machine `m` with value `a`
and machine `m'`, then `Q a m'` (exceptional halts satisfy every postcondition: the step
semantics discards the machine of a failing instruction). The simp lemmas `wp_bind`,
`wp_pure`, `wp_get`, … push `Wp` through `do` blocks, so a generic property of an instruction
(one that must hold for *every* stack, memory, gas and world) reduces to a formula over the
machine's fields that `split` and `simp` close.

Used by `NestedExtraFrame` to prove, once for every opcode, what an instruction can change.
-/

namespace EvmLean.Program.Nested

open Interpreter

/-- Weakest precondition: if `x` succeeds from `m` with value `a` and machine `m'`, then
`Q a m'`. -/
def Wp {α : Type} (x : M α) (Q : α → Machine → Prop) (m : Machine) : Prop :=
  match x.run m with
  | .ok (a, m') => Q a m'
  | .error _ => True

variable {α β : Type} {Q : α → Machine → Prop} {m : Machine}

/-- Read off a successful run. -/
theorem Wp.of_run {x : M α} {a : α} {m' : Machine} (hw : Wp x Q m) (h : x.run m = .ok (a, m')) :
    Q a m' := by
  unfold Wp at hw; rw [h] at hw; exact hw

/-- Consequence. -/
theorem Wp.mono {x : M α} {Q' : α → Machine → Prop} (h : Wp x Q m)
    (hq : ∀ a m', Q a m' → Q' a m') : Wp x Q' m := by
  unfold Wp at *
  split at h
  · exact hq _ _ h
  · trivial

@[simp] theorem wp_pure (a : α) : Wp (pure a : M α) Q m ↔ Q a m := Iff.rfl

@[simp] theorem wp_bind (x : M α) (f : α → M β) (Q : β → Machine → Prop) :
    Wp (x >>= f) Q m ↔ Wp x (fun a m' => Wp (f a) Q m') m := by
  unfold Wp
  simp only [StateT.run_bind]
  cases x.run m with
  | error e => simp [bind, Except.bind]
  | ok p => obtain ⟨a, m'⟩ := p; simp [bind, Except.bind]

@[simp] theorem wp_get {Q : Machine → Machine → Prop} : Wp (get : M Machine) Q m ↔ Q m m :=
  Iff.rfl

@[simp] theorem wp_set (m' : Machine) {Q : PUnit → Machine → Prop} :
    Wp (set m' : M PUnit) Q m ↔ Q ⟨⟩ m' := Iff.rfl

@[simp] theorem wp_modify (f : Machine → Machine) {Q : PUnit → Machine → Prop} :
    Wp (modify f : M PUnit) Q m ↔ Q ⟨⟩ (f m) := Iff.rfl

@[simp] theorem wp_modifyGet (f : Machine → α × Machine) :
    Wp (modifyGet f : M α) Q m ↔ Q (f m).1 (f m).2 := Iff.rfl

@[simp] theorem wp_throw (e : ExceptionalHalt) : Wp (throw e : M α) Q m := trivial

@[simp] theorem wp_throwThe (e : ExceptionalHalt) : Wp (throwThe ExceptionalHalt e : M α) Q m :=
  trivial

@[simp] theorem wp_ite {c : Prop} [Decidable c] (x y : M α) :
    Wp (if c then x else y) Q m ↔ (c → Wp x Q m) ∧ (¬ c → Wp y Q m) := by
  by_cases h : c <;> simp [h]

@[simp] theorem wp_dite {c : Prop} [Decidable c] (x : c → M α) (y : ¬ c → M α) :
    Wp (dite c x y) Q m ↔ (∀ h : c, Wp (x h) Q m) ∧ (∀ h : ¬ c, Wp (y h) Q m) := by
  by_cases h : c <;> simp [h]

@[simp] theorem wp_getFrame {Q : Frame → Machine → Prop} : Wp getFrame Q m ↔ Q m.frame m :=
  Iff.rfl

@[simp] theorem wp_modifyFrame (f : Frame → Frame) {Q : Unit → Machine → Prop} :
    Wp (modifyFrame f) Q m ↔ Q () { m with frame := f m.frame } := Iff.rfl

@[simp] theorem wp_modifyWorld (f : World → World) {Q : Unit → Machine → Prop} :
    Wp (modifyWorld f) Q m ↔ Q () { m with world := f m.world } := Iff.rfl

@[simp] theorem wp_modifySub (f : Substate → Substate) {Q : Unit → Machine → Prop} :
    Wp (modifySub f) Q m ↔ Q () { m with frame := { m.frame with sub := f m.frame.sub } } :=
  Iff.rfl

@[simp] theorem wp_map (f : α → β) (x : M α) (Q : β → Machine → Prop) :
    Wp (f <$> x) Q m ↔ Wp x (fun a m' => Q (f a) m') m := by
  rw [map_eq_pure_bind, wp_bind]; rfl

@[simp] theorem wp_seqRight (x : M α) (y : M β) (Q : β → Machine → Prop) :
    Wp (x *> y) Q m ↔ Wp x (fun _ m' => Wp y Q m') m := by
  rw [seqRight_eq_bind, wp_bind]

/-! ## The stack, gas and pc primitives -/

@[simp] theorem wp_pop {Q : Word → Machine → Prop} :
    Wp pop Q m ↔ ∀ x xs, m.frame.stack = x :: xs →
      Q x { m with frame := { m.frame with stack := xs } } := by
  unfold pop
  rw [wp_bind, wp_getFrame]
  cases h : m.frame.stack with
  | nil => simp
  | cons x xs => simp

@[simp] theorem wp_popNat {Q : Nat → Machine → Prop} :
    Wp popNat Q m ↔ ∀ x xs, m.frame.stack = x :: xs →
      Q x.toNat { m with frame := { m.frame with stack := xs } } := by
  unfold popNat
  simp only [wp_bind, wp_pop, wp_pure]

@[simp] theorem wp_popAddress {Q : Address → Machine → Prop} :
    Wp popAddress Q m ↔ ∀ x xs, m.frame.stack = x :: xs →
      Q (Word.toAddress x) { m with frame := { m.frame with stack := xs } } := by
  unfold popAddress
  simp only [wp_bind, wp_pop, wp_pure]

@[simp] theorem wp_push (w : Word) {Q : Unit → Machine → Prop} :
    Wp (push w) Q m ↔ (m.frame.stack.length < Gas.stackLimit →
      Q () { m with frame := { m.frame with stack := w :: m.frame.stack } }) := by
  unfold push
  simp

@[simp] theorem wp_charge (c : Nat) {Q : Unit → Machine → Prop} :
    Wp (charge c) Q m ↔ (c ≤ m.frame.gasLeft →
      Q () { m with frame := { m.frame with gasLeft := m.frame.gasLeft - c } }) := by
  unfold charge
  simp

@[simp] theorem wp_refundGas (c : Nat) {Q : Unit → Machine → Prop} :
    Wp (refundGas c) Q m ↔ Q () { m with frame := { m.frame with gasLeft := m.frame.gasLeft + c } } :=
  Iff.rfl

@[simp] theorem wp_advance (n : Nat) {Q : Unit → Machine → Prop} :
    Wp (advance n) Q m ↔ Q () { m with frame := { m.frame with pc := m.frame.pc + n } } := Iff.rfl

/-- `popN` only pops: a postcondition holding for every popped list and remaining stack holds. -/
theorem wp_popN_of (n : Nat) {Q : List Word → Machine → Prop} {m : Machine}
    (h : ∀ xs rest, Q xs { m with frame := { m.frame with stack := rest } }) :
    Wp (popN n) Q m := by
  induction n generalizing Q m with
  | zero => exact h [] m.frame.stack
  | succ n ih =>
    unfold popN
    simp only [wp_bind, wp_pop, wp_pure]
    intro x xs _
    exact ih (fun ys rest => h (x :: ys) rest)

end EvmLean.Program.Nested
