import EvmLogic.Step.Basic

/-!
# Run composition

`stepN n m` counts steps exactly (the machine after `n` steps, or the final result) and is
related to `run fuel m`: `run_eq_stepN`, sequencing (`stepN_add_of_running`,
`run_add_of_stepN`) and fuel monotonicity (`run_mono`). Independent of the instruction semantics.
-/

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter

/-- The machine after `n` steps, or the final result if the top-level frame finished within
`n` steps. -/
def stepN : Nat → Machine → StepResult
  | 0, m => .running m
  | n + 1, m =>
    match step m with
    | .done r => .done r
    | .running m' => stepN n m'

variable {m m' : Machine} {r : MessageResult}

@[simp] theorem stepN_zero (m : Machine) : stepN 0 m = .running m := rfl

theorem stepN_succ_of_running {n : Nat} (h : step m = .running m') :
    stepN (n + 1) m = stepN n m' := by
  simp only [stepN, h]

theorem stepN_succ_of_done {n : Nat} (h : step m = .done r) : stepN (n + 1) m = .done r := by
  simp only [stepN, h]

theorem stepN_one (m : Machine) : stepN 1 m = step m := by
  simp only [stepN]
  split <;> simp_all

theorem stepN_add_of_done {a : Nat} (h : stepN a m = .done r) (b : Nat) :
    stepN (a + b) m = .done r := by
  induction a generalizing m with
  | zero => simp at h
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [stepN] at h ⊢
    split at h
    · simp_all
    · exact ih h

/-- **Sequencing of step counts.** -/
theorem stepN_add_of_running {a : Nat} (h : stepN a m = .running m') (b : Nat) :
    stepN (a + b) m = stepN b m' := by
  induction a generalizing m with
  | zero =>
    simp only [stepN_zero, StepResult.running.injEq] at h
    subst h
    simp
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [stepN] at h ⊢
    split at h
    · simp at h
    · exact ih h

theorem stepN_add (a b : Nat) (m : Machine) :
    stepN (a + b) m = match stepN a m with
      | .done r => .done r
      | .running m' => stepN b m' := by
  cases h : stepN a m with
  | done r => exact stepN_add_of_done h b
  | running m' => exact stepN_add_of_running h b

theorem stepN_succ' (n : Nat) (m : Machine) :
    stepN (n + 1) m = match stepN n m with
      | .done r => .done r
      | .running m' => step m' := by
  rw [stepN_add]
  cases stepN n m <;> simp [stepN_one]

/-- `run` is `stepN` with running-out-of-fuel reported as an error. -/
theorem run_eq_stepN (n : Nat) (m : Machine) :
    run n m = match stepN n m with
      | .done r => .ok r
      | .running _ => .error {} := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    cases hs : step m with
    | done r => simp only [run, stepN, hs]
    | running m' => simp only [run, stepN, hs]; exact ih _

theorem run_eq_ok_iff {n : Nat} : run n m = .ok r ↔ stepN n m = .done r := by
  rw [run_eq_stepN]
  split <;> simp_all

theorem run_of_stepN_done {n : Nat} (h : stepN n m = .done r) : run n m = .ok r :=
  run_eq_ok_iff.mpr h

/-- **Sequencing for `run`**: after `a` steps reaching the running machine `m'`. -/
theorem run_add_of_stepN {a : Nat} (h : stepN a m = .running m') (b : Nat) :
    run (a + b) m = run b m' := by
  rw [run_eq_stepN, run_eq_stepN, stepN_add_of_running h]

/-- **Fuel monotonicity**: once `run` has a result, more fuel gives the same result. -/
theorem run_mono {n n' : Nat} (h : run n m = .ok r) (hle : n ≤ n') : run n' m = .ok r := by
  obtain ⟨k, rfl⟩ : ∃ k, n' = n + k := ⟨n' - n, by omega⟩
  exact run_add_of_ok h k

theorem run_eq_of_le {n : Nat} (h : run n m = .ok r) :
    ∀ fuel, n ≤ fuel → run fuel m = .ok r :=
  fun _ hle => run_mono h hle

end EvmLogic.Program
