import EvmLogic.Step.Basic

/-!
# Run composition

`run fuel m` iterates `step` at most `fuel` times. To compose facts about pieces of an
execution we count steps exactly with `stepN n m : StepResult`, the machine after `n` steps
(or the final `MessageResult` if the top-level frame finished earlier), and relate it to `run`:

* `run_eq_stepN`: `run n m` is `.ok r` iff `stepN n m = .done r`, and runs out of fuel iff
  `stepN n m` is still running;
* `stepN_add_of_running`, `run_add_of_stepN`: an execution prefix of `a` steps that ends in a
  running machine `m'` can be cut off, `run (a + b) m = run b m'` (**sequencing**);
* `run_mono`: more fuel never changes a finished result (**fuel monotonicity**).

Nothing here depends on the instruction semantics: everything follows from the definitions of
`run` and `stepN`, for every fork, every `Crypto` and every precompile implementation.
-/

namespace EvmLogic.Program
open EvmLean

open EvmLean.Interpreter

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

/-- One step, then `n` more. -/
theorem stepN_succ_of_running {n : Nat} (h : step m = .running m') :
    stepN (n + 1) m = stepN n m' := by
  simp only [stepN, h]

/-- A finished execution stays finished. -/
theorem stepN_succ_of_done {n : Nat} (h : step m = .done r) : stepN (n + 1) m = .done r := by
  simp only [stepN, h]

/-- One step of `stepN` is `step`. -/
theorem stepN_one (m : Machine) : stepN 1 m = step m := by
  simp only [stepN]
  split <;> simp_all

/-- `stepN` is never finished after zero steps, and `.done` is absorbing. -/
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

/-- `stepN` splits at any intermediate point. -/
theorem stepN_add (a b : Nat) (m : Machine) :
    stepN (a + b) m = match stepN a m with
      | .done r => .done r
      | .running m' => stepN b m' := by
  cases h : stepN a m with
  | done r => exact stepN_add_of_done h b
  | running m' => exact stepN_add_of_running h b

/-- `n + 1` steps: `n` steps, then one more. -/
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

/-- `run` succeeds exactly when `stepN` finishes. -/
theorem run_eq_ok_iff {n : Nat} : run n m = .ok r ↔ stepN n m = .done r := by
  rw [run_eq_stepN]
  split <;> simp_all

/-- A finished `stepN` is a finished `run`. -/
theorem run_of_stepN_done {n : Nat} (h : stepN n m = .done r) : run n m = .ok r :=
  run_eq_ok_iff.mpr h

/-- **Sequencing for `run`**: after a prefix of `a` steps reaching the running machine `m'`,
`run` continues from `m'` with the remaining fuel. -/
theorem run_add_of_stepN {a : Nat} (h : stepN a m = .running m') (b : Nat) :
    run (a + b) m = run b m' := by
  rw [run_eq_stepN, run_eq_stepN, stepN_add_of_running h]

/-- **Fuel monotonicity**: once `run` has a result, more fuel gives the same result. -/
theorem run_mono {n n' : Nat} (h : run n m = .ok r) (hle : n ≤ n') : run n' m = .ok r := by
  obtain ⟨k, rfl⟩ : ∃ k, n' = n + k := ⟨n' - n, by omega⟩
  exact run_add_of_ok h k

/-- A finished `run` is unaffected by extra fuel, stated with a lower bound. -/
theorem run_eq_of_le {n : Nat} (h : run n m = .ok r) :
    ∀ fuel, n ≤ fuel → run fuel m = .ok r :=
  fun _ hle => run_mono h hle

end EvmLogic.Program
