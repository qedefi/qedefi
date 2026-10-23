import QEDefi.Actor.Delay

/-!
# Worked example: notice from a timelock

OpenZeppelin `TimelockController` semantics, for the parameter `value` it governs: an
operation id `k` is content-addressed (`pl k`, the hash of target and calldata, determines its
payload); proposers `schedule(k, delay)` with `delay ≥ minDelay`, setting the ready time to
`now + delay`; once ready, `execute(k)` (by an executor; the open role when `executors` is
everything) runs the payload once; cancellers `cancel(k)`. `updateDelay` is a payload: the delay
changes only through the timelock itself.

`value_notice`: whenever `value` changes, at time `τ`, some operation was pending at the start
or was scheduled at a time `t` with `t + minDelay ≤ η ≤ τ`, the delay being the one in force
when it was scheduled. This is `QEDefi.Actor.Delayed.notice`; the model only discharges its two
obligations.
-/

namespace Examples.Actor.Timelock

open QEDefi.Actor QEDefi.Trace.Lift
open Classical

variable {A K : Type}

/-- What an operation does when executed. -/
inductive Payload where
  | setValue (v : ℕ)
  | updateDelay (d : ℕ)

structure St (K : Type) where
  ready : K → Option ℕ
  done : K → Bool
  minDelay : ℕ
  value : ℕ

/-- The timelock's roles and the content addressing of operations. -/
structure Params (A K : Type) where
  proposers : Set A
  executors : Set A
  cancellers : Set A
  pl : K → Payload

/-- A transaction, with the block timestamp it runs at. -/
inductive Tx (A K : Type) where
  | schedule (sender : A) (k : K) (delay now : ℕ)
  | execute (sender : A) (k : K) (now : ℕ)
  | cancel (sender : A) (k : K) (now : ℕ)

def Tx.now : Tx A K → ℕ
  | .schedule _ _ _ n | .execute _ _ n | .cancel _ _ n => n

variable (D : Params A K)

/-- The effect of a payload. -/
def apply (s : St K) : Payload → St K
  | .setValue v => { s with value := v }
  | .updateDelay d => { s with minDelay := d }

noncomputable def step (s : St K) : Tx A K → Option (St K)
  | .schedule b k delay now =>
    if b ∈ D.proposers ∧ s.ready k = none ∧ s.done k = false ∧ s.minDelay ≤ delay then
      some { s with ready := Function.update s.ready k (some (now + delay)) }
    else none
  | .execute b k now =>
    if b ∈ D.executors ∧ s.done k = false ∧ ∃ η, s.ready k = some η ∧ η ≤ now then
      some { apply s (D.pl k) with
        ready := Function.update s.ready k none, done := Function.update s.done k true }
    else none
  | .cancel b k _ =>
    if b ∈ D.cancellers ∧ s.done k = false ∧ s.ready k ≠ none then
      some { s with ready := Function.update s.ready k none }
    else none

/-- **The obligations of a delayed effect** for `value`. -/
theorem delayed :
    Delayed (step D) Tx.now (fun k s => s.ready k) St.minDelay (Same St.value) := by
  refine ⟨Same.refl _, ?_, ?_⟩
  · intro s op s' he hk
    cases op with
    | schedule b k delay now =>
      simp only [step] at he; split_ifs at he; cases he; exact absurd rfl hk
    | execute b k now =>
      simp only [step] at he; split_ifs at he with h
      obtain ⟨-, -, η, hη, hle⟩ := h
      exact ⟨k, η, hη, hle⟩
    | cancel b k now =>
      simp only [step] at he; split_ifs at he; cases he; exact absurd rfl hk
  · intro s op s' k η he hs hne
    cases op with
    | schedule b k' delay now =>
      simp only [step] at he; split_ifs at he with h
      obtain ⟨-, -, -, hd⟩ := h
      cases he
      by_cases hk : k = k'
      · subst hk; simp at hs; simp [Tx.now]; omega
      · simp [Function.update_of_ne hk] at hs; exact absurd hs hne
    | execute b k' now =>
      simp only [step] at he; split_ifs at he; cases he
      by_cases hk : k = k'
      · subst hk; simp at hs
      · simp [Function.update_of_ne hk] at hs; exact absurd hs hne
    | cancel b k' now =>
      simp only [step] at he; split_ifs at he; cases he
      by_cases hk : k = k'
      · subst hk; simp at hs
      · simp [Function.update_of_ne hk] at hs; exact absurd hs hne

/-- **Notice for `value`.** If the transaction `op` after `ops₁` changes `value`, it runs no
earlier than the ready time `η` of some operation `k`, which was pending at the start or was
scheduled by an earlier transaction `o` at least `minDelay` (as of then) before `η`. -/
theorem value_notice (s₀ : St K) (ops₁ : List (Tx A K)) (op : Tx A K)
    (hb : (stepD (step D) (exec (step D) s₀ ops₁) op).value ≠ (exec (step D) s₀ ops₁).value) :
    ∃ k η, η ≤ op.now ∧ (s₀.ready k = some η ∨ ∃ l₁ o l₂, ops₁ = l₁ ++ o :: l₂ ∧
      o.now + (exec (step D) s₀ l₁).minDelay ≤ η) := by
  obtain ⟨k, η, hle, h⟩ := (delayed D).notice s₀ ops₁ op hb
  exact ⟨k, η, hle, h.imp id fun ⟨l₁, o, l₂, he, ht, _⟩ => ⟨l₁, o, l₂, he, ht⟩⟩

end Examples.Actor.Timelock
