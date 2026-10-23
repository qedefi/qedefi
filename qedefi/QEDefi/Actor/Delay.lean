import QEDefi.Actor.Trace

/-!
# Notice: delayed effects are announced in advance

Timelocks (OpenZeppelin `TimelockController`, Compound `Timelock`, `DSPause`, `AccessManager`
scheduled operations, `AccessControlDefaultAdminRules`, Solady's ownership handover) protect an
effect by stored **ready times** `eta k s : Option ℕ`, one per operation id `k`: the effect needs
a ripe ready time, `eta k s = some η` with `η ≤ now`, and a step that sets a ready time puts it
at least the delay `d s` in force (e.g. `minDelay`) after its own time. Then every occurrence of
the effect at time `τ` was preceded by a step at a time `t` with `t + d ≤ η ≤ τ` that set the
ready time, unless it was already pending at the start (`Delayed.notice`). With the event the
setting step emits, users have at least `d` seconds to react. No assumption on clocks is needed:
the bound comes from the stored `η`. Delays that change (`updateDelay`, itself timelocked) are
covered because `d` is read in the state of the setting step.
-/

namespace QEDefi.Actor

open QEDefi.Trace.Lift

variable {S O K : Type}

/-- **A delayed effect**: steps that break `Keep` need a ripe ready time; a step that changes the
ready time of `k` to `some η` runs at a time `t` with `t + d s ≤ η` (`s` its pre-state). -/
structure Delayed (step : S → O → Option S) (time : O → ℕ) (eta : K → S → Option ℕ)
    (d : S → ℕ) (Keep : S → S → Prop) : Prop where
  refl : ∀ s, Keep s s
  ripe : ∀ s op s', step s op = some s' → ¬ Keep s s' →
    ∃ k η, eta k s = some η ∧ η ≤ time op
  set : ∀ s op s' k η, step s op = some s' → eta k s' = some η → eta k s ≠ some η →
    time op + d s ≤ η

variable {step : S → O → Option S} {time : O → ℕ} {eta : K → S → Option ℕ} {d : S → ℕ}
  {Keep : S → S → Prop}

/-- A stored ready time was either there at the start or set by a step of the execution, at a
time at least the delay then in force before it. -/
theorem Delayed.origin (h : Delayed step time eta d Keep) (k : K) {η : ℕ} :
    ∀ (s₀ : S) (ops : List O), eta k (exec step s₀ ops) = some η →
      eta k s₀ = some η ∨ ∃ l₁ o l₂, ops = l₁ ++ o :: l₂ ∧ time o + d (exec step s₀ l₁) ≤ η ∧
        eta k (exec step s₀ l₁) ≠ some η ∧ eta k (stepD step (exec step s₀ l₁) o) = some η
  | s₀, [], he => Or.inl he
  | s₀, o :: ops, he => by
    rcases Delayed.origin h k (stepD step s₀ o) ops he with h₁ | ⟨l₁, o', l₂, rfl, ht, hne, hset⟩
    · by_cases h₀ : eta k s₀ = some η
      · exact Or.inl h₀
      · refine Or.inr ⟨[], o, ops, rfl, ?_, h₀, h₁⟩
        unfold QEDefi.Trace.Lift.stepD at h₁
        cases e : step s₀ o with
        | none => rw [e] at h₁; exact absurd h₁ h₀
        | some s' => rw [e] at h₁; exact h.set s₀ o s' k η e h₁ h₀
    · exact Or.inr ⟨o :: l₁, o', l₂, rfl, ht, hne, hset⟩

/-- **Notice.** If the step `op` after the prefix `ops₁` breaks `Keep`, it runs at a time
`time op ≥ η` for the ready time `η` of some operation `k` that was pending at the start or was
set by an earlier step `o`, with `time o + d ≤ η` for the delay `d` in force before `o`. -/
theorem Delayed.notice (h : Delayed step time eta d Keep) (s₀ : S) (ops₁ : List O) (op : O)
    (hb : ¬ Keep (exec step s₀ ops₁) (stepD step (exec step s₀ ops₁) op)) :
    ∃ k η, η ≤ time op ∧ (eta k s₀ = some η ∨ ∃ l₁ o l₂, ops₁ = l₁ ++ o :: l₂ ∧
      time o + d (exec step s₀ l₁) ≤ η ∧ eta k (exec step s₀ l₁) ≠ some η ∧
      eta k (stepD step (exec step s₀ l₁) o) = some η) := by
  unfold QEDefi.Trace.Lift.stepD at hb
  cases e : step (exec step s₀ ops₁) op with
  | none => rw [e] at hb; exact absurd (h.refl _) hb
  | some s' =>
    rw [e] at hb
    obtain ⟨k, η, he, hle⟩ := h.ripe _ op s' e hb
    exact ⟨k, η, hle, h.origin k s₀ ops₁ he⟩

end QEDefi.Actor
