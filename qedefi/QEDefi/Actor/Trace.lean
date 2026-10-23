import QEDefi.Actor.Derive
import QEDefi.Trace.Lift

/-!
# Who can cause an effect, along any trace

A model (`step : S → O → Option S`, `QEDefi.Trace.Lift` conventions) with authority rules `R`
and, for each operation, the keys that **consent** to it (`consent op`: its sender, the
signers of the signatures it carries) meets two obligations:

- `Stable`: a step adds authority only through its own consenters: whatever is derivable
  after it from keys `X` was derivable before it from `X` and the step's consenters. A role
  grant, an added owner, a scheduled operation, an approved hash all satisfy this, because the
  consenters were authorised to make them. A model whose rules forget a path to authority
  (an escalation, an open initialiser, a relay) fails it.
- `Guards Q Keep`: a step whose consenters derive no capability in `Q` keeps `Keep` (the
  protected part of the state is unchanged, or changes only in allowed ways).

Then (`Guards.exec_keep`) along **any** sequence of operations whose consenters are among `T`,
if `T` derives nothing in `Q` initially, `Keep` holds from the initial to the final state. No
trust assumption: the statement says exactly whose action can break `Keep`. Its contrapositive
(`Guards.derives_of_not_keep`) reads "if the protected state changed, the actors of the trace
could derive a capability in `Q`".

Trust assumptions go through `ExecAll` (every step of the execution satisfies a policy, e.g.
"every step that exercises `Q` follows `π`"); `Guards.lift` and `ExecAll.lift_invariant`
transfer both kinds of statement to bytecode through any `System.Refinement`.
-/

namespace QEDefi.Actor

open QEDefi.Trace.Lift

variable {S O A P : Type}

/-! ## Obligations -/

/-- **Authority stability**: a successful step extends what any keys `X` derive by at most what
the step's consenters derived before it. -/
def Stable (step : S → O → Option S) (consent : O → Set A) (R : Rules S A P) : Prop :=
  ∀ s op s', step s op = some s' → ∀ (X : Set A) r, Derives R s' X r →
    Derives R s (X ∪ consent op) r

/-- **How stability is proved, generally**: every rule after the step, with premises derivable
before it from `X` and the consenters `C`, yields a capability so derivable. -/
theorem stable_step {R : Rules S A P} {s s' : S} {C : Set A}
    (h : ∀ (X : Set A) q Y, R s' q Y → (∀ r ∈ Y, Derives R s (X ∪ C) r) →
      Derives R s (X ∪ C) q) (X : Set A) {r : A × P} (hd : Derives R s' X r) :
    Derives R s (X ∪ C) r :=
  Derives.le_of_closed (fun _ ha p => .key p (Set.mem_union_left C ha))
    (fun q Y hr hY => h X q Y hr hY) hd

/-- **How stability is proved, usually**: each rule after the step either held before it, or
its conclusion was derivable before it by the step's consenters alone ("only who controls a
capability creates new ways to it": a grant by the role's admin, an owner added by the Safe's
signers, a hash approved by its owner). -/
theorem stable_of_grows {R : Rules S A P} {s s' : S} {C : Set A}
    (h : ∀ q Y, R s' q Y → R s q Y ∨ Derives R s C q) (X : Set A) {r : A × P}
    (hd : Derives R s' X r) : Derives R s (X ∪ C) r :=
  stable_step (fun _ q Y hr hY => (h q Y hr).elim (fun h₀ => .rule h₀ hY)
    (fun hc => hc.mono_keys Set.subset_union_right)) X hd

/-- A step that only removes rules is stable. -/
theorem stable_of_le {R : Rules S A P} {s s' : S} {C : Set A}
    (h : ∀ q Y, R s' q Y → R s q Y) (X : Set A) {r : A × P} (hd : Derives R s' X r) :
    Derives R s (X ∪ C) r :=
  stable_of_grows (fun q Y hr => Or.inl (h q Y hr)) X hd

/-- **Effect guard**: a successful step whose consenters derive no capability in `Q` keeps
`Keep`, a preorder on states (the protected part does not change, or changes only as allowed).
`Q` is typically one capability (`(· = q)`) or a family (`(px, act (upgrade x))` for all `x`). -/
structure Guards (step : S → O → Option S) (consent : O → Set A) (R : Rules S A P)
    (Q : A × P → Prop) (Keep : S → S → Prop) : Prop where
  refl : ∀ s, Keep s s
  trans : ∀ {s₁ s₂ s₃}, Keep s₁ s₂ → Keep s₂ s₃ → Keep s₁ s₃
  effect : ∀ s op s', step s op = some s' → (∀ q, Q q → ¬ Derives R s (consent op) q) →
    Keep s s'

/-- The protected part `f` of the state is unchanged. -/
def Same {β : Type} (f : S → β) (s s' : S) : Prop := f s' = f s

theorem Same.refl {β : Type} (f : S → β) (s : S) : Same f s s := rfl

theorem Same.trans {β : Type} {f : S → β} {s₁ s₂ s₃ : S} (h₁ : Same f s₁ s₂)
    (h₂ : Same f s₂ s₃) : Same f s₁ s₃ := Eq.trans h₂ h₁

/-- A guard for "`f` unchanged" from its step obligation. -/
theorem Guards.same {β : Type} {step : S → O → Option S} {consent : O → Set A}
    {R : Rules S A P} {Q : A × P → Prop} {f : S → β}
    (h : ∀ s op s', step s op = some s' → (∀ q, Q q → ¬ Derives R s (consent op) q) →
      f s' = f s) :
    Guards step consent R Q (Same f) :=
  ⟨Same.refl f, Same.trans, h⟩

/-! ## Executions -/

variable {step : S → O → Option S} {consent : O → Set A} {R : Rules S A P}

/-- `Stable` for a step that may revert (a reverted step changes nothing). -/
theorem Stable.stepD (h : Stable step consent R) (s : S) (op : O) {X : Set A} {r : A × P}
    (hd : Derives R (QEDefi.Trace.Lift.stepD step s op) X r) : Derives R s (X ∪ consent op) r := by
  unfold QEDefi.Trace.Lift.stepD at hd
  cases e : step s op with
  | none => rw [e] at hd; exact hd.mono_keys Set.subset_union_left
  | some s' => rw [e] at hd; exact h s op s' e X r hd

/-- **Authority along an execution**: whatever keys `X` derive at the end, they derived at the
start together with the trace's consenters `T`. -/
theorem Stable.exec (h : Stable step consent R) {T : Set A} :
    ∀ (s : S) (ops : List O), (∀ op ∈ ops, consent op ⊆ T) → ∀ {X : Set A} {r : A × P},
      Derives R (QEDefi.Trace.Lift.exec step s ops) X r → Derives R s (X ∪ T) r
  | s, [], _, _, _, hd => hd.mono_keys Set.subset_union_left
  | s, op :: ops, hT, X, r, hd => by
    have h₁ := h.exec (QEDefi.Trace.Lift.stepD step s op) ops (fun o ho => hT o (by simp [ho])) hd
    have h₂ := h.stepD s op h₁
    refine h₂.mono_keys ?_
    have hc := hT op (by simp)
    intro a ha
    rcases ha with (ha | ha) | ha
    · exact Or.inl ha
    · exact Or.inr ha
    · exact Or.inr (hc ha)

/-- **Until a controller acts.** Along any execution whose consenters are among `T`, if `T`
derives no capability in `Q` at the start, the protected state is kept. -/
theorem Guards.exec_keep {Q : A × P → Prop} {Keep : S → S → Prop} (hs : Stable step consent R)
    (hg : Guards step consent R Q Keep) {T : Set A} :
    ∀ (s₀ : S) (ops : List O), (∀ op ∈ ops, consent op ⊆ T) →
      (∀ q, Q q → ¬ Derives R s₀ T q) → Keep s₀ (QEDefi.Trace.Lift.exec step s₀ ops)
  | s₀, [], _, _ => hg.refl s₀
  | s₀, op :: ops, hT, hq => by
    have hc : consent op ⊆ T := hT op (by simp)
    have hT' : ∀ o ∈ ops, consent o ⊆ T := fun o ho => hT o (by simp [ho])
    have hk₁ : Keep s₀ (QEDefi.Trace.Lift.stepD step s₀ op) := by
      unfold QEDefi.Trace.Lift.stepD
      cases e : step s₀ op with
      | none => exact hg.refl s₀
      | some s' => exact hg.effect s₀ op s' e (fun q hQ hd => hq q hQ (hd.mono_keys hc))
    -- `T` derives nothing in `Q` after the step either.
    have hq₁ : ∀ q, Q q → ¬ Derives R (QEDefi.Trace.Lift.stepD step s₀ op) T q :=
      fun q hQ hd => by
        have := hs.stepD s₀ op hd
        exact hq q hQ (this.mono_keys (Set.union_subset (subset_refl T) hc))
    exact hg.trans hk₁ (Guards.exec_keep hs hg _ ops hT' hq₁)

/-- **Who changed it**: if the protected state was not kept, the trace's consenters could
derive a capability in `Q` at the start. -/
theorem Guards.derives_of_not_keep {Q : A × P → Prop} {Keep : S → S → Prop}
    (hs : Stable step consent R) (hg : Guards step consent R Q Keep) {T : Set A} {s₀ : S}
    {ops : List O} (hT : ∀ op ∈ ops, consent op ⊆ T)
    (hk : ¬ Keep s₀ (QEDefi.Trace.Lift.exec step s₀ ops)) : ∃ q, Q q ∧ Derives R s₀ T q :=
  Classical.byContradiction fun hq =>
    hk (hg.exec_keep hs s₀ ops hT (fun q hQ hd => hq ⟨q, hQ, hd⟩))

/-- Non-derivability is kept along any execution by the keys that cannot derive `q`. -/
theorem Stable.exec_not {q : A × P} (hs : Stable step consent R) {T : Set A} {s₀ : S}
    {ops : List O} (hT : ∀ op ∈ ops, consent op ⊆ T) (hq : ¬ Derives R s₀ T q) :
    ¬ Derives R (QEDefi.Trace.Lift.exec step s₀ ops) T q := fun hd =>
  hq ((hs.exec s₀ ops hT hd).mono_keys (Set.union_subset (subset_refl T) (subset_refl T)))

/-! ## Policies: trust assumptions as hypotheses on executions -/

/-- `ExecAll step Pol s ops`: every operation satisfies `Pol` at the state the execution has
reached when it runs. -/
def ExecAll (step : S → O → Option S) (Pol : S → O → Prop) : S → List O → Prop
  | _, [] => True
  | s, op :: ops => Pol s op ∧ ExecAll step Pol (QEDefi.Trace.Lift.stepD step s op) ops

/-- An invariant preserved by every successful step that satisfies the policy holds at the end
of every execution satisfying it. -/
theorem ExecAll.invariant {Pol : S → O → Prop} {I : S → Prop}
    (hI : ∀ s op s', I s → Pol s op → step s op = some s' → I s') :
    ∀ (s : S) (ops : List O), I s → ExecAll step Pol s ops →
      I (QEDefi.Trace.Lift.exec step s ops)
  | _, [], h, _ => h
  | s, op :: ops, h, ⟨hp, ha⟩ => by
    refine ExecAll.invariant hI (QEDefi.Trace.Lift.stepD step s op) ops ?_ ha
    unfold QEDefi.Trace.Lift.stepD
    cases e : step s op with
    | none => exact h
    | some s' => exact hI s op s' h hp e

/-- **The trust policy "every exercise of `Q` follows `π`"**: steps whose consenters can derive
a capability in `Q` satisfy `π`. -/
def Exercises (R : Rules S A P) (consent : O → Set A) (Q : A × P → Prop) (π : S → O → Prop)
    (s : S) (op : O) : Prop :=
  (∃ q, Q q ∧ Derives R s (consent op) q) → π s op

/-- **Invariant under a trust policy.** `I` holds at the end of an execution in which every
step able to exercise `Q` follows `π`, provided steps unable to derive anything in `Q` keep `I`
(typically via `Guards`) and steps following `π` keep it. -/
theorem Exercises.invariant {Q : A × P → Prop} {π : S → O → Prop} {I : S → Prop}
    (hu : ∀ s op s', I s → step s op = some s' → (∀ q, Q q → ¬ Derives R s (consent op) q) →
      I s')
    (hπ : ∀ s op s', I s → π s op → step s op = some s' → I s') {s : S} {ops : List O}
    (hI : I s) (ha : ExecAll step (Exercises R consent Q π) s ops) :
    I (QEDefi.Trace.Lift.exec step s ops) :=
  ExecAll.invariant (Pol := Exercises R consent Q π)
    (fun s op s' hs hp he => by
      by_cases hd : ∃ q, Q q ∧ Derives R s (consent op) q
      · exact hπ s op s' hs (hp hd) he
      · exact hu s op s' hs he (fun q hQ hq => hd ⟨q, hQ, hq⟩)) s ops hI ha

/-! ## On bytecode -/

section Lift

variable {W : Type} {σ : System W S O}

/-- **`Guards.exec_keep` on the concrete system.** Along any concrete trace (calls and
environment steps) whose calls' consenters are among `T`, if `T` derives nothing in `Q` in the
initial abstraction, `Keep` holds between the initial and final abstractions. `Keep` must be
insensitive to `Agree` on its second argument. -/
theorem Guards.lift {Q : A × P → Prop} {Keep : S → S → Prop} (hσ : σ.Refinement)
    (hs : Stable σ.step consent R) (hg : Guards σ.step consent R Q Keep)
    (hKa : ∀ s t u, σ.Agree t u → Keep s t → Keep s u) {w₀ w : W} {ops : List O}
    (hr : σ.Reach w₀ ops w) (hok : ∀ op ∈ ops, σ.Ok op) (hp : σ.Pre w₀)
    (hi : σ.Inv (σ.abs w₀)) {T : Set A} (hT : ∀ op ∈ ops, consent op ⊆ T)
    (hq : ∀ q, Q q → ¬ Derives R (σ.abs w₀) T q) : Keep (σ.abs w₀) (σ.abs w) := by
  obtain ⟨-, -, ha⟩ := hσ.lift hr hok hp hi
  exact hKa _ _ _ (hσ.agree.symm ha) (hg.exec_keep hs _ ops hT hq)

/-- **An invariant under a policy, on the concrete system.** `I` must be insensitive to
`Agree`, and the policy is stated on the model execution of the trace's operations. -/
theorem ExecAll.lift_invariant {Pol : S → O → Prop} {I : S → Prop} (hσ : σ.Refinement)
    (hI : ∀ s op s', I s → Pol s op → σ.step s op = some s' → I s')
    (hIa : ∀ s t, σ.Agree s t → I s → I t) {w₀ w : W} {ops : List O}
    (hr : σ.Reach w₀ ops w) (hok : ∀ op ∈ ops, σ.Ok op) (hp : σ.Pre w₀)
    (hi : σ.Inv (σ.abs w₀)) (hI₀ : I (σ.abs w₀)) (ha : ExecAll σ.step Pol (σ.abs w₀) ops) :
    I (σ.abs w) := by
  obtain ⟨-, -, hag⟩ := hσ.lift hr hok hp hi
  exact hIa _ _ (hσ.agree.symm hag) (ExecAll.invariant hI _ ops hI₀ ha)

end Lift

end QEDefi.Actor
