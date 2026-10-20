/-!
# Lifting per-call refinement to arbitrary call sequences

A generic forward simulation, independent of the EVM: if every concrete call refines its
model operation (`System.Refinement`) and other transitions leave the abstraction unchanged,
then along any trace the abstraction follows the model's `exec` (`Refinement.lift`) and model
invariants hold on every reachable state. Agreement is a relation `Agree` rather than `=`
because hashed storage frames are only pointwise (see `Defi.ERC4626.AgreeOn`).
-/

namespace Defi.Trace.Lift

/-! ## Model executions -/

section Model

variable {S O : Type}

/-- One model step in which a revert (`none`) leaves the state unchanged. -/
def stepD (step : S → O → Option S) (s : S) (op : O) : S := (step s op).getD s

/-- A sequence of model steps (reverted ones are no-ops). -/
def exec (step : S → O → Option S) (s : S) : List O → S
  | [] => s
  | op :: ops => exec step (stepD step s op) ops

@[simp] theorem exec_nil (step : S → O → Option S) (s : S) : exec step s [] = s := rfl

@[simp] theorem exec_cons (step : S → O → Option S) (s : S) (op : O) (ops : List O) :
    exec step s (op :: ops) = exec step (stepD step s op) ops := rfl

theorem exec_append (step : S → O → Option S) (s : S) (ops₁ ops₂ : List O) :
    exec step s (ops₁ ++ ops₂) = exec step (exec step s ops₁) ops₂ := by
  induction ops₁ generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih _

theorem exec_induction {step : S → O → Option S} {Inv I : S → Prop}
    (hinv : ∀ s op s', Inv s → step s op = some s' → Inv s')
    (hI : ∀ s op s', Inv s → I s → step s op = some s' → I s') {s : S} (hs : Inv s) (h : I s)
    (ops : List O) : Inv (exec step s ops) ∧ I (exec step s ops) := by
  induction ops generalizing s with
  | nil => exact ⟨hs, h⟩
  | cons op ops ih =>
    apply ih
    · unfold stepD
      cases e : step s op with
      | none => exact hs
      | some s' => exact hinv s op s' hs e
    · unfold stepD
      cases e : step s op with
      | none => exact h
      | some s' => exact hI s op s' hs h e

end Model

/-! ## Systems and their refinement obligations -/

/-- A concrete system `W` refining an abstract state machine over `S` with operations `O`. -/
structure System (W S O : Type) where
  /-- The model's transition function (`none` = the operation reverts). -/
  step : S → O → Option S
  /-- The abstraction function. -/
  abs : W → S
  /-- `call w op w'`: a concrete call implementing `op` takes `w` to `w'`. -/
  call : W → O → W → Prop
  /-- Any other concrete transition (one the model does not see). -/
  env : W → W → Prop
  /-- Concrete well-formedness, preserved by every transition (e.g. deployment). -/
  Pre : W → Prop
  /-- The model invariant the per-call refinement theorems assume. -/
  Inv : S → Prop
  /-- Indistinguishability of abstract states for the properties of interest. -/
  Agree : S → S → Prop
  /-- Side condition on an operation for its refinement theorem to apply. -/
  Ok : O → Prop

namespace System

variable {W S O : Type} (σ : System W S O)

/-- The shape of a per-call refinement theorem: if the model operation succeeds with `s'`, the
concrete call ends in a state whose abstraction agrees with `s'`; if it reverts, the concrete
call leaves the state unchanged. -/
def OpRefines (w : W) (op : O) (w' : W) : Prop :=
  match σ.step (σ.abs w) op with
  | some s' => σ.Agree (σ.abs w') s'
  | none => w' = w

/-- The proof obligations of a refinement. -/
structure Refinement : Prop where
  /-- `Agree` is an equivalence. -/
  agree : Equivalence σ.Agree
  /-- `Agree` preserves the model invariant. -/
  inv_agree : ∀ s t, σ.Agree s t → σ.Inv s → σ.Inv t
  /-- The model preserves its invariant. -/
  inv_step : ∀ s op s', σ.Inv s → σ.step s op = some s' → σ.Inv s'
  /-- The model respects `Agree` on admissible operations (reverting steps included). -/
  step_agree : ∀ s t op, σ.Ok op → σ.Inv s → σ.Agree s t →
    σ.Agree (stepD σ.step s op) (stepD σ.step t op)
  /-- **Per-call refinement**: every admissible call from a well-formed state whose
  abstraction satisfies the invariant refines its operation and keeps the state well formed. -/
  call : ∀ w op w', σ.Pre w → σ.Inv (σ.abs w) → σ.Ok op → σ.call w op w' →
    σ.Pre w' ∧ σ.OpRefines w op w'
  /-- Environment steps keep the state well formed and do not change the abstraction. -/
  env : ∀ w w', σ.Pre w → σ.env w w' → σ.Pre w' ∧ σ.abs w' = σ.abs w

/-- Concrete traces: `Reach σ w ops w'` when `w'` is reached from `w` by calls implementing
`ops` in order, interleaved with any number of environment steps. -/
inductive Reach : W → List O → W → Prop
  /-- The empty trace. -/
  | refl (w : W) : Reach w [] w
  /-- An environment step, then a trace. -/
  | env {w w' w'' : W} {ops : List O} : σ.env w w' → Reach w' ops w'' → Reach w ops w''
  /-- A call implementing `op`, then a trace. -/
  | call {w w' w'' : W} {op : O} {ops : List O} :
      σ.call w op w' → Reach w' ops w'' → Reach w (op :: ops) w''

variable {σ}

theorem Reach.mono {σ' : System W S O} (hc : ∀ w op w', σ.call w op w' → σ'.call w op w')
    (he : ∀ w w', σ.env w w' → σ'.env w w') {w w' : W} {ops : List O} (h : σ.Reach w ops w') :
    σ'.Reach w ops w' := by
  induction h with
  | refl w => exact .refl w
  | env h _ ih => exact .env (he _ _ h) ih
  | call h _ ih => exact .call (hc _ _ _ h) ih

theorem Reach.single {w w' : W} {op : O} (h : σ.call w op w') : σ.Reach w [op] w' :=
  .call h (.refl w')

theorem Reach.trans {w₁ w₂ w₃ : W} {ops₁ ops₂ : List O} (h₁ : σ.Reach w₁ ops₁ w₂)
    (h₂ : σ.Reach w₂ ops₂ w₃) : σ.Reach w₁ (ops₁ ++ ops₂) w₃ := by
  induction h₁ with
  | refl => exact h₂
  | env he _ ih => exact .env he (ih h₂)
  | call hc _ ih => exact .call hc (ih h₂)

theorem Reach.split {w₁ w₃ : W} {ops₁ ops₂ : List O} (h : σ.Reach w₁ (ops₁ ++ ops₂) w₃) :
    ∃ w₂, σ.Reach w₁ ops₁ w₂ ∧ σ.Reach w₂ ops₂ w₃ := by
  generalize hops : ops₁ ++ ops₂ = ops at h
  induction h generalizing ops₁ with
  | refl w =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hops
    exact ⟨w, .refl w, .refl w⟩
  | env he _ ih =>
    obtain ⟨w₂, h₁, h₂⟩ := ih hops
    exact ⟨w₂, .env he h₁, h₂⟩
  | @call w w' w'' op ops hc hr ih =>
    cases ops₁ with
    | nil => exact ⟨w, .refl w, by simp only [List.nil_append] at hops; subst hops; exact .call hc hr⟩
    | cons op₁ ops₁ =>
      simp only [List.cons_append, List.cons.injEq] at hops
      obtain ⟨rfl, hops⟩ := hops
      obtain ⟨w₂, h₁, h₂⟩ := ih hops
      exact ⟨w₂, .call hc h₁, h₂⟩

theorem Reach.single_inv {w w'' : W} {op : O} (h : σ.Reach w [op] w'') :
    ∃ v v', σ.Reach w [] v ∧ σ.call v op v' ∧ σ.Reach v' [] w'' := by
  generalize hops : [op] = ops at h
  induction h with
  | refl => cases hops
  | env he _ ih =>
    obtain ⟨v, v', h₁, hc, h₂⟩ := ih hops
    exact ⟨v, v', .env he h₁, hc, h₂⟩
  | @call w w' w'' op' ops hc hr _ =>
    simp only [List.cons.injEq] at hops
    obtain ⟨rfl, rfl⟩ := hops
    exact ⟨w, w', .refl w, hc, hr⟩

/-! ## The lifting theorem -/

theorem Refinement.call_stepD (h : σ.Refinement) {w w' : W} {op : O} (hp : σ.Pre w)
    (hi : σ.Inv (σ.abs w)) (hok : σ.Ok op) (hc : σ.call w op w') :
    σ.Pre w' ∧ σ.Agree (σ.abs w') (stepD σ.step (σ.abs w) op) := by
  obtain ⟨hp', hr⟩ := h.call w op w' hp hi hok hc
  refine ⟨hp', ?_⟩
  unfold OpRefines at hr
  unfold stepD
  revert hr
  cases σ.step (σ.abs w) op with
  | some s' => exact id
  | none => intro hr; subst hr; exact h.agree.refl _

theorem Refinement.simulation (h : σ.Refinement) {w w' : W} {ops : List O}
    (hr : σ.Reach w ops w') (hok : ∀ op ∈ ops, σ.Ok op) {s : S} (hp : σ.Pre w)
    (hs : σ.Inv s) (ha : σ.Agree (σ.abs w) s) :
    σ.Pre w' ∧ σ.Agree (σ.abs w') (exec σ.step s ops) ∧ σ.Inv (exec σ.step s ops) := by
  induction hr generalizing s with
  | refl => exact ⟨hp, ha, hs⟩
  | env he _ ih =>
    obtain ⟨hp', habs⟩ := h.env _ _ hp he
    exact ih hok hp' hs (by rw [habs]; exact ha)
  | @call w w₁ w'' op ops hc _ ih =>
    have hokop : σ.Ok op := hok op (by simp)
    have hi : σ.Inv (σ.abs w) := h.inv_agree _ _ (h.agree.symm ha) hs
    obtain ⟨hp₁, ha₁⟩ := h.call_stepD hp hi hokop hc
    have hstep := h.step_agree _ _ op hokop hi ha
    have hs₁ : σ.Inv (stepD σ.step s op) := by
      unfold stepD
      cases e : σ.step s op with
      | none => exact hs
      | some s' => exact h.inv_step s op s' hs e
    exact ih (fun op' hop' => hok op' (by simp [hop'])) hp₁ hs₁ (h.agree.trans ha₁ hstep)

/-- **The lifting theorem.** Along every trace of admissible calls (with any environment
steps) from a well-formed state, the final abstraction agrees with `exec` of the operations
from the initial abstraction. -/
theorem Refinement.lift (h : σ.Refinement) {w₀ w : W} {ops : List O}
    (hr : σ.Reach w₀ ops w) (hok : ∀ op ∈ ops, σ.Ok op) (hp : σ.Pre w₀)
    (hi : σ.Inv (σ.abs w₀)) :
    σ.Pre w ∧ σ.Inv (σ.abs w) ∧ σ.Agree (σ.abs w) (exec σ.step (σ.abs w₀) ops) := by
  obtain ⟨hp', ha, hs⟩ := h.simulation hr hok hp hi (h.agree.refl _)
  exact ⟨hp', h.inv_agree _ _ (h.agree.symm ha) hs, ha⟩

/-- A model invariant that is preserved by steps and stable under `Agree` holds on the
abstraction of every reachable state. -/
theorem Refinement.invariant (h : σ.Refinement) {I : S → Prop}
    (hI : ∀ s op s', σ.Inv s → I s → σ.step s op = some s' → I s')
    (hIa : ∀ s t, σ.Agree s t → I s → I t) {w₀ w : W} {ops : List O}
    (hr : σ.Reach w₀ ops w) (hok : ∀ op ∈ ops, σ.Ok op) (hp : σ.Pre w₀)
    (hi : σ.Inv (σ.abs w₀)) (hI₀ : I (σ.abs w₀)) : I (σ.abs w) := by
  obtain ⟨-, -, ha⟩ := h.lift hr hok hp hi
  exact hIa _ _ (h.agree.symm ha) (exec_induction h.inv_step hI hi hI₀ ops).2

theorem Refinement.invariant_eq (h : σ.Refinement) (heq : ∀ s t, σ.Agree s t → s = t)
    {I : S → Prop} (hI : ∀ s op s', σ.Inv s → I s → σ.step s op = some s' → I s')
    {w₀ w : W} {ops : List O} (hr : σ.Reach w₀ ops w) (hok : ∀ op ∈ ops, σ.Ok op)
    (hp : σ.Pre w₀) (hi : σ.Inv (σ.abs w₀)) (hI₀ : I (σ.abs w₀)) : I (σ.abs w) :=
  h.invariant hI (fun s t hst hs => heq s t hst ▸ hs) hr hok hp hi hI₀

theorem Refinement.lift_eq (h : σ.Refinement) (heq : ∀ s t, σ.Agree s t → s = t)
    {w₀ w : W} {ops : List O} (hr : σ.Reach w₀ ops w) (hok : ∀ op ∈ ops, σ.Ok op)
    (hp : σ.Pre w₀) (hi : σ.Inv (σ.abs w₀)) :
    σ.abs w = exec σ.step (σ.abs w₀) ops :=
  heq _ _ (h.lift hr hok hp hi).2.2

/-- One call inside a trace refines its model step from the model state reached so far, so
two-state properties of single operations can be read off any trace. -/
theorem Refinement.lift_step (h : σ.Refinement) {w₀ w : W} {ops₁ ops₂ : List O} {op : O}
    (hr : σ.Reach w₀ (ops₁ ++ op :: ops₂) w) (hok : ∀ o ∈ ops₁ ++ op :: ops₂, σ.Ok o)
    (hp : σ.Pre w₀) (hi : σ.Inv (σ.abs w₀)) :
    ∃ v v', σ.call v op v' ∧
      σ.Agree (σ.abs v) (exec σ.step (σ.abs w₀) ops₁) ∧
      σ.Agree (σ.abs v') (stepD σ.step (exec σ.step (σ.abs w₀) ops₁) op) ∧
      σ.Inv (exec σ.step (σ.abs w₀) ops₁) := by
  obtain ⟨w₁, h₁, h₂⟩ := Reach.split hr
  obtain ⟨w₂, h₂, -⟩ := Reach.split (ops₁ := [op]) h₂
  obtain ⟨v, v', hv, hc, hv'⟩ := Reach.single_inv h₂
  have hok₁ : ∀ o ∈ ops₁, σ.Ok o := fun o ho => hok o (List.mem_append_left _ ho)
  obtain ⟨hp₁, hi₁, ha₁⟩ := h.lift h₁ hok₁ hp hi
  obtain ⟨hpv, hav, -⟩ := h.simulation hv (by simp) hp₁ hi₁ (h.agree.refl _)
  simp only [exec_nil] at hav
  have hsv : σ.Inv (σ.abs v) := h.inv_agree _ _ (h.agree.symm hav) hi₁
  have hsx : σ.Inv (exec σ.step (σ.abs w₀) ops₁) := h.inv_agree _ _ ha₁ hi₁
  have hav' : σ.Agree (σ.abs v) (exec σ.step (σ.abs w₀) ops₁) := h.agree.trans hav ha₁
  have hokop : σ.Ok op := hok op (by simp)
  obtain ⟨-, hc'⟩ := h.call_stepD hpv hsv hokop hc
  refine ⟨v, v', hc, hav', ?_, hsx⟩
  exact h.agree.trans hc' (h.step_agree _ _ op hokop hsv hav')

end System

end Defi.Trace.Lift
