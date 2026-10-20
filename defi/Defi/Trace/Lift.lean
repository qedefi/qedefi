/-!
# Lifting per-call refinement to arbitrary call sequences

A generic forward-simulation argument, independent of the EVM and of the vault: if every
concrete call implements the corresponding abstract operation (in the shape the refinement
theorems of this directory have: `match step (abs w) op with | some s' => abs w' ≈ s' |
none => w' = w`), and every other concrete transition leaves the abstraction unchanged, then
along **any** concrete trace the abstraction follows the model's `exec` (a reverting step is a
no-op, as in `Solmate.exec`), and every model invariant holds on the abstraction of every
reachable concrete state.

The relation `≈` (`System.Agree`) is part of the interface rather than equality because a
refinement theorem can only describe what a hashed storage layout says *pointwise*: after a
write, an allowance entry whose slot is (by a Keccak collision) the written slot changes in
the concrete world but not in the model. The concrete instantiation (`Invariants.lean`) takes
`≈` = "equal, except possibly for allowances of pairs outside a finite set of actors"; for
invariants that do not read those allowances (supply, solvency, prices) this is as good as
equality, and `Agree := Eq` recovers the textbook statement (`lift_eq`).

## Interface

* `System W S O`: concrete states `W`, abstract states `S`, operations `O`; the model `step`,
  the abstraction `abs`, the concrete transitions `call` (a call implementing an operation)
  and `env` (any other transition), a concrete well-formedness `Pre` (e.g. "the contracts are
  deployed"), the model invariant `Inv` the refinement theorems need (e.g. well-formed
  ledgers), the agreement `Agree`, and a per-operation side condition `Ok` (e.g. hash
  freshness of the actors involved).
* `System.Refinement σ`: the proof obligations — `Agree` is an equivalence that preserves
  `Inv`, `step` preserves `Inv` and respects `Agree` on `Ok` operations, each `Ok` call
  refines its operation (`OpRefines`), each environment step preserves `Pre` and `abs`.

## Results

* `Reach σ w ops w'`: `w'` is reachable from `w` by a trace whose calls implement `ops`, in
  order, interleaved with any number of environment steps.
* `lift`: `Reach σ w₀ ops w → (∀ op ∈ ops, σ.Ok op) → σ.Pre w ∧ σ.Inv (σ.abs w) ∧
  σ.Agree (σ.abs w) (exec σ.step (σ.abs w₀) ops)`.
* `invariant`: every model invariant `I` (true initially, preserved by every successful step
  from an `Inv` state, and stable under `Agree`) holds on `abs` of every reachable state;
  `invariant_eq` is the version for `Agree = Eq` without the stability side condition.
* `reach_append` / `reach_split`: traces compose and split along the operation list, so
  two-state properties (e.g. price monotonicity of one call) can be read off a trace.
-/

namespace Defi.Trace.Lift

/-! ## Model executions -/

section Model

variable {S O : Type}

/-- One model step in which a revert (`none`) leaves the state unchanged. -/
def stepD (step : S → O → Option S) (s : S) (op : O) : S := (step s op).getD s

/-- A sequence of model steps (reverted ones are no-ops); `Solmate.exec` is
`exec Solmate.step` (`Invariants.exec_eq`). -/
def exec (step : S → O → Option S) (s : S) : List O → S
  | [] => s
  | op :: ops => exec step (stepD step s op) ops

@[simp] theorem exec_nil (step : S → O → Option S) (s : S) : exec step s [] = s := rfl

@[simp] theorem exec_cons (step : S → O → Option S) (s : S) (op : O) (ops : List O) :
    exec step s (op :: ops) = exec step (stepD step s op) ops := rfl

/-- `exec` of a concatenation. -/
theorem exec_append (step : S → O → Option S) (s : S) (ops₁ ops₂ : List O) :
    exec step s (ops₁ ++ ops₂) = exec step (exec step s ops₁) ops₂ := by
  induction ops₁ generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih _

/-- A property preserved by every successful step (from states satisfying `Inv`, itself
preserved) holds after every execution. -/
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

/-- Traces only depend on the transitions: a trace of `σ` is a trace of every system `σ'`
with at least the same calls and environment steps (e.g. one with other `Ok`, `Agree`, …). -/
theorem Reach.mono {σ' : System W S O} (hc : ∀ w op w', σ.call w op w' → σ'.call w op w')
    (he : ∀ w w', σ.env w w' → σ'.env w w') {w w' : W} {ops : List O} (h : σ.Reach w ops w') :
    σ'.Reach w ops w' := by
  induction h with
  | refl w => exact .refl w
  | env h _ ih => exact .env (he _ _ h) ih
  | call h _ ih => exact .call (hc _ _ _ h) ih

/-- A single call is a trace. -/
theorem Reach.single {w w' : W} {op : O} (h : σ.call w op w') : σ.Reach w [op] w' :=
  .call h (.refl w')

/-- Traces compose. -/
theorem Reach.trans {w₁ w₂ w₃ : W} {ops₁ ops₂ : List O} (h₁ : σ.Reach w₁ ops₁ w₂)
    (h₂ : σ.Reach w₂ ops₂ w₃) : σ.Reach w₁ (ops₁ ++ ops₂) w₃ := by
  induction h₁ with
  | refl => exact h₂
  | env he _ ih => exact .env he (ih h₂)
  | call hc _ ih => exact .call hc (ih h₂)

/-- A trace splits at any point of its operation list. -/
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

/-- A one-operation trace is environment steps, the call, environment steps. -/
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

/-- A refining call, in `stepD` form. -/
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

/-- **Simulation.** From a well-formed state whose abstraction agrees with a model state
`s` satisfying the invariant, a trace of admissible calls ends in a well-formed state whose
abstraction agrees with the model's execution of the same operations from `s`. -/
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

/-- **The lifting theorem.** Along every trace of admissible calls (interleaved with any
environment steps) from a well-formed state whose abstraction satisfies the model invariant,
the abstraction follows the model: the final abstraction agrees with `exec` of the operations
from the initial abstraction. -/
theorem Refinement.lift (h : σ.Refinement) {w₀ w : W} {ops : List O}
    (hr : σ.Reach w₀ ops w) (hok : ∀ op ∈ ops, σ.Ok op) (hp : σ.Pre w₀)
    (hi : σ.Inv (σ.abs w₀)) :
    σ.Pre w ∧ σ.Inv (σ.abs w) ∧ σ.Agree (σ.abs w) (exec σ.step (σ.abs w₀) ops) := by
  obtain ⟨hp', ha, hs⟩ := h.simulation hr hok hp hi (h.agree.refl _)
  exact ⟨hp', h.inv_agree _ _ (h.agree.symm ha) hs, ha⟩

/-- **Invariants transfer.** A model invariant `I` — true on the initial abstraction, preserved
by every successful step from a state satisfying `Inv`, and stable under `Agree` — holds on the
abstraction of every state reachable by admissible calls. -/
theorem Refinement.invariant (h : σ.Refinement) {I : S → Prop}
    (hI : ∀ s op s', σ.Inv s → I s → σ.step s op = some s' → I s')
    (hIa : ∀ s t, σ.Agree s t → I s → I t) {w₀ w : W} {ops : List O}
    (hr : σ.Reach w₀ ops w) (hok : ∀ op ∈ ops, σ.Ok op) (hp : σ.Pre w₀)
    (hi : σ.Inv (σ.abs w₀)) (hI₀ : I (σ.abs w₀)) : I (σ.abs w) := by
  obtain ⟨-, -, ha⟩ := h.lift hr hok hp hi
  exact hIa _ _ (h.agree.symm ha) (exec_induction h.inv_step hI hi hI₀ ops).2

/-- **Invariants transfer, `Agree = Eq`.** The textbook form: when the abstraction is
determined exactly, every model invariant (true initially and preserved by every successful
step) holds on the abstraction of every reachable state. -/
theorem Refinement.invariant_eq (h : σ.Refinement) (heq : ∀ s t, σ.Agree s t → s = t)
    {I : S → Prop} (hI : ∀ s op s', σ.Inv s → I s → σ.step s op = some s' → I s')
    {w₀ w : W} {ops : List O} (hr : σ.Reach w₀ ops w) (hok : ∀ op ∈ ops, σ.Ok op)
    (hp : σ.Pre w₀) (hi : σ.Inv (σ.abs w₀)) (hI₀ : I (σ.abs w₀)) : I (σ.abs w) :=
  h.invariant hI (fun s t hst hs => heq s t hst ▸ hs) hr hok hp hi hI₀

/-- With `Agree = Eq`, the abstraction of the final state *is* the model execution. -/
theorem Refinement.lift_eq (h : σ.Refinement) (heq : ∀ s t, σ.Agree s t → s = t)
    {w₀ w : W} {ops : List O} (hr : σ.Reach w₀ ops w) (hok : ∀ op ∈ ops, σ.Ok op)
    (hp : σ.Pre w₀) (hi : σ.Inv (σ.abs w₀)) :
    σ.abs w = exec σ.step (σ.abs w₀) ops :=
  heq _ _ (h.lift hr hok hp hi).2.2

/-- **One call inside a trace.** If `ops₁ ++ op :: ops₂` is executed from `w₀`, the concrete
call implementing `op` starts in a state `v` with `abs v ≈ exec (abs w₀) ops₁` and ends in a
state `v'` with `abs v' ≈ stepD (exec (abs w₀) ops₁) op`: two-state properties of single
operations (e.g. price monotonicity) can be read off any trace. -/
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
