import QEDefi.Trace.Lift

/-!
# Time and multiple blocks: lifting time-indexed refinement

`QEDefi.Trace.Lift` lifts per-call refinement to traces of calls. Here the model is
**time-indexed**: `step now s op` may depend on the time `now` at which `op` runs (a block
timestamp, a block number, …). Nothing is ever enumerated over time:

* per-call refinement is stated for a symbolic time `t` (`TSystem.Refinement.call`), so
  bytecode proofs run once with the block context symbolic;
* a multi-block trace (`BlockTrace`) is a list of blocks, each with its own time, and the
  calls inside them; the only assumption relating blocks is that their times do not decrease
  (`List.Pairwise`), stated as a hypothesis;
* time-dependent invariants (`TimeInvariant`: `I t s` preserved by a step at time `t` and by
  advancing the clock `t ≤ t'`) are carried by one induction over the trace
  (`texec_timeInvariant`), using only monotonicity of the times.

A timed operation is an operation stamped with its time (`Timed`); `TSystem.untimed` turns a
time-indexed system into a `Lift.System` over timed operations, so the lifting theorems of
`Lift` apply unchanged. Time-independent systems are the constant case (`TSystem.const`): their
statements hold for every sequence of blocks, monotone or not (`texec_const`).
-/

namespace QEDefi.Trace.Time
open QEDefi.Trace.Lift

/-! ## Timed operations -/

/-- An operation `op` executed at time `time`. -/
structure Timed (O : Type) where
  /-- The time at which the operation runs (e.g. the block timestamp). -/
  time : Nat
  /-- The operation. -/
  op : O

section Model

variable {S O : Type}

/-- A time-indexed model step as a step on timed operations: each runs at its own time. -/
def atTime (step : Nat → S → O → Option S) (s : S) (o : Timed O) : Option S :=
  step o.time s o.op

/-- Execution of timed operations; reverted steps are no-ops (`Lift.exec` of `atTime`). -/
abbrev texec (step : Nat → S → O → Option S) (s : S) (ops : List (Timed O)) : S :=
  exec (atTime step) s ops

/-- Times never decrease along `ops`. -/
def Monotone (ops : List (Timed O)) : Prop :=
  ops.Pairwise fun a b => a.time ≤ b.time

/-- Every operation of `ops` runs at a time in `[t₀, t₁]`. -/
def Within (t₀ t₁ : Nat) (ops : List (Timed O)) : Prop :=
  ∀ o ∈ ops, t₀ ≤ o.time ∧ o.time ≤ t₁

theorem Monotone.nil : Monotone ([] : List (Timed O)) := List.Pairwise.nil

theorem Monotone.tail {o : Timed O} {ops : List (Timed O)} (h : Monotone (o :: ops)) :
    Monotone ops :=
  (List.pairwise_cons.1 h).2

theorem Monotone.head_le {o : Timed O} {ops : List (Timed O)} (h : Monotone (o :: ops)) :
    ∀ o' ∈ ops, o.time ≤ o'.time :=
  (List.pairwise_cons.1 h).1

theorem Within.cons_iff {t₀ t₁ : Nat} {o : Timed O} {ops : List (Timed O)} :
    Within t₀ t₁ (o :: ops) ↔ (t₀ ≤ o.time ∧ o.time ≤ t₁) ∧ Within t₀ t₁ ops := by
  simp [Within]

/-- **A time-dependent invariant** of a time-indexed model with state invariant `Inv`:
`I t s` reads "`s` is good at time `t`". It is preserved by every successful step at the
current time, and by advancing the clock. Time-independent invariants are the case
`I t = J` (`TimeInvariant.const`). -/
structure TimeInvariant (step : Nat → S → O → Option S) (Inv : S → Prop)
    (I : Nat → S → Prop) : Prop where
  /-- A successful step at time `t` keeps `I t`. -/
  step : ∀ t s op s', Inv s → I t s → step t s op = some s' → I t s'
  /-- Advancing the clock keeps `I`. -/
  advance : ∀ t t' s, Inv s → t ≤ t' → I t s → I t' s

/-- A time-independent invariant is a time invariant. -/
theorem TimeInvariant.const {step : Nat → S → O → Option S} {Inv J : S → Prop}
    (h : ∀ t s op s', Inv s → J s → step t s op = some s' → J s') :
    TimeInvariant step Inv (fun _ => J) :=
  ⟨h, fun _ _ _ _ _ hs => hs⟩

/-- Two time invariants together. -/
theorem TimeInvariant.and {step : Nat → S → O → Option S} {Inv : S → Prop}
    {I J : Nat → S → Prop} (hI : TimeInvariant step Inv I) (hJ : TimeInvariant step Inv J) :
    TimeInvariant step Inv (fun t s => I t s ∧ J t s) :=
  ⟨fun t s op s' hi h he => ⟨hI.step t s op s' hi h.1 he, hJ.step t s op s' hi h.2 he⟩,
    fun t t' s hi ht h => ⟨hI.advance t t' s hi ht h.1, hJ.advance t t' s hi ht h.2⟩⟩

/-- **Time-dependent invariants along monotone timed executions.** From a state good at time
`t₀`, after operations whose times do not decrease and lie in `[t₀, t₁]`, the state is good
at `t₁`. One induction over the operations: the clock is advanced to each operation's time,
then the step is taken at that time. -/
theorem texec_timeInvariant {step : Nat → S → O → Option S} {Inv : S → Prop}
    {I : Nat → S → Prop} (hinv : ∀ t s op s', Inv s → step t s op = some s' → Inv s')
    (hI : TimeInvariant step Inv I) {ops : List (Timed O)} (hmono : Monotone ops) :
    ∀ {s : S} {t₀ t₁ : Nat}, Inv s → I t₀ s → Within t₀ t₁ ops → t₀ ≤ t₁ →
      Inv (texec step s ops) ∧ I t₁ (texec step s ops) := by
  induction ops with
  | nil => intro s t₀ t₁ hs h _ ht; exact ⟨hs, hI.advance t₀ t₁ s hs ht h⟩
  | cons o ops ih =>
    intro s t₀ t₁ hs h hw ht
    obtain ⟨⟨h₀, h₁⟩, hw'⟩ := Within.cons_iff.1 hw
    have ha : I o.time s := hI.advance t₀ o.time s hs h₀ h
    have hstep : Inv (stepD (atTime step) s o) ∧ I o.time (stepD (atTime step) s o) := by
      unfold stepD
      cases e : atTime step s o with
      | none => exact ⟨hs, ha⟩
      | some s' => exact ⟨hinv _ _ _ _ hs e, hI.step _ _ _ _ hs ha e⟩
    exact ih hmono.tail hstep.1 hstep.2
      (fun o' ho' => ⟨hmono.head_le o' ho', (hw' o' ho').2⟩) h₁

/-- **A quantity that never decreases** — in time, and under every successful step at the
current time — is at least its initial value after any monotone timed execution. -/
theorem texec_quantity_mono {step : Nat → S → O → Option S} {Inv : S → Prop}
    (hinv : ∀ t s op s', Inv s → step t s op = some s' → Inv s') {f : Nat → S → Nat}
    (hstep : ∀ t s op s', Inv s → step t s op = some s' → f t s ≤ f t s')
    (hadv : ∀ t t' s, Inv s → t ≤ t' → f t s ≤ f t' s) {ops : List (Timed O)}
    (hmono : Monotone ops) {s : S} {t₀ t₁ : Nat} (hs : Inv s) (hw : Within t₀ t₁ ops)
    (ht : t₀ ≤ t₁) : f t₀ s ≤ f t₁ (texec step s ops) := by
  have hI : TimeInvariant step Inv (fun t s' => f t₀ s ≤ f t s') :=
    ⟨fun t s₁ op s₂ hi h he => Nat.le_trans h (hstep t s₁ op s₂ hi he),
      fun t t' s₁ hi htt h => Nat.le_trans h (hadv t t' s₁ hi htt)⟩
  exact (texec_timeInvariant hinv hI hmono hs (Nat.le_refl _) hw ht).2

/-- A time-independent model: `texec` of the constant-in-time step forgets the times. -/
theorem texec_const (step : S → O → Option S) (s : S) (ops : List (Timed O)) :
    texec (fun _ => step) s ops = exec step s (ops.map Timed.op) := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih => exact ih _

end Model

/-! ## Time-indexed systems -/

/-- A concrete system `W` refining a **time-indexed** model over `S` with operations `O`: as
`Lift.System`, but the model step and the concrete calls take the time `t` at which the
operation runs. -/
structure TSystem (W S O : Type) where
  /-- The model's transition at time `t` (`none` = the operation reverts). -/
  step : Nat → S → O → Option S
  /-- The abstraction function. -/
  abs : W → S
  /-- `call t w op w'`: a concrete call implementing `op` at time `t` takes `w` to `w'`. -/
  call : Nat → W → O → W → Prop
  /-- Any other concrete transition (one the model does not see). -/
  env : W → W → Prop
  /-- Concrete well-formedness, preserved by every transition. -/
  Pre : W → Prop
  /-- The model invariant the per-call refinement theorems assume. -/
  Inv : S → Prop
  /-- Indistinguishability of abstract states for the properties of interest. -/
  Agree : S → S → Prop
  /-- Side condition on an operation for its refinement theorem to apply. -/
  Ok : O → Prop

namespace TSystem

variable {W S O : Type} (σ : TSystem W S O)

/-- The system over timed operations: a timed operation is a call at its time. -/
def untimed : System W S (Timed O) where
  step := atTime σ.step
  abs := σ.abs
  call w o w' := σ.call o.time w o.op w'
  env := σ.env
  Pre := σ.Pre
  Inv := σ.Inv
  Agree := σ.Agree
  Ok o := σ.Ok o.op

/-- A time-independent system as a time-indexed one (constant in time). -/
def const (σ : System W S O) : TSystem W S O where
  step _ := σ.step
  abs := σ.abs
  call _ := σ.call
  env := σ.env
  Pre := σ.Pre
  Inv := σ.Inv
  Agree := σ.Agree
  Ok := σ.Ok

/-- Per-call refinement at time `t` (`System.OpRefines` with the model step at `t`). -/
def OpRefinesAt (t : Nat) (w : W) (op : O) (w' : W) : Prop :=
  match σ.step t (σ.abs w) op with
  | some s' => σ.Agree (σ.abs w') s'
  | none => w' = w

/-- **The proof obligations of a time-indexed refinement**, each for a symbolic time `t`. -/
structure Refinement : Prop where
  /-- `Agree` is an equivalence. -/
  agree : Equivalence σ.Agree
  /-- `Agree` preserves the model invariant. -/
  inv_agree : ∀ s t, σ.Agree s t → σ.Inv s → σ.Inv t
  /-- The model preserves its invariant, at every time. -/
  inv_step : ∀ t s op s', σ.Inv s → σ.step t s op = some s' → σ.Inv s'
  /-- The model respects `Agree` on admissible operations, at every time. -/
  step_agree : ∀ t s s' op, σ.Ok op → σ.Inv s → σ.Agree s s' →
    σ.Agree (stepD (σ.step t) s op) (stepD (σ.step t) s' op)
  /-- **Per-call refinement at a symbolic time** `t`. -/
  call : ∀ t w op w', σ.Pre w → σ.Inv (σ.abs w) → σ.Ok op → σ.call t w op w' →
    σ.Pre w' ∧ σ.OpRefinesAt t w op w'
  /-- Environment steps keep the state well formed and do not change the abstraction. -/
  env : ∀ w w', σ.Pre w → σ.env w w' → σ.Pre w' ∧ σ.abs w' = σ.abs w

variable {σ}

/-- A time-indexed refinement is a refinement of the system over timed operations. -/
theorem Refinement.untimed (h : σ.Refinement) : σ.untimed.Refinement where
  agree := h.agree
  inv_agree := h.inv_agree
  inv_step s o s' := h.inv_step o.time s o.op s'
  step_agree s s' o := h.step_agree o.time s s' o.op
  call w o w' hp hi hok hc := h.call o.time w o.op w' hp hi hok hc
  env := h.env

/-- A time-independent refinement is a time-indexed one (for every time). -/
theorem refinement_const {τ : System W S O} (h : τ.Refinement) : (const τ).Refinement where
  agree := h.agree
  inv_agree := h.inv_agree
  inv_step _ := h.inv_step
  step_agree _ s s' op := h.step_agree s s' op
  call _ w op w' hp hi hok hc := h.call w op w' hp hi hok hc
  env := h.env

/-! ## Multi-block traces -/

/-- The concrete transitions inside block `b` of a system whose clock reads `time b`: an
admissible call at that time, or an environment step. -/
inductive BlockStep {B : Type} (σ : TSystem W S O) (time : B → Nat) (b : B) : W → W → Prop
  /-- An admissible call implementing `op` at the block's time. -/
  | call {w w' : W} (op : O) : σ.Ok op → σ.call (time b) w op w' → BlockStep σ time b w w'
  /-- An environment step. -/
  | env {w w' : W} : σ.env w w' → BlockStep σ time b w w'

end TSystem

/-- **Multi-block traces.** `BlockTrace step bs w w'`: `w'` is reached from `w` by running the
blocks `bs` in order, each a sequence of transitions `step b` of that block. -/
inductive BlockTrace {B W : Type} (step : B → W → W → Prop) : List B → W → W → Prop
  /-- No blocks left. -/
  | nil (w : W) : BlockTrace step [] w w
  /-- A transition of the current block `b`, then the rest of `b` and the later blocks. -/
  | step {b : B} {bs : List B} {w w' w'' : W} :
      step b w w' → BlockTrace step (b :: bs) w' w'' → BlockTrace step (b :: bs) w w''
  /-- Block `b` is finished: continue with the later blocks. -/
  | next {b : B} {bs : List B} {w w' : W} :
      BlockTrace step bs w w' → BlockTrace step (b :: bs) w w'

namespace BlockTrace

variable {B W : Type} {step : B → W → W → Prop}

theorem mono {step' : B → W → W → Prop} (hs : ∀ b w w', step b w w' → step' b w w')
    {bs : List B} {w w' : W} (h : BlockTrace step bs w w') : BlockTrace step' bs w w' := by
  induction h with
  | nil w => exact .nil w
  | step hst _ ih => exact .step (hs _ _ _ hst) ih
  | next _ ih => exact .next ih

/-- Forgetting the blocks: a multi-block trace is a sequence of transitions of its blocks
(for time-independent statements such as the Solmate `TxTrace`). -/
theorem induction_on {R : W → W → Prop} (hrefl : ∀ w, R w w)
    (htail : ∀ b w w' w'', R w w' → step b w' w'' → R w w'')
    {bs : List B} {w w' : W} (h : BlockTrace step bs w w') : R w w' := by
  suffices ∀ {bs : List B} {v v' : W}, BlockTrace step bs v v' → ∀ {u}, R u v → R u v' from
    this h (hrefl w)
  intro bs v v' h
  induction h with
  | nil => exact id
  | step hst _ ih => exact fun hu => ih (htail _ _ _ _ hu hst)
  | next _ ih => exact ih

end BlockTrace

/-- The timed operations of blocks: block `bs[i]` contributes `opss[i]`, stamped with its
time. -/
def stamp {B O : Type} (time : B → Nat) : List B → List (List O) → List (Timed O)
  | b :: bs, os :: opss => os.map (fun op => ⟨time b, op⟩) ++ stamp time bs opss
  | _, _ => []

section Stamp

variable {B O : Type} {time : B → Nat}

theorem mem_stamp {bs : List B} {opss : List (List O)} {o : Timed O}
    (h : o ∈ stamp time bs opss) : ∃ b ∈ bs, o.time = time b := by
  induction bs generalizing opss with
  | nil => cases opss <;> simp [stamp] at h
  | cons b bs ih =>
    cases opss with
    | nil => simp [stamp] at h
    | cons os opss =>
      simp only [stamp, List.mem_append, List.mem_map] at h
      rcases h with ⟨op, -, rfl⟩ | h
      · exact ⟨b, List.mem_cons_self .., rfl⟩
      · obtain ⟨b', hb', he⟩ := ih h
        exact ⟨b', List.mem_cons_of_mem _ hb', he⟩

/-- Blocks with non-decreasing times give monotone timed operations. -/
theorem monotone_stamp {bs : List B} (hb : bs.Pairwise fun b b' => time b ≤ time b')
    (opss : List (List O)) : Monotone (stamp time bs opss) := by
  induction bs generalizing opss with
  | nil => cases opss <;> exact List.Pairwise.nil
  | cons b bs ih =>
    cases opss with
    | nil => exact List.Pairwise.nil
    | cons os opss =>
      obtain ⟨hb₁, hb₂⟩ := List.pairwise_cons.1 hb
      simp only [stamp, Monotone]
      refine List.pairwise_append.2 ⟨?_, ih hb₂ opss, ?_⟩
      · exact List.pairwise_map.2 (List.Pairwise.imp (fun _ => Nat.le_refl _)
          (List.pairwise_of_forall (fun _ _ => trivial)))
      · intro a ha c hc
        obtain ⟨op, -, rfl⟩ := List.mem_map.1 ha
        obtain ⟨b', hb', he⟩ := mem_stamp hc
        rw [he]; exact hb₁ b' hb'

/-- Blocks with times in `[t₀, t₁]` give timed operations in `[t₀, t₁]`. -/
theorem within_stamp {bs : List B} {t₀ t₁ : Nat} (hb : ∀ b ∈ bs, t₀ ≤ time b ∧ time b ≤ t₁)
    (opss : List (List O)) : Within t₀ t₁ (stamp time bs opss) := by
  intro o ho
  obtain ⟨b, hb', he⟩ := mem_stamp ho
  rw [he]; exact hb b hb'

end Stamp

namespace TSystem

variable {W S O B : Type} {σ : TSystem W S O} {time : B → Nat}

/-- **A multi-block trace is a trace of timed operations**: the calls of each block, stamped
with the block's time, in order. -/
theorem reach_of_blockTrace {bs : List B} {w w' : W} (h : BlockTrace (BlockStep σ time) bs w w') :
    ∃ opss : List (List O), (∀ os ∈ opss, ∀ op ∈ os, σ.Ok op) ∧
      σ.untimed.Reach w (stamp time bs opss) w' := by
  induction h with
  | nil w => exact ⟨[], by simp, .refl w⟩
  | @step b bs w w₁ w₂ hst _ ih =>
    obtain ⟨opss, hok, hr⟩ := ih
    cases hst with
    | env he => exact ⟨opss, hok, .env he hr⟩
    | call op hop hc =>
      cases opss with
      | nil => exact ⟨[[op]], by simp [hop], .call (op := (⟨time b, op⟩ : Timed O)) hc (by simpa [stamp] using hr)⟩
      | cons os opss =>
        refine ⟨(op :: os) :: opss, ?_, ?_⟩
        · intro os' hos' op' hop'
          simp only [List.mem_cons] at hos'
          rcases hos' with rfl | hos'
          · simp only [List.mem_cons] at hop'
            rcases hop' with rfl | hop'
            · exact hop
            · exact hok os (List.mem_cons_self ..) op' hop'
          · exact hok os' (List.mem_cons_of_mem _ hos') op' hop'
        · exact .call (op := (⟨time b, op⟩ : Timed O)) hc (by simpa [stamp] using hr)
  | @next b bs w w' _ ih =>
    obtain ⟨opss, hok, hr⟩ := ih
    exact ⟨[] :: opss, by simpa using hok, by simpa [stamp] using hr⟩

theorem ok_stamp {bs : List B} {opss : List (List O)} (hok : ∀ os ∈ opss, ∀ op ∈ os, σ.Ok op) :
    ∀ o ∈ stamp time bs opss, σ.untimed.Ok o := by
  induction bs generalizing opss with
  | nil => cases opss <;> simp [stamp]
  | cons b bs ih =>
    cases opss with
    | nil => simp [stamp]
    | cons os opss =>
      intro o ho
      simp only [stamp, List.mem_append, List.mem_map] at ho
      rcases ho with ⟨op, hop, rfl⟩ | ho
      · exact hok os (List.mem_cons_self ..) op hop
      · exact ih (fun os' hos' => hok os' (List.mem_cons_of_mem _ hos')) o ho

/-- **The lifting theorem across blocks.** Along any multi-block trace from a well-formed
state, the final abstraction agrees with the model's execution of the blocks' calls, each at
its block's time. No assumption on the times is needed for this. -/
theorem Refinement.lift_blocks (h : σ.Refinement) {bs : List B} {w₀ w : W}
    (htr : BlockTrace (BlockStep σ time) bs w₀ w) (hp : σ.Pre w₀) (hi : σ.Inv (σ.abs w₀)) :
    ∃ opss : List (List O), (∀ os ∈ opss, ∀ op ∈ os, σ.Ok op) ∧
      σ.Pre w ∧ σ.Inv (σ.abs w) ∧
      σ.Agree (σ.abs w) (texec σ.step (σ.abs w₀) (stamp time bs opss)) := by
  obtain ⟨opss, hok, hr⟩ := reach_of_blockTrace htr
  obtain ⟨hp', hi', ha⟩ := h.untimed.lift hr (ok_stamp hok) hp hi
  exact ⟨opss, hok, hp', hi', ha⟩

/-- **Time-dependent invariants across blocks.** Let `I` be a time invariant of the model,
stable under `Agree`, holding of the initial abstraction at time `t₀`. Along any multi-block
trace whose block times do not decrease and lie in `[t₀, t₁]`, `I t₁` holds of the final
abstraction. The proof is one induction over the trace: no case split on times. -/
theorem Refinement.timeInvariant_blocks (h : σ.Refinement) {I : Nat → S → Prop}
    (hI : TimeInvariant σ.step σ.Inv I) (hIa : ∀ t s s', σ.Agree s s' → I t s → I t s')
    {bs : List B} {w₀ w : W} (htr : BlockTrace (BlockStep σ time) bs w₀ w)
    (hmono : bs.Pairwise fun b b' => time b ≤ time b') {t₀ t₁ : Nat}
    (hwithin : ∀ b ∈ bs, t₀ ≤ time b ∧ time b ≤ t₁) (ht : t₀ ≤ t₁) (hp : σ.Pre w₀)
    (hi : σ.Inv (σ.abs w₀)) (hI₀ : I t₀ (σ.abs w₀)) : I t₁ (σ.abs w) := by
  obtain ⟨opss, -, -, -, ha⟩ := h.lift_blocks htr hp hi
  have := (texec_timeInvariant h.inv_step hI (monotone_stamp hmono opss) hi hI₀
    (within_stamp hwithin opss) ht).2
  exact hIa _ _ _ (h.agree.symm ha) this

end TSystem

end QEDefi.Trace.Time
