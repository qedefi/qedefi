import EvmLogic.Program.Run

/-!
# A frame-local program logic

A weakest-precondition calculus for *one frame* of the explicit call stack: `SameFrame m m'`
(same parents, message, code, snapshot), `Halts m H` (the frame ends with outcome `o` at `mf`,
`H mf o`), `WP m Q H` (reach `Q` in the same frame, or end it with `H`), `Triple`. All are total
correctness; `WP.bind`, `WP.mono`, `WP.loop` compose them and `Halts.run` gives a `run` result.
-/

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter

/-! ## How a frame ends -/

/-- What a finished frame hands to its parent: the `ChildResult`, and the world and transient
storage after code deposit or rollback (the `let` at the start of `finishFrame`). -/
def frameResult (m : Machine) (o : Outcome) : ChildResult × World × TransientStorage :=
  let f := m.frame
  let target := f.msg.currentTarget
  let failed (e : ExceptionalHalt) : ChildResult × World × TransientStorage :=
    ({ gasLeft := 0, error := some e, reverted := false, output := .empty, sub := f.sub,
       target, kind := f.kind }, f.snapshot.1, f.snapshot.2)
  match o with
  | .success out =>
    let ok (gasLeft : Nat) : ChildResult :=
      { gasLeft, error := none, reverted := false, output := out, sub := f.sub, target,
        kind := f.kind }
    match f.kind with
    | .call _ _ => (ok f.gasLeft, m.world, m.transient)
    | .create =>
      match depositCode m.ctx.fork f.gasLeft out with
      | .ok gasLeft => (ok gasLeft, setCode m.world target out, m.transient)
      | .error e => failed e
  | .revert out =>
    ({ gasLeft := f.gasLeft, error := none, reverted := true, output := out, sub := f.sub,
       target, kind := f.kind }, f.snapshot.1, f.snapshot.2)
  | .halt e => failed e

/-- The machine in which the parent `p` (with ancestors `ps`) resumes after the frame of `mf`
ended with outcome `o`. -/
def resumeAfter (p : Frame) (ps : List Frame) (mf : Machine) (o : Outcome) : Machine :=
  resume { mf with frame := p, parents := ps, world := (frameResult mf o).2.1,
                   transient := (frameResult mf o).2.2 } (frameResult mf o).1

/-- `finishFrame`: return to the parent, or produce the top-level result. -/
theorem finishFrame_eq (m : Machine) (o : Outcome) :
    finishFrame m o = match m.parents with
      | [] => .done (topLevelResult m.frame.msg.target (frameResult m o).2.1
          (frameResult m o).2.2 (frameResult m o).1)
      | p :: ps => .running (resumeAfter p ps m o) := by
  have e : finishFrame m o = match frameResult m o with
      | (r, world, transient) => match m.parents with
        | [] => .done (topLevelResult m.frame.msg.target world transient r)
        | p :: ps => .running (resume { m with frame := p, parents := ps, world, transient } r) :=
    rfl
  rw [e]
  unfold resumeAfter
  obtain ⟨r, w, t⟩ := frameResult m o
  cases m.parents <;> rfl

theorem finishFrame_of_parents {m : Machine} {p : Frame} {ps : List Frame} (o : Outcome)
    (h : m.parents = p :: ps) : finishFrame m o = .running (resumeAfter p ps m o) := by
  rw [finishFrame_eq, h]

theorem finishFrame_of_top {m : Machine} (o : Outcome) (h : m.parents = []) :
    finishFrame m o = .done (topLevelResult m.frame.msg.target (frameResult m o).2.1
      (frameResult m o).2.2 (frameResult m o).1) := by
  rw [finishFrame_eq, h]

/-! ## Staying in the same frame -/

/-- `m'` executes the same frame as `m`, with the same parents and transaction constants. -/
structure SameFrame (m m' : Machine) : Prop where
  ctx : m'.ctx = m.ctx
  precompiles : m'.precompiles = m.precompiles
  originalWorld : m'.originalWorld = m.originalWorld
  parents : m'.parents = m.parents
  msg : m'.frame.msg = m.frame.msg
  code : m'.frame.code = m.frame.code
  jumpDests : m'.frame.jumpDests = m.frame.jumpDests
  kind : m'.frame.kind = m.frame.kind
  snapshot : m'.frame.snapshot = m.frame.snapshot

namespace SameFrame

variable {m₁ m₂ m₃ : Machine}

@[refl] theorem refl (m : Machine) : SameFrame m m :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem trans (h₁ : SameFrame m₁ m₂) (h₂ : SameFrame m₂ m₃) : SameFrame m₁ m₃ :=
  ⟨h₂.ctx.trans h₁.ctx, h₂.precompiles.trans h₁.precompiles,
   h₂.originalWorld.trans h₁.originalWorld, h₂.parents.trans h₁.parents, h₂.msg.trans h₁.msg,
   h₂.code.trans h₁.code, h₂.jumpDests.trans h₁.jumpDests, h₂.kind.trans h₁.kind,
   h₂.snapshot.trans h₁.snapshot⟩

/-- Updating only mutable fields keeps the frame (covers every non-halting, non-calling step
lemma). -/
theorem of_update (m : Machine) (w : World) (t : TransientStorage) (c : AddressSet)
    (pc : Nat) (stack : List Word) (mem : Memory) (gas : Nat) (rd : ByteArray)
    (sub : Substate) :
    SameFrame m { m with world := w, transient := t, createdAccounts := c, frame :=
      { m.frame with pc := pc, stack := stack, memory := mem, gasLeft := gas, returnData := rd,
                     sub := sub } } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SameFrame

/-! ## Reachability within a frame -/

/-- `m` reaches `m'` in some number of steps, still executing the same frame. -/
def Steps (m m' : Machine) : Prop := ∃ n, stepN n m = .running m' ∧ SameFrame m m'

/-- From `m`, the executing frame ends: some number of steps lead to `finishFrame mf o`, with
`mf` still in the frame of `m`, and `H mf o` holds. -/
def Halts (m : Machine) (H : Machine → Outcome → Prop) : Prop :=
  ∃ n mf o, stepN n m = finishFrame mf o ∧ SameFrame m mf ∧ H mf o

namespace Steps

variable {m₁ m₂ m₃ : Machine}

@[refl] theorem refl (m : Machine) : Steps m m := ⟨0, rfl, .refl m⟩

theorem trans (h₁ : Steps m₁ m₂) (h₂ : Steps m₂ m₃) : Steps m₁ m₃ := by
  obtain ⟨a, ha, hs₁⟩ := h₁
  obtain ⟨b, hb, hs₂⟩ := h₂
  exact ⟨a + b, by rw [stepN_add_of_running ha, hb], hs₁.trans hs₂⟩

theorem of_step (h : step m₁ = .running m₂) (hs : SameFrame m₁ m₂) : Steps m₁ m₂ :=
  ⟨1, by rw [stepN_one, h], hs⟩

theorem run_eq (h : Steps m₁ m₂) : ∃ n, ∀ k, run (n + k) m₁ = run k m₂ := by
  obtain ⟨n, hn, _⟩ := h
  exact ⟨n, fun k => run_add_of_stepN hn k⟩

end Steps

namespace Halts

variable {m m' : Machine} {H H' : Machine → Outcome → Prop}

theorem of_steps (h₁ : Steps m m') (h₂ : Halts m' H) : Halts m H := by
  obtain ⟨a, ha, hs₁⟩ := h₁
  obtain ⟨b, mf, o, hb, hs₂, hH⟩ := h₂
  exact ⟨a + b, mf, o, by rw [stepN_add_of_running ha, hb], hs₁.trans hs₂, hH⟩

theorem of_step {mf : Machine} {o : Outcome} (h : step m = finishFrame mf o)
    (hs : SameFrame m mf) (hH : H mf o) : Halts m H :=
  ⟨1, mf, o, by rw [stepN_one, h], hs, hH⟩

theorem mono (h : Halts m H) (hH : ∀ mf o, SameFrame m mf → H mf o → H' mf o) : Halts m H' := by
  obtain ⟨n, mf, o, hn, hs, hh⟩ := h
  exact ⟨n, mf, o, hn, hs, hH mf o hs hh⟩

/-- **Top level.** A halting top-level frame is a finished `run` (for all large enough fuel). -/
theorem run (h : Halts m H) (hp : m.parents = []) :
    ∃ n mf o, H mf o ∧ SameFrame m mf ∧ ∀ fuel, n ≤ fuel →
      Interpreter.run fuel m = .ok (topLevelResult m.frame.msg.target (frameResult mf o).2.1
        (frameResult mf o).2.2 (frameResult mf o).1) := by
  obtain ⟨n, mf, o, hn, hs, hH⟩ := h
  refine ⟨n, mf, o, hH, hs, fun fuel hle => run_mono (run_of_stepN_done ?_) hle⟩
  rw [hn, finishFrame_of_top o (hs.parents.trans hp), hs.msg]

/-- **Nested frames.** In a frame with parent `p`, a halting frame resumes the parent. -/
theorem resume {p : Frame} {ps : List Frame} (h : Halts m H) (hp : m.parents = p :: ps) :
    ∃ n mf o, H mf o ∧ SameFrame m mf ∧ stepN n m = .running (resumeAfter p ps mf o) := by
  obtain ⟨n, mf, o, hn, hs, hH⟩ := h
  exact ⟨n, mf, o, hH, hs, by rw [hn, finishFrame_of_parents o (hs.parents.trans hp)]⟩

end Halts

/-! ## Weakest preconditions -/

/-- `WP m Q H`: from `m`, execution reaches `m'` in the same frame with `Q m'`, or ends the
frame with `H mf o` (total correctness). -/
def WP (m : Machine) (Q : Machine → Prop) (H : Machine → Outcome → Prop) : Prop :=
  (∃ m', Steps m m' ∧ Q m') ∨ Halts m H

/-- Hoare triple: `∀ m, P m → WP m Q H`. -/
def Triple (P : Machine → Prop) (Q : Machine → Prop) (H : Machine → Outcome → Prop) : Prop :=
  ∀ m, P m → WP m Q H

namespace WP

variable {m m' : Machine} {Q Q' : Machine → Prop} {H H' : Machine → Outcome → Prop}

theorem ret (h : Q m) : WP m Q H := .inl ⟨m, .refl m, h⟩

/-- `ret` up to an equation (useful when the reached machine is computed). -/
theorem ret_of_eq (he : m = m') (h : Q m') : WP m Q H := he ▸ ret h

theorem halts (h : Halts m H) : WP m Q H := .inr h

theorem of_steps (h₁ : Steps m m') (h₂ : WP m' Q H) : WP m Q H := by
  rcases h₂ with ⟨m'', h, hq⟩ | h
  · exact .inl ⟨m'', h₁.trans h, hq⟩
  · exact .inr (Halts.of_steps h₁ h)

/-- **One instruction.** Prepend a step that stays in the frame. -/
theorem of_step (h : step m = .running m') (hs : SameFrame m m') (hw : WP m' Q H) :
    WP m Q H :=
  of_steps (Steps.of_step h hs) hw

/-- **Halting instruction.** The next step ends the frame. -/
theorem halt_of_step {mf : Machine} {o : Outcome} (h : step m = finishFrame mf o)
    (hs : SameFrame m mf) (hH : H mf o) : WP m Q H :=
  .inr (Halts.of_step h hs hH)

/-- **Sequencing**: run to `Q₁`, then continue from any machine satisfying it. -/
theorem bind {Q₁ : Machine → Prop} (h : WP m Q₁ H)
    (k : ∀ m', SameFrame m m' → Q₁ m' → WP m' Q H) : WP m Q H := by
  rcases h with ⟨m', hst, hq⟩ | h
  · exact of_steps hst (k m' (let ⟨_, _, hs⟩ := hst; hs) hq)
  · exact .inr h

/-- **Consequence.** -/
theorem mono (h : WP m Q H) (hq : ∀ m', SameFrame m m' → Q m' → Q' m')
    (hh : ∀ mf o, SameFrame m mf → H mf o → H' mf o) : WP m Q' H' := by
  rcases h with ⟨m', hst, h⟩ | h
  · exact .inl ⟨m', hst, hq m' (let ⟨_, _, hs⟩ := hst; hs) h⟩
  · exact .inr (h.mono hh)

theorem mono_left (h : WP m Q H) (hq : ∀ m', Q m' → Q' m') : WP m Q' H :=
  h.mono (fun m' _ h => hq m' h) (fun _ _ _ h => h)

theorem halts_of_false (h : WP m (fun _ => False) H) : Halts m H := by
  rcases h with ⟨_, _, h⟩ | h
  · exact h.elim
  · exact h

theorem sameFrame (h : WP m Q H) : WP m (fun m' => SameFrame m m' ∧ Q m') H :=
  h.mono (fun _ hs h => ⟨hs, h⟩) (fun _ _ _ h => h)

/-- **Loop rule** with invariant `I` and measure `μ`: the body returns to `I` with a smaller
measure, exits with `Q`, or ends the frame with `H`. -/
theorem loop (μ : Machine → Nat) (I : Machine → Prop) (hI : I m)
    (body : ∀ m, I m → WP m (fun m' => (I m' ∧ μ m' < μ m) ∨ Q m') H) : WP m Q H := by
  suffices ∀ n m, μ m = n → I m → WP m Q H from this _ m rfl hI
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m hm hI
    refine bind (body m hI) fun m' _ h => ?_
    rcases h with ⟨hI', hlt⟩ | hq
    · exact ih (μ m') (hm ▸ hlt) m' rfl hI'
    · exact ret hq

/-- Loop rule with the invariant `I k` indexed by a decreasing counter. -/
theorem loop_nat (I : Nat → Machine → Prop) {k : Nat} (hI : I k m)
    (body : ∀ k m, I k m → WP m (fun m' => (∃ j < k, I j m') ∨ Q m') H) : WP m Q H := by
  suffices ∀ k m, I k m → WP m Q H from this k m hI
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro m hI
    refine bind (body k m hI) fun m' _ h => ?_
    rcases h with ⟨j, hj, hI'⟩ | hq
    · exact ih j hj m' hI'
    · exact ret hq

end WP

namespace Triple

variable {P P' Q Q' R : Machine → Prop} {H H' : Machine → Outcome → Prop}

theorem seq (h₁ : Triple P Q H) (h₂ : Triple Q R H) : Triple P R H :=
  fun m hp => (h₁ m hp).bind fun m' _ hq => h₂ m' hq

theorem conseq (h : Triple P Q H) (hp : ∀ m, P' m → P m) (hq : ∀ m, Q m → Q' m)
    (hh : ∀ mf o, H mf o → H' mf o) : Triple P' Q' H' :=
  fun m hp' => (h m (hp m hp')).mono (fun m' _ => hq m') (fun mf o _ => hh mf o)

theorem cases (h₁ : Triple (fun m => P m ∧ P' m) Q H) (h₂ : Triple (fun m => P m ∧ ¬ P' m) Q H) :
    Triple P Q H := by
  intro m hp
  by_cases h : P' m
  · exact h₁ m ⟨hp, h⟩
  · exact h₂ m ⟨hp, h⟩

theorem skip : Triple P P H := fun _ hp => WP.ret hp

theorem loop (μ : Machine → Nat) (I : Machine → Prop)
    (body : ∀ m, I m → WP m (fun m' => (I m' ∧ μ m' < μ m) ∨ Q m') H) : Triple I Q H :=
  fun _ hI => WP.loop μ I hI body

end Triple

end EvmLogic.Program
