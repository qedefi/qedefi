import EvmLogic.Program.Nested.Step
import EvmLogic.GasMono.Interface

/-!
# Gas monotonicity: the first exit of a frame

`Halts m H` (`Program/Logic.lean`) says that *some* number of steps from `m` reach
`finishFrame mf o` with `SameFrame m mf` and `H mf o`. Such a witness need not be the frame's
real end: after the frame has returned, its parent may come back to a machine that looks like
a resumption after the same frame (`finishFrame` forgets much of `mf`). A simulation that
relates the real end of a low-gas frame to the end of the same frame with more gas needs the
**real** end, so this file defines it:

* `exitOf m`: if the next step of `m` ends its frame, the machine `finishFrame` sees and the
  outcome (`step m = finishFrame mf o`, `step_of_exitOf`), else `none`.
* `Above m₀ m`: `m` still runs the frame of `m₀` (`SameFrame`) or a descendant of it: the
  frame of `m₀` is suspended in `m.parents`, above `m₀.parents`, with its identity (`SameId`).
* `Exit m n mf o`: the frame of `m` runs `n` steps without returning to its parent
  (`Above`), and the next step ends it with `exitOf = some (mf, o)`. Unique (`Exit.unique`),
  and it exists whenever the frame returns at all (`find_exit`, `exit_of_halts_top`).
* `Exit.step`, `Exit.split`: the exit seen from the next machine of the frame, and from a
  child call (the child exits first, then the frame continues from `resumeAfter`).
-/

namespace EvmLean.Program.GasMono

open Interpreter Nested

/-! ## The step that ends a frame -/

/-- If the next step of `m` ends its frame: the machine `finishFrame` sees and the outcome.
Mirrors the `finishFrame` arms of `step`. -/
def exitOf (m : Machine) : Option (Machine × Outcome) :=
  if h : m.frame.pc < m.frame.code.size then
    match (exec (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc])).run m with
    | .error e => some (m, .halt e)
    | .ok (.stop out, m') => some (m', .success out)
    | .ok (.revert out, m') => some (m', .revert out)
    | .ok (.next, _) => none
    | .ok (.call _, _) => none
    | .ok (.create _, _) => none
  else some (m, .success .empty)

/-- An exit is a `finishFrame` step, from a machine the instruction reached. -/
theorem step_of_exitOf {m mf : Machine} {o : Outcome} (h : exitOf m = some (mf, o)) :
    step m = finishFrame mf o ∧ InstrFrame m mf := by
  unfold exitOf at h
  unfold step
  dsimp only
  split
  · rename_i hpc
    simp only [hpc, ↓reduceDIte] at h
    have hw := exec_frame (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m
    split at h
    · rename_i e he
      cases h
      rw [he]
      exact ⟨rfl, .refl m⟩
    · rename_i out m' he
      cases h
      rw [he]
      exact ⟨rfl, (hw.of_run he).1⟩
    · rename_i out m' he
      cases h
      rw [he]
      exact ⟨rfl, (hw.of_run he).1⟩
    all_goals cases h
  · rename_i hpc
    simp only [hpc, ↓reduceDIte] at h
    cases h
    exact ⟨rfl, .refl m⟩

/-- A step that does not end the frame stays in it, or starts a child. -/
theorem step_of_exitOf_none {m : Machine} (h : exitOf m = none) :
    (∃ m', step m = .running m' ∧ InstrFrame m m') ∨
    (∃ m' req, step m = .running (launchCall m' req) ∧ InstrFrame m m') ∨
    (∃ m' msg, step m = .running (launchCreate m' msg) ∧ InstrFrame m m') := by
  unfold exitOf at h
  unfold step
  dsimp only
  split
  · rename_i hpc
    simp only [hpc, ↓reduceDIte] at h
    have hw := exec_frame (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m
    split at h
    · cases h
    · cases h
    · cases h
    · rename_i m' he; rw [he]; exact .inl ⟨m', rfl, (hw.of_run he).1⟩
    · rename_i req m' he; rw [he]; exact .inr (.inl ⟨m', req, rfl, (hw.of_run he).1⟩)
    · rename_i msg m' he; rw [he]; exact .inr (.inr ⟨m', msg, rfl, (hw.of_run he).1⟩)
  · rename_i hpc
    simp only [hpc, ↓reduceDIte] at h
    cases h

/-! ## Frames above a machine -/

/-- The identity of a frame: the fields no instruction changes. -/
structure SameId (f g : Frame) : Prop where
  /-- Same message. -/
  msg : f.msg = g.msg
  /-- Same code. -/
  code : f.code = g.code
  /-- Same jump table. -/
  jumpDests : f.jumpDests = g.jumpDests
  /-- Same kind. -/
  kind : f.kind = g.kind
  /-- Same snapshot. -/
  snapshot : f.snapshot = g.snapshot

/-- Symmetry of `SameFrame`. -/
theorem _root_.EvmLean.Program.SameFrame.symm {m m' : Machine} (h : SameFrame m m') : SameFrame m' m :=
  ⟨h.ctx.symm, h.precompiles.symm, h.originalWorld.symm, h.parents.symm, h.msg.symm,
   h.code.symm, h.jumpDests.symm, h.kind.symm, h.snapshot.symm⟩

/-- The frame of `m₀` is still running in `m` (`SameFrame`), or suspended below the executing
frame of `m`, directly above `m₀.parents`. -/
def Above (m₀ m : Machine) : Prop :=
  SameFrame m₀ m ∨
    (m.ctx = m₀.ctx ∧ m.precompiles = m₀.precompiles ∧ m.originalWorld = m₀.originalWorld ∧
      ∃ fs f, m.parents = fs ++ f :: m₀.parents ∧ SameId f m₀.frame)

namespace Above

variable {m₀ m₁ m : Machine}

/-- `Above` only depends on the frame of `m₀`. -/
theorem congr (h₀ : SameFrame m₀ m₁) (h : Above m₀ m) : Above m₁ m := by
  rcases h with h | ⟨hc, hp, ho, fs, f, hpar, hid⟩
  · exact .inl (h₀.symm.trans h)
  · refine .inr ⟨hc.trans h₀.ctx.symm, hp.trans h₀.precompiles.symm,
      ho.trans h₀.originalWorld.symm, fs, f, by rw [hpar, h₀.parents], ?_⟩
    exact ⟨hid.msg.trans h₀.msg.symm, hid.code.trans h₀.code.symm,
      hid.jumpDests.trans h₀.jumpDests.symm, hid.kind.trans h₀.kind.symm,
      hid.snapshot.trans h₀.snapshot.symm⟩

/-- A machine above `m₀` has at least as many parents. -/
theorem length_le (h : Above m₀ m) : m₀.parents.length ≤ m.parents.length := by
  rcases h with h | ⟨_, _, _, fs, f, hpar, _⟩
  · rw [h.parents]; exact Nat.le_refl _
  · rw [hpar]; simp only [List.length_append, List.length_cons]; omega

/-- A machine in the frame of `m₀` is above it. -/
theorem of_same (h : SameFrame m₀ m) : Above m₀ m := .inl h

end Above

/-- `resume` keeps the resumed frame's identity. -/
theorem sameId_resume (M : Machine) (r : ChildResult) : SameId (resume M r).frame M.frame :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A machine after a pushed child is above the caller's machine. -/
theorem above_push {m₀ m' : Machine} (hs : SameFrame m₀ m') (M : Machine)
    (hc : M.ctx = m'.ctx) (hp : M.precompiles = m'.precompiles)
    (ho : M.originalWorld = m'.originalWorld) (hpar : M.parents = m'.frame :: m'.parents) :
    Above m₀ M :=
  .inr ⟨hc.trans hs.ctx, hp.trans hs.precompiles, ho.trans hs.originalWorld, [], m'.frame,
    by rw [hpar, hs.parents]; rfl,
    ⟨hs.msg, hs.code, hs.jumpDests, hs.kind, hs.snapshot⟩⟩

/-- A machine after a pushed child, below further frames, stays above. -/
theorem above_push_deep {m₀ m' : Machine} {fs : List Frame} {f : Frame}
    (hc' : m'.ctx = m₀.ctx) (hp' : m'.precompiles = m₀.precompiles)
    (ho' : m'.originalWorld = m₀.originalWorld)
    (hpar' : m'.parents = fs ++ f :: m₀.parents) (hid : SameId f m₀.frame) (M : Machine)
    (hc : M.ctx = m'.ctx) (hp : M.precompiles = m'.precompiles)
    (ho : M.originalWorld = m'.originalWorld) (hpar : M.parents = m'.frame :: m'.parents) :
    Above m₀ M :=
  .inr ⟨hc.trans hc', hp.trans hp', ho.trans ho', m'.frame :: fs, f,
    by rw [hpar, hpar']; rfl, hid⟩

/-- **One step from above** either stays above or ends the frame of `m₀` itself. -/
theorem Above.step {m₀ m : Machine} (h : Above m₀ m) :
    (∃ m', step m = .running m' ∧ Above m₀ m') ∨
      (SameFrame m₀ m ∧ ∃ mf o, exitOf m = some (mf, o)) := by
  cases hx : exitOf m with
  | some p =>
    obtain ⟨mf, o⟩ := p
    obtain ⟨hst, hf⟩ := step_of_exitOf hx
    rcases h with h | ⟨hc, hp, ho, fs, f, hpar, hid⟩
    · exact .inr ⟨h, mf, o, rfl⟩
    · left
      have hmpar : mf.parents = fs ++ f :: m₀.parents := hf.same.parents.trans hpar
      cases fs with
      | nil =>
        refine ⟨_, by rw [hst, finishFrame_of_parents o hmpar], .inl ?_⟩
        exact ⟨hf.same.ctx.trans hc, hf.same.precompiles.trans hp,
          hf.same.originalWorld.trans ho, rfl, hid.msg, hid.code, hid.jumpDests, hid.kind,
          hid.snapshot⟩
      | cons g fs =>
        refine ⟨_, by rw [hst, finishFrame_of_parents o hmpar], .inr ?_⟩
        exact ⟨hf.same.ctx.trans hc, hf.same.precompiles.trans hp,
          hf.same.originalWorld.trans ho, fs, f, rfl, hid⟩
  | none =>
    left
    rcases step_of_exitOf_none hx with ⟨m', hst, hf⟩ | ⟨m', req, hst, hf⟩ | ⟨m', msg, hst, hf⟩
    · refine ⟨m', hst, ?_⟩
      rcases h with h | ⟨hc, hp, ho, fs, f, hpar, hid⟩
      · exact .inl (h.trans hf.same)
      · exact .inr ⟨hf.same.ctx.trans hc, hf.same.precompiles.trans hp,
          hf.same.originalWorld.trans ho, fs, f, hf.same.parents.trans hpar, hid⟩
    · refine ⟨_, hst, ?_⟩
      rcases launchCall_cases m' req with ⟨r, w, t, he, -, -⟩ | he <;> rw [he]
      · have hs : SameFrame m' (resume { m' with world := w, transient := t } r) :=
          SameFrame.trans (m₂ := { m' with world := w, transient := t })
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (sameFrame_resume _ _)
        rcases h with h | ⟨hc, hp, ho, fs, f, hpar, hid⟩
        · exact .inl ((h.trans hf.same).trans hs)
        · exact .inr ⟨(hs.ctx.trans hf.same.ctx).trans hc,
            (hs.precompiles.trans hf.same.precompiles).trans hp,
            (hs.originalWorld.trans hf.same.originalWorld).trans ho, fs, f,
            (hs.parents.trans hf.same.parents).trans hpar, hid⟩
      · rcases h with h | ⟨hc, hp, ho, fs, f, hpar, hid⟩
        · exact above_push (h.trans hf.same) _ rfl rfl rfl rfl
        · exact above_push_deep (hf.same.ctx.trans hc) (hf.same.precompiles.trans hp)
            (hf.same.originalWorld.trans ho) (hf.same.parents.trans hpar) hid _ rfl rfl rfl rfl
    · refine ⟨_, hst, ?_⟩
      rcases h with h | ⟨hc, hp, ho, fs, f, hpar, hid⟩
      · exact above_push (h.trans hf.same) _ rfl rfl rfl rfl
      · exact above_push_deep (hf.same.ctx.trans hc) (hf.same.precompiles.trans hp)
          (hf.same.originalWorld.trans ho) (hf.same.parents.trans hpar) hid _ rfl rfl rfl rfl

/-! ## The exit -/

/-- **The real end of the frame of `m`**: for `n` steps the machine stays above `m`, and the
`n`-th machine, in the frame of `m`, ends it from `mf` with outcome `o`. -/
structure Exit (m : Machine) (n : Nat) (mf : Machine) (o : Outcome) : Prop where
  /-- Up to step `n`, the frame of `m` has not returned. -/
  within : ∀ k ≤ n, ∃ m', stepN k m = .running m' ∧ Above m m'
  /-- Step `n` is in the frame of `m`, and its step ends the frame. -/
  last : ∃ m', stepN n m = .running m' ∧ SameFrame m m' ∧ exitOf m' = some (mf, o)

/-- The machine after an exit: `finishFrame`. -/
theorem Exit.finish {m mf : Machine} {n : Nat} {o : Outcome} (h : Exit m n mf o) :
    stepN (n + 1) m = finishFrame mf o ∧ SameFrame m mf := by
  obtain ⟨m', hn, hs, hx⟩ := h.last
  obtain ⟨hst, hf⟩ := step_of_exitOf hx
  refine ⟨?_, hs.trans hf.same⟩
  rw [stepN_add_of_running hn 1, stepN_one, hst]

/-- An exit is a `Halts` witness. -/
theorem Exit.halts {m mf : Machine} {n : Nat} {o : Outcome} (h : Exit m n mf o) :
    Halts m (fun mf' o' => mf' = mf ∧ o' = o) :=
  ⟨n + 1, mf, o, h.finish.1, h.finish.2, rfl, rfl⟩

/-- `finishFrame` leaves the frame: what it produces is not above. -/
theorem not_above_finishFrame {m₀ mf m' : Machine} {o : Outcome}
    (hs : SameFrame m₀ mf) (h : finishFrame mf o = .running m') : ¬ Above m₀ m' := by
  intro ha
  have hl := ha.length_le
  rw [finishFrame_eq] at h
  split at h
  · cases h
  · rename_i p ps hp
    cases h
    have : m₀.parents = p :: ps := hs.parents.symm.trans hp
    simp only [resumeAfter, resume_parents, this, List.length_cons] at hl
    omega

/-- Before the exit, every step stays above (and is not `finishFrame` of the frame). -/
theorem find_exit {m₀ : Machine} :
    ∀ n m, Above m₀ m → ¬ (∃ m', stepN n m = .running m' ∧ Above m₀ m') →
      ∃ k < n, (∀ j ≤ k, ∃ m', stepN j m = .running m' ∧ Above m₀ m') ∧
        ∃ m', stepN k m = .running m' ∧ SameFrame m₀ m' ∧ ∃ mf o, exitOf m' = some (mf, o) := by
  intro n
  induction n with
  | zero => intro m ha hn; exact absurd ⟨m, rfl, ha⟩ hn
  | succ n ih =>
    intro m ha hn
    rcases ha.step with ⟨m', hst, ha'⟩ | ⟨hs, mf, o, hx⟩
    · have hn' : ¬ (∃ m'', stepN n m' = .running m'' ∧ Above m₀ m'') := by
        rw [stepN_succ_of_running hst] at hn; exact hn
      obtain ⟨k, hk, hw, m'', hk', hs, hx⟩ := ih m' ha' hn'
      refine ⟨k + 1, by omega, ?_, m'', by rw [stepN_succ_of_running hst]; exact hk', hs, hx⟩
      intro j hj
      cases j with
      | zero => exact ⟨m, rfl, ha⟩
      | succ j => rw [stepN_succ_of_running hst]; exact hw j (by omega)
    · exact ⟨0, by omega, fun j hj => by
        rw [Nat.le_zero.1 hj]; exact ⟨m, rfl, ha⟩, m, rfl, hs, mf, o, hx⟩

/-- An exit exists as soon as the frame is left within `n` steps. -/
theorem exit_of_leaves {m : Machine} {n : Nat}
    (h : ¬ (∃ m', stepN n m = .running m' ∧ Above m m')) :
    ∃ k < n, ∃ mf o, Exit m k mf o := by
  obtain ⟨k, hk, hw, m', hk', hs, mf, o, hx⟩ := find_exit n m (.of_same (.refl m)) h
  exact ⟨k, hk, mf, o, hw, m', hk', hs, hx⟩

/-- **The exit is unique.** -/
theorem Exit.unique {m mf mf' : Machine} {n n' : Nat} {o o' : Outcome} (h : Exit m n mf o)
    (h' : Exit m n' mf' o') : n = n' ∧ mf = mf' ∧ o = o' := by
  have key : ∀ {a b mfa mfb oa ob}, Exit m a mfa oa → Exit m b mfb ob → ¬ a < b := by
    intro a b mfa mfb oa ob ha hb hab
    obtain ⟨m', hn, hm'⟩ := hb.within (a + 1) (by omega)
    have := ha.finish
    rw [this.1] at hn
    exact not_above_finishFrame this.2 hn hm'
  have hnn : n = n' := by
    have h1 := key h h'
    have h2 := key h' h
    omega
  subst hnn
  obtain ⟨m₁, h₁, -, hx₁⟩ := h.last
  obtain ⟨m₂, h₂, -, hx₂⟩ := h'.last
  rw [h₁] at h₂
  cases h₂
  rw [hx₁] at hx₂
  cases hx₂
  exact ⟨rfl, rfl, rfl⟩

/-- An exit seen from a later machine of the same frame. -/
theorem Exit.shift {m m' mf : Machine} {n j : Nat} {o : Outcome} (h : Exit m n mf o)
    (hj : stepN j m = .running m') (hs : SameFrame m m') (hle : j ≤ n) :
    Exit m' (n - j) mf o := by
  constructor
  · intro k hk
    obtain ⟨x, hx, ha⟩ := h.within (j + k) (by omega)
    rw [stepN_add_of_running hj] at hx
    exact ⟨x, hx, ha.congr hs⟩
  · obtain ⟨x, hx, hsx, hxx⟩ := h.last
    refine ⟨x, ?_, hs.symm.trans hsx, hxx⟩
    rw [← stepN_add_of_running hj, show j + (n - j) = n by omega]
    exact hx

/-- A step that stays in the frame comes before the exit. -/
theorem Exit.next {m m' mf : Machine} {n : Nat} {o : Outcome} (h : Exit m n mf o)
    (hst : step m = .running m') (hs : SameFrame m m') : 1 ≤ n ∧ Exit m' (n - 1) mf o := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      obtain ⟨x, hx, -, hxx⟩ := h.last
      cases hx
      have := (step_of_exitOf hxx)
      rw [hst] at this
      exact absurd (.of_same hs) (not_above_finishFrame ((SameFrame.refl m).trans this.2.same)
        this.1.symm)
    · exact h0
  exact ⟨hn, h.shift (by rw [stepN_one, hst]) hs hn⟩

/-- **The exit of a frame across a child call.** If the next step of `m` pushes a child `mc`
(with `m`'s frame, as `p`, suspended on top of `m.parents`), the child exits first, after `nc`
steps, and the frame of `m` exits from the machine resuming `p` after the child. -/
theorem Exit.split {m mc mf : Machine} {p : Frame} {n : Nat} {o : Outcome} (h : Exit m n mf o)
    (hst : step m = .running mc) (hpar : mc.parents = p :: m.parents) (hid : SameId p m.frame)
    (hc : mc.ctx = m.ctx) (hp : mc.precompiles = m.precompiles)
    (ho : mc.originalWorld = m.originalWorld) :
    ∃ nc mfc oc, Exit mc nc mfc oc ∧ nc + 2 ≤ n ∧
      stepN (nc + 2) m = .running (resumeAfter p m.parents mfc oc) ∧
      SameFrame m (resumeAfter p m.parents mfc oc) ∧
      Exit (resumeAfter p m.parents mfc oc) (n - (nc + 2)) mf o := by
  obtain ⟨x, hx, hsx, hxx⟩ := h.last
  -- `n ≥ 1`: the first step does not end the frame.
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      cases hx
      have := step_of_exitOf hxx
      rw [hst, finishFrame_eq] at this
      obtain ⟨he, hf⟩ := this
      split at he
      · cases he
      · rename_i q qs hq
        cases he
        have h1 := congrArg List.length hpar
        have h2 : (resumeAfter q qs mf o).parents = qs := rfl
        have h3 : m.parents = q :: qs := hf.same.parents.symm.trans hq
        rw [h2, h3] at h1
        simp only [List.length_cons] at h1
        omega
    · exact h0
  -- The child leaves `Above mc` by step `n - 1`.
  have hleave : ¬ (∃ m', stepN (n - 1) mc = .running m' ∧ Above mc m') := by
    rintro ⟨y, hy, hay⟩
    have : stepN n m = stepN (n - 1) mc := by
      rw [show n = 1 + (n - 1) by omega, stepN_add_of_running (by rw [stepN_one, hst])]
      simp
    rw [this, hy] at hx
    cases hx
    have h1 := hay.length_le
    rw [hpar, hsx.parents] at h1
    simp only [List.length_cons] at h1
    omega
  obtain ⟨k, hk, mfc, oc, hex⟩ := exit_of_leaves hleave
  have hc' := hex.finish
  have hpc : mfc.parents = p :: m.parents := hc'.2.parents.trans hpar
  have hres : stepN (k + 2) m = .running (resumeAfter p m.parents mfc oc) := by
    rw [show k + 2 = 1 + (k + 1) by omega, stepN_add_of_running (by rw [stepN_one, hst]),
      hc'.1, finishFrame_of_parents oc hpc]
  have hsame : SameFrame m (resumeAfter p m.parents mfc oc) := by
    refine SameFrame.trans ?_ (sameFrame_resume _ _)
    exact ⟨hc'.2.ctx.trans hc, hc'.2.precompiles.trans hp, hc'.2.originalWorld.trans ho, rfl,
      hid.msg, hid.code, hid.jumpDests, hid.kind, hid.snapshot⟩
  refine ⟨k, mfc, oc, hex, by omega, hres, hsame, h.shift hres hsame (by omega)⟩

/-- **Top level: an exit exists**, and every `Halts` witness gives the same final result as
the exit (a finished top-level message is absorbing). -/
theorem exit_of_halts_top {m : Machine} {H : Machine → Outcome → Prop} (hp : m.parents = [])
    (h : Halts m H) :
    ∃ n mf o, Exit m n mf o ∧ ∃ mf' o', H mf' o' ∧ SameFrame m mf' ∧
      finishFrame mf' o' = finishFrame mf o := by
  obtain ⟨b, mf', o', hb, hs', hH⟩ := h
  have hdone : ∃ r, finishFrame mf' o' = .done r := by
    rw [finishFrame_of_top o' (hs'.parents.trans hp)]; exact ⟨_, rfl⟩
  obtain ⟨r, hr⟩ := hdone
  have hleave : ¬ (∃ m', stepN b m = .running m' ∧ Above m m') := by
    rintro ⟨y, hy, -⟩; rw [hb, hr] at hy; cases hy
  obtain ⟨k, hk, mf, o, hex⟩ := exit_of_leaves hleave
  refine ⟨k, mf, o, hex, mf', o', hH, hs', ?_⟩
  have h1 := hex.finish
  obtain ⟨r', hr'⟩ : ∃ r', finishFrame mf o = .done r' := by
    rw [finishFrame_of_top o (h1.2.parents.trans hp)]; exact ⟨_, rfl⟩
  have h2 := stepN_add_of_done (h1.1.trans hr') (b - (k + 1))
  rw [show k + 1 + (b - (k + 1)) = b by omega, hb, hr] at h2
  rw [hr, hr', h2]

end EvmLean.Program.GasMono
