import EvmLogic.Program.Reentrancy.Exec
import EvmLogic.Program.Nested.Run

/-!
# Every frame halts, and arbitrary code keeps a protected invariant

The machine-level simulation of `EvmLogic.Program.Nested.Run` works on whole runs and needs
protected frames to be atomic. This module proves its **frame-local** counterpart, by strong
induction on the frame's gas (every step strictly decreases it, `step_strict`):

* `halts_inv` (**the havoc theorem**): a frame of arbitrary code that is not itself dangerous,
  started in a `Good` world with a `Good` snapshot, ends (it always does: total correctness) in a
  `Good` world, provided every dangerous frame it reaches at any depth keeps `Good` (`Covers`).
  Dangerous frames may be reached with dangerous ancestors: this is what reentrancy needs.
* `halts_any`: every frame halts (EVM termination, from `halts_inv` with nothing protected).
* `halts_low` (**the stipend lemma**): a frame with at most `Gas.callStipend` gas, and every frame
  it starts, leaves the world unchanged (`SSTORE` is below its sentry, value transfers, creations
  and `SELFDESTRUCT` are unaffordable); only transient storage, logs and return data change.
* `halts_static`: a static frame keeps `Good` with no frame summaries at all.

`EvmLogic.Program.Reentrancy.Havoc` turns these into rules for the frame-local logic.
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested

variable {P : Address → Prop} {Good : World → Prop}

/-! ## One step, with strict gas -/

/-- `Wp` distributes over conjunction. -/
theorem wp_and {α : Type} {x : M α} {Q R : α → Machine → Prop} {m : Machine} (h₁ : Wp x Q m)
    (h₂ : Wp x R m) : Wp x (fun a m' => Q a m' ∧ R a m') m := by
  unfold Wp at *
  cases he : x.run m with
  | ok p => rw [he] at h₁ h₂; exact ⟨h₁, h₂⟩
  | error e => trivial

/-- The frame of `m` has at most the call stipend (2300). -/
abbrev Low (m : Machine) : Prop := m.frame.gasLeft ≤ Gas.callStipend

/-- **How a step goes, with strict gas**: `step_cases`, plus: a step staying in the frame leaves
strictly less gas, a requested child gets strictly less than the caller gave up, a creation comes
from a non-static frame and needs more than the stipend, and with at most the stipend the world
is unchanged and no requested call moves value. -/
theorem step_strict (m : Machine) :
    (∃ m' o, step m = finishFrame m' o ∧ InstrFrame m m' ∧ (Low m → m'.world = m.world)) ∨
    (∃ m', step m = .running m' ∧ InstrFrame m m' ∧ m'.frame.gasLeft < m.frame.gasLeft ∧
      (Low m → m'.world = m.world)) ∨
    (∃ m' req, step m = .running (launchCall m' req) ∧ InstrFrame m m' ∧ CallOk m m' req ∧
      m'.frame.gasLeft + req.msg.gas < m.frame.gasLeft ∧
      (Low m → m'.world = m.world ∧ (req.msg.shouldTransferValue = false ∨ req.msg.value = 0))) ∨
    (∃ m' msg, step m = .running (launchCreate m' msg) ∧ InstrFrame m m' ∧ CreateOk m m' msg ∧
      m'.frame.gasLeft + msg.gas < m.frame.gasLeft ∧ m.frame.msg.isStatic = false ∧ ¬ Low m) := by
  unfold step
  dsimp only
  split
  · have hw := wp_and (exec_frame (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m)
      (exec_strict (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc]) m)
    split
    · exact .inl ⟨m, _, rfl, .refl m, fun _ => rfl⟩
    · rename_i m' h
      obtain ⟨⟨hf, -⟩, hs, hl⟩ := hw.of_run h
      exact .inr (.inl ⟨m', rfl, hf, hs, hl⟩)
    · rename_i out m' h
      obtain ⟨⟨hf, -⟩, -, hl⟩ := hw.of_run h
      exact .inl ⟨m', _, rfl, hf, hl⟩
    · rename_i out m' h
      obtain ⟨⟨hf, -⟩, -, hl⟩ := hw.of_run h
      exact .inl ⟨m', _, rfl, hf, hl⟩
    · rename_i req m' h
      obtain ⟨⟨hf, hc⟩, hs, hl⟩ := hw.of_run h
      exact .inr (.inr (.inl ⟨m', req, rfl, hf, hc, hs, hl⟩))
    · rename_i msg m' h
      obtain ⟨⟨hf, hc⟩, ⟨hs, hst⟩, hl⟩ := hw.of_run h
      exact .inr (.inr (.inr ⟨m', msg, rfl, hf, hc, hs, hst, hl⟩))
  · exact .inl ⟨m, _, rfl, .refl m, fun _ => rfl⟩

/-! ## Returning from a child -/

/-- **Return from a child frame.** If `step m` pushes a child `mc` (caller frame `p`) that halts
with `Hc`, the caller resumes in the frame of `m`, with at most `p`'s gas plus the child's. -/
theorem halts_resume {m mc : Machine} {p : Frame} {Hc H : Machine → Outcome → Prop}
    (hstep : step m = .running mc) (hpar : mc.parents = p :: m.parents)
    (hp : SameFrame m { mc with frame := p, parents := m.parents })
    (hpre : PrecompilesOk mc.precompiles) (hcallee : Halts mc Hc)
    (k : ∀ mf o, SameFrame mc mf → Hc mf o →
      (resumeAfter p m.parents mf o).frame.gasLeft ≤ p.gasLeft + mc.frame.gasLeft →
      Halts (resumeAfter p m.parents mf o) H) : Halts m H := by
  obtain ⟨n, mf, o, hH, hs, hn⟩ := hcallee.resume hpar
  have hsame : SameFrame m (resumeAfter p m.parents mf o) := by
    refine SameFrame.trans ?_ (sameFrame_resume _ _)
    exact ⟨hs.ctx.trans hp.ctx, hs.precompiles.trans hp.precompiles,
      hs.originalWorld.trans hp.originalWorld, rfl, hp.msg, hp.code, hp.jumpDests, hp.kind,
      hp.snapshot⟩
  have hg := stepN_gas hpre n
  rw [hn] at hg
  simp only [resultGas, gasSum, resumeAfter, resume_gasLeft, resume_parents, hpar,
    List.map_cons, List.sum_cons] at hg
  refine Halts.of_steps ⟨n + 1, ?_, hsame⟩ (k mf o hs hH ?_)
  · rw [show n + 1 = 1 + n by omega, stepN_add_of_running (by rw [stepN_one, hstep]), hn]
  · simp only [resumeAfter, resume_gasLeft]; omega

/-- The child of `pushCall` starts with the requested gas. -/
@[simp] theorem pushCall_gasLeft (m : Machine) (req : CallRequest) :
    (pushCall m req).frame.gasLeft = req.msg.gas := rfl
/-- `pushCall` suspends the caller frame. -/
@[simp] theorem pushCall_parents (m : Machine) (req : CallRequest) :
    (pushCall m req).parents = m.frame :: m.parents := rfl
/-- The child of `launchCreate` starts with the requested gas. -/
@[simp] theorem launchCreate_gasLeft (m : Machine) (msg : Message) :
    (launchCreate m msg).frame.gasLeft = msg.gas := rfl
/-- `launchCreate` suspends the caller frame. -/
@[simp] theorem launchCreate_parents (m : Machine) (msg : Message) :
    (launchCreate m msg).parents = m.frame :: m.parents := rfl

/-! ## The invariant of a frame of arbitrary code -/

/-- What `halts_inv` assumes of a machine: a `Good` world, a frame that cannot write protected
storage and whose rollback snapshot is `Good`, standard precompiles. Nothing about the parents. -/
structure Inv (P : Address → Prop) (Good : World → Prop) (m : Machine) : Prop where
  /-- The current world is `Good`. -/
  world : Good m.world
  /-- The executing frame is not dangerous and its snapshot is `Good`. -/
  frame : FrameInv P Good m.frame
  /-- Standard precompiles. -/
  pre : m.precompiles = PrecompileImpl.standard m.ctx

/-- **Frame summaries of the protected code**: every dangerous frame with at most `G` gas, started
from a `Good` snapshot (with any parents, in particular dangerous ones), keeps `Good`. -/
def Covers (P : Address → Prop) (Good : World → Prop) (G : Nat) : Prop :=
  ∀ m, DangerStart P Good G m → Halts m (fun mf o => Good (frameResult mf o).2.1)

/-- `Covers` for more gas gives `Covers` for less. -/
theorem Covers.mono {G G' : Nat} (h : Covers P Good G) (hle : G' ≤ G) : Covers P Good G' :=
  fun m hd => h m { hd with gas := Nat.le_trans hd.gas hle }

/-- **Proving `Covers` by induction on gas**: a dangerous frame's summary may assume the summaries
of every dangerous frame with less gas (all reentrant frames have less gas than their ancestors). -/
theorem covers_of_lt (h : ∀ G, (∀ G' < G, Covers P Good G') → Covers P Good G) (G : Nat) :
    Covers P Good G := by
  induction G using Nat.strongRecOn with
  | ind G ih => exact h G ih

/-- A caller satisfying `FrameInv` resumes into `Inv` after a child ending in a `Good` world. -/
theorem Inv.of_resume {mf : Machine} {p : Frame} {ps : List Frame} {o : Outcome}
    (hp : FrameInv P Good p) (hw : Good (frameResult mf o).2.1)
    (hpre : mf.precompiles = PrecompileImpl.standard mf.ctx) :
    Inv P Good (resumeAfter p ps mf o) where
  world := hw
  frame := hp.of_same rfl rfl rfl
  pre := hpre

/-- The child of a call requested by a non-dangerous frame: a dangerous frame start, or a frame
satisfying `Inv`. -/
theorem child_cases (S : GoodOk P Good) {G : Nat} {m m' : Machine} {req : CallRequest}
    (h : Inv P Good m) (hf : InstrFrame m m') (hc : CallOk m m' req) (hg : req.msg.gas ≤ G) :
    DangerStart P Good G (pushCall m' req) ∨ Inv P Good (pushCall m' req) := by
  have hw' := hf.good S h.frame.safe h.world
  have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
    rw [hf.same.precompiles, hf.same.ctx]; exact h.pre
  by_cases hd : P req.msg.currentTarget ∧ req.msg.isStatic = false
  · obtain ⟨hst, hcur⟩ := hc.nonstatic hd.2
    have hne : req.msg.currentTarget ≠ m.frame.msg.currentTarget := by
      rintro he; exact h.frame.safe ⟨he ▸ hd.1, hst⟩
    obtain ⟨hcaller, hcode⟩ := hcur.resolve_left hne
    have hdel := S.deleg _ h.world _ hd.1
    obtain ⟨hcode, hca, -⟩ := hcode hdel
    have hkeep := hf.keep _ (S.code _ h.world _ hd.1) fun hwr => hne hwr.1
    refine .inl ⟨⟨_, _, rfl⟩, hd, hw', fun p hp => keep_transferValue (S.code _ hw' p hp),
      ?_, hc.target, hca, ?_, hg, hc.depthLe, hpre'⟩
    · show req.msg.code = (transferValue m'.world req.msg).code req.msg.currentTarget
      rw [(keep_transferValue (S.code _ hw' _ hd.1)).code, hkeep.code]; exact hcode
    · show ¬ P req.msg.caller
      rw [hcaller]; intro hp; exact h.frame.safe ⟨hp, hst⟩
  · exact .inr ⟨S.transferValue hw' _, ⟨hw', hd, fun hk => by cases hk⟩, hpre'⟩

/-- **The havoc theorem.** Under `Covers` for its gas, a frame satisfying `Inv` halts in a `Good`
world, whatever code it and its descendants run. -/
theorem halts_inv (S : GoodOk P Good) {G : Nat} (hcov : Covers P Good G) :
    ∀ m, m.frame.gasLeft ≤ G → Inv P Good m →
      Halts m (fun mf o => Good (frameResult mf o).2.1) := by
  suffices ∀ n m, m.frame.gasLeft = n → n ≤ G → Inv P Good m →
      Halts m (fun mf o => Good (frameResult mf o).2.1) from fun m hg h => this _ m rfl hg h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m hn hG h
    have ih' : ∀ m'', m''.frame.gasLeft < m.frame.gasLeft → Inv P Good m'' →
        Halts m'' (fun mf o => Good (frameResult mf o).2.1) :=
      fun m'' hlt hi => ih _ (hn ▸ hlt) m'' rfl (by omega) hi
    rcases step_strict m with ⟨m', o, he, hf, -⟩ | ⟨m', he, hf, hs, -⟩ |
      ⟨m', req, he, hf, hc, hs, -⟩ | ⟨m', msg, he, hf, hc, hs, -, -⟩
    · exact Halts.of_step he hf.same
        (frameResult_good S (h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind)
          (hf.good S h.frame.safe h.world) o)
    · refine Halts.of_steps (Steps.of_step he hf.same) (ih' m' hs ?_)
      exact ⟨hf.good S h.frame.safe h.world,
        h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind,
        by rw [hf.same.precompiles, hf.same.ctx]; exact h.pre⟩
    · have hw' := hf.good S h.frame.safe h.world
      have hfr' := h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind
      have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
        rw [hf.same.precompiles, hf.same.ctx]; exact h.pre
      rcases launchCall_cases m' req with ⟨r, w, t, hl, hw, hr⟩ | hl <;> rw [hl] at he
      · have hr' := hr (by rw [hpre']; exact precompilesOk_standard _)
        have hsf : SameFrame m (resume { m' with world := w, transient := t } r) :=
          (hf.same.trans (show SameFrame m' { m' with world := w, transient := t } from
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)).trans (sameFrame_resume _ _)
        refine Halts.of_steps (Steps.of_step he hsf) (ih' _ ?_ ?_)
        · simp only [resume_gasLeft]; omega
        · refine ⟨?_, hfr'.of_same rfl rfl rfl, hpre'⟩
          rcases hw with rfl | rfl
          · exact S.transferValue hw' _
          · exact hw'
      · have hpar : (pushCall m' req).parents = m'.frame :: m.parents := by
          simp only [pushCall, hf.same.parents]
        have hcallee : Halts (pushCall m' req) (fun mf o => Good (frameResult mf o).2.1) := by
          rcases child_cases (G := G) S h hf hc (by omega) with hd | hi
          · exact hcov _ hd
          · exact ih' _ (by rw [pushCall_gasLeft]; omega) hi
        refine halts_resume he hpar ⟨hf.same.ctx, hf.same.precompiles, hf.same.originalWorld,
          rfl, hf.same.msg, hf.same.code, hf.same.jumpDests, hf.same.kind, hf.same.snapshot⟩
          (by simp only [pushCall]; rw [hpre']; exact precompilesOk_standard _) hcallee ?_
        intro mf o hsf hgood hgas
        refine ih' _ ?_ (Inv.of_resume hfr' hgood ?_)
        · rw [pushCall_gasLeft] at hgas; omega
        · rw [hsf.precompiles, hsf.ctx]; exact hpre'
    · have hw' := hf.good S h.frame.safe h.world
      have hfr' := h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind
      have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
        rw [hf.same.precompiles, hf.same.ctx]; exact h.pre
      have hnp : ¬ P msg.currentTarget := fun hp => S.code _ hw' _ hp hc.code
      have hpar : (launchCreate m' msg).parents = m'.frame :: m.parents := by
        simp only [launchCreate, hf.same.parents]
      have hcallee : Halts (launchCreate m' msg) (fun mf o => Good (frameResult mf o).2.1) := by
        refine ih' _ (by rw [launchCreate_gasLeft]; omega) ⟨?_, ⟨hw', ?_, ?_⟩, ?_⟩
        · simp only [launchCreate, beginCreate]
          refine S.keep _ _ hw' fun p hp => ?_
          have h1 := keep_incrementNonce (a := msg.currentTarget) (S.code _ hw' p hp)
          exact h1.trans (keep_transferValue (by rw [h1.code]; exact S.code _ hw' p hp))
        · exact fun hd => hnp hd.1
        · exact fun _ => hnp
        · simp only [launchCreate]; exact hpre'
      refine halts_resume he hpar ⟨hf.same.ctx, hf.same.precompiles, hf.same.originalWorld,
        rfl, hf.same.msg, hf.same.code, hf.same.jumpDests, hf.same.kind, hf.same.snapshot⟩
        (by simp only [launchCreate]; rw [hpre']; exact precompilesOk_standard _) hcallee ?_
      intro mf o hsf hgood hgas
      refine ih' _ ?_ (Inv.of_resume hfr' hgood ?_)
      · rw [launchCreate_gasLeft] at hgas; omega
      · rw [hsf.precompiles, hsf.ctx]; exact hpre'

/-! ## Termination -/

/-- Nothing protected, everything `Good`. -/
theorem goodOk_none : GoodOk (fun _ => False) (fun _ => True) :=
  ⟨fun _ _ _ _ => trivial, fun _ _ _ hp => hp.elim, fun _ _ _ hp => hp.elim⟩

/-- **Every frame halts** (with standard precompiles): gas strictly decreases along the frame, and
every child it starts halts with less gas. -/
theorem halts_any {m : Machine} (hpre : m.precompiles = PrecompileImpl.standard m.ctx) :
    Halts m (fun _ _ => True) := by
  have h := halts_inv (P := fun _ => False) (Good := fun _ => True) goodOk_none
    (G := m.frame.gasLeft) (fun _ hd => hd.danger.1.elim) m (Nat.le_refl _)
    ⟨trivial, ⟨trivial, fun hd => hd.1.elim, fun _ hp => hp.elim⟩, hpre⟩
  exact h.mono fun _ _ _ _ => trivial

/-! ## Static frames -/

/-- **A static frame keeps `Good`**, with no frame summaries: it and all its descendants are static,
hence never dangerous, and a static frame starts no creation. -/
theorem halts_static (S : GoodOk P Good) :
    ∀ m, m.frame.msg.isStatic = true → Inv P Good m →
      Halts m (fun mf o => Good (frameResult mf o).2.1) := by
  suffices ∀ n m, m.frame.gasLeft = n → m.frame.msg.isStatic = true → Inv P Good m →
      Halts m (fun mf o => Good (frameResult mf o).2.1) from fun m hs h => this _ m rfl hs h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m hn hst h
    have ih' : ∀ m'', m''.frame.gasLeft < m.frame.gasLeft → m''.frame.msg.isStatic = true →
        Inv P Good m'' →
        Halts m'' (fun mf o => Good (frameResult mf o).2.1) :=
      fun m'' hlt hs hi => ih _ (hn ▸ hlt) m'' rfl hs hi
    rcases step_strict m with ⟨m', o, he, hf, -⟩ | ⟨m', he, hf, hs, -⟩ |
      ⟨m', req, he, hf, hc, hs, -⟩ | ⟨m', msg, he, hf, hc, hs, hst', -⟩
    · exact Halts.of_step he hf.same
        (frameResult_good S (h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind)
          (hf.good S h.frame.safe h.world) o)
    · refine Halts.of_steps (Steps.of_step he hf.same)
        (ih' m' hs (by rw [hf.same.msg]; exact hst) ?_)
      exact ⟨hf.good S h.frame.safe h.world,
        h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind,
        by rw [hf.same.precompiles, hf.same.ctx]; exact h.pre⟩
    · have hw' := hf.good S h.frame.safe h.world
      have hfr' := h.frame.of_same hf.same.msg hf.same.snapshot hf.same.kind
      have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
        rw [hf.same.precompiles, hf.same.ctx]; exact h.pre
      have hcst : req.msg.isStatic = true := by
        cases hq : req.msg.isStatic
        · have := (hc.nonstatic hq).1; rw [hst] at this; cases this
        · rfl
      have hst'' : m'.frame.msg.isStatic = true := by rw [hf.same.msg]; exact hst
      rcases launchCall_cases m' req with ⟨r, w, t, hl, hw, hr⟩ | hl <;> rw [hl] at he
      · have hr' := hr (by rw [hpre']; exact precompilesOk_standard _)
        have hsf : SameFrame m (resume { m' with world := w, transient := t } r) :=
          (hf.same.trans (show SameFrame m' { m' with world := w, transient := t } from
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)).trans (sameFrame_resume _ _)
        refine Halts.of_steps (Steps.of_step he hsf) (ih' _ ?_ hst'' ?_)
        · simp only [resume_gasLeft]; omega
        · refine ⟨?_, hfr'.of_same rfl rfl rfl, hpre'⟩
          rcases hw with rfl | rfl
          · exact S.transferValue hw' _
          · exact hw'
      · have hpar : (pushCall m' req).parents = m'.frame :: m.parents := by
          simp only [pushCall, hf.same.parents]
        have hcallee : Halts (pushCall m' req) (fun mf o => Good (frameResult mf o).2.1) := by
          refine ih' _ (by rw [pushCall_gasLeft]; omega) hcst ⟨S.transferValue hw' _, ⟨hw', ?_, ?_⟩,
            by simp only [pushCall]; exact hpre'⟩
          · intro hd; simp only [Danger, pushCall, Frame.init, hcst] at hd; cases hd.2
          · intro hk; cases hk
        refine halts_resume he hpar ⟨hf.same.ctx, hf.same.precompiles, hf.same.originalWorld,
          rfl, hf.same.msg, hf.same.code, hf.same.jumpDests, hf.same.kind, hf.same.snapshot⟩
          (by simp only [pushCall]; rw [hpre']; exact precompilesOk_standard _) hcallee ?_
        intro mf o hsf hgood hgas
        refine ih' _ ?_ hst'' (Inv.of_resume hfr' hgood ?_)
        · rw [pushCall_gasLeft] at hgas; omega
        · rw [hsf.precompiles, hsf.ctx]; exact hpre'
    · rw [hst] at hst'; cases hst'

/-! ## The stipend lemma -/

/-- **The stipend lemma.** A frame with at most `Gas.callStipend` (2300) gas, and every frame it
starts, leaves the world unchanged: at its end the world is the one it started with (only
transient storage, logs and return data may differ). -/
theorem halts_low :
    ∀ m, m.frame.gasLeft ≤ Gas.callStipend → m.precompiles = PrecompileImpl.standard m.ctx →
      Halts m (fun mf _ => mf.world = m.world) := by
  suffices ∀ n m, m.frame.gasLeft = n → n ≤ Gas.callStipend →
      m.precompiles = PrecompileImpl.standard m.ctx →
      Halts m (fun mf _ => mf.world = m.world) from fun m hg h => this _ m rfl hg h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m hn hlow hpre
    have ih' : ∀ m'', m''.frame.gasLeft < m.frame.gasLeft →
        m''.precompiles = PrecompileImpl.standard m''.ctx →
        Halts m'' (fun mf _ => mf.world = m''.world) :=
      fun m'' hlt hp => ih _ (hn ▸ hlt) m'' rfl (by omega) hp
    have hl : Low m := by simp only [Low]; omega
    rcases step_strict m with ⟨m', o, he, hf, hw⟩ | ⟨m', he, hf, hs, hw⟩ |
      ⟨m', req, he, hf, hc, hs, hw⟩ | ⟨m', msg, he, hf, hc, hs, -, hnl⟩
    · exact Halts.of_step he hf.same (hw hl)
    · have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
        rw [hf.same.precompiles, hf.same.ctx]; exact hpre
      exact Halts.of_steps (Steps.of_step he hf.same)
        ((ih' m' hs hpre').mono fun mf _ _ h => h.trans (hw hl))
    · obtain ⟨hw, hv⟩ := hw hl
      have hpre' : m'.precompiles = PrecompileImpl.standard m'.ctx := by
        rw [hf.same.precompiles, hf.same.ctx]; exact hpre
      have htv : transferValue m'.world req.msg = m'.world := by
        unfold transferValue
        rcases hv with hv | hv <;> simp [hv]
      rcases launchCall_cases m' req with ⟨r, w, t, hl', hw', hr⟩ | hl' <;> rw [hl'] at he
      · have hr' := hr (by rw [hpre']; exact precompilesOk_standard _)
        have hsf : SameFrame m (resume { m' with world := w, transient := t } r) :=
          (hf.same.trans (show SameFrame m' { m' with world := w, transient := t } from
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)).trans (sameFrame_resume _ _)
        have hww : w = m.world := by
          rcases hw' with rfl | rfl
          · rw [htv, hw]
          · exact hw
        refine Halts.of_steps (Steps.of_step he hsf)
          ((ih' (resume { m' with world := w, transient := t } r) ?_ hpre').mono
            fun mf _ _ h => h.trans (by simp only [resume_world]; exact hww))
        simp only [resume_gasLeft]; omega
      · have hpar : (pushCall m' req).parents = m'.frame :: m.parents := by
          simp only [pushCall, hf.same.parents]
        have hcallee := ih' (pushCall m' req) (by rw [pushCall_gasLeft]; omega)
          (by simp only [pushCall]; exact hpre')
        have hcallee' : Halts (pushCall m' req) (fun mf o => (frameResult mf o).2.1 = m'.world) := by
          refine hcallee.mono fun mf o hsf h => ?_
          rcases frameResult_world mf o with h' | ⟨hk, -⟩ | h'
          · rw [h', h]; simp only [pushCall, htv]
          · rw [hsf.kind] at hk; simp [pushCall, Frame.init] at hk
          · rw [h', hsf.snapshot]; rfl
        refine halts_resume he hpar ⟨hf.same.ctx, hf.same.precompiles, hf.same.originalWorld,
          rfl, hf.same.msg, hf.same.code, hf.same.jumpDests, hf.same.kind, hf.same.snapshot⟩
          (by simp only [pushCall]; rw [hpre']; exact precompilesOk_standard _) hcallee' ?_
        intro mf o hsf hres hgas
        refine (ih' _ ?_ ?_).mono fun mf' _ _ h => h.trans ?_
        · rw [pushCall_gasLeft] at hgas; omega
        · show mf.precompiles = PrecompileImpl.standard mf.ctx
          rw [hsf.precompiles, hsf.ctx]; exact hpre'
        · show (frameResult mf o).2.1 = m.world
          rw [hres, hw]
    · exact absurd hl hnl

end EvmLogic.Program.Reentrancy
