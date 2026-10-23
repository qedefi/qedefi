import EvmLogic.Program.Nested.Guard
import EvmLogic.Program.Nested.OwnG

/-!
# Guarded relays with doomed frames: effects that are rolled back

`Guard.lean` keeps the world invariant `G` on every world of the transaction. Some relays run
arbitrary code whose effects are always rolled back: Safe's `simulateAndRevert`
`DELEGATECALL`s any code in the Safe's own context and then reverts, whatever that code did.
Inside such a call any relay may act (the delegated code may call the ProxyAdmin as the Safe),
so `G` fails on the current world, but it still holds on the rollback snapshot of the frame
that will revert. This module extends the simulation of `Guard.lean` (whose statements are
unchanged) with **doomed frames** (`Doomed` of `OwnG.lean`: every own path reverts, whatever
the children do):

- a relay frame may reach a *doom point* (`Dm r m`), where it requests any call; it must then
  be doomed when it resumes (`GuardInvD.doom`);
- above a suspended doomed frame nothing is required of any frame, and `G` is only kept on the
  snapshots of the doomed frame and of the frames below it (`DoomAt`);
- when the doomed frame ends, by a revert or an exceptional halt, the world is its snapshot,
  so `G` holds again and the simulation of `Guard.lean` resumes.

Two refinements over `Guard.lean`: a resumed frame may assume `G` of the world it resumes in
and the kind of the child (so where its output was written), and every step of a relay frame
outside doomed regions may assume a **run predicate** `R` of the machine (a run-level
hypothesis, assumed of every machine the call reaches).

`processMessageCall_guardD`: from a world satisfying `G` (relays holding their code, idle
accounts idle), a top-level call whose reached machines satisfy `R` ends in a world satisfying
`G`.
-/

namespace EvmLogic.Program.Nested
open EvmLean EvmLean.Interpreter EvmLogic.AbsInt EvmLogic.GasMono

/-! ## Suspended frames -/

/-- The kind of the child frame an action starts (as `resume` reads it). -/
def kindOf : Action → FrameKind
  | .call req => .call req.retOffset req.retSize
  | _ => .create

/-- The suspended frame `p` (ancestors `ps`), whose child has kind `kd`, satisfies `Q` when it
resumes in a world satisfying `Pw`. -/
def ResumesTo (Pw : World → Prop) (Q : Machine → Prop) (ctx : Context) (pre : PrecompileImpl)
    (kd : FrameKind) (p : Frame) (ps : List Frame) : Prop :=
  ∀ (M : Machine) (res : ChildResult), M.frame = p → M.parents = ps → M.ctx = ctx → M.precompiles = pre → res.kind = kd →
    Pw M.world → Q (resume M res)

/-- Below the frame `c`: every suspended relay frame satisfies its invariant when it resumes
in a world satisfying `G`. -/
def SuspD (Rl : Address → Prop) (G : World → Prop) (J : Address → Machine → Prop)
    (ctx : Context) (pre : PrecompileImpl) : Frame → List Frame → Prop
  | _, [] => True
  | c, p :: ps => (Danger Rl p → ResumesTo G (J p.msg.currentTarget) ctx pre c.kind p ps) ∧
      SuspD Rl G J ctx pre p ps

/-- Below the frame `c` there is a suspended doomed frame `p`: doomed when it resumes, `G` on
its snapshot and below, and the frames below it as in `SuspD`. -/
def DoomAt (Rl : Address → Prop) (G : World → Prop) (J : Address → Machine → Prop)
    (ctx : Context) (pre : PrecompileImpl) : Frame → List Frame → Prop
  | _, [] => False
  | c, p :: ps => (ResumesTo (fun _ => True) Doomed ctx pre c.kind p ps ∧
      (∀ f ∈ p :: ps, G f.snapshot.1) ∧ SuspD Rl G J ctx pre p ps) ∨
      DoomAt Rl G J ctx pre p ps

variable {m : Machine} {Rl : Address → Prop} {C : Address → ByteArray} {X : Address → Prop}
  {G : World → Prop} {J : Address → Machine → Prop} {K : Context → Prop}
  {Iss : Address → Machine → Message → Prop} {R : Machine → Prop}
  {Dm : Address → Machine → Prop}

theorem suspD_congr {ctx : Context} {pre : PrecompileImpl} {c c' : Frame} (hk : c'.kind = c.kind) :
    ∀ {ps : List Frame}, SuspD Rl G J ctx pre c ps → SuspD Rl G J ctx pre c' ps
  | [], _ => trivial
  | _ :: _, h => ⟨by rw [hk]; exact h.1, h.2⟩

theorem doomAt_congr {ctx : Context} {pre : PrecompileImpl} {c c' : Frame} (hk : c'.kind = c.kind) :
    ∀ {ps : List Frame}, DoomAt Rl G J ctx pre c ps → DoomAt Rl G J ctx pre c' ps
  | [], h => h
  | _ :: _, h => by
    rcases h with h | h
    · exact .inl (by rw [hk]; exact h)
    · exact .inr h

/-! ## The simulation invariant -/

/-- What every machine of the call satisfies, doomed regions included. -/
structure SandCommon (K : Context → Prop) (Rl : Address → Prop) (C : Address → ByteArray)
    (X : Address → Prop) (m : Machine) : Prop where
  world : RelayCode Rl C m.world
  snapshots : ∀ f ∈ m.frame :: m.parents, RelayCode Rl C f.snapshot.1
  create : ∀ f ∈ m.frame :: m.parents, f.kind = .create → ¬ Rl f.msg.currentTarget
  pre : m.precompiles = PrecompileImpl.standard m.ctx
  idle : AllWorlds (IdleW X) m
  callers : ∀ f ∈ m.frame :: m.parents, ¬ X f.msg.caller
  idleRun : ∀ f ∈ m.frame :: m.parents, X f.msg.currentTarget → f.code.size = 0
  createIdle : ∀ f ∈ m.frame :: m.parents, f.kind = .create → ¬ X f.msg.currentTarget
  ctx : K m.ctx

/-- Outside doomed regions: `G` on the world and every snapshot, the executing relay frame's
invariant, the suspended relay frames'. -/
def NormalD (Rl : Address → Prop) (G : World → Prop) (J : Address → Machine → Prop)
    (m : Machine) : Prop :=
  G m.world ∧ (∀ f ∈ m.frame :: m.parents, G f.snapshot.1) ∧
    (Danger Rl m.frame → J m.frame.msg.currentTarget m) ∧
    SuspD Rl G J m.ctx m.precompiles m.frame m.parents

/-- The executing frame is doomed: `G` on every snapshot only. -/
def DoomCur (Rl : Address → Prop) (G : World → Prop) (J : Address → Machine → Prop)
    (m : Machine) : Prop :=
  (∀ f ∈ m.frame :: m.parents, G f.snapshot.1) ∧ Doomed m ∧
    SuspD Rl G J m.ctx m.precompiles m.frame m.parents

/-- **The simulation invariant** with doomed frames. -/
structure SandInv (K : Context → Prop) (Rl : Address → Prop) (C : Address → ByteArray)
    (X : Address → Prop) (G : World → Prop) (J : Address → Machine → Prop) (m : Machine) :
    Prop where
  common : SandCommon K Rl C X m
  mode : NormalD Rl G J m ∨ DoomCur Rl G J m ∨ DoomAt Rl G J m.ctx m.precompiles m.frame m.parents

/-! ## The relay obligation -/

/-- **The frame obligation of relay `r`** with doom points `Dm` and run predicate `R`: as
`GuardInvK`, with every step assuming `R` and idleness; a request at a doom point is free, and
the frame must then be doomed when it resumes. -/
structure GuardInvD (K : Context → Prop) (Rl : Address → Prop) (C : Address → ByteArray)
    (X : Address → Prop) (G : World → Prop) (R : Machine → Prop)
    (Iss : Address → Machine → Message → Prop) (Dm : Machine → Prop) (r : Address)
    (J : Machine → Prop) : Prop where
  start : ∀ m, GuardStartK K Rl C X G Iss r m → J m
  issue : ∀ m c, J m → G m.world → R m → RelayCode Rl C m.world → IdleW X m.world →
    Requests m c → ¬ Dm m → Iss r m c
  good : ∀ m b a m', J m → G m.world → R m → RelayCode Rl C m.world → IdleW X m.world →
    m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m') → G m'.world
  next : ∀ m b m', J m → G m.world → R m → RelayCode Rl C m.world → IdleW X m.world →
    m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m') → J m'
  /-- After a requested child, in a world satisfying `G`, the child of the kind requested. -/
  resumeJ : ∀ m b a m', J m → G m.world → R m → RelayCode Rl C m.world → IdleW X m.world →
    m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m') → ¬ Dm m →
    ((∃ req, a = .call req) ∨ ∃ msg, a = .create msg) →
    ∀ (M : Machine) (res : ChildResult), M.frame = m'.frame → M.parents = m.parents → M.ctx = m.ctx →
      M.precompiles = m.precompiles → res.kind = kindOf a → G M.world →
      (∀ req, a = .call req → precompileOf m'.precompiles req.msg ≠ none →
        resume M res = launchCall m' req) → J (resume M res)
  /-- At a doom point the frame is doomed when it resumes, whatever the child did. -/
  doom : ∀ m b req m', J m → G m.world → R m → RelayCode Rl C m.world → IdleW X m.world →
    m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m') → Dm m →
    ∀ (M : Machine) (res : ChildResult), M.frame = m'.frame → M.parents = m.parents → M.ctx = m.ctx →
      M.precompiles = m.precompiles → res.kind = .call req.retOffset req.retSize →
      Doomed (resume M res)
  doomCreate : ∀ m b msg m', J m → G m.world → R m → RelayCode Rl C m.world → IdleW X m.world →
    m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.create msg, m') → Dm m → False

/-- A relay without doom points: the obligation of `Guard.lean` gives this one. -/
theorem GuardInvK.toD {Jr : Machine → Prop} {r : Address}
    (h : GuardInvK K Rl C X G Iss r Jr) : GuardInvD K Rl C X G R Iss (fun _ => False) r Jr where
  start := h.start
  issue m c hJ hg _ hw _ hr _ := h.issue m c hJ hg hw hr
  good m b a m' hJ hg _ hw _ hb he := h.good m b a m' hJ hg hw hb he
  next m b m' hJ hg _ hw _ hb he := h.next m b m' hJ hg hw hb he
  resumeJ m b a m' hJ hg _ hw _ hb he _ ha M res hM hMp hMc hMpre _ _ hpre :=
    h.resume m b a m' hJ hg hw hb he ha M res hM hMp hMc hMpre hpre
  doom _ _ _ _ _ _ _ _ _ _ _ hd := hd.elim
  doomCreate _ _ _ _ _ _ _ _ _ _ _ hd := hd

/-! ## Auxiliary facts -/

/-- A frame ends successfully only at a `STOP`/`RETURN` or past the end of its code. -/
theorem exitOf_success {m mf : Machine} {out : ByteArray}
    (h : exitOf m = some (mf, .success out)) :
    m.frame.code[m.frame.pc]? = none ∨ ∃ b, m.frame.code[m.frame.pc]? = some b ∧
      (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.stop out, mf) := by
  unfold exitOf at h
  by_cases hpc : m.frame.pc < m.frame.code.size
  · simp only [hpc, ↓reduceDIte] at h
    right
    refine ⟨_, getElem?_pos m.frame.code m.frame.pc hpc, ?_⟩
    cases he : (exec (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc])).run m with
    | error e => rw [he] at h; cases h
    | ok p =>
      obtain ⟨a, m'⟩ := p
      rw [he] at h
      cases a <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, Outcome.success.injEq]
        at h
      · rw [h.1, h.2]
      all_goals exact absurd h (by simp)
  · left; exact getElem?_of_size_le (Nat.le_of_not_lt hpc)

/-- A doomed frame that ends leaves its snapshot. -/
theorem doomed_exit {m mf : Machine} {o : Outcome} (hd : Doomed m) (hx : exitOf m = some (mf, o))
    (hsn : mf.frame.snapshot = m.frame.snapshot) :
    (Program.frameResult mf o).2.1 = m.frame.snapshot.1 := by
  cases o with
  | success out =>
    rcases exitOf_success hx with hn | ⟨b, hb, he⟩
    · exact (hd.end_ trivial hn).elim
    · exact (hd.stop trivial hb he).elim
  | revert out => simp [Program.frameResult, hsn]
  | halt e => simp [Program.frameResult, hsn]

theorem not_idle_of_instrD (h : SandCommon K Rl C X m) {b : UInt8}
    (hb : m.frame.code[m.frame.pc]? = some b) : ¬ X m.frame.msg.currentTarget := fun hx => by
  have h0 := h.idleRun _ List.mem_cons_self hx
  rw [getElem?_of_size_le (by omega)] at hb
  cases hb

/-! ## Common facts across steps -/

/-- The common facts for a machine whose frames are those of `m`, the executing one updated. -/
theorem sandCommon_same (h : SandCommon K Rl C X m) {m' : Machine}
    (hw : RelayCode Rl C m'.world) (hi : IdleW X m'.world) (hmsg : m'.frame.msg = m.frame.msg)
    (hk : m'.frame.kind = m.frame.kind) (hs : m'.frame.snapshot = m.frame.snapshot)
    (hcd : m'.frame.code = m.frame.code) (hp : m'.parents = m.parents) (hc : m'.ctx = m.ctx)
    (hpre : m'.precompiles = m.precompiles) : SandCommon K Rl C X m' := by
  have hstack : ∀ f ∈ m'.frame :: m'.parents, f = m'.frame ∨ f ∈ m.parents := by
    intro f hf
    rw [hp] at hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact .inl rfl
    · exact .inr hf
  refine ⟨hw, ?_, ?_, by rw [hpre, hc]; exact h.pre, ⟨hi, ?_⟩, ?_, ?_, ?_, by rw [hc]; exact h.ctx⟩
  · intro f hf
    rcases hstack f hf with rfl | hf
    · rw [hs]; exact h.snapshots _ List.mem_cons_self
    · exact h.snapshots f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases hstack f hf with rfl | hf
    · rw [hk, hmsg]; exact h.create _ List.mem_cons_self
    · exact h.create f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases hstack f hf with rfl | hf
    · rw [hs]; exact h.idle.2 _ List.mem_cons_self
    · exact h.idle.2 f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases hstack f hf with rfl | hf
    · rw [hmsg]; exact h.callers _ List.mem_cons_self
    · exact h.callers f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases hstack f hf with rfl | hf
    · rw [hmsg, hcd]; exact h.idleRun _ List.mem_cons_self
    · exact h.idleRun f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases hstack f hf with rfl | hf
    · rw [hk, hmsg]; exact h.createIdle _ List.mem_cons_self
    · exact h.createIdle f (List.mem_cons_of_mem _ hf)

/-- The common facts for a pushed frame `mc.frame` above the suspended `m'.frame`. -/
theorem sandCommon_push (h : SandCommon K Rl C X m) {m' mc : Machine} (hif : InstrFrame m m')
    (hw : RelayCode Rl C mc.world) (hsnap : RelayCode Rl C mc.frame.snapshot.1)
    (hcreate : mc.frame.kind = .create → ¬ Rl mc.frame.msg.currentTarget)
    (hpar : mc.parents = m'.frame :: m.parents) (hc : mc.ctx = m.ctx)
    (hpre : mc.precompiles = m.precompiles) (hi : IdleW X mc.world)
    (his : IdleW X mc.frame.snapshot.1) (hcl : ¬ X mc.frame.msg.caller)
    (hrun : X mc.frame.msg.currentTarget → mc.frame.code.size = 0)
    (hci : mc.frame.kind = .create → ¬ X mc.frame.msg.currentTarget) :
    SandCommon K Rl C X mc := by
  have hstack : ∀ f ∈ mc.frame :: mc.parents, f = mc.frame ∨ f = m'.frame ∨ f ∈ m.parents := by
    intro f hf
    rw [hpar] at hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact .inl rfl
    rcases List.mem_cons.1 hf with rfl | hf
    · exact .inr (.inl rfl)
    · exact .inr (.inr hf)
  refine ⟨hw, ?_, ?_, by rw [hpre, hc]; exact h.pre, ⟨hi, ?_⟩, ?_, ?_, ?_, by rw [hc]; exact h.ctx⟩
  · intro f hf
    rcases hstack f hf with rfl | rfl | hf
    · exact hsnap
    · rw [hif.same.snapshot]; exact h.snapshots _ List.mem_cons_self
    · exact h.snapshots f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases hstack f hf with rfl | rfl | hf
    · exact hcreate
    · rw [hif.same.kind, hif.same.msg]; exact h.create _ List.mem_cons_self
    · exact h.create f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases hstack f hf with rfl | rfl | hf
    · exact his
    · rw [hif.same.snapshot]; exact h.idle.2 _ List.mem_cons_self
    · exact h.idle.2 f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases hstack f hf with rfl | rfl | hf
    · exact hcl
    · rw [hif.same.msg]; exact h.callers _ List.mem_cons_self
    · exact h.callers f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases hstack f hf with rfl | rfl | hf
    · exact hrun
    · rw [hif.same.msg, hif.same.code]; exact h.idleRun _ List.mem_cons_self
    · exact h.idleRun f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases hstack f hf with rfl | rfl | hf
    · exact hci
    · rw [hif.same.kind, hif.same.msg]; exact h.createIdle _ List.mem_cons_self
    · exact h.createIdle f (List.mem_cons_of_mem _ hf)

/-- The common facts after the executing frame ends and its parent `p` resumes. -/
theorem sandCommon_pop (h : SandCommon K Rl C X m) {mf : Machine} {p : Frame} {ps : List Frame}
    (o : Outcome) (hif : InstrFrame m mf) (hpar : m.parents = p :: ps)
    (hw : RelayCode Rl C (Program.frameResult mf o).2.1)
    (hi : IdleW X (Program.frameResult mf o).2.1) :
    SandCommon K Rl C X (resumeAfter p ps mf o) := by
  let M : Machine :=
    { mf with frame := p, parents := ps, world := (Program.frameResult mf o).2.1,
              transient := (Program.frameResult mf o).2.2 }
  have hsf := sameFrame_resume M (Program.frameResult mf o).1
  have hmem : ∀ f ∈ (resume M (Program.frameResult mf o).1).frame ::
      (resume M (Program.frameResult mf o).1).parents,
      f = (resume M (Program.frameResult mf o).1).frame ∨ f ∈ ps := by
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact .inl rfl
    · exact .inr (by rw [hsf.parents] at hf; exact hf)
  have hps : ∀ f ∈ p :: ps, f ∈ m.frame :: m.parents := fun f hf => by
    rw [hpar]; exact List.mem_cons_of_mem _ hf
  show SandCommon K Rl C X (resume M (Program.frameResult mf o).1)
  refine ⟨hw, ?_, ?_, ?_, ⟨hi, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rcases hmem f hf with rfl | hf
    · rw [hsf.snapshot]; exact h.snapshots p (hps p List.mem_cons_self)
    · exact h.snapshots f (hps f (List.mem_cons_of_mem _ hf))
  · intro f hf
    rcases hmem f hf with rfl | hf
    · rw [hsf.kind, hsf.msg]; exact h.create p (hps p List.mem_cons_self)
    · exact h.create f (hps f (List.mem_cons_of_mem _ hf))
  · show (resume M _).precompiles = PrecompileImpl.standard (resume M _).ctx
    rw [hsf.ctx, hsf.precompiles]
    show mf.precompiles = PrecompileImpl.standard mf.ctx
    rw [hif.same.ctx, hif.same.precompiles]; exact h.pre
  · intro f hf
    rcases hmem f hf with rfl | hf
    · rw [hsf.snapshot]; exact h.idle.2 p (hps p List.mem_cons_self)
    · exact h.idle.2 f (hps f (List.mem_cons_of_mem _ hf))
  · intro f hf
    rcases hmem f hf with rfl | hf
    · rw [hsf.msg]; exact h.callers p (hps p List.mem_cons_self)
    · exact h.callers f (hps f (List.mem_cons_of_mem _ hf))
  · intro f hf
    rcases hmem f hf with rfl | hf
    · rw [hsf.msg, hsf.code]; exact h.idleRun p (hps p List.mem_cons_self)
    · exact h.idleRun f (hps f (List.mem_cons_of_mem _ hf))
  · intro f hf
    rcases hmem f hf with rfl | hf
    · rw [hsf.kind, hsf.msg]; exact h.createIdle p (hps p List.mem_cons_self)
    · exact h.createIdle f (hps f (List.mem_cons_of_mem _ hf))
  · show K (resume M _).ctx
    rw [hsf.ctx]; show K mf.ctx; rw [hif.same.ctx]; exact h.ctx

/-! ## One step -/

/-- **One step keeps the simulation invariant**, given the run predicate of the machine. -/
theorem sandInv_step (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvD K Rl C X G R Iss (Dm r) r (J r)) {m m' : Machine}
    (h : SandInv K Rl C X G J m) (hR : R m) (hst : step m = .running m') :
    SandInv K Rl C X G J m' := by
  have S := goodC_ok hC hG
  have hcm := h.common
  cases hx : exitOf m with
  | some p =>
    obtain ⟨mf, o⟩ := p
    obtain ⟨hst', hif⟩ := step_of_exitOf hx
    have hmw : RelayCode Rl C mf.world ∧ IdleW X mf.world := by
      rcases exitOf_cases hx with rfl | ⟨b, a, -, he⟩
      · exact ⟨hcm.world, hcm.idle.1⟩
      · exact ⟨hcm.world.congr ((exec_code _ m).of_run he),
          hcm.idle.1.congr ((exec_code _ m).of_run he) ((exec_nonce _ m).of_run he)⟩
    rw [hst', finishFrame_eq] at hst
    split at hst
    · cases hst
    rename_i p ps hp
    cases hst
    have hpar : m.parents = p :: ps := hif.same.parents ▸ hp
    have hcr : mf.frame.kind = .create → ¬ Rl mf.frame.msg.currentTarget := by
      rw [hif.same.kind, hif.same.msg]; exact hcm.create _ List.mem_cons_self
    have hci : mf.frame.kind = .create → ¬ X mf.frame.msg.currentTarget := by
      rw [hif.same.kind, hif.same.msg]; exact hcm.createIdle _ List.mem_cons_self
    have hsn : mf.frame.snapshot = m.frame.snapshot := hif.same.snapshot
    have hir : IdleW X (Program.frameResult mf o).2.1 :=
      frameResult_P o hmw.2 (hsn ▸ hcm.idle.2 _ List.mem_cons_self) fun _ hk =>
        hmw.2.setCode (hci hk)
    have hwr : RelayCode Rl C (Program.frameResult mf o).2.1 :=
      frameResult_P o hmw.1 (hsn ▸ hcm.snapshots _ List.mem_cons_self) fun out hk r hr => by
        rw [code_setCode_ne fun he => hcr hk (by rw [he]; exact hr)]; exact hmw.1 r hr
    have hcom := sandCommon_pop hcm o hif hpar hwr hir
    let M : Machine :=
      { mf with frame := p, parents := ps, world := (Program.frameResult mf o).2.1,
                transient := (Program.frameResult mf o).2.2 }
    have hsf := sameFrame_resume M (Program.frameResult mf o).1
    have hkind : (Program.frameResult mf o).1.kind = m.frame.kind := by
      rw [← hif.same.kind]; cases o <;> simp only [Program.frameResult] <;> split <;> try rfl
      all_goals (try split) <;> rfl
    -- The resumed parent after a frame that leaves a world satisfying `G`.
    have hnormal : G (Program.frameResult mf o).2.1 → (∀ f ∈ p :: ps, G f.snapshot.1) →
        SuspD Rl G J m.ctx m.precompiles m.frame (p :: ps) →
        SandInv K Rl C X G J (resumeAfter p ps mf o) := by
      intro hg hgs hsusp
      refine ⟨hcom, .inl ⟨hg, ?_, ?_, ?_⟩⟩
      · intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · show G (resume M _).frame.snapshot.1
          rw [hsf.snapshot]; exact hgs p List.mem_cons_self
        · exact hgs f (List.mem_cons_of_mem _ (by simpa only [resumeAfter, resume_parents] using hf))
      · intro hd
        show J (resume M _).frame.msg.currentTarget (resume M _)
        rw [hsf.msg]
        exact hsusp.1 ((danger_congr hsf.msg).1 hd) _ _ rfl rfl hif.same.ctx
          hif.same.precompiles hkind hg
      · show SuspD Rl G J (resume M _).ctx (resume M _).precompiles (resume M _).frame
          (resume M _).parents
        rw [hsf.parents, hsf.ctx, hsf.precompiles]
        refine suspD_congr (c := p) hsf.kind ?_
        show SuspD Rl G J mf.ctx mf.precompiles p ps
        rw [hif.same.ctx, hif.same.precompiles]; exact hsusp.2
    rcases h.mode with ⟨hg, hgs, hcur, hsusp⟩ | ⟨hgs, hdm, hsusp⟩ | hda
    · -- A frame outside doomed regions ends.
      have hgmf : G mf.world := by
        rcases exitOf_cases hx with rfl | ⟨b, a, hb, he⟩
        · exact hg
        · by_cases hd : Danger Rl m.frame
          · exact (hJ _ hd.1).good m b a mf (hcur hd) hg hR hcm.world hcm.idle.1 hb he
          · exact (((exec_frame _ m).of_run he).1.good (goodC_ok hC hG) hd ⟨hg, hcm.world⟩).1
      have hgr : G (Program.frameResult mf o).2.1 :=
        frameResult_P o hgmf (hsn ▸ hgs _ List.mem_cons_self) fun out hk =>
          hG _ _ hgmf fun r hr => keep_setCode fun he => hcr hk (he ▸ hr)
      rw [hpar] at hgs hsusp
      exact hnormal hgr (fun f hf => hgs f (List.mem_cons_of_mem _ hf)) hsusp
    · -- The doomed frame ends: its snapshot is restored.
      have hgr : G (Program.frameResult mf o).2.1 := by
        rw [doomed_exit hdm hx hsn]; exact hgs _ List.mem_cons_self
      rw [hpar] at hgs hsusp
      exact hnormal hgr (fun f hf => hgs f (List.mem_cons_of_mem _ hf)) hsusp
    · -- A frame above a doomed frame ends.
      rw [hpar] at hda
      rcases hda with ⟨hres, hgs, hsusp⟩ | hda
      · refine ⟨hcom, .inr (.inl ⟨?_, ?_, ?_⟩)⟩
        · intro f hf
          rcases List.mem_cons.1 hf with rfl | hf
          · show G (resume M _).frame.snapshot.1
            rw [hsf.snapshot]; exact hgs p List.mem_cons_self
          · exact hgs f (List.mem_cons_of_mem _ (by simpa only [resumeAfter, resume_parents] using hf))
        · exact hres _ _ rfl rfl hif.same.ctx hif.same.precompiles hkind trivial
        · show SuspD Rl G J (resume M _).ctx (resume M _).precompiles (resume M _).frame
            (resume M _).parents
          rw [hsf.parents, hsf.ctx, hsf.precompiles]
          refine suspD_congr (c := p) hsf.kind ?_
          show SuspD Rl G J mf.ctx mf.precompiles p ps
          rw [hif.same.ctx, hif.same.precompiles]; exact hsusp
      · refine ⟨hcom, .inr (.inr ?_)⟩
        show DoomAt Rl G J (resume M _).ctx (resume M _).precompiles (resume M _).frame
          (resume M _).parents
        rw [hsf.parents, hsf.ctx, hsf.precompiles]
        refine doomAt_congr (c := p) hsf.kind ?_
        show DoomAt Rl G J mf.ctx mf.precompiles p ps
        rw [hif.same.ctx, hif.same.precompiles]; exact hda
  | none =>
    obtain ⟨b, hb, a, m₁, he, hcase⟩ := step_exec hx hst
    have hpost := (exec_frame _ m).of_run he
    have hif : InstrFrame m m₁ := hpost.1
    have hcode : SameCode m.world m₁.world := (exec_code _ m).of_run he
    have hw₁ : RelayCode Rl C m₁.world := hcm.world.congr hcode
    have hi₁ : IdleW X m₁.world := hcm.idle.1.congr hcode ((exec_nonce _ m).of_run he)
    have hnx : ¬ X m.frame.msg.currentTarget := not_idle_of_instrD hcm hb
    -- `G` after the instruction, outside doomed regions.
    have hg₁ : NormalD Rl G J m → G m₁.world := by
      rintro ⟨hg, -, hcur, -⟩
      by_cases hd : Danger Rl m.frame
      · exact (hJ _ hd.1).good m b a m₁ (hcur hd) hg hR hcm.world hcm.idle.1 hb he
      · exact (hif.good (goodC_ok hC hG) hd ⟨hg, hcm.world⟩).1
    -- The mode after a step that keeps the frame stack (`m'.frame` the executing one updated).
    have hsame : ∀ {m' : Machine}, m'.frame.kind = m.frame.kind →
        m'.frame.snapshot = m.frame.snapshot → m'.parents = m.parents → m'.ctx = m.ctx →
        m'.precompiles = m.precompiles →
        ((∀ f ∈ m.frame :: m.parents, G f.snapshot.1) → (G m'.world ∧
          (Danger Rl m'.frame → J m'.frame.msg.currentTarget m')) ∨ Doomed m') →
        (NormalD Rl G J m ∨ DoomCur Rl G J m) →
        NormalD Rl G J m' ∨ DoomCur Rl G J m' := by
      intro m' hk hs hp hc hpre hcase' hmode
      have hgs : ∀ f ∈ m.frame :: m.parents, G f.snapshot.1 := by
        rcases hmode with ⟨-, hgs, -⟩ | ⟨hgs, -⟩ <;> exact hgs
      have hsusp : SuspD Rl G J m.ctx m.precompiles m.frame m.parents := by
        rcases hmode with ⟨-, -, -, hs⟩ | ⟨-, -, hs⟩ <;> exact hs
      have hgs' : ∀ f ∈ m'.frame :: m'.parents, G f.snapshot.1 := by
        intro f hf
        rw [hp] at hf
        rcases List.mem_cons.1 hf with rfl | hf
        · rw [hs]; exact hgs _ List.mem_cons_self
        · exact hgs f (List.mem_cons_of_mem _ hf)
      have hsusp' : SuspD Rl G J m'.ctx m'.precompiles m'.frame m'.parents := by
        rw [hp, hc, hpre]; exact suspD_congr hk hsusp
      rcases hcase' hgs with ⟨hg', hcur'⟩ | hd'
      · exact .inl ⟨hg', hgs', hcur', hsusp'⟩
      · exact .inr ⟨hgs', hd', hsusp'⟩
    rcases hcase with ⟨rfl, rfl⟩ | ⟨req, rfl, rfl⟩ | ⟨msg, rfl, rfl⟩
    · -- An instruction continuing the frame.
      have hcom := sandCommon_same hcm hw₁ hi₁ hif.same.msg hif.same.kind hif.same.snapshot
        hif.same.code hif.same.parents hif.same.ctx hif.same.precompiles
      refine ⟨hcom, ?_⟩
      rcases h.mode with hn | hdc | hda
      · refine (hsame hif.same.kind hif.same.snapshot hif.same.parents hif.same.ctx
          hif.same.precompiles (fun _ => .inl ⟨hg₁ hn, fun hd => ?_⟩) (.inl hn)).elim .inl
          (fun h => .inr (.inl h))
        have hd' := (danger_congr hif.same.msg).1 hd
        rw [hif.same.msg]
        exact (hJ _ hd'.1).next m b m' (hn.2.2.1 hd') hn.1 hR hcm.world hcm.idle.1 hb he
      · refine (hsame hif.same.kind hif.same.snapshot hif.same.parents hif.same.ctx
          hif.same.precompiles (fun _ => .inr (hdc.2.1.next trivial hb he)) (.inr hdc)).elim .inl
          (fun h => .inr (.inl h))
      · refine .inr (.inr ?_)
        rw [hif.same.parents, hif.same.ctx, hif.same.precompiles]
        exact doomAt_congr hif.same.kind hda
    · -- A call.
      have hcall : CallOk m m₁ req := hpost.2
      have hids : CallIds m req := (exec_ids _ m).of_run he req rfl
      have htgt : CallTarget m req := (exec_target _ m).of_run he req rfl
      have hreq : Requests m req.msg := ⟨b, _, m₁, hb, he, .inl ⟨req, rfl, rfl⟩⟩
      by_cases hpc : precompileOf m₁.precompiles req.msg = none
      · -- A child frame is pushed.
        rw [launchCall_none hpc]
        have hcl : ¬ X req.msg.caller := by
          rcases hids.1 with he' | ⟨he', -⟩ <;> rw [he']
          · exact hnx
          · exact hcm.callers _ List.mem_cons_self
        have hrun : X req.msg.currentTarget → req.msg.code.size = 0 := by
          intro hxt
          rcases hids.2 with he' | ⟨t, ht, he'⟩
          · exact absurd (he' ▸ hxt) hnx
          · obtain ⟨t', ht', hct⟩ := htgt
            rw [ht] at ht'
            cases ht'
            have h0 := (hcm.idle.1 _ hxt).1
            rw [he'] at h0
            have hnd : delegatedAddress? (m.world.code (Word.toAddress t)) = none := by
              cases hdl : delegatedAddress? (m.world.code (Word.toAddress t)) with
              | none => rfl
              | some d => exact absurd h0 (delegated_size hdl)
            rw [(hct (.inr hnd)).2.1]; exact h0
        have hcom := sandCommon_push (mc := pushCall m₁ req) hcm hif
          (hw₁.congr (pushCall_code _ _)) hw₁ (fun hk => by cases hk)
          (by simp only [pushCall]; rw [hif.same.parents]) hif.same.ctx hif.same.precompiles
          (hi₁.congr (code_transferValue _ _) (nonce_transferValue _ _)) hi₁ hcl hrun
          (fun hk => by cases hk)
        have hpk : (pushCall m₁ req).frame.kind = .call req.retOffset req.retSize := rfl
        have hpp : (pushCall m₁ req).parents = m₁.frame :: m.parents := by
          simp only [pushCall]; rw [hif.same.parents]
        refine ⟨hcom, ?_⟩
        rcases h.mode with hn | hdc | hda
        · obtain ⟨hg, hgs, hcur, hsusp⟩ := hn
          have hg₁' := hg₁ ⟨hg, hgs, hcur, hsusp⟩
          by_cases hdoom : Danger Rl m.frame ∧ Dm m.frame.msg.currentTarget m
          · -- A doom point: the frame is doomed when it resumes.
            refine .inr (.inr ?_)
            show DoomAt Rl G J (pushCall m₁ req).ctx (pushCall m₁ req).precompiles
              (pushCall m₁ req).frame (pushCall m₁ req).parents
            rw [hpp]
            refine .inl ⟨?_, ?_, ?_⟩
            · intro M res hM hMp hMc hMpre hk _
              rw [hpk] at hk
              exact (hJ _ hdoom.1.1).doom m b req m₁ (hcur hdoom.1) hg hR hcm.world hcm.idle.1
                hb he hdoom.2 M res hM hMp (hMc.trans hif.same.ctx) (hMpre.trans hif.same.precompiles) hk
            · intro f hf
              rcases List.mem_cons.1 hf with rfl | hf
              · rw [hif.same.snapshot]; exact hgs _ List.mem_cons_self
              · exact hgs f (List.mem_cons_of_mem _ hf)
            · show SuspD Rl G J m₁.ctx m₁.precompiles m₁.frame m.parents
              rw [hif.same.ctx, hif.same.precompiles]; exact suspD_congr hif.same.kind hsusp
          · -- A request under `Iss`, or from a frame that is no relay frame.
            have hiss : Danger Rl m.frame → Iss m.frame.msg.currentTarget m req.msg := fun hd =>
              (hJ _ hd.1).issue m req.msg (hcur hd) hg hR hcm.world hcm.idle.1 hreq
                fun hdm => hdoom ⟨hd, hdm⟩
            refine .inl ⟨(S.transferValue ⟨hg₁', hw₁⟩ req.msg).1, ?_, ?_, ?_⟩
            · intro f hf
              rw [hpp] at hf
              rcases List.mem_cons.1 hf with rfl | hf
              · exact hg₁'
              rcases List.mem_cons.1 hf with rfl | hf
              · rw [hif.same.snapshot]; exact hgs _ List.mem_cons_self
              · exact hgs f (List.mem_cons_of_mem _ hf)
            · intro hd
              show J req.msg.currentTarget (pushCall m₁ req)
              have hrel : Rl req.msg.currentTarget := hd.1
              have hst' : req.msg.isStatic = false := hd.2
              obtain ⟨hps, hcur'⟩ := hcall.nonstatic hst'
              refine (hJ _ hrel).start _ ⟨⟨⟨_, _, rfl⟩, rfl, hst', ?_,
                hw₁.congr (pushCall_code _ _), ?_⟩, (S.transferValue ⟨hg₁', hw₁⟩ req.msg).1, hg₁',
                fun r hr => keep_transferValue (S.code _ ⟨hg₁', hw₁⟩ r hr),
                hi₁.congr (code_transferValue _ _) (nonce_transferValue _ _), hcl,
                .inr ⟨m, hif.same.ctx.symm, hps, hreq, hids.1, fun hr => hiss ⟨hr, hps⟩⟩,
                by show K m₁.ctx; rw [hif.same.ctx]; exact hcm.ctx⟩
              · by_cases heq : req.msg.currentTarget = m.frame.msg.currentTarget
                · right
                  refine ⟨m, hif.same.ctx.symm, heq.symm, hps, hreq, ?_⟩
                  show Iss req.msg.currentTarget m req.msg
                  rw [heq]; exact hiss ⟨heq ▸ hrel, hps⟩
                · left
                  obtain ⟨-, hc⟩ := hcur'.resolve_left heq
                  have hwr := hcm.world _ hrel
                  obtain ⟨hc1, hc2, -⟩ := hc (by rw [hwr]; exact hC.deleg _ hrel)
                  exact ⟨by show req.msg.code = _; rw [hc1, hwr], hc2⟩
              · show m₁.precompiles = PrecompileImpl.standard m₁.ctx
                rw [hif.same.ctx, hif.same.precompiles]; exact hcm.pre
            · show SuspD Rl G J (pushCall m₁ req).ctx (pushCall m₁ req).precompiles
                (pushCall m₁ req).frame (pushCall m₁ req).parents
              rw [hpp]
              refine ⟨fun hd M res hM hMp hMc hMpre hk hgM => ?_, ?_⟩
              · have hd' := (danger_congr hif.same.msg).1 hd
                rw [hif.same.msg]
                exact (hJ _ hd'.1).resumeJ m b _ m₁ (hcur hd') hg hR hcm.world hcm.idle.1 hb he
                  (fun hdm => hdoom ⟨hd', hdm⟩) (.inl ⟨req, rfl⟩) M res hM
                  hMp (hMc.trans hif.same.ctx) (hMpre.trans hif.same.precompiles) (by rw [hk]; rfl) hgM
                  fun req' h' hpre' => by cases h'; exact absurd hpc hpre'
              · show SuspD Rl G J m₁.ctx m₁.precompiles m₁.frame m.parents
                rw [hif.same.ctx, hif.same.precompiles]; exact suspD_congr hif.same.kind hsusp
        · -- A doomed frame calls: its own invariant covers any child.
          obtain ⟨hgs, hdm, hsusp⟩ := hdc
          refine .inr (.inr ?_)
          show DoomAt Rl G J (pushCall m₁ req).ctx (pushCall m₁ req).precompiles
            (pushCall m₁ req).frame (pushCall m₁ req).parents
          rw [hpp]
          refine .inl ⟨?_, ?_, ?_⟩
          · intro M res hM hMp hMc hMpre hk _
            exact hdm.real trivial hb he id hpc res hM hMp (hMc.trans hif.same.ctx)
              (hMpre.trans hif.same.precompiles) hk trivial
          · intro f hf
            rcases List.mem_cons.1 hf with rfl | hf
            · rw [hif.same.snapshot]; exact hgs _ List.mem_cons_self
            · exact hgs f (List.mem_cons_of_mem _ hf)
          · show SuspD Rl G J m₁.ctx m₁.precompiles m₁.frame m.parents
            rw [hif.same.ctx, hif.same.precompiles]; exact suspD_congr hif.same.kind hsusp
        · refine .inr (.inr ?_)
          show DoomAt Rl G J (pushCall m₁ req).ctx (pushCall m₁ req).precompiles
            (pushCall m₁ req).frame (pushCall m₁ req).parents
          rw [hpp]
          refine .inr ?_
          show DoomAt Rl G J m₁.ctx m₁.precompiles m₁.frame m.parents
          rw [hif.same.ctx, hif.same.precompiles]; exact doomAt_congr hif.same.kind hda
      · -- A precompile answers the call.
        obtain ⟨w, t, res, hl, hwv, hrk⟩ := OwnB.launchCall_some_kind hpc
        rw [hl]
        let M : Machine := { m₁ with world := w, transient := t }
        have hsf := sameFrame_resume M res
        have hwM : RelayCode Rl C w ∧ IdleW X w := by
          rcases hwv with rfl | rfl
          · exact ⟨hw₁.congr (code_transferValue _ _),
              hi₁.congr (code_transferValue _ _) (nonce_transferValue _ _)⟩
          · exact ⟨hw₁, hi₁⟩
        have hcom := sandCommon_same (m' := resume M res) hcm hwM.1 hwM.2
          (hsf.msg.trans hif.same.msg) (hsf.kind.trans hif.same.kind)
          (hsf.snapshot.trans hif.same.snapshot) (hsf.code.trans hif.same.code)
          (hsf.parents.trans hif.same.parents) (hsf.ctx.trans hif.same.ctx)
          (hsf.precompiles.trans hif.same.precompiles)
        refine ⟨hcom, ?_⟩
        rcases h.mode with hn | hdc | hda
        · obtain ⟨hg, hgs, hcur, hsusp⟩ := hn
          have hg₁' := hg₁ ⟨hg, hgs, hcur, hsusp⟩
          have hgw : G w := by
            rcases hwv with rfl | rfl
            · exact (S.transferValue ⟨hg₁', hw₁⟩ _).1
            · exact hg₁'
          refine (hsame (hsf.kind.trans hif.same.kind) (hsf.snapshot.trans hif.same.snapshot)
            (hsf.parents.trans hif.same.parents) (hsf.ctx.trans hif.same.ctx)
            (hsf.precompiles.trans hif.same.precompiles) (fun _ => ?_)
            (.inl ⟨hg, hgs, hcur, hsusp⟩)).elim .inl (fun h => .inr (.inl h))
          by_cases hdoom : Danger Rl m.frame ∧ Dm m.frame.msg.currentTarget m
          · exact .inr ((hJ _ hdoom.1.1).doom m b req m₁ (hcur hdoom.1) hg hR hcm.world
              hcm.idle.1 hb he hdoom.2 M res rfl hif.same.parents hif.same.ctx
              hif.same.precompiles hrk)
          · refine .inl ⟨hgw, fun hd => ?_⟩
            have hd' : Danger Rl m.frame :=
              (danger_congr (hsf.msg.trans hif.same.msg).symm).2 hd
            rw [hsf.msg, hif.same.msg]
            exact (hJ _ hd'.1).resumeJ m b _ m₁ (hcur hd') hg hR hcm.world hcm.idle.1 hb he
              (fun hdm => hdoom ⟨hd', hdm⟩) (.inl ⟨req, rfl⟩) M res rfl hif.same.parents
              hif.same.ctx hif.same.precompiles hrk hgw fun req' h' _ => by cases h'; exact hl.symm
        · refine (hsame (hsf.kind.trans hif.same.kind) (hsf.snapshot.trans hif.same.snapshot)
            (hsf.parents.trans hif.same.parents) (hsf.ctx.trans hif.same.ctx)
            (hsf.precompiles.trans hif.same.precompiles) (fun _ => .inr ?_) (.inr hdc)).elim .inl
            (fun h => .inr (.inl h))
          rw [← hl]
          exact hdc.2.1.pre trivial hb he id hpc
        · refine .inr (.inr ?_)
          show DoomAt Rl G J (resume M res).ctx (resume M res).precompiles (resume M res).frame
            (resume M res).parents
          rw [hsf.parents, hsf.ctx, hsf.precompiles]
          show DoomAt Rl G J m₁.ctx m₁.precompiles _ m₁.parents
          rw [hif.same.ctx, hif.same.precompiles, hif.same.parents]
          exact doomAt_congr (hsf.kind.trans hif.same.kind) hda
    · -- A creation: never of a relay, never at an idle account.
      have hcr : CreateOk m m₁ msg := hpost.2
      have hcids : CreateIds m msg := (exec_create_ids _ m).of_run he msg rfl
      have hnr : ¬ Rl msg.currentTarget := fun hr =>
        hC.size _ hr (by rw [← hw₁ _ hr]; exact hcr.code)
      have hnx' : ¬ X msg.currentTarget := hcm.idle.1.not_deployable hcids.2
      have hwc : SameCode m₁.world (launchCreate m₁ msg).world :=
        (code_incrementNonce _ _).trans (code_transferValue _ _)
      have hnc : NonceLe m₁.world (launchCreate m₁ msg).world :=
        (nonce_incrementNonce _ _).trans (nonce_transferValue _ _)
      have hcom := sandCommon_push (mc := launchCreate m₁ msg) hcm hif (hw₁.congr hwc) hw₁
        (fun _ => hnr) (by simp only [launchCreate]; rw [hif.same.parents]) hif.same.ctx
        hif.same.precompiles (hi₁.congr hwc hnc) hi₁
        (by show ¬ X msg.caller; rw [hcids.1]; exact hnx) (fun hx' => absurd hx' hnx')
        (fun _ => hnx')
      have hpp : (launchCreate m₁ msg).parents = m₁.frame :: m.parents := by
        simp only [launchCreate]; rw [hif.same.parents]
      refine ⟨hcom, ?_⟩
      rcases h.mode with hn | hdc | hda
      · obtain ⟨hg, hgs, hcur, hsusp⟩ := hn
        have hg₁' := hg₁ ⟨hg, hgs, hcur, hsusp⟩
        have hdoom : ¬ (Danger Rl m.frame ∧ Dm m.frame.msg.currentTarget m) := fun hd =>
          (hJ _ hd.1.1).doomCreate m b msg m₁ (hcur hd.1) hg hR hcm.world hcm.idle.1 hb he hd.2
        have hgc : G (launchCreate m₁ msg).world := by
          simp only [launchCreate, beginCreate]
          refine hG _ _ hg₁' fun r hr => (keep_incrementNonce (S.code _ ⟨hg₁', hw₁⟩ r hr)).trans
            (keep_transferValue ?_)
          rw [code_incrementNonce _ _ r]; exact S.code _ ⟨hg₁', hw₁⟩ r hr
        refine .inl ⟨hgc, ?_, fun hd => absurd hd.1 hnr, ?_⟩
        · intro f hf
          rw [hpp] at hf
          rcases List.mem_cons.1 hf with rfl | hf
          · exact hg₁'
          rcases List.mem_cons.1 hf with rfl | hf
          · rw [hif.same.snapshot]; exact hgs _ List.mem_cons_self
          · exact hgs f (List.mem_cons_of_mem _ hf)
        · show SuspD Rl G J (launchCreate m₁ msg).ctx (launchCreate m₁ msg).precompiles
            (launchCreate m₁ msg).frame (launchCreate m₁ msg).parents
          rw [hpp]
          refine ⟨fun hd M res hM hMp hMc hMpre hk hgM => ?_, ?_⟩
          · have hd' := (danger_congr hif.same.msg).1 hd
            rw [hif.same.msg]
            exact (hJ _ hd'.1).resumeJ m b _ m₁ (hcur hd') hg hR hcm.world hcm.idle.1 hb he
              (fun hdm => hdoom ⟨hd', hdm⟩) (.inr ⟨msg, rfl⟩) M res hM
              hMp (hMc.trans hif.same.ctx) (hMpre.trans hif.same.precompiles) hk hgM fun _ h' => by cases h'
          · show SuspD Rl G J m₁.ctx m₁.precompiles m₁.frame m.parents
            rw [hif.same.ctx, hif.same.precompiles]; exact suspD_congr hif.same.kind hsusp
      · exact (hdc.2.1.create trivial hb he).elim
      · refine .inr (.inr ?_)
        show DoomAt Rl G J (launchCreate m₁ msg).ctx (launchCreate m₁ msg).precompiles
          (launchCreate m₁ msg).frame (launchCreate m₁ msg).parents
        rw [hpp]
        refine .inr ?_
        show DoomAt Rl G J m₁.ctx m₁.precompiles m₁.frame m.parents
        rw [hif.same.ctx, hif.same.precompiles]; exact doomAt_congr hif.same.kind hda

/-- **The last step**: a finished top-level frame leaves a world satisfying `G`. -/
theorem sandInv_done (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvD K Rl C X G R Iss (Dm r) r (J r)) {m : Machine}
    {r : MessageResult} (h : SandInv K Rl C X G J m) (hR : R m) (hst : step m = .done r) :
    G r.world := by
  have hcm := h.common
  cases hx : exitOf m with
  | none =>
    rcases step_of_exitOf_none hx with ⟨m', hs, -⟩ | ⟨m', req, hs, -⟩ | ⟨m', msg, hs, -⟩ <;>
      rw [hs] at hst <;> cases hst
  | some p =>
    obtain ⟨mf, o⟩ := p
    obtain ⟨hst', hif⟩ := step_of_exitOf hx
    have hcr : mf.frame.kind = .create → ¬ Rl mf.frame.msg.currentTarget := by
      rw [hif.same.kind, hif.same.msg]; exact hcm.create _ List.mem_cons_self
    rw [hst', finishFrame_eq] at hst
    split at hst
    · rename_i hp
      cases hst
      have hgr : G (Program.frameResult mf o).2.1 := by
        rcases h.mode with ⟨hg, hgs, hcur, -⟩ | ⟨hgs, hdm, -⟩ | hda
        · have hgmf : G mf.world := by
            rcases exitOf_cases hx with rfl | ⟨b, a, hb, he⟩
            · exact hg
            · by_cases hd : Danger Rl m.frame
              · exact (hJ _ hd.1).good m b a mf (hcur hd) hg hR hcm.world hcm.idle.1 hb he
              · exact (((exec_frame _ m).of_run he).1.good (goodC_ok hC hG) hd
                  ⟨hg, hcm.world⟩).1
          exact frameResult_P o hgmf (hif.same.snapshot ▸ hgs _ List.mem_cons_self)
            fun out hk => hG _ _ hgmf fun r hr => keep_setCode fun he => hcr hk (he ▸ hr)
        · rw [doomed_exit hdm hx hif.same.snapshot]; exact hgs _ List.mem_cons_self
        · rw [← hif.same.parents, hp] at hda; exact hda.elim
      unfold topLevelResult
      split <;> exact hgr
    · cases hst

/-- From a machine satisfying the invariant, a finished run whose machines satisfy `R` ends in
a world satisfying `G`. -/
theorem sandInv_run (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvD K Rl C X G R Iss (Dm r) r (J r)) {m₀ : Machine}
    (hR : ∀ n m, stepN n m₀ = .running m → R m) :
    ∀ (fuel n : Nat) {m : Machine} {r : MessageResult}, stepN n m₀ = .running m →
      SandInv K Rl C X G J m → run fuel m = .ok r → G r.world
  | 0, _, _, _, _, _, hr => by cases hr
  | fuel + 1, n, m, r, hn, h, hr => by
    simp only [run] at hr
    cases hs : step m with
    | done r' => rw [hs] at hr; cases hr; exact sandInv_done hC hG hJ h (hR n m hn) hs
    | running m' =>
      rw [hs] at hr
      refine sandInv_run hC hG hJ hR fuel (n + 1) ?_ (sandInv_step hC hG hJ h (hR n m hn) hs) hr
      rw [stepN_add_of_running hn 1, stepN_one, hs]

/-! ## Top-level message calls -/

theorem sandInv_start (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvD K Rl C X G R Iss (Dm r) r (J r)) {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {m₀ : Machine}
    (hw : RelayCode Rl C w) (hg : G w) (hi : IdleW X w) (hmsg : GuardTop Rl X w msg)
    (hin : initMachine (PrecompileImpl.standard ctx) ctx w tr msg = .inr m₀)
    (hK : K ctx := by trivial) :
    SandInv K Rl C X G J m₀ := by
  have S := goodC_ok hC hG
  unfold initMachine at hin
  dsimp only at hin
  split at hin
  · cases hin
  split at hin
  · cases hin
  split at hin
  · split at hin
    · cases hin
    · rename_i hdep
      cases hin
      have hdep' : accountDeployable w msg.currentTarget = true := by simpa using hdep
      have hnr : ¬ Rl msg.currentTarget := fun hr =>
        hC.size _ hr (by rw [← hw _ hr]; exact size_code_of_deployable hdep')
      have hnx : ¬ X msg.currentTarget := hi.not_deployable hdep'
      have hwc : SameCode w (Interpreter.transferValue (incrementNonce w msg.currentTarget) msg) :=
        (code_incrementNonce _ _).trans (code_transferValue _ _)
      have hgc : G (Interpreter.transferValue (incrementNonce w msg.currentTarget) msg) := by
        refine hG _ _ hg fun r hr => (keep_incrementNonce (S.code _ ⟨hg, hw⟩ r hr)).trans
          (keep_transferValue ?_)
        rw [code_incrementNonce _ _ r]; exact S.code _ ⟨hg, hw⟩ r hr
      refine ⟨⟨hw.congr hwc, ?_, ?_, rfl,
        ⟨hi.congr hwc ((nonce_incrementNonce _ _).trans (nonce_transferValue _ _)), ?_⟩,
        ?_, ?_, ?_, hK⟩, .inl ⟨hgc, ?_, fun hd => absurd hd.1 hnr, trivial⟩⟩ <;>
        intro f hf <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hf <;> subst hf
      · exact hw
      · exact fun _ => hnr
      · exact hi
      · exact hmsg.caller
      · exact fun hx => absurd hx hnx
      · exact fun _ => hnx
      · exact hg
  · rename_i a hsome
    have htgt : msg.target = some msg.currentTarget := by
      rcases hmsg.top.target with h | h
      · exact h
      · rw [hsome] at h; cases h
    split at hin
    · cases hin
    · cases hin
      refine ⟨⟨hw.congr (code_transferValue _ _), ?_, ?_, rfl,
        ⟨hi.congr (code_transferValue _ _) (nonce_transferValue _ _), ?_⟩, ?_, ?_, ?_, hK⟩,
        .inl ⟨(S.transferValue ⟨hg, hw⟩ msg).1, ?_, ?_, trivial⟩⟩
      · intro f hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        subst hf; exact hw
      · intro f hf hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        subst hf; cases hk
      all_goals try (intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf; subst hf)
      · exact hi
      · exact hmsg.caller
      · exact fun hx => hmsg.idle hx htgt
      · intro hk; cases hk
      · exact hg
      · intro hd
        obtain ⟨hr, hst⟩ := hd
        obtain ⟨hc, hca⟩ := hmsg.top.code hr htgt
        refine (hJ _ hr).start _ ⟨⟨⟨0, 0, rfl⟩, rfl, hst, .inl ⟨?_, hca⟩,
          hw.congr (code_transferValue _ _), rfl⟩, (S.transferValue ⟨hg, hw⟩ msg).1, hg,
          fun r hr => keep_transferValue (S.code _ ⟨hg, hw⟩ r hr),
          hi.congr (code_transferValue _ _) (nonce_transferValue _ _), hmsg.caller,
          .inl ⟨rfl, hmsg.top.caller⟩, hK⟩
        show msg.code = C msg.currentTarget
        rw [hc]; exact hw _ hr

/-- **A guarded message call with doomed frames keeps the world invariant.** From a world
satisfying `G`, where the relays hold their code (not empty, no designator) and the idle accounts
are idle, before Prague or without EIP-7702 authorizations: if each relay's frames keep an
invariant (`GuardInvD`), a top-level call from a sender that is neither a relay nor idle, whose
reached machines all satisfy the run predicate `R`, ends in a world satisfying `G`. -/
theorem processMessageCall_guardD (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvD K Rl C X G R Iss (Dm r) r (J r))
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message} (hw : RelayCode Rl C w)
    (hg : G w) (hi : IdleW X w) (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : GuardTop Rl X w msg) (hR : ∀ m, Reaches ctx w tr msg m → R m) {fuel : Nat}
    {r : MessageResult} (hr : processMessageCall fuel ctx w tr msg = .ok r)
    (hK : K ctx := by trivial) : G r.world := by
  have S := goodC_ok hC hG
  obtain ⟨msg', hdl, hmsg'⟩ := guardTop_delegation
    (isPre := (PrecompileImpl.standard ctx).isPrecompile) hC hw hdeleg hmsg
  unfold processMessageCall processMessageCallWith at hr
  rw [hdl] at hr
  dsimp only at hr
  rcases initMachine_out (ctx := ctx) (tr := tr) S ⟨hg, hw⟩ hmsg'.top (Nat.le_refl _) with
    ⟨r', hin, hgr⟩ | ⟨m₀, hin, -⟩ <;> rw [hin] at hr <;> dsimp only at hr
  · cases hr; exact hgr.1
  · cases hrun : run fuel m₀ with
    | error e => rw [hrun] at hr; cases hr
    | ok r' =>
      rw [hrun] at hr
      cases hr
      show G r'.world
      have hs : StartsAt ctx w tr msg m₀ := by unfold StartsAt; rw [hdl]; exact hin
      exact sandInv_run hC hG hJ (fun n m hn => hR m ⟨m₀, n, hs, hn⟩) fuel 0 rfl
        (sandInv_start hC hG hJ hw hg hi hmsg' hin hK) hrun

end EvmLogic.Program.Nested
