import EvmLogic.AbsInt.Check
import EvmLogic.GasMono.Lockstep

/-!
# Abstract interpretation: soundness for a whole frame

`exit_frame_ind`: induction along a frame up to its exit, skipping each child's steps.
`absint_frame`: with a `Cert` of the frame's code, every machine of the frame before its exit
is described by a recorded abstract state; `absint_call` bounds its call targets and
`absint_no_create` rules out creations.
-/

namespace EvmLogic.AbsInt
open EvmLean EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested EvmLogic.GasMono

/-! ## Steps of a frame -/

theorem step_exec {m m1 : Machine} (hx : exitOf m = none) (hst : step m = .running m1) :
    ∃ b, m.frame.code[m.frame.pc]? = some b ∧ ∃ a m',
      (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m') ∧
      ((a = .next ∧ m1 = m') ∨ (∃ req, a = .call req ∧ m1 = launchCall m' req) ∨
        (∃ msg, a = .create msg ∧ m1 = launchCreate m' msg)) := by
  unfold exitOf at hx
  unfold step at hst
  by_cases hpc : m.frame.pc < m.frame.code.size
  · simp only [hpc, ↓reduceDIte] at hx hst
    refine ⟨m.frame.code[m.frame.pc], getElem?_pos m.frame.code m.frame.pc hpc, ?_⟩
    cases he : (exec (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc])).run m with
    | error e => rw [he] at hx; cases hx
    | ok p =>
      obtain ⟨a, m'⟩ := p
      rw [he] at hx hst
      refine ⟨a, m', rfl, ?_⟩
      cases a with
      | next => simp only [StepResult.running.injEq] at hst; exact .inl ⟨rfl, hst.symm⟩
      | stop _ => cases hx
      | revert _ => cases hx
      | call req =>
        simp only [StepResult.running.injEq] at hst; exact .inr (.inl ⟨req, rfl, hst.symm⟩)
      | create msg =>
        simp only [StepResult.running.injEq] at hst; exact .inr (.inr ⟨msg, rfl, hst.symm⟩)
  · simp only [hpc, ↓reduceDIte] at hx; cases hx

theorem exitOf_cases {m mf : Machine} {o : Outcome} (h : exitOf m = some (mf, o)) :
    mf = m ∨ ∃ b a, m.frame.code[m.frame.pc]? = some b ∧
      (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, mf) := by
  unfold exitOf at h
  by_cases hpc : m.frame.pc < m.frame.code.size
  · simp only [hpc, ↓reduceDIte] at h
    cases he : (exec (Opcode.decode m.ctx.fork m.frame.code[m.frame.pc])).run m with
    | error e => rw [he] at h; cases h; exact .inl rfl
    | ok p =>
      obtain ⟨a, m'⟩ := p
      rw [he] at h
      refine .inr ⟨_, a, getElem?_pos m.frame.code m.frame.pc hpc, ?_⟩
      cases a <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
      · rw [he, h.1]
      · rw [he, h.1]
  · simp only [hpc, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq] at h
    exact .inl h.1.symm

theorem launchCall_some {m : Machine} {req : CallRequest}
    (h : precompileOf m.precompiles req.msg ≠ none) :
    ∃ w t r, launchCall m req = resume { m with world := w, transient := t } r ∧
      (w = transferValue m.world req.msg ∨ w = m.world) := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h
  unfold launchCall runPrecompile
  simp only [ha]
  split
  · exact ⟨_, _, _, rfl, .inl rfl⟩
  · exact ⟨_, _, _, rfl, .inr rfl⟩

/-- A step that stays in the frame: an instruction continuing, or a call answered by a
precompile. -/
def Within (m' : Machine) (a : Action) (m₁ : Machine) : Prop :=
  (a = .next ∧ m₁ = m') ∨
    (∃ req, a = .call req ∧ precompileOf m'.precompiles req.msg ≠ none ∧ m₁ = launchCall m' req)

/-- A step that starts a child frame: a call not answered by a precompile, or a creation. -/
def Pushed (m' : Machine) (a : Action) (mc : Machine) : Prop :=
  (∃ req, a = .call req ∧ precompileOf m'.precompiles req.msg = none ∧ mc = pushCall m' req) ∨
    (∃ msg, a = .create msg ∧ mc = launchCreate m' msg)

theorem resume_frame (M : Machine) (r : ChildResult) :
    (resume M r).frame.pc = M.frame.pc + 1 ∧ (∃ w, (resume M r).frame.stack = w :: M.frame.stack) ∧
      (resume M r).frame.code = M.frame.code := by
  unfold resume
  dsimp only
  split <;> exact ⟨rfl, ⟨_, rfl⟩, rfl⟩

/-- **Induction along a frame up to its exit.** -/
theorem exit_frame_ind (Q : Machine → Prop)
    (hnext : ∀ m b a m' m₁, Q m → m.frame.code[m.frame.pc]? = some b →
      (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m') → Within m' a m₁ →
      SameFrame m m₁ → Q m₁)
    (hchild : ∀ m b a m' mc nc mfc oc, Q m → m.frame.code[m.frame.pc]? = some b →
      (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m') → Pushed m' a mc →
      Exit mc nc mfc oc → SameFrame m (resumeAfter m'.frame m.parents mfc oc) →
      Q (resumeAfter m'.frame m.parents mfc oc)) :
    ∀ n m₀ mf o, Exit m₀ n mf o → Q m₀ →
      ∀ k ≤ n, ∀ m, stepN k m₀ = .running m → SameFrame m₀ m → Q m := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro m₀ mf o hex hQ k hk m hm hs
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [stepN_zero, StepResult.running.injEq] at hm
    exact hm ▸ hQ
  cases hx : exitOf m₀ with
  | some p =>
    obtain ⟨mf', o'⟩ := p
    have := (exit_zero hx).unique hex
    omega
  | none =>
    obtain ⟨m₁, hst⟩ : ∃ m₁, step m₀ = .running m₁ := by
      cases h : step m₀ with
      | running m₁ => exact ⟨m₁, rfl⟩
      | done r =>
        rw [show k = 1 + (k - 1) by omega, stepN_add_of_done (by rw [stepN_one, h])] at hm
        cases hm
    have hm₁ : stepN (k - 1) m₁ = .running m := by
      rw [show k = (k - 1) + 1 by omega, stepN_succ_of_running hst] at hm; exact hm
    obtain ⟨b, hb, a, m', he, hcase⟩ := step_exec hx hst
    have hif : InstrFrame m₀ m' := ((exec_frame _ m₀).of_run he).1
    have within : Within m' a m₁ → SameFrame m₀ m₁ → Q m := by
      intro hw hs₁
      have hQ₁ := hnext m₀ b a m' m₁ hQ hb he hw hs₁
      obtain ⟨hn1, hex'⟩ := hex.next hst hs₁
      exact ih (n - 1) (by omega) m₁ mf o hex' hQ₁ (k - 1) (by omega) m hm₁ (hs₁.symm.trans hs)
    have pushed : ∀ mc, Pushed m' a mc → step m₀ = .running mc →
        mc.parents = m'.frame :: m₀.parents → mc.ctx = m₀.ctx →
        mc.precompiles = m₀.precompiles → mc.originalWorld = m₀.originalWorld → Q m := by
      intro mc hp hstc hpar hc hpre ho
      have hid : SameId m'.frame m₀.frame :=
        ⟨hif.same.msg, hif.same.code, hif.same.jumpDests, hif.same.kind, hif.same.snapshot⟩
      obtain ⟨nc, mfc, oc, hexc, hle, hres, hsame, hexR⟩ := hex.split hstc hpar hid hc hpre ho
      have hQR := hchild m₀ b a m' mc nc mfc oc hQ hb he hp hexc hsame
      have hm₁c : m₁ = mc := by rw [hst] at hstc; cases hstc; rfl
      subst hm₁c
      by_cases hkk : nc + 2 ≤ k
      · have hR : stepN (k - (nc + 2)) (resumeAfter m'.frame m₀.parents mfc oc) = .running m := by
          rw [← stepN_add_of_running hres, show nc + 2 + (k - (nc + 2)) = k by omega]; exact hm
        exact ih (n - (nc + 2)) (by omega) _ mf o hexR hQR (k - (nc + 2)) (by omega) m hR
          (hsame.symm.trans hs)
      · obtain ⟨m'', hm'', hab⟩ := hexc.within (k - 1) (by omega)
        rw [hm₁] at hm''
        cases hm''
        have hl := hab.length_le
        rw [hpar, ← hs.parents] at hl
        simp only [List.length_cons] at hl
        omega
    rcases hcase with ⟨rfl, rfl⟩ | ⟨req, rfl, rfl⟩ | ⟨msg, rfl, rfl⟩
    · exact within (.inl ⟨rfl, rfl⟩) hif.same
    · by_cases hpre : precompileOf m'.precompiles req.msg = none
      · rw [launchCall_none hpre] at hst
        exact pushed _ (.inl ⟨req, rfl, hpre, rfl⟩) hst (by rw [← hif.same.parents]; rfl)
          hif.same.ctx hif.same.precompiles hif.same.originalWorld
      · obtain ⟨w, t, r, hl, -⟩ := launchCall_some hpre
        refine within (.inr ⟨req, rfl, hpre, rfl⟩) ?_
        rw [hl]
        exact hif.same.trans (SameFrame.trans (m₂ := { m' with world := w, transient := t })
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (sameFrame_resume _ _))
    · exact pushed _ (.inr ⟨msg, rfl, rfl⟩) hst (by rw [← hif.same.parents]; rfl)
        hif.same.ctx hif.same.precompiles hif.same.originalWorld

/-! ## The abstract interpretation of a frame -/

/-- The machine is described by a recorded abstract state. -/
def InCert (ρ : Nat → Address) (t : Tree) (m : Machine) : Prop :=
  ∃ s, InT t m.frame.pc s ∧ StackOk ρ s m.frame.stack

variable {ρ : Nat → Address} {allowed : AVal → Bool} {code : ByteArray} {init : AStack}
  {t : Tree}

theorem InCert.entry (hc : Cert ρ allowed code init t) {m : Machine} (hcode : m.frame.code = code)
    (h : InCert ρ t m) {b : UInt8} (hb : m.frame.code[m.frame.pc]? = some b) :
    ∃ s imm succs, StackOk ρ s m.frame.stack ∧ callOk allowed (byteEff b) s = true ∧
      asucc (byteEff b) imm m.frame.pc s = some succs ∧ (∀ x ∈ succs, InT t x.1 x.2) ∧
      ∀ n, byteEff b = .push n →
        imm.Holds ρ (Bytes.toWord (readBytes m.frame.code (m.frame.pc + 1) n)) := by
  obtain ⟨s, hin, hst⟩ := h
  obtain ⟨e, imm, ss, hf, hok, succs, ha, hall⟩ := hc.closed _ _ hin
  obtain ⟨b', hb', he, himm⟩ := hc.ins.find hf
  rw [← hcode, hb] at hb'
  cases hb'
  subst he
  refine ⟨s, imm, succs, hst, hok, ha, hall, fun n hn => ?_⟩
  rw [byteEff_push hn, hcode]; exact himm

theorem inCert_resume (hc : Cert ρ allowed code init t) {m m' : Machine} {b : UInt8}
    {a : Action} (hcode : m.frame.code = code) (h : InCert ρ t m)
    (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m'))
    (ha : (∃ req, a = .call req) ∨ ∃ msg, a = .create msg) (M : Machine) (r : ChildResult)
    (hM : M.frame = m'.frame) : InCert ρ t (resume M r) := by
  obtain ⟨s, imm, succs, hst, -, hsucc, hall, -⟩ := h.entry hc hcode hb
  have hpost := (exec_eff_byte m.ctx.fork b m).of_run he
  have hcp : CallPost (byteEff b) m m' ∨ CreatePost (byteEff b) m m' := by
    rcases ha with ⟨req, rfl⟩ | ⟨msg, rfl⟩
    · exact .inl hpost
    · exact .inr hpost
  have hpc' : m'.frame.pc = m.frame.pc := by
    cases hb' : byteEff b <;> rw [hb'] at hcp <;>
      simp only [CallPost, CreatePost, or_false, false_or] at hcp <;> exact hcp.1
  obtain ⟨hpc, ⟨w, hw⟩, -⟩ := resume_frame M r
  obtain ⟨x, hx, hx1, hx2⟩ := asucc_child hst hcp hsucc w
  refine ⟨x.2, ?_, ?_⟩
  · rw [hpc, hM, hpc', ← hx1]; exact hall x hx
  · rw [hw, hM]; exact hx2

theorem inCert_within (hc : Cert ρ allowed code init t) {m m' m₁ : Machine} {b : UInt8}
    {a : Action} (hcm : m.frame.code = code) (hQ : InCert ρ t m)
    (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m')) (hw : Within m' a m₁) :
    m₁.frame.code = code ∧ InCert ρ t m₁ := by
  have hif : InstrFrame m m' := ((exec_frame _ m).of_run he).1
  rcases hw with ⟨rfl, hm1⟩ | ⟨req, rfl, hpre, hm1⟩ <;> rw [hm1]
  · refine ⟨hif.same.code.trans hcm, ?_⟩
    obtain ⟨s, imm, succs, hst, -, hsucc, hall, himm⟩ := hQ.entry hc hcm hb
    have hpost : NextPost (byteEff b) m m' := (exec_eff_byte m.ctx.fork b m).of_run he
    obtain ⟨x, hx, hx1, hx2⟩ := asucc_next hst rfl himm hpost hsucc
    exact ⟨x.2, by rw [← hx1]; exact hall x hx, hx2⟩
  · obtain ⟨w, tr, r, hl, -⟩ := launchCall_some hpre
    rw [hl]
    refine ⟨(resume_frame _ r).2.2.trans (hif.same.code.trans hcm), ?_⟩
    exact inCert_resume hc hcm hQ hb he (.inl ⟨req, rfl⟩) _ r rfl

theorem inCert_pushed (hc : Cert ρ allowed code init t) {m m' mc : Machine} {b : UInt8}
    {a : Action} (hcm : m.frame.code = code) (hQ : InCert ρ t m)
    (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m')) (hp : Pushed m' a mc)
    (mfc : Machine) (oc : Outcome) :
    (resumeAfter m'.frame m.parents mfc oc).frame.code = code ∧
      InCert ρ t (resumeAfter m'.frame m.parents mfc oc) := by
  have hif : InstrFrame m m' := ((exec_frame _ m).of_run he).1
  have ha : (∃ req, a = .call req) ∨ ∃ msg, a = .create msg := by
    rcases hp with ⟨req, rfl, -⟩ | ⟨msg, rfl, -⟩
    · exact .inl ⟨req, rfl⟩
    · exact .inr ⟨msg, rfl⟩
  refine ⟨?_, inCert_resume hc hcm hQ hb he ha _ _ rfl⟩
  exact (resume_frame _ _).2.2.trans (hif.same.code.trans hcm)

theorem inCert_call (hc : Cert ρ allowed code init t) {m m' : Machine} {b : UInt8}
    {req : CallRequest} (hcm : m.frame.code = code) (hQ : InCert ρ t m)
    (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m')) :
    ∃ tw a, m.frame.stack[1]? = some tw ∧ allowed a = true ∧ a.Holds ρ tw ∧
      ((m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress tw)) = none) →
        req.msg.codeAddress = some (Word.toAddress tw) ∧
        req.msg.code = m.world.code (Word.toAddress tw) ∧ req.msg.disablePrecompiles = false) := by
  obtain ⟨s, imm, succs, hst, hok, -, -, -⟩ := hQ.entry hc hcm hb
  have hpost : CallPost (byteEff b) m m' := (exec_eff_byte m.ctx.fork b m).of_run he
  obtain ⟨tw, htw, hcall⟩ := (exec_target _ m).of_run he req rfl
  cases hbe : byteEff b with
  | call p =>
    rw [hbe] at hok
    obtain ⟨a, ha, hat⟩ := callOk_target hok hst htw
    exact ⟨tw, a, htw, ha, hat, hcall⟩
  | _ => rw [hbe] at hpost; exact hpost.elim

theorem inCert_no_create (hc : Cert ρ allowed code init t) {m m' : Machine} {b : UInt8}
    {msg : Message} (hcm : m.frame.code = code) (hQ : InCert ρ t m)
    (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.create msg, m')) : False := by
  obtain ⟨s, imm, succs, hst, hok, -, -, -⟩ := hQ.entry hc hcm hb
  have hpost : CreatePost (byteEff b) m m' := (exec_eff_byte m.ctx.fork b m).of_run he
  cases hbe : byteEff b with
  | create p => rw [hbe] at hok; simp [callOk] at hok
  | _ => rw [hbe] at hpost; exact hpost.elim

/-- **Soundness of the abstract interpretation for a frame**: every machine of the frame
before its exit is described by a recorded abstract state. -/
theorem absint_frame (hc : Cert ρ allowed code init t) {mh mf : Machine} {N : Nat}
    {o : Outcome} (hex : Exit mh N mf o) (hcode : mh.frame.code = code) (h0 : InCert ρ t mh) :
    ∀ k ≤ N, ∀ m, stepN k mh = .running m → SameFrame mh m → InCert ρ t m := by
  intro k hk m hm hs
  refine (exit_frame_ind (fun m => m.frame.code = code ∧ InCert ρ t m) ?_ ?_ N mh mf o hex
    ⟨hcode, h0⟩ k hk m hm hs).2
  · intro m b a m' m₁ ⟨hcm, hQ⟩ hb he hw _
    exact inCert_within hc hcm hQ hb he hw
  · intro m b a m' mc nc mfc oc ⟨hcm, hQ⟩ hb he hp _ _
    exact inCert_pushed hc hcm hQ hb he hp mfc oc

/-- **The calls of a certified frame** go to allowed targets, running the target's code
(unless it holds an EIP-7702 designator). -/
theorem absint_call (hc : Cert ρ allowed code init t) {mh mf : Machine} {N : Nat}
    {o : Outcome} (hex : Exit mh N mf o) (hcode : mh.frame.code = code) (h0 : InCert ρ t mh) :
    ∀ k ≤ N, ∀ m b req m', stepN k mh = .running m → SameFrame mh m →
      m.frame.code[m.frame.pc]? = some b →
      (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m') →
      ∃ tw a, m.frame.stack[1]? = some tw ∧ allowed a = true ∧ a.Holds ρ tw ∧
        ((m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress tw)) = none) →
          req.msg.codeAddress = some (Word.toAddress tw) ∧
          req.msg.code = m.world.code (Word.toAddress tw) ∧ req.msg.disablePrecompiles = false) :=
  fun k hk m _ _ _ hm hs hb he =>
    inCert_call hc (hs.code.trans hcode) (absint_frame hc hex hcode h0 k hk m hm hs) hb he

/-- **A certified frame requests no creation.** -/
theorem absint_no_create (hc : Cert ρ allowed code init t) {mh mf : Machine} {N : Nat}
    {o : Outcome} (hex : Exit mh N mf o) (hcode : mh.frame.code = code) (h0 : InCert ρ t mh) :
    ∀ k ≤ N, ∀ m b msg m', stepN k mh = .running m → SameFrame mh m →
      m.frame.code[m.frame.pc]? = some b →
      (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.create msg, m') → False :=
  fun k hk m _ _ _ hm hs hb he =>
    inCert_no_create hc (hs.code.trans hcode) (absint_frame hc hex hcode h0 k hk m hm hs) hb he

end EvmLogic.AbsInt
