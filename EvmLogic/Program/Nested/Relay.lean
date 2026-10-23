import EvmLogic.AbsInt.Code

/-!
# Relays: which calls a contract's frames issue

A *relay* is a contract whose frames issue calls on its behalf (a ProxyAdmin calling its proxy,
a Safe executing a transaction, a timelock executing an operation). For a set `Rl` of relay
accounts with **issuance predicates** `Iss r`, `processMessageCall_issues` says: in any
top-level message call, every child message (call or creation) requested by a non-static frame
at a relay `r` satisfies `Iss r`. That frame may run `r`'s own code or code `r` delegatecalls
into; a static frame can only issue static calls, which change nothing.

Each relay discharges one frame-local obligation, `RelayInv`: an invariant `J` of its frames
that holds when a frame starts (`RelayStart`), is kept by each instruction and across each
child call *whatever the child did* (reentrancy included), and implies `Iss r` for every
requested message. Nothing is assumed about the other contracts. The transaction-level proof is
a forward simulation (`RelayTxInv`): every machine reached keeps the relays' code, every
non-static relay frame satisfies its invariant, and every suspended one will satisfy it after
any child returns. Unlike `processMessageCall_good`, no frame summary and no termination is
needed. The obligations have the shape of `EvmLogic.AbsInt.exit_frame_ind` (whose `InCert`
satisfies `next` and `resume`). See `docs/actor-bytecode.md`.
-/

namespace EvmLogic.Program.Nested
open EvmLean EvmLean.Interpreter EvmLogic.AbsInt EvmLogic.GasMono

/-! ## Issued messages and relay frames -/

/-- The instruction at `m` requests the child message `c`: a call (`CALL`, `CALLCODE`,
`DELEGATECALL`, `STATICCALL`) or a creation. -/
def Requests (m : Machine) (c : Message) : Prop :=
  ∃ b a m', m.frame.code[m.frame.pc]? = some b ∧
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m') ∧
    ((∃ req, a = .call req ∧ req.msg = c) ∨ a = .create c)

/-- Every relay holds its code `C r`. -/
def RelayCode (Rl : Address → Prop) (C : Address → ByteArray) (w : World) : Prop :=
  ∀ r, Rl r → w.code r = C r

/-- The relays' code is not empty and is no EIP-7702 designator. -/
structure RelayCodeOk (Rl : Address → Prop) (C : Address → ByteArray) : Prop where
  size : ∀ r, Rl r → (C r).size ≠ 0
  deleg : ∀ r, Rl r → delegatedAddress? (C r) = none

/-- **A frame of relay `r` that has just started**, non-static: what its invariant may assume.
It runs `r`'s own code, or it was requested by a non-static frame at `r` itself (a
`DELEGATECALL`, a `CALLCODE` or a call to itself) under `Iss r`. -/
structure RelayStart (Rl : Address → Prop) (C : Address → ByteArray)
    (Iss : Address → Machine → Message → Prop) (r : Address) (m : Machine) : Prop where
  /-- A fresh message-call frame. -/
  fresh : ∃ o s, m.frame = Frame.init m.frame.msg (.call o s) m.frame.snapshot
  target : m.frame.msg.currentTarget = r
  static : m.frame.msg.isStatic = false
  entry : (m.frame.msg.code = C r ∧ m.frame.msg.codeAddress = some r) ∨
    ∃ mp, mp.ctx = m.ctx ∧ mp.frame.msg.currentTarget = r ∧ mp.frame.msg.isStatic = false ∧
      Requests mp m.frame.msg ∧ Iss r mp m.frame.msg
  /-- Relays hold their code. -/
  world : RelayCode Rl C m.world
  /-- Standard precompiles. -/
  pre : m.precompiles = PrecompileImpl.standard m.ctx

/-- **The frame obligation of relay `r`**: an invariant `J` of its non-static frames. -/
structure RelayInv (Rl : Address → Prop) (C : Address → ByteArray)
    (Iss : Address → Machine → Message → Prop) (r : Address) (J : Machine → Prop) : Prop where
  /-- It holds when a frame starts. -/
  start : ∀ m, RelayStart Rl C Iss r m → J m
  /-- Every message the frame requests satisfies `Iss r`. -/
  issue : ∀ m c, J m → RelayCode Rl C m.world → Requests m c → Iss r m c
  /-- It is kept by an instruction that continues the frame. -/
  next : ∀ m b m', J m → m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m') → J m'
  /-- It holds when the frame resumes after a requested child, whatever the child did. -/
  resume : ∀ m b a m', J m → m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m') →
    ((∃ req, a = .call req) ∨ ∃ msg, a = .create msg) →
    ∀ M res, M.frame = m'.frame → M.parents = m.parents → M.ctx = m.ctx →
      M.precompiles = m.precompiles → J (resume M res)

/-! ## The simulation invariant -/

/-- A suspended frame `p` (with ancestors `ps`): if it is a non-static relay frame, its
invariant holds when it resumes after any child. -/
def ResumeOk (Rl : Address → Prop) (J : Address → Machine → Prop) (ctx : Context)
    (pre : PrecompileImpl) (p : Frame) (ps : List Frame) : Prop :=
  Danger Rl p → ∀ M res, M.frame = p → M.parents = ps → M.ctx = ctx → M.precompiles = pre →
    J p.msg.currentTarget (resume M res)

/-- `ResumeOk` for every suspended frame. -/
def Suspended (Rl : Address → Prop) (J : Address → Machine → Prop) (ctx : Context)
    (pre : PrecompileImpl) : List Frame → Prop
  | [] => True
  | p :: ps => ResumeOk Rl J ctx pre p ps ∧ Suspended Rl J ctx pre ps

/-- **The simulation invariant** of every machine of a message call. -/
structure RelayTxInv (Rl : Address → Prop) (C : Address → ByteArray)
    (J : Address → Machine → Prop) (m : Machine) : Prop where
  world : RelayCode Rl C m.world
  /-- Every rollback snapshot keeps the relays' code. -/
  snapshots : ∀ f ∈ m.frame :: m.parents, RelayCode Rl C f.snapshot.1
  /-- No creation frame creates a relay. -/
  create : ∀ f ∈ m.frame :: m.parents, f.kind = .create → ¬ Rl f.msg.currentTarget
  /-- The executing frame, if a non-static relay frame, satisfies its invariant. -/
  cur : Danger Rl m.frame → J m.frame.msg.currentTarget m
  susp : Suspended Rl J m.ctx m.precompiles m.parents
  pre : m.precompiles = PrecompileImpl.standard m.ctx

variable {Rl : Address → Prop} {C : Address → ByteArray}
  {Iss : Address → Machine → Message → Prop} {J : Address → Machine → Prop} {m : Machine}

/-! ## Worlds -/

theorem RelayCode.congr {w w' : World} (h : RelayCode Rl C w) (hc : SameCode w w') :
    RelayCode Rl C w' := fun r hr => (hc r).trans (h r hr)

theorem RelayCode.frameResult (h : RelayTxInv Rl C J m) {mf : Machine}
    (hw : RelayCode Rl C mf.world) (hf : mf.frame = m.frame ∨ (mf.frame.msg = m.frame.msg ∧
      mf.frame.kind = m.frame.kind ∧ mf.frame.snapshot = m.frame.snapshot)) (o : Outcome) :
    RelayCode Rl C (Program.frameResult mf o).2.1 := by
  have hf' : mf.frame.msg = m.frame.msg ∧ mf.frame.kind = m.frame.kind ∧
      mf.frame.snapshot = m.frame.snapshot := by
    rcases hf with hf | hf
    · rw [hf]; exact ⟨rfl, rfl, rfl⟩
    · exact hf
  rcases frameResult_world mf o with he | ⟨hk, out, he⟩ | he <;> rw [he]
  · exact hw
  · intro r hr
    have hne : r ≠ mf.frame.msg.currentTarget := by
      rintro rfl
      rw [hf'.1] at hr
      exact h.create _ List.mem_cons_self (hf'.2.1 ▸ hk) hr
    rw [code_setCode_ne (Ne.symm hne)]; exact hw r hr
  · rw [hf'.2.2]; exact h.snapshots _ List.mem_cons_self

theorem resume_frame_id (M : Machine) (res : ChildResult) :
    (resume M res).frame.msg = M.frame.msg ∧ (resume M res).frame.kind = M.frame.kind ∧
      (resume M res).frame.snapshot = M.frame.snapshot ∧ (resume M res).parents = M.parents ∧
      (resume M res).ctx = M.ctx ∧ (resume M res).precompiles = M.precompiles := by
  have h := sameFrame_resume M res
  exact ⟨h.msg, h.kind, h.snapshot, h.parents, h.ctx, h.precompiles⟩

/-! ## One step -/

/-- The invariant after resuming the frame `M.frame`, whose identity is that of `m.frame`. -/
theorem relayTxInv_resume (h : RelayTxInv Rl C J m) {M : Machine} (res : ChildResult)
    (hw : RelayCode Rl C M.world) (hmsg : M.frame.msg = m.frame.msg)
    (hk : M.frame.kind = m.frame.kind) (hs : M.frame.snapshot = m.frame.snapshot)
    (hp : M.parents = m.parents) (hc : M.ctx = m.ctx) (hpre : M.precompiles = m.precompiles)
    (hcur : Danger Rl m.frame → J m.frame.msg.currentTarget (resume M res)) :
    RelayTxInv Rl C J (resume M res) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := resume_frame_id M res
  refine ⟨hw, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [h4, hp] at hf
    rcases List.mem_cons.1 hf with rfl | hf
    · rw [h3, hs]; exact h.snapshots _ List.mem_cons_self
    · exact h.snapshots f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rw [h4, hp] at hf
    rcases List.mem_cons.1 hf with rfl | hf
    · rw [h2, hk, h1, hmsg]; exact h.create _ List.mem_cons_self
    · exact h.create f (List.mem_cons_of_mem _ hf)
  · intro hd
    rw [h1, hmsg]
    exact hcur (by unfold Danger at hd ⊢; rw [h1, hmsg] at hd; exact hd)
  · rw [h4, hp, h5, hc, h6, hpre]; exact h.susp
  · rw [h5, hc, h6, hpre]; exact h.pre

theorem danger_congr {f f' : Frame} (h : f'.msg = f.msg) : Danger Rl f' ↔ Danger Rl f := by
  unfold Danger; rw [h]

/-- A pushed frame and its suspended parent. -/
theorem relayTxInv_push (h : RelayTxInv Rl C J m) {m' mc : Machine} (hif : InstrFrame m m')
    (hw : RelayCode Rl C mc.world) (hsnap : RelayCode Rl C mc.frame.snapshot.1)
    (hcreate : mc.frame.kind = .create → ¬ Rl mc.frame.msg.currentTarget)
    (hpar : mc.parents = m'.frame :: m.parents) (hc : mc.ctx = m.ctx)
    (hpre : mc.precompiles = m.precompiles)
    (hcur : Danger Rl mc.frame → J mc.frame.msg.currentTarget mc)
    (hres : Danger Rl m.frame → ResumeOk Rl J m.ctx m.precompiles m'.frame m.parents) :
    RelayTxInv Rl C J mc := by
  refine ⟨hw, ?_, ?_, hcur, ?_, ?_⟩
  · intro f hf
    rw [hpar] at hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hsnap
    rcases List.mem_cons.1 hf with rfl | hf
    · rw [hif.same.snapshot]; exact h.snapshots _ List.mem_cons_self
    · exact h.snapshots f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rw [hpar] at hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact hcreate
    rcases List.mem_cons.1 hf with rfl | hf
    · rw [hif.same.kind, hif.same.msg]; exact h.create _ List.mem_cons_self
    · exact h.create f (List.mem_cons_of_mem _ hf)
  · rw [hpar, hc, hpre]
    refine ⟨fun hd => hres ((danger_congr hif.same.msg).1 hd) hd, h.susp⟩
  · rw [hc, hpre]; exact h.pre

/-- **One step keeps the simulation invariant.** -/
theorem relayTxInv_step (hC : RelayCodeOk Rl C) (hJ : ∀ r, Rl r → RelayInv Rl C Iss r (J r))
    {m m' : Machine} (h : RelayTxInv Rl C J m) (hst : step m = .running m') :
    RelayTxInv Rl C J m' := by
  cases hx : exitOf m with
  | some p =>
    obtain ⟨mf, o⟩ := p
    obtain ⟨hst', hif⟩ := step_of_exitOf hx
    have hwf : RelayCode Rl C mf.world := by
      rcases exitOf_cases hx with rfl | ⟨b, a, -, he⟩
      · exact h.world
      · exact h.world.congr ((exec_code _ m).of_run he)
    rw [hst', finishFrame_eq] at hst
    split at hst
    · cases hst
    rename_i p ps hp
    cases hst
    have hpar : m.parents = p :: ps := hif.same.parents ▸ hp
    have hsusp := h.susp
    rw [hpar] at hsusp
    have hwr := RelayCode.frameResult h hwf (.inr ⟨hif.same.msg, hif.same.kind, hif.same.snapshot⟩) o
    refine ⟨hwr, ?_, ?_, ?_, ?_, ?_⟩
    · intro f hf
      obtain ⟨-, -, h3, h4, -, -⟩ := resume_frame_id
        { mf with frame := p, parents := ps, world := (Program.frameResult mf o).2.1,
                  transient := (Program.frameResult mf o).2.2 } (Program.frameResult mf o).1
      simp only [resumeAfter] at hf ⊢
      rw [h4] at hf
      rcases List.mem_cons.1 hf with rfl | hf
      · rw [h3]; exact h.snapshots p (by rw [hpar]; simp)
      · exact h.snapshots f (by rw [hpar]; simp [hf])
    · intro f hf
      obtain ⟨h1, h2, -, h4, -, -⟩ := resume_frame_id
        { mf with frame := p, parents := ps, world := (Program.frameResult mf o).2.1,
                  transient := (Program.frameResult mf o).2.2 } (Program.frameResult mf o).1
      simp only [resumeAfter] at hf ⊢
      rw [h4] at hf
      rcases List.mem_cons.1 hf with rfl | hf
      · rw [h1, h2]; exact h.create p (by rw [hpar]; simp)
      · exact h.create f (by rw [hpar]; simp [hf])
    · intro hd
      obtain ⟨h1, -, -, -, -, -⟩ := resume_frame_id
        { mf with frame := p, parents := ps, world := (Program.frameResult mf o).2.1,
                  transient := (Program.frameResult mf o).2.2 } (Program.frameResult mf o).1
      simp only [resumeAfter] at hd ⊢
      rw [h1]
      exact hsusp.1 ((danger_congr h1).1 hd) _ _ rfl rfl hif.same.ctx hif.same.precompiles
    · simp only [resumeAfter, resume_parents]
      show Suspended Rl J mf.ctx mf.precompiles ps
      rw [hif.same.ctx, hif.same.precompiles]; exact hsusp.2
    · show mf.precompiles = PrecompileImpl.standard mf.ctx
      rw [hif.same.ctx, hif.same.precompiles]; exact h.pre
  | none =>
    obtain ⟨b, hb, a, m₁, he, hcase⟩ := step_exec hx hst
    have hpost := (exec_frame _ m).of_run he
    have hif : InstrFrame m m₁ := hpost.1
    have hcode : SameCode m.world m₁.world := (exec_code _ m).of_run he
    have hw₁ : RelayCode Rl C m₁.world := h.world.congr hcode
    -- The invariant of the executing frame after any child it requests.
    have hresume : ((∃ req, a = .call req) ∨ ∃ msg, a = .create msg) → Danger Rl m.frame →
        ResumeOk Rl J m.ctx m.precompiles m₁.frame m.parents := by
      intro ha hd _ M res hM hMp hMc hMpre
      have hJm := h.cur hd
      have hr := hJ _ hd.1
      rw [hif.same.msg]
      exact hr.resume m b a m₁ hJm hb he ha M res hM hMp hMc hMpre
    rcases hcase with ⟨rfl, rfl⟩ | ⟨req, rfl, rfl⟩ | ⟨msg, rfl, rfl⟩
    · -- An instruction continuing the frame.
      refine ⟨hw₁, ?_, ?_, ?_, ?_, ?_⟩
      · intro f hf
        rw [hif.same.parents] at hf
        rcases List.mem_cons.1 hf with rfl | hf
        · rw [hif.same.snapshot]; exact h.snapshots _ List.mem_cons_self
        · exact h.snapshots f (List.mem_cons_of_mem _ hf)
      · intro f hf
        rw [hif.same.parents] at hf
        rcases List.mem_cons.1 hf with rfl | hf
        · rw [hif.same.kind, hif.same.msg]; exact h.create _ List.mem_cons_self
        · exact h.create f (List.mem_cons_of_mem _ hf)
      · intro hd
        have hd' := (danger_congr hif.same.msg).1 hd
        rw [hif.same.msg]
        exact (hJ _ hd'.1).next m b m' (h.cur hd') hb he
      · rw [hif.same.parents, hif.same.ctx, hif.same.precompiles]; exact h.susp
      · rw [hif.same.ctx, hif.same.precompiles]; exact h.pre
    · -- A call.
      have hcall : CallOk m m₁ req := hpost.2
      by_cases hpc : precompileOf m₁.precompiles req.msg = none
      · -- A child frame is pushed.
        rw [launchCall_none hpc]
        refine relayTxInv_push (mc := pushCall m₁ req) h hif (hw₁.congr (pushCall_code _ _)) hw₁ (fun hk => by cases hk)
          (by simp only [pushCall]; rw [hif.same.parents]) hif.same.ctx hif.same.precompiles ?_
          (hresume (.inl ⟨req, rfl⟩))
        intro hd
        show J req.msg.currentTarget (pushCall m₁ req)
        have hrel : Rl req.msg.currentTarget := hd.1
        have hst' : req.msg.isStatic = false := hd.2
        refine (hJ _ hrel).start _ ⟨⟨_, _, rfl⟩, rfl, hst', ?_, hw₁.congr (pushCall_code _ _), ?_⟩
        · obtain ⟨hps, hcur⟩ := hcall.nonstatic hst'
          by_cases heq : req.msg.currentTarget = m.frame.msg.currentTarget
          · right
            have hdm : Danger Rl m.frame := ⟨heq ▸ hrel, hps⟩
            refine ⟨m, hif.same.ctx.symm, heq.symm, hps, ⟨b, _, m₁, hb, he, .inl ⟨req, rfl, rfl⟩⟩, ?_⟩
            show Iss req.msg.currentTarget m req.msg
            rw [heq]
            exact (hJ _ (heq ▸ hrel)).issue m req.msg (heq ▸ h.cur hdm) h.world
              ⟨b, _, m₁, hb, he, .inl ⟨req, rfl, rfl⟩⟩
          · left
            obtain ⟨-, hc⟩ := hcur.resolve_left heq
            have hwr := h.world _ hrel
            obtain ⟨hc1, hc2, -⟩ := hc (by rw [hwr]; exact hC.deleg _ hrel)
            exact ⟨by show req.msg.code = _; rw [hc1, hwr], hc2⟩
        · show m₁.precompiles = PrecompileImpl.standard m₁.ctx
          rw [hif.same.ctx, hif.same.precompiles]; exact h.pre
      · -- A precompile answers the call.
        obtain ⟨w, t, res, hl, hwv⟩ := launchCall_some hpc
        rw [hl]
        have hwM : RelayCode Rl C w := by
          rcases hwv with rfl | rfl
          · exact hw₁.congr (code_transferValue _ _)
          · exact hw₁
        refine relayTxInv_resume h res hwM hif.same.msg hif.same.kind hif.same.snapshot
          hif.same.parents hif.same.ctx hif.same.precompiles ?_
        intro hd
        exact (hJ _ hd.1).resume m b _ m₁ (h.cur hd) hb he (.inl ⟨req, rfl⟩) _ res rfl
          hif.same.parents hif.same.ctx hif.same.precompiles
    · -- A creation: never of a relay.
      have hcr : CreateOk m m₁ msg := hpost.2
      have hnr : ¬ Rl msg.currentTarget := fun hr =>
        hC.size _ hr (by rw [← hw₁ _ hr]; exact hcr.code)
      refine relayTxInv_push (mc := launchCreate m₁ msg) h hif ?_ hw₁ (fun _ => hnr)
        (by simp only [launchCreate]; rw [hif.same.parents]) hif.same.ctx hif.same.precompiles
        (fun hd => absurd hd.1 hnr) (hresume (.inr ⟨msg, rfl⟩))
      simp only [launchCreate, beginCreate]
      exact hw₁.congr ((code_incrementNonce _ _).trans (code_transferValue _ _))

theorem relayTxInv_stepN (hC : RelayCodeOk Rl C) (hJ : ∀ r, Rl r → RelayInv Rl C Iss r (J r)) :
    ∀ (n : Nat) {m m' : Machine}, RelayTxInv Rl C J m → stepN n m = .running m' →
      RelayTxInv Rl C J m'
  | 0, _, _, h, hst => by simp only [stepN_zero, StepResult.running.injEq] at hst; exact hst ▸ h
  | n + 1, m, m', h, hst => by
    cases hs : step m with
    | done r =>
      rw [show n + 1 = 1 + n by omega, stepN_add_of_done (by rw [stepN_one, hs])] at hst
      cases hst
    | running m₁ =>
      rw [stepN_succ_of_running hs] at hst
      exact relayTxInv_stepN hC hJ n (relayTxInv_step hC hJ h hs) hst

/-! ## Top-level message calls -/

theorem relayTxInv_start (hC : RelayCodeOk Rl C) (hJ : ∀ r, Rl r → RelayInv Rl C Iss r (J r))
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message} {m₀ : Machine}
    (hw : RelayCode Rl C w) (hmsg : TopOk Rl w msg)
    (hi : initMachine (PrecompileImpl.standard ctx) ctx w tr msg = .inr m₀) :
    RelayTxInv Rl C J m₀ := by
  unfold initMachine at hi
  dsimp only at hi
  split at hi
  · cases hi
  split at hi
  · cases hi
  split at hi
  · split at hi
    · cases hi
    · rename_i hdep
      cases hi
      have hdep' : accountDeployable w msg.currentTarget = true := by simpa using hdep
      have hnr : ¬ Rl msg.currentTarget := fun hr =>
        hC.size _ hr (by rw [← hw _ hr]; exact size_code_of_deployable hdep')
      refine ⟨hw.congr ((code_incrementNonce _ _).trans (code_transferValue _ _)), ?_, ?_,
        fun hd => absurd hd.1 hnr, trivial, rfl⟩
      · intro f hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        subst hf; exact hw
      · intro f hf _
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        subst hf; exact hnr
  · rename_i a hsome
    have htgt : msg.target = some msg.currentTarget := by
      rcases hmsg.target with h | h
      · exact h
      · rw [hsome] at h; cases h
    split at hi
    · cases hi
    · cases hi
      refine ⟨hw.congr (code_transferValue _ _), ?_, ?_, ?_, trivial, rfl⟩
      · intro f hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        subst hf; exact hw
      · intro f hf hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        subst hf; cases hk
      · intro hd
        obtain ⟨hr, hst⟩ := hd
        obtain ⟨hc, hca⟩ := hmsg.code hr htgt
        refine (hJ _ hr).start _ ⟨⟨0, 0, rfl⟩, rfl, hst, .inl ⟨?_, hca⟩,
          hw.congr (code_transferValue _ _), rfl⟩
        show msg.code = C msg.currentTarget
        rw [hc]; exact hw _ hr

/-- **Relays issue only what their predicates allow, in a whole top-level message call.**
From a world where every relay `r` holds its code `C r` (not empty, no designator), for a
`TopOk` message, before Prague or without EIP-7702 authorizations: if each relay's frames keep
an invariant (`RelayInv`), then every machine the call reaches whose executing frame is a
non-static frame at a relay `r` requests only messages satisfying `Iss r`. -/
theorem processMessageCall_issues (hC : RelayCodeOk Rl C)
    (hJ : ∀ r, Rl r → RelayInv Rl C Iss r (J r)) {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} (hw : RelayCode Rl C w)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hmsg : TopOk Rl w msg)
    {m : Machine} (hm : Reaches ctx w tr msg m) (hd : Danger Rl m.frame) {c : Message}
    (hc : Requests m c) : Iss m.frame.msg.currentTarget m c := by
  obtain ⟨msg', hdl, hcur, hcaller, htarget, hdepth, -, -, hsame⟩ :=
    applyTopLevelDelegation_spec (isPre := (PrecompileImpl.standard ctx).isPrecompile) (w := w)
      (msg := msg) hdeleg
  have hmsg' : TopOk Rl w msg' := by
    refine ⟨hdepth.trans hmsg.depth, hcaller ▸ hmsg.caller, ?_, fun hp ht => ?_⟩
    · rw [htarget, hcur]; exact hmsg.target
    · rw [hcur] at hp ht ⊢
      rw [htarget] at ht
      obtain ⟨hc, hca⟩ := hmsg.code hp ht
      have := hsame (by rw [hc, hw _ hp]; exact hC.deleg _ hp)
      subst this
      exact ⟨hc, hca⟩
  obtain ⟨m₀, n, hs, hn⟩ := hm
  unfold StartsAt at hs
  rw [hdl] at hs
  have h := relayTxInv_stepN hC hJ n (relayTxInv_start hC hJ hw hmsg' hs) hn
  exact (hJ _ hd.1).issue m c (h.cur hd) h.world hc

/-- **The non-static calls a relay issues**, from any of its frames: a non-static call requested
by a frame at a relay `r` (static or not) satisfies `Iss r`, since only a non-static frame
requests a non-static call. -/
theorem processMessageCall_issues_call (hC : RelayCodeOk Rl C)
    (hJ : ∀ r, Rl r → RelayInv Rl C Iss r (J r)) {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} (hw : RelayCode Rl C w)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hmsg : TopOk Rl w msg)
    {m : Machine} (hm : Reaches ctx w tr msg m) (hr : Rl m.frame.msg.currentTarget)
    {b : UInt8} {req : CallRequest} {m' : Machine} (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m'))
    (hst : req.msg.isStatic = false) : Iss m.frame.msg.currentTarget m req.msg := by
  have hcall : CallOk m m' req := ((exec_frame _ m).of_run he).2
  exact processMessageCall_issues hC hJ hw hdeleg hmsg hm ⟨hr, (hcall.nonstatic hst).1⟩
    ⟨b, _, m', hb, he, .inl ⟨req, rfl, rfl⟩⟩

end EvmLogic.Program.Nested
