import EvmLogic.Program.Nested.Relay
import EvmLogic.Program.Nested.Idle

/-!
# Guarded relays: a protected world invariant, and principals that do not act

`Relay.lean` proves that each relay's frames request only what its predicate `Iss` allows. To
prove that a transaction keeps protected state (the implementation slot of a proxy, the owner of
a ProxyAdmin), two more things are needed, and this module adds them to the same step-local
simulation:

- a **world invariant** `G`, depending only on the protected accounts' storage, held by the
  current world and every rollback snapshot of every machine. Frames that are not protected
  cannot change it (the frame condition), and each relay's frame invariant shows that the
  relay's own instructions keep it (`GuardInv.good`);
- **idle principals** `X`: accounts with no code that have sent a transaction (`IdleW`). They
  never appear as the sender of any frame (`GuardTxInv.callers`): a frame at an idle account
  runs no code, so it requests nothing, and no creation lands on an account with a nonzero
  nonce. An externally owned account that does not send the transaction is idle; this is how
  "the owner does not act" becomes a fact about bytecode.

A relay's invariant may assume, when its frame starts (`GuardStart`), that `G` held, that the
sender is not idle, and who requested the frame (`origin`): the top-level sender (not a relay),
or a machine whose request satisfies its own `Iss` when it is a relay. So "ProxyAdmin issues
nothing to a non-owner" becomes "the proxy is never called by its admin" at the proxy.

`processMessageCall_guard`: from a world where `G` holds, the relays hold their code and the idle
accounts are idle, a top-level message call whose sender is idle-free ends in a world satisfying
`G`. `processMessageCall_guard_issues` restates `Relay.lean`'s conclusion.
-/

namespace EvmLogic.Program.Nested
open EvmLean EvmLean.Interpreter EvmLogic.AbsInt EvmLogic.GasMono

/-! ## Idle accounts -/

/-- Idle accounts hold no code and have a nonzero nonce. -/
def IdleW (X : Address → Prop) (w : World) : Prop :=
  ∀ x, X x → (w.code x).size = 0 ∧ (w.account x).nonce ≠ 0

variable {X : Address → Prop}

theorem IdleW.congr {w w' : World} (h : IdleW X w) (hc : SameCode w w') (hn : NonceLe w w') :
    IdleW X w' := fun x hx =>
  ⟨by rw [hc x]; exact (h x hx).1, fun h0 => (h x hx).2 (by have := hn x; omega)⟩

theorem IdleW.setCode {w : World} {a : Address} {out : ByteArray} (h : IdleW X w)
    (ha : ¬ X a) : IdleW X (setCode w a out) := fun x hx => by
  have hne : a ≠ x := fun e => ha (e ▸ hx)
  refine ⟨by rw [code_setCode_ne hne]; exact (h x hx).1, fun h0 => (h x hx).2 ?_⟩
  have := nonce_setCode w a out x
  omega

theorem IdleW.not_deployable {w : World} {a : Address} (h : IdleW X w)
    (hd : accountDeployable w a = true) : ¬ X a := fun hx => by
  have h0 := (h a hx).2
  simp only [accountDeployable, Bool.and_eq_true, decide_eq_true_eq] at hd
  exact h0 hd.1.1

theorem getElem?_of_size_le {c : ByteArray} {i : Nat} (h : c.size ≤ i) : c[i]? = none := by
  simp [getElem?_neg, Nat.not_lt.2 h]

theorem delegated_size {c : ByteArray} {d : Address} (h : delegatedAddress? c = some d) :
    c.size ≠ 0 := by
  intro h0
  have := getElem?_zero_of_delegated h
  rw [getElem?_of_size_le (by omega)] at this
  cases this

/-! ## The relay obligation -/

/-- **A non-static frame at relay `r` that has just started**: `RelayStart`, the world invariant
before and after the value transfer, idle accounts idle, an active sender, and who requested
the frame. -/
structure GuardStartK (K : Context → Prop) (Rl : Address → Prop) (C : Address → ByteArray)
    (X : Address → Prop) (G : World → Prop) (Iss : Address → Machine → Message → Prop)
    (r : Address) (m : Machine) : Prop where
  base : RelayStart Rl C Iss r m
  good : G m.world
  goodSnap : G m.frame.snapshot.1
  /-- The world differs from the snapshot only by a value transfer. -/
  keep : KeepP Rl m.frame.snapshot.1 m.world
  idle : IdleW X m.world
  /-- The sender is not idle. -/
  caller : ¬ X m.frame.msg.caller
  /-- The top-level frame, whose sender is no relay; or a child requested by a non-static frame
  of `mp`, under that relay's `Iss` if `mp` runs at a relay. -/
  origin : (m.parents = [] ∧ ¬ Rl m.frame.msg.caller) ∨
    ∃ mp, mp.ctx = m.ctx ∧ mp.frame.msg.isStatic = false ∧ Requests mp m.frame.msg ∧
      (m.frame.msg.caller = mp.frame.msg.currentTarget ∨
        (m.frame.msg.caller = mp.frame.msg.caller ∧
          m.frame.msg.currentTarget = mp.frame.msg.currentTarget)) ∧
      (Rl mp.frame.msg.currentTarget → Iss mp.frame.msg.currentTarget mp m.frame.msg)
  /-- The transaction's context satisfies `K`. -/
  ctx : K m.ctx

/-- `GuardStartK` with no assumption on the context. -/
abbrev GuardStart (Rl : Address → Prop) (C : Address → ByteArray) (X : Address → Prop)
    (G : World → Prop) (Iss : Address → Machine → Message → Prop) (r : Address) (m : Machine) :
    Prop := GuardStartK (fun _ => True) Rl C X G Iss r m

/-- **The frame obligation of relay `r`**: `RelayInv`, where every instruction may assume the
world invariant and must keep it. -/
structure GuardInvK (K : Context → Prop) (Rl : Address → Prop) (C : Address → ByteArray)
    (X : Address → Prop) (G : World → Prop) (Iss : Address → Machine → Message → Prop)
    (r : Address) (J : Machine → Prop) : Prop where
  start : ∀ m, GuardStartK K Rl C X G Iss r m → J m
  issue : ∀ m c, J m → G m.world → RelayCode Rl C m.world → Requests m c → Iss r m c
  /-- Each instruction keeps the world invariant. -/
  good : ∀ m b a m', J m → G m.world → RelayCode Rl C m.world → m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m') → G m'.world
  next : ∀ m b m', J m → G m.world → RelayCode Rl C m.world → m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m') → J m'
  /-- It holds when the frame resumes after a requested child, whatever the child did; after a
  precompile, the frame resumes as `launchCall` resumes it (so the precompile's output is
  known). -/
  resume : ∀ m b a m', J m → G m.world → RelayCode Rl C m.world →
    m.frame.code[m.frame.pc]? = some b →
    (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m') →
    ((∃ req, a = .call req) ∨ ∃ msg, a = .create msg) →
    ∀ M res, M.frame = m'.frame → M.parents = m.parents → M.ctx = m.ctx →
      M.precompiles = m.precompiles →
      (∀ req, a = .call req → precompileOf m'.precompiles req.msg ≠ none →
        resume M res = launchCall m' req) → J (resume M res)

/-- `GuardInvK` with no assumption on the context. -/
abbrev GuardInv (Rl : Address → Prop) (C : Address → ByteArray) (X : Address → Prop)
    (G : World → Prop) (Iss : Address → Machine → Message → Prop) (r : Address)
    (J : Machine → Prop) : Prop := GuardInvK (fun _ => True) Rl C X G Iss r J

/-! ## The simulation invariant -/

/-- **The simulation invariant** of every machine of a message call. -/
structure GuardTxInvK (K : Context → Prop) (Rl : Address → Prop) (C : Address → ByteArray)
    (X : Address → Prop) (G : World → Prop) (J : Address → Machine → Prop) (m : Machine) :
    Prop where
  relay : RelayTxInv Rl C J m
  good : AllWorlds G m
  idle : AllWorlds (IdleW X) m
  /-- No frame is sent by an idle account. -/
  callers : ∀ f ∈ m.frame :: m.parents, ¬ X f.msg.caller
  /-- A frame at an idle account runs no code. -/
  idleRun : ∀ f ∈ m.frame :: m.parents, X f.msg.currentTarget → f.code.size = 0
  /-- No creation frame is at an idle account. -/
  createIdle : ∀ f ∈ m.frame :: m.parents, f.kind = .create → ¬ X f.msg.currentTarget
  /-- The transaction's context satisfies `K`. -/
  ctx : K m.ctx

/-- `GuardTxInvK` with no assumption on the context. -/
abbrev GuardTxInv (Rl : Address → Prop) (C : Address → ByteArray) (X : Address → Prop)
    (G : World → Prop) (J : Address → Machine → Prop) (m : Machine) : Prop :=
  GuardTxInvK (fun _ => True) Rl C X G J m

variable {K : Context → Prop} {Rl : Address → Prop} {C : Address → ByteArray} {G : World → Prop}
  {Iss : Address → Machine → Message → Prop} {J : Address → Machine → Prop} {m : Machine}

/-- The world invariant together with the relays' code: the `Good` of `Run.lean`. -/
def GoodC (Rl : Address → Prop) (C : Address → ByteArray) (G : World → Prop) (w : World) :
    Prop := G w ∧ RelayCode Rl C w

theorem goodC_ok (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w') :
    GoodOk Rl (GoodC Rl C G) where
  keep w w' h hk := ⟨hG w w' h.1 hk, fun r hr => (hk r hr).2.trans (h.2 r hr)⟩
  code w h r hr := by
    show (w.code r).size ≠ 0
    rw [h.2 r hr]; exact hC.size r hr
  deleg w h r hr := by
    show delegatedAddress? (w.code r) = none
    rw [h.2 r hr]; exact hC.deleg r hr

/-- A frame with an instruction at its pc is not at an idle account. -/
theorem not_idle_of_instr (h : GuardTxInvK K Rl C X G J m) {b : UInt8}
    (hb : m.frame.code[m.frame.pc]? = some b) : ¬ X m.frame.msg.currentTarget := fun hx => by
  have h0 := h.idleRun _ List.mem_cons_self hx
  rw [getElem?_of_size_le (by omega)] at hb
  cases hb

/-- One instruction keeps the world invariant (relay frames by their obligation, others by the
frame condition) and idleness. -/
theorem instr_good (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvK K Rl C X G Iss r (J r)) (h : GuardTxInvK K Rl C X G J m) {b : UInt8}
    {a : Action} {m' : Machine} (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m')) :
    G m'.world ∧ RelayCode Rl C m'.world ∧ IdleW X m'.world := by
  have hcode : SameCode m.world m'.world := (exec_code _ m).of_run he
  have hn : NonceLe m.world m'.world := (exec_nonce _ m).of_run he
  have hw' : RelayCode Rl C m'.world := h.relay.world.congr hcode
  refine ⟨?_, hw', h.idle.1.congr hcode hn⟩
  by_cases hd : Danger Rl m.frame
  · exact (hJ _ hd.1).good m b a m' (h.relay.cur hd) h.good.1 h.relay.world hb he
  · have hif : InstrFrame m m' := ((exec_frame _ m).of_run he).1
    exact (hif.good (goodC_ok hC hG) hd ⟨h.good.1, h.relay.world⟩).1

/-! ## One step -/

/-- The world a finished frame leaves: its current world, a deposit on the created account,
or its snapshot. -/
theorem frameResult_P {P : World → Prop} {mf : Machine} (o : Outcome) (h1 : P mf.world)
    (h2 : P mf.frame.snapshot.1)
    (h3 : ∀ out, mf.frame.kind = .create → P (setCode mf.world mf.frame.msg.currentTarget out)) :
    P (Program.frameResult mf o).2.1 := by
  rcases frameResult_world mf o with he | ⟨hk, out, he⟩ | he <;> rw [he]
  · exact h1
  · exact h3 out hk
  · exact h2

/-- The invariant of a resumed frame `M.frame`, whose identity is that of `m.frame`. -/
theorem guardTxInv_resume (h : GuardTxInvK K Rl C X G J m) {M : Machine} (res : ChildResult)
    (hw : RelayCode Rl C M.world) (hg : G M.world) (hi : IdleW X M.world)
    (hmsg : M.frame.msg = m.frame.msg) (hk : M.frame.kind = m.frame.kind)
    (hs : M.frame.snapshot = m.frame.snapshot) (hcd : M.frame.code = m.frame.code)
    (hp : M.parents = m.parents) (hc : M.ctx = m.ctx) (hpre : M.precompiles = m.precompiles)
    (hcur : Danger Rl m.frame → J m.frame.msg.currentTarget (resume M res)) :
    GuardTxInvK K Rl C X G J (resume M res) := by
  have hsf := sameFrame_resume M res
  have hstack : ∀ f ∈ (resume M res).frame :: (resume M res).parents,
      f = (resume M res).frame ∨ f ∈ m.parents := by
    intro f hf
    rw [hsf.parents, hp] at hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact .inl rfl
    · exact .inr hf
  refine ⟨relayTxInv_resume h.relay res hw hmsg hk hs hp hc hpre hcur, ⟨hg, ?_⟩, ⟨hi, ?_⟩,
    ?_, ?_, ?_, by rw [hsf.ctx, hc]; exact h.ctx⟩
  · intro f hf
    rcases hstack f hf with rfl | hf
    · rw [hsf.snapshot, hs]; exact h.good.2 _ List.mem_cons_self
    · exact h.good.2 f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases hstack f hf with rfl | hf
    · rw [hsf.snapshot, hs]; exact h.idle.2 _ List.mem_cons_self
    · exact h.idle.2 f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases hstack f hf with rfl | hf
    · rw [hsf.msg, hmsg]; exact h.callers _ List.mem_cons_self
    · exact h.callers f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases hstack f hf with rfl | hf
    · rw [hsf.msg, hmsg, hsf.code, hcd]; exact h.idleRun _ List.mem_cons_self
    · exact h.idleRun f (List.mem_cons_of_mem _ hf)
  · intro f hf
    rcases hstack f hf with rfl | hf
    · rw [hsf.kind, hk, hsf.msg, hmsg]; exact h.createIdle _ List.mem_cons_self
    · exact h.createIdle f (List.mem_cons_of_mem _ hf)

/-- A pushed frame `mc.frame` above the suspended `m'.frame`. -/
theorem guardTxInv_push (h : GuardTxInvK K Rl C X G J m) {m' mc : Machine} (hif : InstrFrame m m')
    (hw : RelayCode Rl C mc.world) (hsnap : RelayCode Rl C mc.frame.snapshot.1)
    (hcreate : mc.frame.kind = .create → ¬ Rl mc.frame.msg.currentTarget)
    (hpar : mc.parents = m'.frame :: m.parents) (hc : mc.ctx = m.ctx)
    (hpre : mc.precompiles = m.precompiles)
    (hcur : Danger Rl mc.frame → J mc.frame.msg.currentTarget mc)
    (hres : Danger Rl m.frame → ResumeOk Rl J m.ctx m.precompiles m'.frame m.parents)
    (hg : G mc.world) (hgs : G mc.frame.snapshot.1) (hi : IdleW X mc.world)
    (his : IdleW X mc.frame.snapshot.1) (hcl : ¬ X mc.frame.msg.caller)
    (hrun : X mc.frame.msg.currentTarget → mc.frame.code.size = 0)
    (hci : mc.frame.kind = .create → ¬ X mc.frame.msg.currentTarget) :
    GuardTxInvK K Rl C X G J mc := by
  have hstack : ∀ f ∈ mc.frame :: mc.parents, f = mc.frame ∨ f = m'.frame ∨ f ∈ m.parents := by
    intro f hf
    rw [hpar] at hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact .inl rfl
    rcases List.mem_cons.1 hf with rfl | hf
    · exact .inr (.inl rfl)
    · exact .inr (.inr hf)
  refine ⟨relayTxInv_push h.relay hif hw hsnap hcreate hpar hc hpre hcur hres, ⟨hg, ?_⟩,
    ⟨hi, ?_⟩, ?_, ?_, ?_, by rw [hc]; exact h.ctx⟩
  · intro f hf
    rcases hstack f hf with rfl | rfl | hf
    · exact hgs
    · rw [hif.same.snapshot]; exact h.good.2 _ List.mem_cons_self
    · exact h.good.2 f (List.mem_cons_of_mem _ hf)
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

/-- **One step keeps the simulation invariant.** -/
theorem guardTxInv_step (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvK K Rl C X G Iss r (J r)) {m m' : Machine}
    (h : GuardTxInvK K Rl C X G J m) (hst : step m = .running m') : GuardTxInvK K Rl C X G J m' := by
  have S := goodC_ok hC hG
  cases hx : exitOf m with
  | some p =>
    obtain ⟨mf, o⟩ := p
    obtain ⟨hst', hif⟩ := step_of_exitOf hx
    have hmf : G mf.world ∧ RelayCode Rl C mf.world ∧ IdleW X mf.world := by
      rcases exitOf_cases hx with rfl | ⟨b, a, hb, he⟩
      · exact ⟨h.good.1, h.relay.world, h.idle.1⟩
      · exact instr_good hC hG hJ h hb he
    rw [hst', finishFrame_eq] at hst
    split at hst
    · cases hst
    rename_i p ps hp
    cases hst
    have hpar : m.parents = p :: ps := hif.same.parents ▸ hp
    have hcr : mf.frame.kind = .create → ¬ Rl mf.frame.msg.currentTarget := by
      rw [hif.same.kind, hif.same.msg]; exact h.relay.create _ List.mem_cons_self
    have hci : mf.frame.kind = .create → ¬ X mf.frame.msg.currentTarget := by
      rw [hif.same.kind, hif.same.msg]; exact h.createIdle _ List.mem_cons_self
    have hsn : mf.frame.snapshot = m.frame.snapshot := hif.same.snapshot
    have hgr : G (Program.frameResult mf o).2.1 :=
      frameResult_P o hmf.1 (hsn ▸ h.good.2 _ List.mem_cons_self) fun out hk =>
        hG _ _ hmf.1 fun r hr => keep_setCode fun he => hcr hk (he ▸ hr)
    have hir : IdleW X (Program.frameResult mf o).2.1 :=
      frameResult_P o hmf.2.2 (hsn ▸ h.idle.2 _ List.mem_cons_self) fun _ hk =>
        hmf.2.2.setCode (hci hk)
    have hwr := RelayCode.frameResult h.relay hmf.2.1
      (.inr ⟨hif.same.msg, hif.same.kind, hif.same.snapshot⟩) o
    -- The resumed parent `p`.
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
    have hsusp := h.relay.susp
    rw [hpar] at hsusp
    refine ⟨⟨hwr, ?_, ?_, ?_, ?_, ?_⟩, ⟨hgr, ?_⟩, ⟨hir, ?_⟩, ?_, ?_, ?_,
      by show K (resume M (Program.frameResult mf o).1).ctx
         rw [hsf.ctx, show M.ctx = mf.ctx from rfl, hif.same.ctx]; exact h.ctx⟩
    · intro f hf
      rcases hmem f hf with rfl | hf
      · rw [hsf.snapshot]; exact h.relay.snapshots p (hps p List.mem_cons_self)
      · exact h.relay.snapshots f (hps f (List.mem_cons_of_mem _ hf))
    · intro f hf
      rcases hmem f hf with rfl | hf
      · rw [hsf.kind, hsf.msg]; exact h.relay.create p (hps p List.mem_cons_self)
      · exact h.relay.create f (hps f (List.mem_cons_of_mem _ hf))
    · intro hd
      show J (resume M (Program.frameResult mf o).1).frame.msg.currentTarget
        (resume M (Program.frameResult mf o).1)
      rw [hsf.msg]
      exact hsusp.1 ((danger_congr hsf.msg).1 hd) _ _ rfl rfl hif.same.ctx hif.same.precompiles
    · show Suspended Rl J (resume M (Program.frameResult mf o).1).ctx
        (resume M (Program.frameResult mf o).1).precompiles
        (resume M (Program.frameResult mf o).1).parents
      rw [hsf.parents, hsf.ctx, hsf.precompiles]
      show Suspended Rl J mf.ctx mf.precompiles ps
      rw [hif.same.ctx, hif.same.precompiles]; exact hsusp.2
    · show (resume M (Program.frameResult mf o).1).precompiles =
        PrecompileImpl.standard (resume M (Program.frameResult mf o).1).ctx
      rw [hsf.ctx, hsf.precompiles]
      show mf.precompiles = PrecompileImpl.standard mf.ctx
      rw [hif.same.ctx, hif.same.precompiles]; exact h.relay.pre
    · intro f hf
      rcases hmem f hf with rfl | hf
      · rw [hsf.snapshot]; exact h.good.2 p (hps p List.mem_cons_self)
      · exact h.good.2 f (hps f (List.mem_cons_of_mem _ hf))
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
  | none =>
    obtain ⟨b, hb, a, m₁, he, hcase⟩ := step_exec hx hst
    have hpost := (exec_frame _ m).of_run he
    have hif : InstrFrame m m₁ := hpost.1
    obtain ⟨hg₁, hw₁, hi₁⟩ := instr_good hC hG hJ h hb he
    have hnx : ¬ X m.frame.msg.currentTarget := not_idle_of_instr h hb
    have hresume : ((∃ req, a = .call req) ∨ ∃ msg, a = .create msg) →
        (∀ req, a = .call req → precompileOf m₁.precompiles req.msg = none) → Danger Rl m.frame →
        ResumeOk Rl J m.ctx m.precompiles m₁.frame m.parents := by
      intro ha hnp hd _ M res hM hMp hMc hMpre
      rw [hif.same.msg]
      refine (hJ _ hd.1).resume m b a m₁ (h.relay.cur hd) h.good.1 h.relay.world hb he ha M res hM
        hMp hMc hMpre fun req hreq hpre => ?_
      -- A real child: no precompile answered.
      subst hreq
      exact absurd (hnp req rfl) hpre
    rcases hcase with ⟨rfl, rfl⟩ | ⟨req, rfl, rfl⟩ | ⟨msg, rfl, rfl⟩
    · -- An instruction continuing the frame.
      have hstack : ∀ f ∈ m'.frame :: m'.parents, f = m'.frame ∨ f ∈ m.parents := by
        intro f hf
        rw [hif.same.parents] at hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact .inl rfl
        · exact .inr hf
      refine ⟨⟨hw₁, ?_, ?_, ?_, ?_, ?_⟩, ⟨hg₁, ?_⟩, ⟨hi₁, ?_⟩, ?_, ?_, ?_,
        by rw [hif.same.ctx]; exact h.ctx⟩
      · intro f hf
        rcases hstack f hf with rfl | hf
        · rw [hif.same.snapshot]; exact h.relay.snapshots _ List.mem_cons_self
        · exact h.relay.snapshots f (List.mem_cons_of_mem _ hf)
      · intro f hf
        rcases hstack f hf with rfl | hf
        · rw [hif.same.kind, hif.same.msg]; exact h.relay.create _ List.mem_cons_self
        · exact h.relay.create f (List.mem_cons_of_mem _ hf)
      · intro hd
        have hd' := (danger_congr hif.same.msg).1 hd
        rw [hif.same.msg]
        exact (hJ _ hd'.1).next m b m' (h.relay.cur hd') h.good.1 h.relay.world hb he
      · rw [hif.same.parents, hif.same.ctx, hif.same.precompiles]; exact h.relay.susp
      · rw [hif.same.ctx, hif.same.precompiles]; exact h.relay.pre
      · intro f hf
        rcases hstack f hf with rfl | hf
        · rw [hif.same.snapshot]; exact h.good.2 _ List.mem_cons_self
        · exact h.good.2 f (List.mem_cons_of_mem _ hf)
      · intro f hf
        rcases hstack f hf with rfl | hf
        · rw [hif.same.snapshot]; exact h.idle.2 _ List.mem_cons_self
        · exact h.idle.2 f (List.mem_cons_of_mem _ hf)
      · intro f hf
        rcases hstack f hf with rfl | hf
        · rw [hif.same.msg]; exact h.callers _ List.mem_cons_self
        · exact h.callers f (List.mem_cons_of_mem _ hf)
      · intro f hf
        rcases hstack f hf with rfl | hf
        · rw [hif.same.msg, hif.same.code]; exact h.idleRun _ List.mem_cons_self
        · exact h.idleRun f (List.mem_cons_of_mem _ hf)
      · intro f hf
        rcases hstack f hf with rfl | hf
        · rw [hif.same.kind, hif.same.msg]; exact h.createIdle _ List.mem_cons_self
        · exact h.createIdle f (List.mem_cons_of_mem _ hf)
    · -- A call.
      have hcall : CallOk m m₁ req := hpost.2
      have hids : CallIds m req := (exec_ids _ m).of_run he req rfl
      have htgt : CallTarget m req := (exec_target _ m).of_run he req rfl
      by_cases hpc : precompileOf m₁.precompiles req.msg = none
      · -- A child frame is pushed.
        rw [launchCall_none hpc]
        have hcl : ¬ X req.msg.caller := by
          rcases hids.1 with he' | ⟨he', -⟩ <;> rw [he']
          · exact hnx
          · exact h.callers _ List.mem_cons_self
        have hrun : X req.msg.currentTarget → req.msg.code.size = 0 := by
          intro hxt
          rcases hids.2 with he' | ⟨t, ht, he'⟩
          · exact absurd (he' ▸ hxt) hnx
          · obtain ⟨t', ht', hct⟩ := htgt
            rw [ht] at ht'
            cases ht'
            have h0 := (h.idle.1 _ hxt).1
            rw [he'] at h0
            have hnd : delegatedAddress? (m.world.code (Word.toAddress t)) = none := by
              cases hdl : delegatedAddress? (m.world.code (Word.toAddress t)) with
              | none => rfl
              | some d => exact absurd h0 (delegated_size hdl)
            rw [(hct (.inr hnd)).2.1]; exact h0
        refine guardTxInv_push (mc := pushCall m₁ req) h hif (hw₁.congr (pushCall_code _ _)) hw₁
          (fun hk => by cases hk) (by simp only [pushCall]; rw [hif.same.parents]) hif.same.ctx
          hif.same.precompiles ?_
          (hresume (.inl ⟨req, rfl⟩) fun req' h => by cases h; exact hpc)
          (S.transferValue ⟨hg₁, hw₁⟩ req.msg).1 hg₁
          (hi₁.congr (code_transferValue _ _) (nonce_transferValue _ _)) hi₁ hcl hrun
          (fun hk => by cases hk)
        intro hd
        show J req.msg.currentTarget (pushCall m₁ req)
        have hrel : Rl req.msg.currentTarget := hd.1
        have hst' : req.msg.isStatic = false := hd.2
        obtain ⟨hps, hcur⟩ := hcall.nonstatic hst'
        have hreq : Requests m req.msg := ⟨b, _, m₁, hb, he, .inl ⟨req, rfl, rfl⟩⟩
        refine (hJ _ hrel).start _ ⟨⟨⟨_, _, rfl⟩, rfl, hst', ?_, hw₁.congr (pushCall_code _ _),
          ?_⟩, (S.transferValue ⟨hg₁, hw₁⟩ req.msg).1, hg₁,
          fun r hr => keep_transferValue (S.code _ ⟨hg₁, hw₁⟩ r hr),
          hi₁.congr (code_transferValue _ _) (nonce_transferValue _ _), hcl,
          .inr ⟨m, hif.same.ctx.symm, hps, hreq, hids.1, fun hr => ?_⟩,
          by show K m₁.ctx; rw [hif.same.ctx]; exact h.ctx⟩
        · by_cases heq : req.msg.currentTarget = m.frame.msg.currentTarget
          · right
            have hdm : Danger Rl m.frame := ⟨heq ▸ hrel, hps⟩
            refine ⟨m, hif.same.ctx.symm, heq.symm, hps, hreq, ?_⟩
            show Iss req.msg.currentTarget m req.msg
            rw [heq]
            exact (hJ _ (heq ▸ hrel)).issue m req.msg (heq ▸ h.relay.cur hdm) h.good.1
              h.relay.world hreq
          · left
            obtain ⟨-, hc⟩ := hcur.resolve_left heq
            have hwr := h.relay.world _ hrel
            obtain ⟨hc1, hc2, -⟩ := hc (by rw [hwr]; exact hC.deleg _ hrel)
            exact ⟨by show req.msg.code = _; rw [hc1, hwr], hc2⟩
        · show m₁.precompiles = PrecompileImpl.standard m₁.ctx
          rw [hif.same.ctx, hif.same.precompiles]; exact h.relay.pre
        · exact (hJ _ hr).issue m req.msg (h.relay.cur ⟨hr, hps⟩) h.good.1 h.relay.world hreq
      · -- A precompile answers the call.
        obtain ⟨w, t, res, hl, hwv⟩ := launchCall_some hpc
        rw [hl]
        have hwM : GoodC Rl C G w ∧ IdleW X w := by
          rcases hwv with rfl | rfl
          · exact ⟨S.transferValue ⟨hg₁, hw₁⟩ _,
              hi₁.congr (code_transferValue _ _) (nonce_transferValue _ _)⟩
          · exact ⟨⟨hg₁, hw₁⟩, hi₁⟩
        refine guardTxInv_resume h res hwM.1.2 hwM.1.1 hwM.2 hif.same.msg hif.same.kind
          hif.same.snapshot hif.same.code hif.same.parents hif.same.ctx hif.same.precompiles ?_
        intro hd
        exact (hJ _ hd.1).resume m b _ m₁ (h.relay.cur hd) h.good.1 h.relay.world hb he
          (.inl ⟨req, rfl⟩) _ res rfl hif.same.parents hif.same.ctx hif.same.precompiles
          fun req' h' _ => by cases h'; exact hl.symm
    · -- A creation: never of a relay, never at an idle account.
      have hcr : CreateOk m m₁ msg := hpost.2
      have hcids : CreateIds m msg := (exec_create_ids _ m).of_run he msg rfl
      have hnr : ¬ Rl msg.currentTarget := fun hr =>
        hC.size _ hr (by rw [← hw₁ _ hr]; exact hcr.code)
      have hnx' : ¬ X msg.currentTarget := h.idle.1.not_deployable hcids.2
      have hwc : SameCode m₁.world (launchCreate m₁ msg).world :=
        (code_incrementNonce _ _).trans (code_transferValue _ _)
      have hnc : NonceLe m₁.world (launchCreate m₁ msg).world :=
        (nonce_incrementNonce _ _).trans (nonce_transferValue _ _)
      have hgc : G (launchCreate m₁ msg).world := by
        simp only [launchCreate, beginCreate]
        refine hG _ _ hg₁ fun r hr => (keep_incrementNonce (S.code _ ⟨hg₁, hw₁⟩ r hr)).trans
          (keep_transferValue ?_)
        rw [code_incrementNonce _ _ r]; exact S.code _ ⟨hg₁, hw₁⟩ r hr
      refine guardTxInv_push (mc := launchCreate m₁ msg) h hif (hw₁.congr hwc) hw₁ (fun _ => hnr)
        (by simp only [launchCreate]; rw [hif.same.parents]) hif.same.ctx hif.same.precompiles
        (fun hd => absurd hd.1 hnr) (hresume (.inr ⟨msg, rfl⟩) fun _ h => by cases h) hgc hg₁ (hi₁.congr hwc hnc) hi₁
        (by show ¬ X msg.caller; rw [hcids.1]; exact hnx) (fun hx' => absurd hx' hnx')
        (fun _ => hnx')

theorem guardTxInv_stepN (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvK K Rl C X G Iss r (J r)) :
    ∀ (n : Nat) {m m' : Machine}, GuardTxInvK K Rl C X G J m → stepN n m = .running m' →
      GuardTxInvK K Rl C X G J m'
  | 0, _, _, h, hst => by simp only [stepN_zero, StepResult.running.injEq] at hst; exact hst ▸ h
  | n + 1, m, m', h, hst => by
    cases hs : step m with
    | done r =>
      rw [show n + 1 = 1 + n by omega, stepN_add_of_done (by rw [stepN_one, hs])] at hst
      cases hst
    | running m₁ =>
      rw [stepN_succ_of_running hs] at hst
      exact guardTxInv_stepN hC hG hJ n (guardTxInv_step hC hG hJ h hs) hst

/-- **The last step**: a finished top-level frame leaves a world satisfying `G`. -/
theorem guardTxInv_done (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvK K Rl C X G Iss r (J r)) {m : Machine} {r : MessageResult}
    (h : GuardTxInvK K Rl C X G J m) (hst : step m = .done r) : G r.world := by
  cases hx : exitOf m with
  | none =>
    rcases step_of_exitOf_none hx with ⟨m', hs, -⟩ | ⟨m', req, hs, -⟩ | ⟨m', msg, hs, -⟩ <;>
      rw [hs] at hst <;> cases hst
  | some p =>
    obtain ⟨mf, o⟩ := p
    obtain ⟨hst', hif⟩ := step_of_exitOf hx
    have hmf : G mf.world ∧ RelayCode Rl C mf.world ∧ IdleW X mf.world := by
      rcases exitOf_cases hx with rfl | ⟨b, a, hb, he⟩
      · exact ⟨h.good.1, h.relay.world, h.idle.1⟩
      · exact instr_good hC hG hJ h hb he
    have hcr : mf.frame.kind = .create → ¬ Rl mf.frame.msg.currentTarget := by
      rw [hif.same.kind, hif.same.msg]; exact h.relay.create _ List.mem_cons_self
    have hgr : G (Program.frameResult mf o).2.1 :=
      frameResult_P o hmf.1 (hif.same.snapshot ▸ h.good.2 _ List.mem_cons_self) fun out hk =>
        hG _ _ hmf.1 fun r hr => keep_setCode fun he => hcr hk (he ▸ hr)
    rw [hst', finishFrame_eq] at hst
    split at hst
    · cases hst
      unfold topLevelResult
      split <;> exact hgr
    · cases hst

/-- From a machine satisfying the invariant, every finished run ends in a world satisfying
`G`. -/
theorem guard_run (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvK K Rl C X G Iss r (J r)) :
    ∀ (fuel : Nat) {m : Machine} {r : MessageResult}, GuardTxInvK K Rl C X G J m →
      run fuel m = .ok r → G r.world
  | 0, _, _, _, hr => by cases hr
  | fuel + 1, m, r, h, hr => by
    simp only [run] at hr
    cases hs : step m with
    | done r' => rw [hs] at hr; cases hr; exact guardTxInv_done hC hG hJ h hs
    | running m' => rw [hs] at hr; exact guard_run hC hG hJ fuel (guardTxInv_step hC hG hJ h hs) hr

/-! ## Top-level message calls -/

/-- The message a top-level call starts with, for the simulation: `TopOk`, a sender that is
not idle, and no code when it calls an idle account. -/
structure GuardTop (Rl : Address → Prop) (X : Address → Prop) (w : World) (msg : Message) :
    Prop where
  top : TopOk Rl w msg
  caller : ¬ X msg.caller
  idle : X msg.currentTarget → msg.target = some msg.currentTarget → msg.code.size = 0

theorem guardTxInv_start (hC : RelayCodeOk Rl C) (hG : ∀ w w', G w → KeepP Rl w w' → G w')
    (hJ : ∀ r, Rl r → GuardInvK K Rl C X G Iss r (J r)) {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {m₀ : Machine}
    (hw : RelayCode Rl C w) (hg : G w) (hi : IdleW X w) (hmsg : GuardTop Rl X w msg)
    (hin : initMachine (PrecompileImpl.standard ctx) ctx w tr msg = .inr m₀)
    (hK : K ctx := by trivial) :
    GuardTxInvK K Rl C X G J m₀ := by
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
      refine ⟨⟨hw.congr hwc, ?_, ?_, fun hd => absurd hd.1 hnr, trivial, rfl⟩, ⟨hgc, ?_⟩,
        ⟨hi.congr hwc ((nonce_incrementNonce _ _).trans (nonce_transferValue _ _)), ?_⟩,
        ?_, ?_, ?_, hK⟩ <;>
        intro f hf <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hf <;> subst hf
      · exact hw
      · exact fun _ => hnr
      · exact hg
      · exact hi
      · exact hmsg.caller
      · exact fun hx => absurd hx hnx
      · exact fun _ => hnx
  · rename_i a hsome
    have htgt : msg.target = some msg.currentTarget := by
      rcases hmsg.top.target with h | h
      · exact h
      · rw [hsome] at h; cases h
    split at hin
    · cases hin
    · cases hin
      refine ⟨⟨hw.congr (code_transferValue _ _), ?_, ?_, ?_, trivial, rfl⟩,
        ⟨(S.transferValue ⟨hg, hw⟩ msg).1, ?_⟩,
        ⟨hi.congr (code_transferValue _ _) (nonce_transferValue _ _), ?_⟩, ?_, ?_, ?_, hK⟩
      · intro f hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        subst hf; exact hw
      · intro f hf hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        subst hf; cases hk
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
      all_goals intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf; subst hf
      · exact hg
      · exact hi
      · exact hmsg.caller
      · exact fun hx => hmsg.idle hx htgt
      · intro hk; cases hk

/-- `GuardTop` survives top-level delegation (an idle target holds no designator). -/
theorem guardTop_delegation {ctx : Context} {isPre : Address → Bool} {w : World} {msg : Message}
    (hC : RelayCodeOk Rl C) (hw : RelayCode Rl C w)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : GuardTop Rl X w msg) :
    ∃ msg', applyTopLevelDelegation ctx isPre w msg = (w, msg', 0) ∧ GuardTop Rl X w msg' := by
  obtain ⟨msg', hdl, hcur, hcaller, htarget, hdepth, -, -, hsame⟩ :=
    applyTopLevelDelegation_spec (isPre := isPre) (w := w) (msg := msg) hdeleg
  refine ⟨msg', hdl, ⟨⟨hdepth.trans hmsg.top.depth, hcaller ▸ hmsg.top.caller, ?_, ?_⟩,
    hcaller ▸ hmsg.caller, ?_⟩⟩
  · rw [htarget, hcur]; exact hmsg.top.target
  · intro hp ht
    rw [hcur] at hp ht ⊢
    rw [htarget] at ht
    obtain ⟨hc, hca⟩ := hmsg.top.code hp ht
    have := hsame (by rw [hc, hw _ hp]; exact hC.deleg _ hp)
    subst this
    exact ⟨hc, hca⟩
  · intro hx ht
    rw [hcur] at hx
    rw [htarget, hcur] at ht
    have h0 := hmsg.idle hx ht
    have hnd : delegatedAddress? msg.code = none := by
      cases hdl : delegatedAddress? msg.code with
      | none => rfl
      | some d => exact absurd h0 (delegated_size hdl)
    rw [hsame hnd]; exact h0

/-- **A guarded message call keeps the world invariant.** From a world satisfying `G`, where
the relays hold their code (not empty, no designator) and the idle accounts are idle, before
Prague or without EIP-7702 authorizations: if each relay's frames keep an invariant
(`GuardInv`), a top-level call from a sender that is neither a relay nor idle ends in a world
satisfying `G`. -/
theorem processMessageCall_guard (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w') (hJ : ∀ r, Rl r → GuardInvK K Rl C X G Iss r (J r))
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message} (hw : RelayCode Rl C w)
    (hg : G w) (hi : IdleW X w) (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : GuardTop Rl X w msg) {fuel : Nat} {r : MessageResult}
    (hr : processMessageCall fuel ctx w tr msg = .ok r) (hK : K ctx := by trivial) :
    G r.world := by
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
      exact guard_run hC hG hJ fuel (guardTxInv_start hC hG hJ hw hg hi hmsg' hin hK) hrun

/-- **What guarded relays issue**: every message requested by a non-static frame at a relay,
in a guarded message call, satisfies that relay's `Iss`. -/
theorem processMessageCall_guard_issues (hC : RelayCodeOk Rl C)
    (hG : ∀ w w', G w → KeepP Rl w w' → G w') (hJ : ∀ r, Rl r → GuardInvK K Rl C X G Iss r (J r))
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message} (hw : RelayCode Rl C w)
    (hg : G w) (hi : IdleW X w) (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : GuardTop Rl X w msg) {m : Machine} (hm : Reaches ctx w tr msg m)
    (hd : Danger Rl m.frame) {c : Message} (hc : Requests m c) (hK : K ctx := by trivial) :
    Iss m.frame.msg.currentTarget m c := by
  obtain ⟨msg', hdl, hmsg'⟩ := guardTop_delegation
    (isPre := (PrecompileImpl.standard ctx).isPrecompile) hC hw hdeleg hmsg
  obtain ⟨m₀, n, hs, hn⟩ := hm
  unfold StartsAt at hs
  rw [hdl] at hs
  have h := guardTxInv_stepN hC hG hJ n (guardTxInv_start hC hG hJ hw hg hi hmsg' hs hK) hn
  exact (hJ _ hd.1).issue m c (h.relay.cur hd) h.good.1 h.relay.world hc

end EvmLogic.Program.Nested
