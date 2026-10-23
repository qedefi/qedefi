import Examples.Actor.Bytecode.Certify
import EvmLogic.Program.Nested.Guard

/-!
# Only the owner can upgrade: the upgrade guard on bytecode

The deployed OpenZeppelin v5.7.0 contracts: a `TransparentUpgradeableProxy` at `px` whose
immutable admin is the `ProxyAdmin` at `pa`, owned by `o` (slot `0`), with the implementation
`ActorImpl` at `ia` (ERC-1967 implementation slot). `impl_kept`: **in any transaction not sent
by the owner, from an owner that is an externally owned account, the implementation slot and the
ProxyAdmin's owner are unchanged** — whatever the transaction does: any calldata, any value,
calls into the proxy at any depth, reentrancy, other contracts calling ProxyAdmin, reverts of
enclosing frames.

This is `EvmLogic.Program.Nested.processMessageCall_guard` with:

- relays the proxy, ProxyAdmin and the implementation (their code is fixed);
- the world invariant `G`: slot `implSlot` of `px` holds `ia`, slot `0` of `pa` holds `o`;
- the idle principal `o` (no code, nonce `≠ 0`: an EOA that has sent a transaction), so no frame
  has sender `o`;
- frame invariants read off the guarded certificates of `Certify.lean`: a ProxyAdmin frame's
  sender is not the owner, so it requests nothing and writes nothing (`inv_pa`); a proxy frame's
  sender is not ProxyAdmin (the only account that could have requested it is the top-level
  sender or some non-ProxyAdmin frame, since ProxyAdmin requests nothing), so it takes the
  non-admin branch, writes nothing and only delegatecalls the implementation (`inv_px`); the
  implementation writes only its slot `0` (`inv_ia`).

In actor-model terms (`QEDefi.Actor.Lib.Ownable`): the consenting keys `T = {sender}` do not
contain the owner, so they derive no upgrade; here that is proved of the bytecode, for every
reachable machine of the EVM. The implementation enters only through its own certificate
(`ActorImpl` writes slot `0` only): an implementation that could write the implementation slot
would itself be an upgrade path.
-/

namespace Examples.Actor.ProxyGuard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open EvmLogic.AbsInt EvmLogic.AbsInt.Guard Examples.OpenZeppelin.Contracts EvmLogic.Solidity

/-- The ERC-1967 implementation slot. -/
abbrev implSlot : Word := OzTransparentProxy.implementationSlot

/-- A deployment: proxy, ProxyAdmin, implementation (distinct), and ProxyAdmin's owner. -/
structure Dep where
  px : Address
  pa : Address
  ia : Address
  o : Address
  px_pa : px ≠ pa
  px_ia : px ≠ ia
  pa_ia : pa ≠ ia

namespace Dep

variable (D : Dep)

/-- The code of each relay. -/
def code (a : Address) : ByteArray :=
  if a = D.px then OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩
  else if a = D.pa then OzProxyAdmin.runtimeCode else ActorImpl.runtimeCode

def Rl (a : Address) : Prop := a = D.px ∨ a = D.pa ∨ a = D.ia

def X (a : Address) : Prop := a = D.o

/-- **The protected state**: the implementation and the owner. -/
def G (w : World) : Prop :=
  w.sload D.px implSlot = Word.ofAddress D.ia ∧ w.sload D.pa 0 = Word.ofAddress D.o

/-- What relays issue: only the proxy, and only calls running the implementation's code. -/
def Iss (r : Address) (_ : Machine) (c : Message) : Prop :=
  r = D.px ∧ c.code = ActorImpl.runtimeCode

/-- Valuations: ProxyAdmin (sender, owner), the proxy (admin; sender, implementation). -/
def envPA (c : Address) : Env := ⟨fun _ => 0, fun i => if i = 0 then c else D.o⟩
def envPX (c : Address) : Env := ⟨fun _ => D.pa, fun i => if i = 0 then c else D.ia⟩
def envIA : Env := ⟨fun _ => 0, fun _ => 0⟩

/-- A frame running the implementation. -/
def Jia (m : Machine) : Prop := m.frame.code = ActorImpl.runtimeCode ∧ GInCert envIA tIA m

def Jpa (m : Machine) : Prop :=
  m.frame.msg.currentTarget = D.pa ∧ m.frame.code = OzProxyAdmin.runtimeCode ∧
    m.frame.msg.caller ≠ D.o ∧ GInCert (D.envPA m.frame.msg.caller) tPA m

def Jpx (m : Machine) : Prop :=
  m.frame.msg.currentTarget = D.px ∧
    ((m.frame.code = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩ ∧ m.frame.msg.caller ≠ D.pa ∧
      GInCert (D.envPX m.frame.msg.caller) tPX m) ∨ Jia m)

def Jim (m : Machine) : Prop := m.frame.msg.currentTarget = D.ia ∧ Jia m

/-- The frame invariants. -/
def J (r : Address) : Machine → Prop :=
  if r = D.pa then D.Jpa else if r = D.px then D.Jpx else D.Jim

theorem code_px : D.code D.px = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩ := by simp [code]
theorem code_pa : D.code D.pa = OzProxyAdmin.runtimeCode := by
  simp [code, Ne.symm D.px_pa]
theorem code_ia : D.code D.ia = ActorImpl.runtimeCode := by
  simp [code, Ne.symm D.px_ia, Ne.symm D.pa_ia]

theorem J_pa : D.J D.pa = D.Jpa := by simp [J]
theorem J_px : D.J D.px = D.Jpx := by simp [J, D.px_pa]
theorem J_ia : D.J D.ia = D.Jim := by simp [J, Ne.symm D.pa_ia, Ne.symm D.px_ia]

/-! ## The world -/

theorem size_proxy (i : OzTransparentProxy.Immutables) :
    (OzTransparentProxy.runtimeCodeWith i).size = 1005 := by
  rw [OzTransparentProxy.runtimeCodeWith, size_patchWords, OzTransparentProxy.size_runtimeCode]

theorem deleg_none {c : ByteArray} (h : c.size ≠ 23) : delegatedAddress? c = none := by
  simp [delegatedAddress?, isValidDelegation, eoaDelegatedCodeLength, h]

theorem codeOk : RelayCodeOk D.Rl D.code where
  size r hr := by
    rcases hr with rfl | rfl | rfl
    · rw [code_px, size_proxy]; decide
    · rw [code_pa, OzProxyAdmin.size_runtimeCode]; decide
    · rw [code_ia, ActorImpl.size_runtimeCode]; decide
  deleg r hr := by
    rcases hr with rfl | rfl | rfl
    · rw [code_px]; exact deleg_none (by rw [size_proxy]; decide)
    · rw [code_pa]; exact deleg_none (by rw [OzProxyAdmin.size_runtimeCode]; decide)
    · rw [code_ia]; exact deleg_none (by rw [ActorImpl.size_runtimeCode]; decide)

theorem G_keep : ∀ w w', D.G w → KeepP D.Rl w w' → D.G w' := fun _ _ h hk =>
  ⟨((hk _ (.inl rfl)).sload' _).trans h.1, ((hk _ (.inr (.inl rfl))).sload' _).trans h.2⟩

theorem implSlot_ne_zero : implSlot.toNat ≠ 0 := by decide

/-- **The world invariant is kept by an instruction** that writes, if anything, a slot `0` at an
account other than ProxyAdmin. -/
theorem G_step {m m' : Machine} {b : UInt8} {a : Action} (hG : D.G m.world)
    (hrc : RelayCode D.Rl D.code m.world)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m'))
    (hss : Opcode.decode m.ctx.fork b = .sstore → ∃ k v, k.toNat = 0 ∧
      m.frame.msg.currentTarget ≠ D.pa ∧
      m'.world = m.world.sstore m.frame.msg.currentTarget k v) : D.G m'.world := by
  by_cases hs : Opcode.decode m.ctx.fork b = .sstore
  · obtain ⟨k, v, hk, hne, hw⟩ := hss hs
    rw [hw]
    refine ⟨?_, ?_⟩
    · by_cases ht : D.px = m.frame.msg.currentTarget
      · rw [← ht, World.sload_sstore_ne_key _ _ _ (fun e => implSlot_ne_zero (by rw [e]; exact hk))]
        exact hG.1
      · rw [World.sload_sstore_ne_addr _ _ _ _ ht]; exact hG.1
    · rw [World.sload_sstore_ne_addr _ _ _ _ (Ne.symm hne)]; exact hG.2
  · have hslot := (exec_slot _ hs m D.px implSlot).of_run he
    have hslot' := (exec_slot _ hs m D.pa 0).of_run he
    refine ⟨?_, ?_⟩
    · rw [hslot (by rw [hrc _ (.inl rfl), code_px, size_proxy]; decide)]; exact hG.1
    · rw [hslot' (by rw [hrc _ (.inr (.inl rfl)), code_pa, OzProxyAdmin.size_runtimeCode]; decide)]
      exact hG.2

/-! ## Facts the certificates assume -/

theorem slotAtom_pa {k i : Nat} (h : cfgPA.slotAtom k = some i) : k = 0 ∧ i = 1 := by
  simp only [Cfg.slotAtom, cfgPA, List.find?] at h
  split at h <;> simp_all

theorem slotAtom_px {k i : Nat} (h : cfgPX.slotAtom k = some i) :
    k = implSlot.toNat ∧ i = 1 := by
  simp only [Cfg.slotAtom, cfgPX, List.find?] at h
  split at h <;> simp_all

theorem envOk_pa {m : Machine} (ht : m.frame.msg.currentTarget = D.pa)
    (hc : m.frame.msg.caller ≠ D.o) (hG : D.G m.world) :
    EnvOk (D.envPA m.frame.msg.caller) cfgPA m where
  caller i hi := by
    simp only [cfgPA, Option.some.injEq] at hi; subst hi; rfl
  slots k i hk key hkey := by
    obtain ⟨rfl, rfl⟩ := slotAtom_pa hk
    have : key = 0 := BitVec.eq_of_toNat_eq (by simpa using hkey)
    rw [this, ht]; exact hG.2
  distinct a b hab := by
    simp only [cfgPA, List.mem_singleton, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨_, _, rfl, rfl, by simpa [envPA] using hc⟩

theorem envOk_px {m : Machine} (ht : m.frame.msg.currentTarget = D.px)
    (hc : m.frame.msg.caller ≠ D.pa) (hG : D.G m.world) :
    EnvOk (D.envPX m.frame.msg.caller) cfgPX m where
  caller i hi := by
    simp only [cfgPX, Option.some.injEq] at hi; subst hi; rfl
  slots k i hk key hkey := by
    obtain ⟨rfl, rfl⟩ := slotAtom_px hk
    have : key = implSlot := BitVec.eq_of_toNat_eq hkey
    rw [this, ht]; exact hG.1
  distinct a b hab := by
    simp only [cfgPX, List.mem_singleton, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨_, _, rfl, rfl, by simpa [envPX] using hc⟩

theorem envOk_ia (m : Machine) : EnvOk envIA cfgIA m where
  caller i hi := by simp [cfgIA] at hi
  slots k i hk := by simp [cfgIA, Cfg.slotAtom] at hk
  distinct a b hab := by simp [cfgIA] at hab

/-! ## Instructions of described frames -/

/-- A frame of a certificate with no allowed call requests nothing. -/
theorem no_requests {ν : Env} {cfg : Cfg} {code : ByteArray} {t : GTree}
    (hc : GCert ν cfg code [] t) (hno : ∀ a, cfg.callAllowed a = false) {m : Machine}
    (hcode : m.frame.code = code) (h : GInCert ν t m) {c : Message} (hr : Requests m c) :
    False := by
  obtain ⟨b, a, m', hb, he, (⟨req, rfl, -⟩ | rfl)⟩ := hr
  · obtain ⟨-, a, -, ha, -⟩ := ginCert_call hc hcode h hb he
    rw [hno] at ha; cases ha
  · exact ginCert_no_create hc hcode h hb he

/-- The frame identity and code are kept by an instruction continuing the frame. -/
theorem same_next {m m' : Machine} {b : UInt8}
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m')) :
    m'.frame.msg = m.frame.msg ∧ m'.frame.code = m.frame.code := by
  have hif : InstrFrame m m' := ((exec_frame _ m).of_run he).1
  exact ⟨hif.same.msg, hif.same.code⟩

/-- … and by a resumption after a child. -/
theorem same_resume {m m' : Machine} {b : UInt8} {a : Action}
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m')) {M : Machine}
    (res : ChildResult) (hM : M.frame = m'.frame) :
    (resume M res).frame.msg = m.frame.msg ∧ (resume M res).frame.code = m.frame.code := by
  have hif : InstrFrame m m' := ((exec_frame _ m).of_run he).1
  refine ⟨?_, ?_⟩
  · rw [(sameFrame_resume M res).msg, hM, hif.same.msg]
  · rw [(resume_frame M res).2.2, hM, hif.same.code]

/-- A frame running the implementation keeps `G` (it writes only slot `0`, never at ProxyAdmin). -/
theorem Jia_good {m m' : Machine} {b : UInt8} {a : Action} (hJ : Jia m)
    (ht : m.frame.msg.currentTarget ≠ D.pa) (hG : D.G m.world)
    (hrc : RelayCode D.Rl D.code m.world) (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m')) : D.G m'.world := by
  refine D.G_step hG hrc he fun hs => ?_
  obtain ⟨k, v, r, av, -, hw, hav, hk⟩ := ginCert_sstore (ia_cert _) hJ.1 hJ.2 hb hs he
  simp only [cfgIA, beq_iff_eq] at hav
  subst hav
  exact ⟨k, v, hk, ht, hw⟩

/-! ## The frame obligations -/

theorem fresh_frame {m : Machine}
    (h : ∃ o s, m.frame = Frame.init m.frame.msg (.call o s) m.frame.snapshot) :
    m.frame.pc = 0 ∧ m.frame.stack = [] ∧ m.frame.code = m.frame.msg.code := by
  obtain ⟨o, s, h⟩ := h
  rw [h]; exact ⟨rfl, rfl, rfl⟩

theorem iss_not_pa {mp : Machine} {c : Message} : ¬ D.Iss D.pa mp c := fun h => D.px_pa h.1.symm

theorem iss_not_ia {mp : Machine} {c : Message} : ¬ D.Iss D.ia mp c := fun h => D.px_ia h.1.symm

/-- **ProxyAdmin, for any sender but the owner**: nothing requested, nothing written. -/
theorem inv_pa : GuardInv D.Rl D.code D.X D.G D.Iss D.pa D.Jpa where
  start m hs := by
    obtain ⟨hpc, hst, hcd⟩ := fresh_frame hs.base.fresh
    have hcode : m.frame.code = OzProxyAdmin.runtimeCode := by
      rcases hs.base.entry with ⟨h1, -⟩ | ⟨mp, -, -, -, -, hiss⟩
      · rw [hcd, h1, code_pa]
      · exact absurd hiss D.iss_not_pa
    exact ⟨hs.base.target, hcode, hs.caller, ginCert_init (pa_cert _) hpc hst⟩
  issue m c hJ _ _ hr :=
    (no_requests (pa_cert _) (fun _ => rfl) hJ.2.1 hJ.2.2.2 hr).elim
  good m b a m' hJ hG hrc hb he := by
    refine D.G_step hG hrc he fun hs => ?_
    obtain ⟨-, -, -, av, -, -, hav, -⟩ := ginCert_sstore (pa_cert _) hJ.2.1 hJ.2.2.2 hb hs he
    cases hav
  next m b m' hJ hG _ hb he := by
    obtain ⟨hmsg, hcd⟩ := same_next he
    refine ⟨hmsg ▸ hJ.1, hcd ▸ hJ.2.1, hmsg ▸ hJ.2.2.1, ?_⟩
    rw [hmsg]
    exact ginCert_next (pa_cert _) hJ.2.1 hJ.2.2.2 (D.envOk_pa hJ.1 hJ.2.2.1 hG) hb he
  resume m b a m' hJ _ _ hb he ha M res hM _ _ _ _ := by
    obtain ⟨hmsg, hcd⟩ := same_resume he res hM
    refine ⟨hmsg ▸ hJ.1, hcd ▸ hJ.2.1, hmsg ▸ hJ.2.2.1, ?_⟩
    rw [hmsg]
    exact ginCert_resume (pa_cert _) hJ.2.1 hJ.2.2.2 hb he ha M res hM

/-- **The implementation at its own address**: nothing requested, only slot `0` written. -/
theorem inv_ia : GuardInv D.Rl D.code D.X D.G D.Iss D.ia D.Jim where
  start m hs := by
    obtain ⟨hpc, hst, hcd⟩ := fresh_frame hs.base.fresh
    have hcode : m.frame.code = ActorImpl.runtimeCode := by
      rcases hs.base.entry with ⟨h1, -⟩ | ⟨mp, -, -, -, -, hiss⟩
      · rw [hcd, h1, code_ia]
      · exact absurd hiss D.iss_not_ia
    exact ⟨hs.base.target, hcode, ginCert_init (ia_cert _) hpc hst⟩
  issue m c hJ _ _ hr :=
    (no_requests (ia_cert _) (fun _ => rfl) hJ.2.1 hJ.2.2 hr).elim
  good m b a m' hJ hG hrc hb he :=
    D.Jia_good hJ.2 (by rw [hJ.1]; exact Ne.symm D.pa_ia) hG hrc hb he
  next m b m' hJ _ _ hb he := by
    obtain ⟨hmsg, hcd⟩ := same_next he
    exact ⟨hmsg ▸ hJ.1, hcd ▸ hJ.2.1,
      ginCert_next (ia_cert _) hJ.2.1 hJ.2.2 (envOk_ia m) hb he⟩
  resume m b a m' hJ _ _ hb he ha M res hM _ _ _ _ := by
    obtain ⟨hmsg, hcd⟩ := same_resume he res hM
    exact ⟨hmsg ▸ hJ.1, hcd ▸ hJ.2.1, ginCert_resume (ia_cert _) hJ.2.1 hJ.2.2 hb he ha M res hM⟩

/-- A proxy frame running the proxy's code is not sent by ProxyAdmin. -/
theorem px_caller {m : Machine} (hs : GuardStart D.Rl D.code D.X D.G D.Iss D.px m)
    (hcode : m.frame.msg.code = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩) :
    m.frame.msg.caller ≠ D.pa := by
  rcases hs.origin with ⟨-, hnr⟩ | ⟨mp, -, -, -, hids, hiss⟩
  · exact fun h => hnr (h ▸ .inr (.inl rfl))
  · rcases hids with hc | ⟨hc, ht⟩
    · intro h
      rw [hc] at h
      exact D.iss_not_pa (h ▸ hiss (h ▸ .inr (.inl rfl)))
    · -- A `DELEGATECALL`/`CALLCODE` from the proxy runs the implementation's code.
      intro _
      have ht' : mp.frame.msg.currentTarget = D.px := ht ▸ hs.base.target
      have hc' := (hiss (ht' ▸ .inl rfl)).2
      rw [hcode] at hc'
      have := congrArg ByteArray.size hc'
      rw [size_proxy, ActorImpl.size_runtimeCode] at this
      cases this

/-- **The proxy, for any sender but ProxyAdmin**: nothing written, and the only requests run
the implementation's code. -/
theorem inv_px : GuardInv D.Rl D.code D.X D.G D.Iss D.px D.Jpx where
  start m hs := by
    obtain ⟨hpc, hst, hcd⟩ := fresh_frame hs.base.fresh
    refine ⟨hs.base.target, ?_⟩
    rcases hs.base.entry with ⟨h1, -⟩ | ⟨mp, -, -, -, -, hiss⟩
    · have hc : m.frame.msg.code = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩ := by
        rw [h1, code_px]
      exact .inl ⟨hcd.trans hc, D.px_caller hs hc,
        ginCert_init (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hpc hst⟩
    · exact .inr ⟨hcd.trans hiss.2, ginCert_init (ia_cert _) hpc hst⟩
  issue m c hJ _ hrc hr := by
    rcases hJ.2 with ⟨hcd, hcl, hin⟩ | hia
    · refine ⟨rfl, ?_⟩
      obtain ⟨b, a, m', hb, he, (⟨req, rfl, rfl⟩ | rfl)⟩ := hr
      · obtain ⟨tw, av, -, hav, hat, hcall⟩ :=
          ginCert_call (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hcd hin hb he
        simp only [cfgPX, beq_iff_eq] at hav
        subst hav
        have htw : Word.toAddress tw = D.ia := by
          rw [show tw = Word.ofAddress D.ia from hat]; simp
        rw [htw] at hcall
        have hia := hrc _ (.inr (.inr rfl))
        rw [(hcall (.inr (by rw [hia]; exact (codeOk D).deleg _ (.inr (.inr rfl))))).2.1, hia,
          code_ia]
      · exact (ginCert_no_create (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hcd hin hb
          he).elim
    · exact (no_requests (ia_cert _) (fun _ => rfl) hia.1 hia.2 hr).elim
  good m b a m' hJ hG hrc hb he := by
    rcases hJ.2 with ⟨hcd, hcl, hin⟩ | hia
    · refine D.G_step hG hrc he fun hs => ?_
      obtain ⟨-, -, -, av, -, -, hav, -⟩ :=
        ginCert_sstore (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hcd hin hb hs he
      cases hav
    · exact D.Jia_good hia (by rw [hJ.1]; exact D.px_pa) hG hrc hb he
  next m b m' hJ hG _ hb he := by
    obtain ⟨hmsg, hcd⟩ := same_next he
    refine ⟨hmsg ▸ hJ.1, ?_⟩
    rcases hJ.2 with ⟨hc, hcl, hin⟩ | hia
    · refine .inl ⟨hcd ▸ hc, hmsg ▸ hcl, ?_⟩
      rw [hmsg]
      exact ginCert_next (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hc hin
        (D.envOk_px hJ.1 hcl hG) hb he
    · exact .inr ⟨hcd ▸ hia.1, ginCert_next (ia_cert _) hia.1 hia.2 (envOk_ia m) hb he⟩
  resume m b a m' hJ _ _ hb he ha M res hM _ _ _ _ := by
    obtain ⟨hmsg, hcd⟩ := same_resume he res hM
    refine ⟨hmsg ▸ hJ.1, ?_⟩
    rcases hJ.2 with ⟨hc, hcl, hin⟩ | hia
    · refine .inl ⟨hcd ▸ hc, hmsg ▸ hcl, ?_⟩
      rw [hmsg]
      exact ginCert_resume (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hc hin hb he ha M
        res hM
    · exact .inr ⟨hcd ▸ hia.1, ginCert_resume (ia_cert _) hia.1 hia.2 hb he ha M res hM⟩

theorem inv : ∀ r, D.Rl r → GuardInv D.Rl D.code D.X D.G D.Iss r (D.J r) := by
  rintro r (rfl | rfl | rfl)
  · rw [J_px]; exact D.inv_px
  · rw [J_pa]; exact D.inv_pa
  · rw [J_ia]; exact D.inv_ia

/-! ## The theorem -/

/-- **Only the owner can upgrade.** From a world where the proxy, its ProxyAdmin and the
implementation are deployed, the implementation slot holds `ia` and ProxyAdmin is owned by an
externally owned account `o` that has sent a transaction (no code, nonce `≠ 0`): every top-level
message call (before Prague or without EIP-7702 authorizations) whose sender is neither `o` nor
one of the three contracts leaves the implementation slot and ProxyAdmin's owner unchanged. -/
theorem impl_kept {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    (hpx : w.code D.px = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩)
    (hpa : w.code D.pa = OzProxyAdmin.runtimeCode) (hia : w.code D.ia = ActorImpl.runtimeCode)
    (himpl : w.sload D.px implSlot = Word.ofAddress D.ia)
    (howner : w.sload D.pa 0 = Word.ofAddress D.o)
    (ho : (w.code D.o).size = 0 ∧ (w.account D.o).nonce ≠ 0)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (htop : TopOk D.Rl w msg) (hsender : msg.caller ≠ D.o)
    (hto : msg.currentTarget = D.o → msg.target = some D.o → msg.code.size = 0)
    {fuel : Nat} {r : MessageResult} (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    r.world.sload D.px implSlot = Word.ofAddress D.ia ∧
      r.world.sload D.pa 0 = Word.ofAddress D.o := by
  have hw : RelayCode D.Rl D.code w := by
    rintro r (rfl | rfl | rfl)
    · rw [hpx, code_px]
    · rw [hpa, code_pa]
    · rw [hia, code_ia]
  exact processMessageCall_guard (codeOk D) D.G_keep D.inv hw ⟨himpl, howner⟩
    (fun x hx => hx ▸ ho) hdeleg ⟨htop, hsender, fun hx ht => hto hx (hx ▸ ht)⟩ hr

end Dep

/-! ## The hypotheses are satisfiable -/

namespace Example

/-- Four distinct addresses. -/
def dep : Dep where
  px := 1
  pa := 2
  ia := 3
  o := 4
  px_pa := by decide
  px_ia := by decide
  pa_ia := by decide

/-- A world with the deployment. -/
def world : World :=
  (∅ : World)
    |>.insert dep.px { code := OzTransparentProxy.runtimeCodeWith ⟨dep.pa⟩,
                       storage := (∅ : Storage).insert implSlot (Word.ofAddress dep.ia) }
    |>.insert dep.pa { code := OzProxyAdmin.runtimeCode,
                       storage := (∅ : Storage).insert 0 (Word.ofAddress dep.o) }
    |>.insert dep.ia { code := ActorImpl.runtimeCode }
    |>.insert dep.o { nonce := 1 }

theorem world_ok :
    world.code dep.px = OzTransparentProxy.runtimeCodeWith ⟨dep.pa⟩ ∧
    world.code dep.pa = OzProxyAdmin.runtimeCode ∧ world.code dep.ia = ActorImpl.runtimeCode ∧
    world.sload dep.px implSlot = Word.ofAddress dep.ia ∧
    world.sload dep.pa 0 = Word.ofAddress dep.o ∧
    (world.code dep.o).size = 0 ∧ (world.account dep.o).nonce ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [world, dep, World.code, World.sload, World.account, Storage.get,
      Std.ExtTreeMap.getD_insert]

/-- **The theorem on this world**: no transaction from anyone but the owner upgrades. -/
theorem world_impl_kept {ctx : Context} {tr : TransientStorage} {msg : Message}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (htop : TopOk dep.Rl world msg) (hsender : msg.caller ≠ dep.o)
    (hto : msg.currentTarget = dep.o → msg.target = some dep.o → msg.code.size = 0)
    {fuel : Nat} {r : MessageResult} (hr : processMessageCall fuel ctx world tr msg = .ok r) :
    r.world.sload dep.px implSlot = Word.ofAddress dep.ia := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := world_ok
  exact (dep.impl_kept h1 h2 h3 h4 h5 ⟨h6, h7⟩ hdeleg htop hsender hto hr).1

end Example

end Examples.Actor.ProxyGuard
