import Examples.Actor.Bytecode.ProxyGuard
import Examples.Actor.Bytecode.MiniSafeFrame

/-!
# Only a quorum of Safe owners can upgrade: the upgrade guard on bytecode, Safe owner

`ProxyGuard` with the owner of the `ProxyAdmin` a threshold multisig instead of an externally
owned account: the deployed OpenZeppelin v5.7.0 `TransparentUpgradeableProxy` at `px`, its
`ProxyAdmin` at `pa` owned by the `MiniSafe` at `ms` (a Safe-style multisig: owners `O`,
threshold `thr`, ECDSA signatures checked as Safe 1.5.0's `checkNSignatures`), and the
implementation `ActorImpl` at `ia`. `impl_kept`: **in any transaction whose signers `T` include
fewer than `thr` owners, the implementation slot, the `ProxyAdmin`'s owner and the Safe's
threshold and owners are unchanged** — any calldata, any value, any depth, reentrancy, reverts.

This is `processMessageCall_guard` with:

- relays the proxy, ProxyAdmin, the implementation and the Safe (their code is fixed);
- the world invariant `G`: the implementation slot holds `ia`, ProxyAdmin's slot `0` holds
  `ms`, the Safe's threshold is `thr` and every set `isOwner` slot is an owner's;
- issuance: the proxy runs only the implementation's code (as in `ProxyGuard`), and the Safe
  calls only address `1` (`ecrecover`);
- frame invariants: ProxyAdmin, the proxy and the implementation as in `ProxyGuard`, except that
  a ProxyAdmin frame's sender is not the Safe (the Safe calls only `ecrecover`); a Safe frame
  satisfies `Own` (`MiniSafeOwn.frame`): every path of the frame reverts or returns before the
  final `CALL` of `execTransaction`, writing only the nonce.

The signers enter only through `Signers` (a hypothesis in the style of `SigUnforgeable`): every
owner that `ecrecover` recovers from a digest of this Safe on this chain is in `T`. In
actor-model terms (`QEDefi.Actor.Lib.Safe`, `Examples.Actor.SafeProxyAdminLib`): the keys `T`
contain fewer than `thr` owners and no module acts (MiniSafe has none), so they derive no
upgrade; here that is proved of the bytecode.
-/

namespace Examples.Actor.SafeGuard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open EvmLogic.AbsInt EvmLogic.AbsInt.Guard Examples.OpenZeppelin.Contracts EvmLogic.Solidity
open Examples.Actor.Contracts Examples.Actor.MiniSafeOwn Examples.Actor.ProxyGuard

/-- A deployment: proxy, ProxyAdmin, implementation and the Safe owning the ProxyAdmin
(distinct, none at the `ecrecover` precompile `1`). -/
structure Dep where
  px : Address
  pa : Address
  ia : Address
  ms : Address
  px_pa : px ≠ pa
  px_ia : px ≠ ia
  pa_ia : pa ≠ ia
  ms_px : ms ≠ px
  ms_pa : ms ≠ pa
  ms_ia : ms ≠ ia
  pa_one : pa ≠ 1
  ms_one : ms ≠ 1

namespace Dep

variable (D : Dep)

/-- The code of each relay. -/
def code (a : Address) : ByteArray :=
  if a = D.px then OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩
  else if a = D.pa then OzProxyAdmin.runtimeCode
  else if a = D.ms then MiniSafe.runtimeCode else ActorImpl.runtimeCode

def Rl (a : Address) : Prop := a = D.px ∨ a = D.pa ∨ a = D.ia ∨ a = D.ms

/-- After Prague, the `ecrecover` address holds no code and has sent a transaction, so no
creation lands there and it holds no delegation designator. -/
def X (fork : Fork) (a : Address) : Prop := a = 1 ∧ .prague ≤ fork

/-- **The protected state**: the implementation, the ProxyAdmin's owner, the Safe's threshold
and owners (slots `isOwner[a]` set only for owners `O`, under `crypto`'s keccak). -/
def G (crypto : Crypto) (O : Finset Address) (thr : Nat) (w : World) : Prop :=
  w.sload D.px implSlot = Word.ofAddress D.ia ∧ w.sload D.pa 0 = Word.ofAddress D.ms ∧
    w.sload D.ms 0 = BitVec.ofNat 256 thr ∧
    ∀ a, w.sload D.ms (ownerSlot crypto a) ≠ 0 → a ∈ O

/-- What relays issue: the proxy runs only the implementation's code; the Safe calls only `1`. -/
def Iss (r : Address) (_ : Machine) (c : Message) : Prop :=
  (r = D.px ∧ c.code = ActorImpl.runtimeCode) ∨ (r = D.ms ∧ c.currentTarget = 1)

/-- Valuations: ProxyAdmin (sender, owner `ms`), the proxy (admin; sender, implementation). -/
def envPA (c : Address) : Env := ⟨fun _ => 0, fun i => if i = 0 then c else D.ms⟩
def envPX (c : Address) : Env := ⟨fun _ => D.pa, fun i => if i = 0 then c else D.ia⟩

def Jpa (m : Machine) : Prop :=
  m.frame.msg.currentTarget = D.pa ∧ m.frame.code = OzProxyAdmin.runtimeCode ∧
    m.frame.msg.caller ≠ D.ms ∧ GInCert (D.envPA m.frame.msg.caller) tPA m

def Jpx (m : Machine) : Prop :=
  m.frame.msg.currentTarget = D.px ∧
    ((m.frame.code = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩ ∧ m.frame.msg.caller ≠ D.pa ∧
      GInCert (D.envPX m.frame.msg.caller) tPX m) ∨ ProxyGuard.Dep.Jia m)

def Jim (m : Machine) : Prop := m.frame.msg.currentTarget = D.ia ∧ ProxyGuard.Dep.Jia m

/-- A Safe frame: every own path ends it safely (`MiniSafeOwn.frame`). -/
def Jms (m : Machine) : Prop := m.frame.msg.currentTarget = D.ms ∧ Own S C m

/-- The frame invariants. -/
def J (r : Address) : Machine → Prop :=
  if r = D.pa then D.Jpa else if r = D.px then D.Jpx else if r = D.ms then D.Jms else D.Jim

theorem code_px : D.code D.px = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩ := by simp [code]
theorem code_pa : D.code D.pa = OzProxyAdmin.runtimeCode := by
  simp [code, Ne.symm D.px_pa]
theorem code_ms : D.code D.ms = MiniSafe.runtimeCode := by
  simp [code, D.ms_px, D.ms_pa]
theorem code_ia : D.code D.ia = ActorImpl.runtimeCode := by
  simp [code, Ne.symm D.px_ia, Ne.symm D.pa_ia, Ne.symm D.ms_ia]

theorem J_pa : D.J D.pa = D.Jpa := by simp [J]
theorem J_px : D.J D.px = D.Jpx := by simp [J, D.px_pa]
theorem J_ms : D.J D.ms = D.Jms := by simp [J, D.ms_pa, D.ms_px]
theorem J_ia : D.J D.ia = D.Jim := by
  simp [J, Ne.symm D.pa_ia, Ne.symm D.px_ia, Ne.symm D.ms_ia]

/-! ## The world -/

theorem codeOk : RelayCodeOk D.Rl D.code where
  size r hr := by
    rcases hr with rfl | rfl | rfl | rfl
    · rw [code_px, Dep.size_proxy]; decide
    · rw [code_pa, OzProxyAdmin.size_runtimeCode]; decide
    · rw [code_ia, ActorImpl.size_runtimeCode]; decide
    · rw [code_ms, MiniSafe.size_runtimeCode]; decide
  deleg r hr := by
    rcases hr with rfl | rfl | rfl | rfl
    · rw [code_px]; exact Dep.deleg_none (by rw [Dep.size_proxy]; decide)
    · rw [code_pa]; exact Dep.deleg_none (by rw [OzProxyAdmin.size_runtimeCode]; decide)
    · rw [code_ia]; exact Dep.deleg_none (by rw [ActorImpl.size_runtimeCode]; decide)
    · rw [code_ms]; exact Dep.deleg_none (by rw [MiniSafe.size_runtimeCode]; decide)

variable {crypto : Crypto} {O : Finset Address} {thr : Nat}

theorem G_keep : ∀ w w', D.G crypto O thr w → KeepP D.Rl w w' → D.G crypto O thr w' :=
  fun _ _ h hk => by
    have hpx := hk _ (.inl rfl)
    have hpa := hk _ (.inr (.inl rfl))
    have hms := hk _ (.inr (.inr (.inr rfl)))
    refine ⟨(hpx.sload' _).trans h.1, (hpa.sload' _).trans h.2.1, (hms.sload' _).trans h.2.2.1,
      fun a ha => h.2.2.2 a ?_⟩
    rwa [hms.sload'] at ha

/-- **An instruction keeps the protected state** if, when it is an `SSTORE`, it writes slot `0`
of an account other than ProxyAdmin and the Safe, or the Safe's nonce (slot `1`). -/
theorem G_step (hslot : ∀ a, ownerSlot crypto a ≠ 1) {m m' : Machine} {b : UInt8} {a : Action}
    (hG : D.G crypto O thr m.world) (hrc : RelayCode D.Rl D.code m.world)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m'))
    (hss : Opcode.decode m.ctx.fork b = .sstore → ∃ k v,
      ((k.toNat = 0 ∧ m.frame.msg.currentTarget ≠ D.pa ∧ m.frame.msg.currentTarget ≠ D.ms) ∨
        (k = 1 ∧ m.frame.msg.currentTarget = D.ms)) ∧
      m'.world = m.world.sstore m.frame.msg.currentTarget k v) : D.G crypto O thr m'.world := by
  by_cases hs : Opcode.decode m.ctx.fork b = .sstore
  · obtain ⟨k, v, hk, hw⟩ := hss hs
    rw [hw]
    rcases hk with ⟨hk, hpa, hms⟩ | ⟨rfl, hms⟩
    · refine ⟨?_, ?_, ?_, fun x hx => hG.2.2.2 x ?_⟩
      · by_cases ht : D.px = m.frame.msg.currentTarget
        · rw [← ht, World.sload_sstore_ne_key _ _ _
            (fun e => Dep.implSlot_ne_zero (by rw [e]; exact hk))]
          exact hG.1
        · rw [World.sload_sstore_ne_addr _ _ _ _ ht]; exact hG.1
      · rw [World.sload_sstore_ne_addr _ _ _ _ (Ne.symm hpa)]; exact hG.2.1
      · rw [World.sload_sstore_ne_addr _ _ _ _ (Ne.symm hms)]; exact hG.2.2.1
      · rwa [World.sload_sstore_ne_addr _ _ _ _ (Ne.symm hms)] at hx
    · rw [hms]
      refine ⟨?_, ?_, ?_, fun x hx => hG.2.2.2 x ?_⟩
      · rw [World.sload_sstore_ne_addr _ _ _ _ (Ne.symm D.ms_px)]; exact hG.1
      · rw [World.sload_sstore_ne_addr _ _ _ _ (Ne.symm D.ms_pa)]; exact hG.2.1
      · rw [World.sload_sstore_ne_key _ _ _ (by decide)]; exact hG.2.2.1
      · rwa [World.sload_sstore_ne_key _ _ _ (hslot x)] at hx
  · have hpx := (exec_slot _ hs m D.px implSlot).of_run he
      (by rw [hrc _ (.inl rfl), code_px, Dep.size_proxy]; decide)
    have hpa := (exec_slot _ hs m D.pa 0).of_run he
      (by rw [hrc _ (.inr (.inl rfl)), code_pa, OzProxyAdmin.size_runtimeCode]; decide)
    have hms : ∀ κ, m'.world.sload D.ms κ = m.world.sload D.ms κ := fun κ =>
      (exec_slot _ hs m D.ms κ).of_run he
        (by rw [hrc _ (.inr (.inr (.inr rfl))), code_ms, MiniSafe.size_runtimeCode]; decide)
    exact ⟨hpx.trans hG.1, hpa.trans hG.2.1, (hms 0).trans hG.2.2.1,
      fun x hx => hG.2.2.2 x (by rwa [hms] at hx)⟩

/-! ## Facts the certificates assume -/

theorem envOk_pa {m : Machine} (ht : m.frame.msg.currentTarget = D.pa)
    (hc : m.frame.msg.caller ≠ D.ms) (hG : D.G crypto O thr m.world) :
    EnvOk (D.envPA m.frame.msg.caller) cfgPA m where
  caller i hi := by
    simp only [cfgPA, Option.some.injEq] at hi; subst hi; rfl
  slots k i hk key hkey := by
    obtain ⟨rfl, rfl⟩ := Dep.slotAtom_pa hk
    have : key = 0 := BitVec.eq_of_toNat_eq (by simpa using hkey)
    rw [this, ht]; exact hG.2.1
  distinct a b hab := by
    simp only [cfgPA, List.mem_singleton, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨_, _, rfl, rfl, by simpa [envPA] using hc⟩

theorem envOk_px {m : Machine} (ht : m.frame.msg.currentTarget = D.px)
    (hc : m.frame.msg.caller ≠ D.pa) (hG : D.G crypto O thr m.world) :
    EnvOk (D.envPX m.frame.msg.caller) cfgPX m where
  caller i hi := by
    simp only [cfgPX, Option.some.injEq] at hi; subst hi; rfl
  slots k i hk key hkey := by
    obtain ⟨rfl, rfl⟩ := Dep.slotAtom_px hk
    have : key = implSlot := BitVec.eq_of_toNat_eq hkey
    rw [this, ht]; exact hG.1
  distinct a b hab := by
    simp only [cfgPX, List.mem_singleton, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨_, _, rfl, rfl, by simpa [envPX] using hc⟩

/-- A frame running the implementation keeps `G` (it writes only slot `0`, never at ProxyAdmin
or the Safe). -/
theorem Jia_good (hslot : ∀ a, ownerSlot crypto a ≠ 1) {m m' : Machine} {b : UInt8} {a : Action}
    (hJ : ProxyGuard.Dep.Jia m) (hpa : m.frame.msg.currentTarget ≠ D.pa)
    (hms : m.frame.msg.currentTarget ≠ D.ms) (hG : D.G crypto O thr m.world)
    (hrc : RelayCode D.Rl D.code m.world) (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m')) :
    D.G crypto O thr m'.world := by
  refine D.G_step hslot hG hrc he fun hs => ?_
  obtain ⟨k, v, r, av, -, hw, hav, hk⟩ := ginCert_sstore (ia_cert _) hJ.1 hJ.2 hb hs he
  simp only [cfgIA, beq_iff_eq] at hav
  subst hav
  exact ⟨k, v, .inl ⟨hk, hpa, hms⟩, hw⟩

/-! ## Who calls whom -/

theorem iss_pa {mp : Machine} {c : Message} : ¬ D.Iss D.pa mp c := by
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact D.px_pa h.symm
  · exact D.ms_pa h.symm

theorem iss_ia {mp : Machine} {c : Message} : ¬ D.Iss D.ia mp c := by
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact D.px_ia h.symm
  · exact D.ms_ia h.symm

/-- The Safe issues only calls to `1`. -/
theorem iss_ms {mp : Machine} {c : Message} (h : D.Iss D.ms mp c) : c.currentTarget = 1 := by
  rcases h with ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd h D.ms_px
  · exact h

variable {K : Context → Prop} {Xi : Address → Prop}

/-- **A ProxyAdmin frame is not sent by the Safe**: the Safe calls only `1`. -/
theorem pa_caller {X : Address → Prop} {G : World → Prop} {m : Machine}
    (hs : GuardStartK K D.Rl D.code X G D.Iss D.pa m) : m.frame.msg.caller ≠ D.ms := by
  rcases hs.origin with ⟨-, hnr⟩ | ⟨mp, -, -, -, hids, hiss⟩
  · exact fun h => hnr (h ▸ .inr (.inr (.inr rfl)))
  · rcases hids with hc | ⟨hc, ht⟩
    · intro h
      rw [hc] at h
      have := D.iss_ms (h ▸ hiss (h ▸ .inr (.inr (.inr rfl))))
      rw [hs.base.target] at this
      exact D.pa_one this
    · intro _
      have ht' : mp.frame.msg.currentTarget = D.pa := ht ▸ hs.base.target
      exact D.iss_pa (ht' ▸ hiss (ht' ▸ .inr (.inl rfl)))

/-- A proxy frame running the proxy's code is not sent by ProxyAdmin. -/
theorem px_caller {X : Address → Prop} {G : World → Prop} {m : Machine}
    (hs : GuardStartK K D.Rl D.code X G D.Iss D.px m)
    (hcode : m.frame.msg.code = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩) :
    m.frame.msg.caller ≠ D.pa := by
  rcases hs.origin with ⟨-, hnr⟩ | ⟨mp, -, -, -, hids, hiss⟩
  · exact fun h => hnr (h ▸ .inr (.inl rfl))
  · rcases hids with hc | ⟨hc, ht⟩
    · intro h
      rw [hc] at h
      exact D.iss_pa (h ▸ hiss (h ▸ .inr (.inl rfl)))
    · -- A `DELEGATECALL`/`CALLCODE` from the proxy runs the implementation's code.
      intro _
      have ht' : mp.frame.msg.currentTarget = D.px := ht ▸ hs.base.target
      rcases hiss (ht' ▸ .inl rfl) with ⟨-, hc'⟩ | ⟨h, -⟩
      · rw [hcode] at hc'
        have := congrArg ByteArray.size hc'
        rw [Dep.size_proxy, ActorImpl.size_runtimeCode] at this
        cases this
      · exact D.ms_px (ht' ▸ h).symm

/-! ## The frame obligations -/

variable (crypto O thr)

/-- The context of the transaction. -/
abbrev Kc (ctx : Context) (c : Context) : Prop := c = ctx

/-- **ProxyAdmin, for any sender but the Safe**: nothing requested, nothing written. -/
theorem inv_pa (hslot : ∀ a, ownerSlot crypto a ≠ 1) :
    GuardInvK K D.Rl D.code Xi (D.G crypto O thr) D.Iss D.pa D.Jpa where
  start m hs := by
    obtain ⟨hpc, hst, hcd⟩ := Dep.fresh_frame hs.base.fresh
    have hcode : m.frame.code = OzProxyAdmin.runtimeCode := by
      rcases hs.base.entry with ⟨h1, -⟩ | ⟨mp, -, -, -, -, hiss⟩
      · rw [hcd, h1, code_pa]
      · exact absurd hiss D.iss_pa
    exact ⟨hs.base.target, hcode, D.pa_caller hs, ginCert_init (pa_cert _) hpc hst⟩
  issue m c hJ _ _ hr :=
    (Dep.no_requests (pa_cert _) (fun _ => rfl) hJ.2.1 hJ.2.2.2 hr).elim
  good m b a m' hJ hG hrc hb he := by
    refine D.G_step hslot hG hrc he fun hs => ?_
    obtain ⟨-, -, -, av, -, -, hav, -⟩ := ginCert_sstore (pa_cert _) hJ.2.1 hJ.2.2.2 hb hs he
    cases hav
  next m b m' hJ hG _ hb he := by
    obtain ⟨hmsg, hcd⟩ := Dep.same_next he
    refine ⟨hmsg ▸ hJ.1, hcd ▸ hJ.2.1, hmsg ▸ hJ.2.2.1, ?_⟩
    rw [hmsg]
    exact ginCert_next (pa_cert _) hJ.2.1 hJ.2.2.2 (D.envOk_pa hJ.1 hJ.2.2.1 hG) hb he
  resume m b a m' hJ _ _ hb he ha M res hM _ _ _ _ := by
    obtain ⟨hmsg, hcd⟩ := Dep.same_resume he res hM
    refine ⟨hmsg ▸ hJ.1, hcd ▸ hJ.2.1, hmsg ▸ hJ.2.2.1, ?_⟩
    rw [hmsg]
    exact ginCert_resume (pa_cert _) hJ.2.1 hJ.2.2.2 hb he ha M res hM

/-- **The implementation at its own address**: nothing requested, only slot `0` written. -/
theorem inv_ia (hslot : ∀ a, ownerSlot crypto a ≠ 1) :
    GuardInvK K D.Rl D.code Xi (D.G crypto O thr) D.Iss D.ia D.Jim where
  start m hs := by
    obtain ⟨hpc, hst, hcd⟩ := Dep.fresh_frame hs.base.fresh
    have hcode : m.frame.code = ActorImpl.runtimeCode := by
      rcases hs.base.entry with ⟨h1, -⟩ | ⟨mp, -, -, -, -, hiss⟩
      · rw [hcd, h1, code_ia]
      · exact absurd hiss D.iss_ia
    exact ⟨hs.base.target, hcode, ginCert_init (ia_cert _) hpc hst⟩
  issue m c hJ _ _ hr :=
    (Dep.no_requests (ia_cert _) (fun _ => rfl) hJ.2.1 hJ.2.2 hr).elim
  good m b a m' hJ hG hrc hb he :=
    D.Jia_good hslot hJ.2 (by rw [hJ.1]; exact Ne.symm D.pa_ia)
      (by rw [hJ.1]; exact Ne.symm D.ms_ia) hG hrc hb he
  next m b m' hJ _ _ hb he := by
    obtain ⟨hmsg, hcd⟩ := Dep.same_next he
    exact ⟨hmsg ▸ hJ.1, hcd ▸ hJ.2.1,
      ginCert_next (ia_cert _) hJ.2.1 hJ.2.2 (Dep.envOk_ia m) hb he⟩
  resume m b a m' hJ _ _ hb he ha M res hM _ _ _ _ := by
    obtain ⟨hmsg, hcd⟩ := Dep.same_resume he res hM
    exact ⟨hmsg ▸ hJ.1, hcd ▸ hJ.2.1, ginCert_resume (ia_cert _) hJ.2.1 hJ.2.2 hb he ha M res hM⟩

/-- **The proxy, for any sender but ProxyAdmin**: nothing written, and the only requests run
the implementation's code. -/
theorem inv_px (hslot : ∀ a, ownerSlot crypto a ≠ 1) :
    GuardInvK K D.Rl D.code Xi (D.G crypto O thr) D.Iss D.px D.Jpx where
  start m hs := by
    obtain ⟨hpc, hst, hcd⟩ := Dep.fresh_frame hs.base.fresh
    refine ⟨hs.base.target, ?_⟩
    rcases hs.base.entry with ⟨h1, -⟩ | ⟨mp, -, -, -, -, hiss⟩
    · have hc : m.frame.msg.code = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩ := by
        rw [h1, code_px]
      exact .inl ⟨hcd.trans hc, D.px_caller hs hc,
        ginCert_init (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hpc hst⟩
    · rcases hiss with ⟨-, hc⟩ | ⟨h, -⟩
      · exact .inr ⟨hcd.trans hc, ginCert_init (ia_cert _) hpc hst⟩
      · exact absurd h.symm D.ms_px
  issue m c hJ _ hrc hr := by
    rcases hJ.2 with ⟨hcd, hcl, hin⟩ | hia
    · refine .inl ⟨rfl, ?_⟩
      obtain ⟨b, a, m', hb, he, (⟨req, rfl, rfl⟩ | rfl)⟩ := hr
      · obtain ⟨tw, av, -, hav, hat, hcall⟩ :=
          ginCert_call (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hcd hin hb he
        simp only [cfgPX, beq_iff_eq] at hav
        subst hav
        have htw : Word.toAddress tw = D.ia := by
          rw [show tw = Word.ofAddress D.ia from hat]; simp
        rw [htw] at hcall
        have hia := hrc _ (.inr (.inr (.inl rfl)))
        rw [(hcall (.inr (by rw [hia]; exact (codeOk D).deleg _ (.inr (.inr (.inl rfl)))))).2.1,
          hia, code_ia]
      · exact (ginCert_no_create (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hcd hin hb
          he).elim
    · exact (Dep.no_requests (ia_cert _) (fun _ => rfl) hia.1 hia.2 hr).elim
  good m b a m' hJ hG hrc hb he := by
    rcases hJ.2 with ⟨hcd, hcl, hin⟩ | hia
    · refine D.G_step hslot hG hrc he fun hs => ?_
      obtain ⟨-, -, -, av, -, -, hav, -⟩ :=
        ginCert_sstore (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hcd hin hb hs he
      cases hav
    · exact D.Jia_good hslot hia (by rw [hJ.1]; exact D.px_pa)
        (by rw [hJ.1]; exact Ne.symm D.ms_px) hG hrc hb he
  next m b m' hJ hG _ hb he := by
    obtain ⟨hmsg, hcd⟩ := Dep.same_next he
    refine ⟨hmsg ▸ hJ.1, ?_⟩
    rcases hJ.2 with ⟨hc, hcl, hin⟩ | hia
    · refine .inl ⟨hcd ▸ hc, hmsg ▸ hcl, ?_⟩
      rw [hmsg]
      exact ginCert_next (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hc hin
        (D.envOk_px hJ.1 hcl hG) hb he
    · exact .inr ⟨hcd ▸ hia.1, ginCert_next (ia_cert _) hia.1 hia.2 (Dep.envOk_ia m) hb he⟩
  resume m b a m' hJ _ _ hb he ha M res hM _ _ _ _ := by
    obtain ⟨hmsg, hcd⟩ := Dep.same_resume he res hM
    refine ⟨hmsg ▸ hJ.1, ?_⟩
    rcases hJ.2 with ⟨hc, hcl, hin⟩ | hia
    · refine .inl ⟨hcd ▸ hc, hmsg ▸ hcl, ?_⟩
      rw [hmsg]
      exact ginCert_resume (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hc hin hb he ha M
        res hM
    · exact .inr ⟨hcd ▸ hia.1, ginCert_resume (ia_cert _) hia.1 hia.2 hb he ha M res hM⟩

theorem decode_sstore_lt : ∀ n < 256, ∀ fk : Fork,
    Opcode.decode fk n.toUInt8 = .sstore → n.toUInt8 = 0x55 := by
  intro n hn fk; cases fk <;> revert n <;> decide +kernel

theorem decode_sstore {fk : Fork} {b : UInt8} (h : Opcode.decode fk b = .sstore) : b = 0x55 := by
  simpa using decode_sstore_lt b.toNat b.toNat_lt fk (by simpa using h)

/-- **The Safe**: every frame ends safely when fewer than `thr` owners sign (`frame`). -/
theorem inv_ms (ctx : Context) (T : Finset Address) (hthr : thr < 2 ^ 256)
    (hcard : (O ∩ T).card < thr) (hslot : ∀ a, ownerSlot ctx.crypto a ≠ 1)
    (hsig : Signers ctx.crypto ctx.block.chainId D.ms O T) :
    GuardInvK (Kc ctx) D.Rl D.code (Dep.X ctx.fork) (D.G ctx.crypto O thr) D.Iss D.ms D.Jms where
  start m hs := by
    have hctx : m.ctx = ctx := hs.ctx
    obtain ⟨o, sn, hfr⟩ := hs.base.fresh
    have hcode : m.frame.code = MiniSafe.runtimeCode := by
      rw [hfr]
      rcases hs.base.entry with ⟨h1, -⟩ | ⟨mp, -, -, -, -, hiss⟩
      · show m.frame.msg.code = _; rw [h1, code_ms]
      · have := D.iss_ms hiss
        rw [hs.base.target] at this
        exact absurd this D.ms_one
    have ht := hs.base.target
    refine ⟨ht, MiniSafeOwn.frame (msg := m.frame.msg) (ctx := m.ctx) (w := m.world)
      (O := O) (T := T) (thr := thr) ⟨hthr, ?_, hcard, ?_, ?_, ?_, ?_⟩
      ⟨rfl, rfl, hs.base.pre, hcode, by rw [hfr]; rfl, by rw [hfr]; rfl, by rw [hfr]; rfl, rfl⟩⟩
    · rw [ht]; exact hs.good.2.2.1
    · rw [ht, hctx]; exact hs.good.2.2.2
    · rw [hctx]; exact hslot
    · rw [ht, hctx]; exact hsig
    · by_cases hf : m.ctx.fork < .prague
      · exact .inl hf
      · right
        have h0 := (hs.idle 1 ⟨rfl, by rw [← hctx]; exact Nat.le_of_not_lt hf⟩).1
        cases hd : delegatedAddress? (m.world.code 1) with
        | none => rfl
        | some d => exact absurd h0 (delegated_size hd)
  issue m c hJ _ _ hr := by
    obtain ⟨b, a, m', hb, he, (⟨req, rfl, rfl⟩ | rfl)⟩ := hr
    · exact .inr ⟨rfl, (hJ.2.call hb he).2.1⟩
    · exact (hJ.2.create hb he).elim
  good m b a m' hJ hG hrc hb he := by
    refine D.G_step hslot hG hrc he fun hs => ?_
    rw [hs] at he
    obtain ⟨k, v, r, hstk, hw⟩ := (exec_sstore_world m).of_run he
    have h55 : m.frame.code[m.frame.pc]? = some 0x55 := by rw [hb, decode_sstore hs]
    exact ⟨k, v, .inr ⟨hJ.2.safe k _ h55 hstk, hJ.1⟩, hw⟩
  next m b m' hJ _ _ hb he := by
    obtain ⟨hmsg, -⟩ := Dep.same_next he
    exact ⟨hmsg ▸ hJ.1, hJ.2.next hb he⟩
  resume m b a m' hJ _ _ hb he ha M res hM _ _ _ hpre := by
    obtain ⟨hmsg, -⟩ := Dep.same_resume he res hM
    refine ⟨hmsg ▸ hJ.1, ?_⟩
    rcases ha with ⟨req, rfl⟩ | ⟨msg, rfl⟩
    · obtain ⟨hp, -, hown⟩ := hJ.2.call hb he
      rw [hpre req rfl hp]
      exact hown
    · exact (hJ.2.create hb he).elim

theorem inv (ctx : Context) (T : Finset Address) (hthr : thr < 2 ^ 256)
    (hcard : (O ∩ T).card < thr) (hslot : ∀ a, ownerSlot ctx.crypto a ≠ 1)
    (hsig : Signers ctx.crypto ctx.block.chainId D.ms O T) :
    ∀ r, D.Rl r →
      GuardInvK (Kc ctx) D.Rl D.code (Dep.X ctx.fork) (D.G ctx.crypto O thr) D.Iss r (D.J r) := by
  rintro r (rfl | rfl | rfl | rfl)
  · rw [J_px]; exact D.inv_px _ _ _ hslot
  · rw [J_pa]; exact D.inv_pa _ _ _ hslot
  · rw [J_ia]; exact D.inv_ia _ _ _ hslot
  · rw [J_ms]; exact D.inv_ms _ _ ctx T hthr hcard hslot hsig

/-! ## The theorem -/

/-- **Only a quorum of the Safe's owners can upgrade.** From a world where the proxy, its
ProxyAdmin, the implementation and the Safe are deployed, the implementation slot holds `ia`,
ProxyAdmin is owned by the Safe, and the Safe has threshold `thr` and owners `O` (every set
`isOwner` slot is an owner's): every top-level message call (before Prague or without EIP-7702
authorizations) whose signers `T` (`Signers`: the owners `ecrecover` recovers from a digest of
this Safe on this chain) include fewer than `thr` owners leaves the implementation, the owner of
ProxyAdmin, and the Safe's threshold and owners unchanged.

Assumed about hashing: no owner slot is the nonce slot `1`. From Prague on, address `1` holds no
code and has a nonzero nonce, and is not the sender (so it never holds a delegation designator). -/
theorem impl_kept {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    {O T : Finset Address} {thr : Nat}
    (hpx : w.code D.px = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩)
    (hpa : w.code D.pa = OzProxyAdmin.runtimeCode) (hia : w.code D.ia = ActorImpl.runtimeCode)
    (hms : w.code D.ms = MiniSafe.runtimeCode)
    (himpl : w.sload D.px implSlot = Word.ofAddress D.ia)
    (howner : w.sload D.pa 0 = Word.ofAddress D.ms)
    (hthreshold : w.sload D.ms 0 = BitVec.ofNat 256 thr) (hthr : thr < 2 ^ 256)
    (howners : ∀ a, w.sload D.ms (ownerSlot ctx.crypto a) ≠ 0 → a ∈ O)
    (hsig : Signers ctx.crypto ctx.block.chainId D.ms O T) (hcard : (O ∩ T).card < thr)
    (hslot : ∀ a, ownerSlot ctx.crypto a ≠ 1)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hone : .prague ≤ ctx.fork → (w.code 1).size = 0 ∧ (w.account 1).nonce ≠ 0 ∧
      msg.caller ≠ 1 ∧ (msg.currentTarget = 1 → msg.target = some 1 → msg.code.size = 0))
    (htop : TopOk D.Rl w msg) {fuel : Nat} {r : MessageResult}
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    D.G ctx.crypto O thr r.world := by
  have hw : RelayCode D.Rl D.code w := by
    rintro r (rfl | rfl | rfl | rfl)
    · rw [hpx, code_px]
    · rw [hpa, code_pa]
    · rw [hia, code_ia]
    · rw [hms, code_ms]
  refine processMessageCall_guard (K := Kc ctx) (codeOk D) D.G_keep
    (D.inv O thr ctx T hthr hcard hslot hsig) hw
    ⟨himpl, howner, hthreshold, howners⟩ (fun x hx => ?_) hdeleg
    ⟨htop, fun (hx : Dep.X ctx.fork msg.caller) => (hone hx.2).2.2.1 hx.1,
      fun (hx : Dep.X ctx.fork msg.currentTarget) ht => ?_⟩ hr rfl
  · obtain ⟨rfl, hf⟩ := (hx : Dep.X ctx.fork x)
    exact ⟨(hone hf).1, (hone hf).2.1⟩
  · obtain ⟨h1, hf⟩ := hx
    exact (hone hf).2.2.2 h1 (h1 ▸ ht)

end Dep

/-! ## The hypotheses are satisfiable -/

namespace Example

/-- Four distinct addresses, none at the `ecrecover` precompile. -/
def dep : Dep where
  px := 10
  pa := 11
  ia := 12
  ms := 13
  px_pa := by decide
  px_ia := by decide
  pa_ia := by decide
  ms_px := by decide
  ms_pa := by decide
  ms_ia := by decide
  pa_one := by decide
  ms_one := by decide

/-- Three owners (alice, bob, carol), threshold `2`; only alice signs. -/
def alice : Address := 0xA11CE
def bob : Address := 0xB0B
def carol : Address := 0xCA401
def owners : Finset Address := {alice, bob, carol}
def signers : Finset Address := {alice}

/-- A stand-in for the cryptography (the theorem holds for any `Crypto`): a "hash" whose owner
slots are `a + 2`, and an `ecrecover` that recovers nothing. -/
def crypto : Crypto :=
  { Crypto.real with
    keccak256 := fun x => Bytes.toWord (x.extract 0 32) + 2
    ecrecover := fun _ _ _ _ => none }

def ctx : Context := { crypto }

theorem ownerSlot_eq (a : Address) : ownerSlot crypto a = Word.ofAddress a + 2 := by
  simp only [ownerSlot, crypto]
  rw [ByteArray.extract_append_eq_left (by simp [Bytes.size_ofWord]), Bytes.toWord_ofWord]

theorem toNat_ofAddress_add_two (a : Address) : (Word.ofAddress a + 2).toNat = a.toNat + 2 := by
  have := a.isLt
  rw [BitVec.toNat_add, show (2 : Word).toNat = 2 from rfl]
  simp only [Word.ofAddress, BitVec.toNat_setWidth]
  omega

/-- The world: the deployment, the Safe's threshold and owner slots. -/
def world : World :=
  (∅ : World)
    |>.insert dep.px { code := OzTransparentProxy.runtimeCodeWith ⟨dep.pa⟩,
                       storage := (∅ : Storage).insert implSlot (Word.ofAddress dep.ia) }
    |>.insert dep.pa { code := OzProxyAdmin.runtimeCode,
                       storage := (∅ : Storage).insert 0 (Word.ofAddress dep.ms) }
    |>.insert dep.ia { code := ActorImpl.runtimeCode }
    |>.insert dep.ms { code := MiniSafe.runtimeCode,
                       storage := (∅ : Storage).insert 0 2
                         |>.insert (Word.ofAddress alice + 2) 1
                         |>.insert (Word.ofAddress bob + 2) 1
                         |>.insert (Word.ofAddress carol + 2) 1 }

theorem world_ok :
    world.code dep.px = OzTransparentProxy.runtimeCodeWith ⟨dep.pa⟩ ∧
    world.code dep.pa = OzProxyAdmin.runtimeCode ∧ world.code dep.ia = ActorImpl.runtimeCode ∧
    world.code dep.ms = MiniSafe.runtimeCode ∧
    world.sload dep.px implSlot = Word.ofAddress dep.ia ∧
    world.sload dep.pa 0 = Word.ofAddress dep.ms ∧ world.sload dep.ms 0 = BitVec.ofNat 256 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [world, dep, alice, bob, carol, World.code, World.sload, World.account, Storage.get,
      Std.ExtTreeMap.getD_insert]
  decide

/-- Only the owners' slots are set. -/
theorem world_owners (a : Address) (h : world.sload dep.ms (ownerSlot crypto a) ≠ 0) :
    a ∈ owners := by
  have h0 : Word.ofAddress a + 2 ≠ 0 := fun h0 => by
    have := congrArg BitVec.toNat h0
    rw [toNat_ofAddress_add_two] at this
    simp at this
  rw [ownerSlot_eq] at h
  simp only [owners, Finset.mem_insert, Finset.mem_singleton]
  by_contra hn
  simp only [not_or] at hn
  obtain ⟨ha, hb, hc⟩ := hn
  apply h
  have e1 : Word.ofAddress alice ≠ Word.ofAddress a := fun e => ha (Word.ofAddress_injective e).symm
  have e2 : Word.ofAddress bob ≠ Word.ofAddress a := fun e => hb (Word.ofAddress_injective e).symm
  have e3 : Word.ofAddress carol ≠ Word.ofAddress a := fun e => hc (Word.ofAddress_injective e).symm
  simp [world, dep, World.sload, World.account, Storage.get, Std.ExtTreeMap.getD_insert, e1, e2, e3]
  exact fun e => h0 e.symm

theorem slot_ne (a : Address) : ownerSlot crypto a ≠ 1 := fun h => by
  rw [ownerSlot_eq] at h
  have := congrArg BitVec.toNat h
  rw [toNat_ofAddress_add_two] at this
  simp at this

theorem signers_ok : Signers crypto ctx.block.chainId dep.ms owners signers := by
  intro x v r s a _ h
  simp only [ecrecoverAddress?, crypto] at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp at h

/-- **The theorem on this world**: with one signer among three owners and threshold `2`, no
transaction upgrades the proxy or changes ProxyAdmin's owner or the Safe's configuration. -/
theorem world_impl_kept {tr : TransientStorage} {msg : Message} (htop : TopOk dep.Rl world msg)
    {fuel : Nat} {r : MessageResult} (hr : processMessageCall fuel ctx world tr msg = .ok r) :
    dep.G crypto owners 2 r.world := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := world_ok
  exact dep.impl_kept h1 h2 h3 h4 h5 h6 h7 (by decide) world_owners signers_ok (by decide)
    slot_ne (.inl (by decide)) (fun h => absurd h (by decide)) htop hr

end Example

end Examples.Actor.SafeGuard
