import Verified.Safe.Bytecode.Proxy
import Verified.Safe.Bytecode.Singleton.Exec

/-!
# Only a quorum of Safe v1.5.0 owners can upgrade: the upgrade guard on bytecode

`Verified.Safe.MiniSafe.Guard.Dep.impl_kept` with the real Safe instead of `MiniSafe`: the deployed
OpenZeppelin v5.7.0 `TransparentUpgradeableProxy` at `px`, its `ProxyAdmin` at `pa` owned by a
`SafeProxy` at `sf` running the Safe v1.5.0 singleton deployed at `sg`, and the implementation
`ActorImpl` at `ia`. `impl_kept`: **in any transaction whose signers `T` include fewer than
`thr` owners, the implementation slot, the ProxyAdmin's owner and the Safe's configuration
(singleton, threshold, owners, modules, guards, fallback handler, the non-signers' approvals) are
unchanged** — any calldata, any value, any depth, reentrancy, reverts, `simulateAndRevert`.

This is `processMessageCall_guardD` (`EvmLogic.Program.Nested.Sandbox`) with:

- relays the proxy, ProxyAdmin, the implementation, the Safe and the singleton account;
- the world invariant `G` (`Defs.lean`), the run predicate `Rw` (hashing), the doom point
  `simulateAndRevert`'s `DELEGATECALL`;
- frame invariants: ProxyAdmin, the proxy and the implementation from their certificates, as
  in `Proxy.Guard` (a ProxyAdmin frame is not sent by the Safe: the Safe calls relays only by
  `DELEGATECALL` of the singleton and by static calls); a Safe frame runs `SafeProxy`
  (`proxy_frame`) or the singleton (`sg_frame`); a frame at the singleton account acts only as
  that account.
-/

namespace Verified.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open EvmLogic.AbsInt EvmLogic.AbsInt.Guard Verified.OpenZeppelin.Contracts EvmLogic.Solidity
open Verified.OpenZeppelin.Proxy Verified.Safe.Contracts

namespace Dep

variable (D : Dep)

/-- Valuations: ProxyAdmin (sender, owner `sf`), the proxy (admin; sender, implementation). -/
def envPA (c : Address) : Env := ⟨fun _ => 0, fun i => if i = 0 then c else D.sf⟩
def envPX (c : Address) : Env := ⟨fun _ => D.pa, fun i => if i = 0 then c else D.ia⟩

def Jpa (m : Machine) : Prop :=
  m.frame.msg.currentTarget = D.pa ∧ m.frame.code = OzProxyAdmin.runtimeCode ∧
    m.frame.msg.caller ≠ D.sf ∧ GInCert (D.envPA m.frame.msg.caller) tPA m

def Jpx (m : Machine) : Prop :=
  m.frame.msg.currentTarget = D.px ∧
    ((m.frame.code = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩ ∧ m.frame.msg.caller ≠ D.pa ∧
      GInCert (D.envPX m.frame.msg.caller) tPX m) ∨ Verified.OpenZeppelin.Proxy.Dep.Jia m)

def Jim (m : Machine) : Prop := m.frame.msg.currentTarget = D.ia ∧ Verified.OpenZeppelin.Proxy.Dep.Jia m

/-- A frame of the Safe: the proxy's code or the singleton's, for a sender other than itself. -/
def Jsf (crypto : Crypto) (chainId : Nat) (O T : Finset Address) (thr : Nat) (h₀ : Word)
    (fork : Fork) (m : Machine) : Prop :=
  m.frame.msg.currentTarget = D.sf ∧ m.frame.msg.caller ≠ D.sf ∧
    ((m.frame.code = SafeProxy.runtimeCode ∧ D.Jproxy crypto chainId O T thr h₀ fork m) ∨
     (m.frame.code = SafeSingleton.runtimeCode ∧ D.Jsg crypto chainId O T thr h₀ fork m))

/-- The frame invariants. -/
def J (crypto : Crypto) (chainId : Nat) (O T : Finset Address) (thr : Nat) (h₀ : Word)
    (fork : Fork) (r : Address) : Machine → Prop :=
  if r = D.pa then D.Jpa else if r = D.px then D.Jpx
  else if r = D.sf then D.Jsf crypto chainId O T thr h₀ fork
  else if r = D.sg then fun m => m.frame.msg.currentTarget = D.sg else D.Jim

/-- Doom points: `simulateAndRevert`'s `DELEGATECALL` in a singleton frame of the Safe. -/
def Dm (r : Address) (m : Machine) : Prop :=
  r = D.sf ∧ m.frame.code = SafeSingleton.runtimeCode ∧ Dsim m

theorem code_px : D.code D.px = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩ := by simp [code]
theorem code_pa : D.code D.pa = OzProxyAdmin.runtimeCode := by simp [code, Ne.symm D.px_pa]
theorem code_ia : D.code D.ia = ActorImpl.runtimeCode := by
  simp [code, Ne.symm D.px_ia, Ne.symm D.pa_ia, Ne.symm D.sf_ia, Ne.symm D.sg_ia]

section
variable {crypto : Crypto} {chainId : Nat} {O T : Finset Address} {thr : Nat} {h₀ : Word}
  {fork : Fork}

theorem J_pa : D.J crypto chainId O T thr h₀ fork D.pa = D.Jpa := by simp [J]
theorem J_px : D.J crypto chainId O T thr h₀ fork D.px = D.Jpx := by simp [J, D.px_pa]
theorem J_sf : D.J crypto chainId O T thr h₀ fork D.sf = D.Jsf crypto chainId O T thr h₀ fork := by
  simp [J, D.sf_pa, D.sf_px]
theorem J_sg : D.J crypto chainId O T thr h₀ fork D.sg = fun m => m.frame.msg.currentTarget = D.sg := by
  simp [J, D.sg_pa, D.sg_px, D.sg_sf]
theorem J_ia : D.J crypto chainId O T thr h₀ fork D.ia = D.Jim := by
  simp [J, Ne.symm D.pa_ia, Ne.symm D.px_ia, Ne.symm D.sf_ia, Ne.symm D.sg_ia]
end

/-! ## The world -/

theorem codeOk : RelayCodeOk D.Rl D.code where
  size r hr := by
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [code_px, Verified.OpenZeppelin.Proxy.Dep.size_proxy]; decide
    · rw [code_pa, OzProxyAdmin.size_runtimeCode]; decide
    · rw [code_ia, ActorImpl.size_runtimeCode]; decide
    · rw [code_sf, SafeProxy.size_runtimeCode]; decide
    · rw [code_sg, SafeSingleton.size_runtimeCode]; decide
  deleg r hr := by
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [code_px]; exact Verified.OpenZeppelin.Proxy.Dep.deleg_none (by rw [Verified.OpenZeppelin.Proxy.Dep.size_proxy]; decide)
    · rw [code_pa]; exact Verified.OpenZeppelin.Proxy.Dep.deleg_none (by rw [OzProxyAdmin.size_runtimeCode]; decide)
    · rw [code_ia]; exact Verified.OpenZeppelin.Proxy.Dep.deleg_none (by rw [ActorImpl.size_runtimeCode]; decide)
    · rw [code_sf]; exact deleg_sf
    · rw [code_sg]; exact deleg_sg

variable {crypto : Crypto} {chainId : Nat} {O T : Finset Address} {thr : Nat} {h₀ : Word}

/-- `G` depends only on the storage of the proxy, ProxyAdmin and the Safe. -/
theorem G_keep3 {w w' : World} (h : D.G crypto chainId O T thr h₀ w)
    (hpx : Keep D.px w w') (hpa : Keep D.pa w w') (hsf : Keep D.sf w w') :
    D.G crypto chainId O T thr h₀ w' := by
  have hs : w'.sload D.sf = w.sload D.sf := funext fun k => hsf.sload' k
  refine ⟨(hpx.sload' _).trans h.1, (hpa.sload' _).trans h.2.1, ?_⟩
  rw [hs]; exact h.2.2

theorem G_keep : ∀ w w', D.G crypto chainId O T thr h₀ w → KeepP D.Rl w w' →
    D.G crypto chainId O T thr h₀ w' := fun _ _ h hk =>
  D.G_keep3 h (hk _ (.inl rfl)) (hk _ (.inr (.inl rfl))) (hk _ (.inr (.inr (.inr (.inl rfl)))))

theorem ite_ne {k κ v : Word} {s : Word → Word} (h : κ ≠ k) :
    (if κ = k then v else s κ) = s κ := by simp [h]

/-- The Safe's configuration survives a write to an unprotected key. -/
theorem SafeOk.sstore {s : Word → Word} (h : D.SafeOk crypto chainId O T thr h₀ s) {k v : Word}
    (hk : ¬ Protected crypto chainId O T D.sf k) :
    D.SafeOk crypto chainId O T thr h₀ (fun κ => if κ = k then v else s κ) := by
  have ne : ∀ κ, Protected crypto chainId O T D.sf κ → κ ≠ k := fun κ hκ e => hk (e ▸ hκ)
  refine ⟨?_, ?_, fun a ha => h.owners a ?_, ?_, fun a ha => ?_, ?_, ?_, ?_,
    fun a hO hT sh hsh => ?_⟩
  · rw [ite_ne (ne _ (.inl rfl))]; exact h.singleton
  · rw [ite_ne (ne _ (.inr (.inl rfl)))]; exact h.threshold
  · rwa [ite_ne (ne _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨a, rfl⟩)))))))] at ha
  · rw [ite_ne (ne _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl⟩))))))))]
    exact h.sentinelModule
  · rw [ite_ne (ne _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl⟩))))))))]
    exact h.modules a ha
  · rw [ite_ne (ne _ (.inr (.inr (.inl rfl))))]; exact h.guard
  · rw [ite_ne (ne _ (.inr (.inr (.inr (.inl rfl)))))]; exact h.moduleGuard
  · rw [ite_ne (ne _ (.inr (.inr (.inr (.inr (.inl rfl))))))]; exact h.handler
  · rw [ite_ne (ne _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨a, sh, hO, hT, hsh, rfl⟩))))))))]
    exact h.approvals a hO hT sh hsh

theorem sload_sstore_fun (w : World) (a : Address) (k v : Word) :
    (w.sstore a k v).sload a = fun κ => if κ = k then v else w.sload a κ := by
  funext κ
  by_cases h : κ = k
  · subst h; simp
  · rw [World.sload_sstore_ne_key _ _ _ h, ite_ne h]

/-- **An instruction keeps the protected state** if, when it is an `SSTORE`, it writes neither the
implementation slot of the proxy nor ProxyAdmin, nor a protected key of the Safe. -/
theorem G_step {m m' : Machine} {b : UInt8} {a : Action}
    (hG : D.G crypto chainId O T thr h₀ m.world) (hrc : RelayCode D.Rl D.code m.world)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m'))
    (hss : Opcode.decode m.ctx.fork b = .sstore → ∃ k v,
      (m.frame.msg.currentTarget ≠ D.pa) ∧
      (m.frame.msg.currentTarget = D.px → k ≠ implSlot) ∧
      (m.frame.msg.currentTarget = D.sf → ¬ Protected crypto chainId O T D.sf k) ∧
      m'.world = m.world.sstore m.frame.msg.currentTarget k v) :
    D.G crypto chainId O T thr h₀ m'.world := by
  by_cases hs : Opcode.decode m.ctx.fork b = .sstore
  · obtain ⟨k, v, hpa, hpx, hsf, hw⟩ := hss hs
    rw [hw]
    set t := m.frame.msg.currentTarget
    refine ⟨?_, ?_, ?_⟩
    · by_cases ht : D.px = t
      · rw [← ht, World.sload_sstore_ne_key _ _ _ (Ne.symm (hpx ht.symm))]
        exact hG.1
      · rw [World.sload_sstore_ne_addr _ _ _ _ ht]; exact hG.1
    · rw [World.sload_sstore_ne_addr _ _ _ _ (Ne.symm hpa)]; exact hG.2.1
    · by_cases ht : D.sf = t
      · rw [← ht, sload_sstore_fun]
        exact SafeOk.sstore D hG.2.2 (hsf ht.symm)
      · have : (m.world.sstore t k v).sload D.sf = m.world.sload D.sf :=
          funext fun κ => World.sload_sstore_ne_addr _ _ _ _ ht
        rw [this]; exact hG.2.2
  · have hpx := (exec_slot _ hs m D.px implSlot).of_run he
      (by rw [hrc _ (.inl rfl), code_px, Verified.OpenZeppelin.Proxy.Dep.size_proxy]; decide)
    have hpa := (exec_slot _ hs m D.pa 0).of_run he
      (by rw [hrc _ (.inr (.inl rfl)), code_pa, OzProxyAdmin.size_runtimeCode]; decide)
    have hsf : m'.world.sload D.sf = m.world.sload D.sf := funext fun κ =>
      (exec_slot _ hs m D.sf κ).of_run he
        (by rw [hrc _ (.inr (.inr (.inr (.inl rfl)))), code_sf, SafeProxy.size_runtimeCode]; decide)
    exact ⟨hpx.trans hG.1, hpa.trans hG.2.1, by rw [hsf]; exact hG.2.2⟩

/-! ## Facts the certificates assume -/

theorem envOk_pa {m : Machine} (ht : m.frame.msg.currentTarget = D.pa)
    (hc : m.frame.msg.caller ≠ D.sf) (hG : D.G crypto chainId O T thr h₀ m.world) :
    EnvOk (D.envPA m.frame.msg.caller) cfgPA m where
  caller i hi := by
    simp only [cfgPA, Option.some.injEq] at hi; subst hi; rfl
  slots k i hk key hkey := by
    obtain ⟨rfl, rfl⟩ := Verified.OpenZeppelin.Proxy.Dep.slotAtom_pa hk
    have : key = 0 := BitVec.eq_of_toNat_eq (by simpa using hkey)
    rw [this, ht]; exact hG.2.1
  distinct a b hab := by
    simp only [cfgPA, List.mem_singleton, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨_, _, rfl, rfl, by simpa [envPA] using hc⟩

theorem envOk_px {m : Machine} (ht : m.frame.msg.currentTarget = D.px)
    (hc : m.frame.msg.caller ≠ D.pa) (hG : D.G crypto chainId O T thr h₀ m.world) :
    EnvOk (D.envPX m.frame.msg.caller) cfgPX m where
  caller i hi := by
    simp only [cfgPX, Option.some.injEq] at hi; subst hi; rfl
  slots k i hk key hkey := by
    obtain ⟨rfl, rfl⟩ := Verified.OpenZeppelin.Proxy.Dep.slotAtom_px hk
    have : key = implSlot := BitVec.eq_of_toNat_eq hkey
    rw [this, ht]; exact hG.1
  distinct a b hab := by
    simp only [cfgPX, List.mem_singleton, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨_, _, rfl, rfl, by simpa [envPX] using hc⟩

/-- A frame running the implementation keeps `G` (it writes only slot `0`, never at ProxyAdmin
or the Safe). -/
theorem Jia_good {m m' : Machine} {b : UInt8} {a : Action} (hJ : Verified.OpenZeppelin.Proxy.Dep.Jia m)
    (hpa : m.frame.msg.currentTarget ≠ D.pa) (hsf : m.frame.msg.currentTarget ≠ D.sf)
    (hG : D.G crypto chainId O T thr h₀ m.world) (hrc : RelayCode D.Rl D.code m.world)
    (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m')) :
    D.G crypto chainId O T thr h₀ m'.world := by
  refine D.G_step hG hrc he fun hs => ?_
  obtain ⟨k, v, r, av, -, hw, hav, hk⟩ := ginCert_sstore (ia_cert _) hJ.1 hJ.2 hb hs he
  simp only [cfgIA, beq_iff_eq] at hav
  subst hav
  refine ⟨k, v, hpa, fun _ e => Verified.OpenZeppelin.Proxy.Dep.implSlot_ne_zero (by rw [← e]; exact hk),
    fun h => absurd h hsf, hw⟩

/-! ## Who calls whom -/

theorem iss_pa {mp : Machine} {c : Message} : ¬ D.Iss D.pa mp c := by
  rintro (⟨h, -⟩ | ⟨h, -⟩ | h)
  · exact D.px_pa h.symm
  · exact D.sf_pa h.symm
  · exact D.sg_pa h.symm

theorem iss_ia {mp : Machine} {c : Message} : ¬ D.Iss D.ia mp c := by
  rintro (⟨h, -⟩ | ⟨h, -⟩ | h)
  · exact D.px_ia h.symm
  · exact D.sf_ia h.symm
  · exact D.sg_ia h.symm

/-- A non-static message the Safe issues to a relay is the singleton's `DELEGATECALL`. -/
theorem iss_sf {mp : Machine} {c : Message} (h : D.Iss D.sf mp c) (hs : c.isStatic = false)
    (hr : D.Rl c.currentTarget) :
    c.currentTarget = D.sf ∧ c.code = SafeSingleton.runtimeCode ∧ c.caller ≠ D.sf := by
  rcases h with ⟨h, -⟩ | ⟨-, h | h | h⟩ | h
  · exact absurd h D.sf_px
  · rw [hs] at h; cases h
  · exact absurd hr h
  · exact h
  · exact absurd h.symm D.sg_sf

variable {K : Context → Prop}

/-- **A ProxyAdmin frame is not sent by the Safe**: the Safe sends relays only static calls and
its own `DELEGATECALL`. -/
theorem pa_caller {X : Address → Prop} {G : World → Prop} {m : Machine}
    (hs : GuardStartK K D.Rl D.code X G D.Iss D.pa m) : m.frame.msg.caller ≠ D.sf := by
  rcases hs.origin with ⟨-, hnr⟩ | ⟨mp, -, -, -, hids, hiss⟩
  · exact fun h => hnr (h ▸ .inr (.inr (.inr (.inl rfl))))
  · rcases hids with hc | ⟨hc, ht⟩
    · intro h
      rw [hc] at h
      have := (D.iss_sf (h ▸ hiss (h ▸ .inr (.inr (.inr (.inl rfl))))) hs.base.static
        (by rw [hs.base.target]; exact .inr (.inl rfl))).1
      rw [hs.base.target] at this
      exact D.sf_pa this.symm
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
    · intro _
      have ht' : mp.frame.msg.currentTarget = D.px := ht ▸ hs.base.target
      rcases hiss (ht' ▸ .inl rfl) with ⟨-, hc'⟩ | ⟨h, -⟩ | h
      · rw [hcode] at hc'
        have := congrArg ByteArray.size hc'
        rw [Verified.OpenZeppelin.Proxy.Dep.size_proxy, ActorImpl.size_runtimeCode] at this
        cases this
      · exact D.sf_px (ht' ▸ h).symm
      · exact D.sg_px (ht' ▸ h).symm

/-- A frame of the Safe is not sent by the Safe; it runs the proxy's code or the singleton's. -/
theorem sf_start {X : Address → Prop} {G : World → Prop} {m : Machine}
    (hs : GuardStartK K D.Rl D.code X G D.Iss D.sf m) :
    m.frame.msg.caller ≠ D.sf ∧
      (m.frame.msg.code = SafeProxy.runtimeCode ∨ m.frame.msg.code = SafeSingleton.runtimeCode) := by
  have hrel : D.Rl m.frame.msg.currentTarget := by
    rw [hs.base.target]; exact .inr (.inr (.inr (.inl rfl)))
  refine ⟨?_, ?_⟩
  · rcases hs.origin with ⟨-, hnr⟩ | ⟨mp, -, -, -, hids, hiss⟩
    · exact fun h => hnr (h ▸ .inr (.inr (.inr (.inl rfl))))
    · rcases hids with hc | ⟨hc, ht⟩
      · intro h
        rw [hc] at h
        exact (D.iss_sf (h ▸ hiss (h ▸ .inr (.inr (.inr (.inl rfl))))) hs.base.static hrel).2.2
          (hc ▸ h)
      · have ht' : mp.frame.msg.currentTarget = D.sf := ht ▸ hs.base.target
        exact (D.iss_sf (ht' ▸ hiss (ht' ▸ .inr (.inr (.inr (.inl rfl))))) hs.base.static
          hrel).2.2
  · rcases hs.base.entry with ⟨h1, -⟩ | ⟨mp, -, ht, -, -, hiss⟩
    · left; rw [h1, code_sf]
    · right
      exact (D.iss_sf hiss hs.base.static hrel).2.1

theorem decode_sstore_lt : ∀ n < 256, ∀ fk : Fork,
    Opcode.decode fk n.toUInt8 = .sstore → n.toUInt8 = 0x55 := by
  intro n hn fk; cases fk <;> revert n <;> decide +kernel

theorem decode_sstore {fk : Fork} {b : UInt8} (h : Opcode.decode fk b = .sstore) : b = 0x55 := by
  simpa using decode_sstore_lt b.toNat b.toNat_lt fk (by simpa using h)

/-! ## The frame obligations -/

variable (crypto chainId O T thr h₀)

/-- The context of the transaction. -/
abbrev Kc (ctx : Context) (c : Context) : Prop := c = ctx

variable {Xi : Address → Prop}

/-- **ProxyAdmin, for any sender but the Safe**: nothing requested, nothing written. -/
theorem inv_pa : GuardInvK K D.Rl D.code Xi (D.G crypto chainId O T thr h₀) D.Iss D.pa D.Jpa where
  start m hs := by
    obtain ⟨hpc, hst, hcd⟩ := Verified.OpenZeppelin.Proxy.Dep.fresh_frame hs.base.fresh
    have hcode : m.frame.code = OzProxyAdmin.runtimeCode := by
      rcases hs.base.entry with ⟨h1, -⟩ | ⟨mp, -, -, -, -, hiss⟩
      · rw [hcd, h1, code_pa]
      · exact absurd hiss D.iss_pa
    exact ⟨hs.base.target, hcode, D.pa_caller hs, ginCert_init (pa_cert _) hpc hst⟩
  issue m c hJ _ _ hr :=
    (Verified.OpenZeppelin.Proxy.Dep.no_requests (pa_cert _) (fun _ => rfl) hJ.2.1 hJ.2.2.2 hr).elim
  good m b a m' hJ hG hrc hb he := by
    refine D.G_step hG hrc he fun hs => ?_
    obtain ⟨-, -, -, av, -, -, hav, -⟩ := ginCert_sstore (pa_cert _) hJ.2.1 hJ.2.2.2 hb hs he
    cases hav
  next m b m' hJ hG _ hb he := by
    obtain ⟨hmsg, hcd⟩ := Verified.OpenZeppelin.Proxy.Dep.same_next he
    refine ⟨hmsg ▸ hJ.1, hcd ▸ hJ.2.1, hmsg ▸ hJ.2.2.1, ?_⟩
    rw [hmsg]
    exact ginCert_next (pa_cert _) hJ.2.1 hJ.2.2.2 (D.envOk_pa hJ.1 hJ.2.2.1 hG) hb he
  resume m b a m' hJ _ _ hb he ha M res hM _ _ _ _ := by
    obtain ⟨hmsg, hcd⟩ := Verified.OpenZeppelin.Proxy.Dep.same_resume he res hM
    refine ⟨hmsg ▸ hJ.1, hcd ▸ hJ.2.1, hmsg ▸ hJ.2.2.1, ?_⟩
    rw [hmsg]
    exact ginCert_resume (pa_cert _) hJ.2.1 hJ.2.2.2 hb he ha M res hM

/-- **The implementation at its own address**: nothing requested, only slot `0` written. -/
theorem inv_ia : GuardInvK K D.Rl D.code Xi (D.G crypto chainId O T thr h₀) D.Iss D.ia D.Jim where
  start m hs := by
    obtain ⟨hpc, hst, hcd⟩ := Verified.OpenZeppelin.Proxy.Dep.fresh_frame hs.base.fresh
    have hcode : m.frame.code = ActorImpl.runtimeCode := by
      rcases hs.base.entry with ⟨h1, -⟩ | ⟨mp, -, -, -, -, hiss⟩
      · rw [hcd, h1, code_ia]
      · exact absurd hiss D.iss_ia
    exact ⟨hs.base.target, hcode, ginCert_init (ia_cert _) hpc hst⟩
  issue m c hJ _ _ hr :=
    (Verified.OpenZeppelin.Proxy.Dep.no_requests (ia_cert _) (fun _ => rfl) hJ.2.1 hJ.2.2 hr).elim
  good m b a m' hJ hG hrc hb he :=
    D.Jia_good hJ.2 (by rw [hJ.1]; exact Ne.symm D.pa_ia) (by rw [hJ.1]; exact Ne.symm D.sf_ia) hG
      hrc hb he
  next m b m' hJ _ _ hb he := by
    obtain ⟨hmsg, hcd⟩ := Verified.OpenZeppelin.Proxy.Dep.same_next he
    exact ⟨hmsg ▸ hJ.1, hcd ▸ hJ.2.1,
      ginCert_next (ia_cert _) hJ.2.1 hJ.2.2 (Verified.OpenZeppelin.Proxy.Dep.envOk_ia m) hb he⟩
  resume m b a m' hJ _ _ hb he ha M res hM _ _ _ _ := by
    obtain ⟨hmsg, hcd⟩ := Verified.OpenZeppelin.Proxy.Dep.same_resume he res hM
    exact ⟨hmsg ▸ hJ.1, hcd ▸ hJ.2.1, ginCert_resume (ia_cert _) hJ.2.1 hJ.2.2 hb he ha M res hM⟩

/-- **The proxy, for any sender but ProxyAdmin**: nothing written, and the only requests run
the implementation's code. -/
theorem inv_px : GuardInvK K D.Rl D.code Xi (D.G crypto chainId O T thr h₀) D.Iss D.px D.Jpx where
  start m hs := by
    obtain ⟨hpc, hst, hcd⟩ := Verified.OpenZeppelin.Proxy.Dep.fresh_frame hs.base.fresh
    refine ⟨hs.base.target, ?_⟩
    rcases hs.base.entry with ⟨h1, -⟩ | ⟨mp, -, -, -, -, hiss⟩
    · have hc : m.frame.msg.code = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩ := by
        rw [h1, code_px]
      exact .inl ⟨hcd.trans hc, D.px_caller hs hc,
        ginCert_init (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hpc hst⟩
    · rcases hiss with ⟨-, hc⟩ | ⟨h, -⟩ | h
      · exact .inr ⟨hcd.trans hc, ginCert_init (ia_cert _) hpc hst⟩
      · exact absurd h.symm D.sf_px
      · exact absurd h.symm D.sg_px
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
    · exact (Verified.OpenZeppelin.Proxy.Dep.no_requests (ia_cert _) (fun _ => rfl) hia.1 hia.2
        hr).elim
  good m b a m' hJ hG hrc hb he := by
    rcases hJ.2 with ⟨hcd, hcl, hin⟩ | hia
    · refine D.G_step hG hrc he fun hs => ?_
      obtain ⟨-, -, -, av, -, -, hav, -⟩ :=
        ginCert_sstore (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hcd hin hb hs he
      cases hav
    · exact D.Jia_good hia (by rw [hJ.1]; exact D.px_pa) (by rw [hJ.1]; exact Ne.symm D.sf_px) hG
        hrc hb he
  next m b m' hJ hG _ hb he := by
    obtain ⟨hmsg, hcd⟩ := Verified.OpenZeppelin.Proxy.Dep.same_next he
    refine ⟨hmsg ▸ hJ.1, ?_⟩
    rcases hJ.2 with ⟨hc, hcl, hin⟩ | hia
    · refine .inl ⟨hcd ▸ hc, hmsg ▸ hcl, ?_⟩
      rw [hmsg]
      exact ginCert_next (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hc hin
        (D.envOk_px hJ.1 hcl hG) hb he
    · exact .inr ⟨hcd ▸ hia.1, ginCert_next (ia_cert _) hia.1 hia.2
        (Verified.OpenZeppelin.Proxy.Dep.envOk_ia m) hb he⟩
  resume m b a m' hJ _ _ hb he ha M res hM _ _ _ _ := by
    obtain ⟨hmsg, hcd⟩ := Verified.OpenZeppelin.Proxy.Dep.same_resume he res hM
    refine ⟨hmsg ▸ hJ.1, ?_⟩
    rcases hJ.2 with ⟨hc, hcl, hin⟩ | hia
    · refine .inl ⟨hcd ▸ hc, hmsg ▸ hcl, ?_⟩
      rw [hmsg]
      exact ginCert_resume (px_cert _ (ν := D.envPX m.frame.msg.caller) rfl) hc hin hb he ha M
        res hM
    · exact .inr ⟨hcd ▸ hia.1, ginCert_resume (ia_cert _) hia.1 hia.2 hb he ha M res hM⟩

/-- A relay without doom points. -/
theorem ofK {Rr : Machine → Prop} {Dmr : Machine → Prop} {r : Address} {Jr : Machine → Prop}
    {Xr : Address → Prop} {Gr : World → Prop}
    (h : GuardInvK K D.Rl D.code Xr Gr D.Iss r Jr) (hD : ∀ m, ¬ Dmr m) :
    GuardInvD K D.Rl D.code Xr Gr Rr D.Iss Dmr r Jr where
  start := h.start
  issue m c hJ hg _ hw _ hr _ := h.issue m c hJ hg hw hr
  good m b a m' hJ hg _ hw _ hb he := h.good m b a m' hJ hg hw hb he
  next m b m' hJ hg _ hw _ hb he := h.next m b m' hJ hg hw hb he
  resumeJ m b a m' hJ hg _ hw _ hb he _ ha M res hM hMp hMc hMpre _ _ hpre :=
    h.resume m b a m' hJ hg hw hb he ha M res hM hMp hMc hMpre hpre
  doom m _ _ _ _ _ _ _ _ _ _ hd := (hD m hd).elim
  doomCreate m _ _ _ _ _ _ _ _ _ _ hd := hD m hd

theorem proxy_ne_singleton : SafeProxy.runtimeCode ≠ SafeSingleton.runtimeCode := fun h => by
  have := congrArg ByteArray.size h
  rw [SafeProxy.size_runtimeCode, SafeSingleton.size_runtimeCode] at this
  cases this

variable {crypto chainId O T thr h₀}

/-- **The Safe**: a `SafeProxy` frame or a singleton frame, for a sender other than itself. -/
theorem inv_sf (ctx : Context) (hthr : thr < 2 ^ 256) (hcard : (O ∩ T).card < thr)
    (hsig : Signers ctx.crypto ctx.block.chainId D.sf O T) (hh : h₀ = 0 ∨ ¬ D.Rl (Word.toAddress h₀)) :
    GuardInvD (Kc ctx) D.Rl D.code (X ctx.fork O T)
      (D.G ctx.crypto ctx.block.chainId O T thr h₀) (D.Rw ctx.crypto ctx.block.chainId O T) D.Iss
      (D.Dm D.sf) D.sf (D.Jsf ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork) where
  start m hs := by
    obtain ⟨hcl, hcode⟩ := D.sf_start hs
    obtain ⟨o, sn, hfr⟩ := hs.base.fresh
    have hctx : m.ctx = ctx := hs.ctx
    have hpre : m.precompiles = PrecompileImpl.standard ctx := by rw [hs.base.pre, hctx]
    refine ⟨hs.base.target, hcl, ?_⟩
    rcases hcode with hc | hc
    · have hmc : m.frame.code = SafeProxy.runtimeCode := by rw [hfr]; exact hc
      refine .inl ⟨hmc, D.proxy_frame (msg := m.frame.msg) (ctx := ctx) (w := m.world)
        hs.base.target hcl ⟨rfl, hctx, hpre, hmc, by rw [hfr]; rfl, by rw [hfr]; rfl,
          by rw [hfr]; rfl, rfl⟩⟩
    · have hmc : m.frame.code = SafeSingleton.runtimeCode := by rw [hfr]; exact hc
      have hC : D.SgCtx O T thr h₀ m.frame.msg ctx :=
        ⟨hs.base.target, hcl, hs.caller, hthr, hcard, hsig, hh⟩
      refine .inr ⟨hmc, D.sg_frame (msg := m.frame.msg) (ctx := ctx) (w := m.world)
        hC (D.sg_execTransaction hC)
        ⟨rfl, hctx, hpre, hmc, by rw [hfr]; rfl, by rw [hfr]; rfl, by rw [hfr]; rfl, rfl⟩⟩
  issue m c hJ hg hR hrc hI hreq hnd := by
    obtain ⟨b, a, m', hb, he, (⟨req, rfl, rfl⟩ | rfl)⟩ := hreq
    · rcases hJ.2.2 with ⟨-, hJp⟩ | ⟨hc, hJs⟩
      · exact hJp.iss ⟨hg, hI, hrc, hR⟩ hb he id
      · exact hJs.iss ⟨hg, hI, hrc, hR⟩ hb he fun hd => hnd ⟨rfl, hc, hd⟩
    · rcases hJ.2.2 with ⟨-, hJp⟩ | ⟨-, hJs⟩
      · exact (hJp.create ⟨hg, hI, hrc, hR⟩ hb he).elim
      · exact (hJs.create ⟨hg, hI, hrc, hR⟩ hb he).elim
  good m b a m' hJ hg hR hrc hI hb he := by
    refine D.G_step hg hrc he fun hs => ?_
    rw [hs] at he
    obtain ⟨k, v, r, hstk, hw⟩ := (exec_sstore_world m).of_run he
    have h55 : m.frame.code[m.frame.pc]? = some 0x55 := by rw [hb, decode_sstore hs]
    refine ⟨k, v, by rw [hJ.1]; exact D.sf_pa, fun h => absurd (hJ.1.symm.trans h) D.sf_px,
      fun _ => ?_, hw⟩
    rcases hJ.2.2 with ⟨-, hJp⟩ | ⟨hc, hJs⟩
    · exact (hJp.safe ⟨hg, hI, hrc, hR⟩ k (v :: r) h55 hstk).elim
    · exact hR hJ.1 hc k (v :: r) h55 hstk (hJs.safe ⟨hg, hI, hrc, hR⟩ k (v :: r) h55 hstk)
  next m b m' hJ hg hR hrc hI hb he := by
    obtain ⟨hmsg, hcd⟩ := Verified.OpenZeppelin.Proxy.Dep.same_next he
    refine ⟨hmsg ▸ hJ.1, hmsg ▸ hJ.2.1, ?_⟩
    rcases hJ.2.2 with ⟨hc, hJp⟩ | ⟨hc, hJs⟩
    · exact .inl ⟨hcd ▸ hc, hJp.next ⟨hg, hI, hrc, hR⟩ hb he⟩
    · exact .inr ⟨hcd ▸ hc, hJs.next ⟨hg, hI, hrc, hR⟩ hb he⟩
  resumeJ m b a m' hJ hg hR hrc hI hb he hnd ha M res hM hMp hMc hMpre hk _ hpre := by
    obtain ⟨hmsg, hcd⟩ := Verified.OpenZeppelin.Proxy.Dep.same_resume he res hM
    refine ⟨hmsg ▸ hJ.1, hmsg ▸ hJ.2.1, ?_⟩
    have hR' : D.Rsf ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := ⟨hg, hI, hrc, hR⟩
    rcases ha with ⟨req, rfl⟩ | ⟨msg, rfl⟩
    · by_cases hp : precompileOf m'.precompiles req.msg = none
      · rcases hJ.2.2 with ⟨hc, hJp⟩ | ⟨hc, hJs⟩
        · exact .inl ⟨hcd ▸ hc, hJp.real hR' hb he id hp res hM hMp hMc hMpre hk trivial⟩
        · exact .inr ⟨hcd ▸ hc, hJs.real hR' hb he (fun hd => hnd ⟨rfl, hc, hd⟩) hp res hM hMp
            hMc hMpre hk trivial⟩
      · rw [hpre req rfl hp]
        rw [hpre req rfl hp] at hcd
        rcases hJ.2.2 with ⟨hc, hJp⟩ | ⟨hc, hJs⟩
        · exact .inl ⟨hcd ▸ hc, hJp.pre hR' hb he id hp⟩
        · exact .inr ⟨hcd ▸ hc, hJs.pre hR' hb he (fun hd => hnd ⟨rfl, hc, hd⟩) hp⟩
    · rcases hJ.2.2 with ⟨-, hJp⟩ | ⟨-, hJs⟩
      · exact (hJp.create hR' hb he).elim
      · exact (hJs.create hR' hb he).elim
  doom m b req m' hJ hg hR hrc hI hb he hdm M res hM hMp hMc hMpre hk := by
    rcases hJ.2.2 with ⟨hc, -⟩ | ⟨-, hJs⟩
    · exact absurd (hc.symm.trans hdm.2.1) proxy_ne_singleton
    · exact hJs.doom ⟨hg, hI, hrc, hR⟩ hb he hdm.2.2 res hM hMp hMc hMpre hk
  doomCreate m b msg m' hJ hg hR hrc hI hb he _ := by
    rcases hJ.2.2 with ⟨-, hJp⟩ | ⟨-, hJs⟩
    · exact hJp.create ⟨hg, hI, hrc, hR⟩ hb he
    · exact hJs.create ⟨hg, hI, hrc, hR⟩ hb he

/-- **The singleton account**: its frames act only as itself, so they keep `G`. -/
theorem inv_sg {Xr : Address → Prop} {Rr : Machine → Prop} :
    GuardInvD K D.Rl D.code Xr (D.G crypto chainId O T thr h₀) Rr D.Iss (D.Dm D.sg) D.sg
      (fun m => m.frame.msg.currentTarget = D.sg) where
  start m hs := hs.base.target
  issue _ _ _ _ _ _ _ _ _ := .inr (.inr rfl)
  good m b a m' hJ hg _ hrc _ hb he := by
    have hif : InstrFrame m m' := ((exec_frame _ m).of_run he).1
    have hk : ∀ p, D.Rl p → p ≠ D.sg → Keep p m.world m'.world := fun p hp hne =>
      hif.keep p (by rw [hrc p hp]; exact (codeOk D).size p hp)
        fun ⟨he', _⟩ => hne (he'.trans hJ)
    exact D.G_keep3 hg (hk _ (.inl rfl) (Ne.symm D.sg_px)) (hk _ (.inr (.inl rfl)) (Ne.symm D.sg_pa))
      (hk _ (.inr (.inr (.inr (.inl rfl)))) (Ne.symm D.sg_sf))
  next m b m' hJ _ _ _ _ _ he := (Verified.OpenZeppelin.Proxy.Dep.same_next he).1 ▸ hJ
  resumeJ m b a m' hJ _ _ _ _ _ he _ _ M res hM _ _ _ _ _ _ :=
    (Verified.OpenZeppelin.Proxy.Dep.same_resume he res hM).1 ▸ hJ
  doom _ _ _ _ _ _ _ _ _ _ _ hd := absurd hd.1 D.sg_sf
  doomCreate _ _ _ _ _ _ _ _ _ _ _ hd := absurd hd.1 D.sg_sf

theorem inv (ctx : Context) (hthr : thr < 2 ^ 256) (hcard : (O ∩ T).card < thr)
    (hsig : Signers ctx.crypto ctx.block.chainId D.sf O T) (hh : h₀ = 0 ∨ ¬ D.Rl (Word.toAddress h₀)) :
    ∀ r, D.Rl r → GuardInvD (Kc ctx) D.Rl D.code (X ctx.fork O T)
      (D.G ctx.crypto ctx.block.chainId O T thr h₀) (D.Rw ctx.crypto ctx.block.chainId O T) D.Iss
      (D.Dm r) r (D.J ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork r) := by
  rintro r (rfl | rfl | rfl | rfl | rfl)
  · rw [J_px]; exact D.ofK (D.inv_px _ _ _ _ _ _) fun _ h => D.sf_px h.1.symm
  · rw [J_pa]; exact D.ofK (D.inv_pa _ _ _ _ _ _) fun _ h => D.sf_pa h.1.symm
  · rw [J_ia]; exact D.ofK (D.inv_ia _ _ _ _ _ _) fun _ h => D.sf_ia h.1.symm
  · rw [J_sf]; exact D.inv_sf ctx hthr hcard hsig hh
  · rw [J_sg]; exact D.inv_sg

/-! ## The theorem -/

/-- **Only a quorum of the Safe's owners can upgrade.** From a world where the proxy, its
ProxyAdmin (owned by the Safe), the implementation, the `SafeProxy` and the Safe v1.5.0 singleton
are deployed, with the implementation slot holding `ia` and the Safe configured as `SafeOk`
(singleton `sg`, threshold `thr`, owners within `O`, only the sentinel module, no guard, no module
guard, fallback handler `h₀` unset or not a relay, no approval of a digest of this Safe by an owner
outside `T`): every top-level message call (before Prague or without EIP-7702 authorizations),
whose signers `T` (`Signers`) include fewer than `thr` owners, ends in a world with the same
implementation, the same owner of ProxyAdmin and the same Safe configuration.

Assumed: the owners outside `T` are externally owned accounts that have sent a transaction and
are not the sender (`hidle`, `hcaller`); from Prague on, likewise the address `1`; the
transaction does not run code at an idle account (`hcode`); hashing: the Safe's nonce and
approval writes during the transaction hit no protected key (`hR`, the run-level hypothesis
`Rw`). -/
theorem impl_kept {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    {O T : Finset Address} {thr : Nat} {h₀ : Word}
    (hpx : w.code D.px = OzTransparentProxy.runtimeCodeWith ⟨D.pa⟩)
    (hpa : w.code D.pa = OzProxyAdmin.runtimeCode) (hia : w.code D.ia = ActorImpl.runtimeCode)
    (hsf : w.code D.sf = SafeProxy.runtimeCode) (hsg : w.code D.sg = SafeSingleton.runtimeCode)
    (himpl : w.sload D.px implSlot = Word.ofAddress D.ia)
    (howner : w.sload D.pa 0 = Word.ofAddress D.sf)
    (hsafe : D.SafeOk ctx.crypto ctx.block.chainId O T thr h₀ (w.sload D.sf))
    (hthr : thr < 2 ^ 256) (hcard : (O ∩ T).card < thr)
    (hsig : Signers ctx.crypto ctx.block.chainId D.sf O T)
    (hh : h₀ = 0 ∨ ¬ D.Rl (Word.toAddress h₀))
    (hidle : ∀ x, X ctx.fork O T x → (w.code x).size = 0 ∧ (w.account x).nonce ≠ 0)
    (hcaller : ¬ X ctx.fork O T msg.caller)
    (hcode : X ctx.fork O T msg.currentTarget → msg.target = some msg.currentTarget →
      msg.code.size = 0)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (htop : TopOk D.Rl w msg)
    (hR : ∀ m, Reaches ctx w tr msg m → D.Rw ctx.crypto ctx.block.chainId O T m)
    {fuel : Nat} {r : MessageResult} (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    D.G ctx.crypto ctx.block.chainId O T thr h₀ r.world := by
  have hw : RelayCode D.Rl D.code w := by
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · rw [hpx, code_px]
    · rw [hpa, code_pa]
    · rw [hia, code_ia]
    · rw [hsf, code_sf]
    · rw [hsg, code_sg]
  exact processMessageCall_guardD (K := Kc ctx) (codeOk D) D.G_keep
    (D.inv ctx hthr hcard hsig hh) hw ⟨himpl, howner, hsafe⟩ hidle hdeleg
    ⟨htop, hcaller, hcode⟩ hR hr rfl

end Dep

end Verified.Safe.Guard
