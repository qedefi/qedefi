import Verified.AaveV3.AToken.Havoc.Run

/-!
# Frames running the AToken code, frames running the proxy code

`FrameOk`: every non-static frame running the AToken code from pc 0 at a protected account
(the proxy, reached by its `DELEGATECALL`, or the implementation called directly), from a `Good`
world and snapshot, for any gas below `G`, ends in a `Good` world, given `CoversA` below `G`.
`ProxyOk`: the same for the proxy code at the proxy, for any caller but the proxy admin.
`FrameOk.halts`/`ProxyOk.halts` turn them into `Halts` statements about fresh frames.
-/

namespace Verified.AaveV3.AToken.Havoc
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Solidity Verified.AaveV3.Contracts

/-- **Every AToken frame at a protected account keeps `Good`** (see the module docstring). -/
def FrameOk : Prop :=
  ∀ (G : Nat) (ctx : Context) (w : World) (tr : TransientStorage) (ow : World)
    (created : AddressSet) (msg : Message) (jd : Array Bool) (g : Nat)
    (sub : Substate) (snap : World × TransientStorage) (ko ks : Nat) (parents : List Frame),
    SlotsOk ctx.crypto → (∀ g' < G, CoversA Prot (Good ctx.crypto) (Ctx ctx.crypto) g') →
    g ≤ G → Good ctx.crypto snap.1 → Good ctx.crypto w → msg.isStatic = false →
    Prot msg.currentTarget →
    WP (Machine.mk ctx (PrecompileImpl.standard ctx) w tr ow created
      (Frame.mk msg AToken.runtimeCode jd 0 [] {} g .empty sub snap (.call ko ks)) parents)
      (fun _ => False) (FailOk (Good ctx.crypto))

/-- **Every proxy frame at the proxy with a caller other than the admin keeps `Good`.** -/
def ProxyOk : Prop :=
  ∀ (G : Nat) (ctx : Context) (w : World) (tr : TransientStorage) (ow : World)
    (created : AddressSet) (msg : Message) (jd : Array Bool) (g : Nat)
    (sub : Substate) (snap : World × TransientStorage) (ko ks : Nat) (parents : List Frame),
    SlotsOk ctx.crypto → (∀ g' < G, CoversA Prot (Good ctx.crypto) (Ctx ctx.crypto) g') →
    g ≤ G → Good ctx.crypto snap.1 → Good ctx.crypto w → msg.isStatic = false →
    msg.currentTarget = proxy → msg.caller ≠ ATokenProxy.admin →
    WP (Machine.mk ctx (PrecompileImpl.standard ctx) w tr ow created
      (Frame.mk msg ATokenProxy.runtimeCode jd 0 [] {} g .empty sub snap (.call ko ks)) parents)
      (fun _ => False) (FailOk (Good ctx.crypto))

/-- A fresh frame running the AToken code at a protected account keeps `Good`. -/
theorem FrameOk.halts (hF : FrameOk) {G : Nat} {mc : Machine} {o s : Nat}
    {snap : World × TransientStorage} (hK : SlotsOk mc.ctx.crypto)
    (hcov : ∀ g' < G, CoversA Prot (Good mc.ctx.crypto) (Ctx mc.ctx.crypto) g')
    (hfr : mc.frame = Frame.init mc.frame.msg (.call o s) snap)
    (hcode : mc.frame.msg.code = AToken.runtimeCode)
    (hpre : mc.precompiles = PrecompileImpl.standard mc.ctx) (hg : mc.frame.msg.gas ≤ G)
    (hsnap : Good mc.ctx.crypto snap.1) (hw : Good mc.ctx.crypto mc.world)
    (hst : mc.frame.msg.isStatic = false) (ht : Prot mc.frame.msg.currentTarget) :
    Halts mc (FailOk (Good mc.ctx.crypto)) := by
  obtain ⟨ctx, pre, w, tr, ow, cr, fr, par⟩ := mc
  dsimp only at hK hcov hfr hcode hpre hg hsnap hw hst ht ⊢
  rw [hfr]; subst hpre
  apply WP.halts_of_false
  unfold Frame.init
  rw [hcode]
  exact hF G ctx w tr ow cr _ _ _ _ snap o s par hK hcov hg hsnap hw hst ht

/-- A fresh frame running the proxy code at the proxy, its caller not the admin, keeps `Good`. -/
theorem ProxyOk.halts (hP : ProxyOk) {G : Nat} {mc : Machine} {o s : Nat}
    {snap : World × TransientStorage} (hK : SlotsOk mc.ctx.crypto)
    (hcov : ∀ g' < G, CoversA Prot (Good mc.ctx.crypto) (Ctx mc.ctx.crypto) g')
    (hfr : mc.frame = Frame.init mc.frame.msg (.call o s) snap)
    (hcode : mc.frame.msg.code = ATokenProxy.runtimeCode)
    (hpre : mc.precompiles = PrecompileImpl.standard mc.ctx) (hg : mc.frame.msg.gas ≤ G)
    (hsnap : Good mc.ctx.crypto snap.1) (hw : Good mc.ctx.crypto mc.world)
    (hst : mc.frame.msg.isStatic = false) (ht : mc.frame.msg.currentTarget = proxy)
    (hadm : mc.frame.msg.caller ≠ ATokenProxy.admin) :
    Halts mc (FailOk (Good mc.ctx.crypto)) := by
  obtain ⟨ctx, pre, w, tr, ow, cr, fr, par⟩ := mc
  dsimp only at hK hcov hfr hcode hpre hg hsnap hw hst ht hadm ⊢
  rw [hfr]; subst hpre
  apply WP.halts_of_false
  unfold Frame.init
  rw [hcode]
  exact hP G ctx w tr ow cr _ _ _ _ snap o s par hK hcov hg hsnap hw hst ht hadm

/-- **The child of the proxy's `DELEGATECALL` keeps `Good`**: it runs the code of the
implementation, which `Good` pins to the AToken code, at the proxy (a protected account), from
the proxy's `Good` world. -/
theorem delegate_child_halts (hF : FrameOk) {G : Nat} {m mc : Machine} {toW : Word}
    (hK : SlotsOk m.ctx.crypto)
    (hcov : ∀ g' < G, CoversA Prot (Good m.ctx.crypto) (Ctx m.ctx.crypto) g')
    (hg : m.frame.gasLeft ≤ G) (hd : DelegateStart m toW mc) (hto : Word.toAddress toW = impl)
    (hgood : Good m.ctx.crypto m.world) (hst : m.frame.msg.isStatic = false)
    (ht : Prot m.frame.msg.currentTarget) (hpre : m.precompiles = PrecompileImpl.standard m.ctx) :
    Halts mc (FailOk (Good m.ctx.crypto)) := by
  obtain ⟨o, s, t, hfr⟩ := hd.fresh
  have hctx := hd.ctx
  rw [← hctx] at hK hcov hgood ⊢
  have hcode : mc.frame.msg.code = AToken.runtimeCode := by
    rw [hd.code (by rw [hto, hgood.implCode]; exact deleg_implCode), hto, hgood.implCode]
  refine hF.halts hK hcov hfr hcode (by rw [hd.pre, hpre, hctx]) (Nat.le_trans
    (Nat.le_of_lt hd.gas) hg) hgood (by rw [hd.world]; exact hgood) (by rw [hd.isStatic]; exact hst)
    (by rw [hd.target]; exact ht)

end Verified.AaveV3.AToken.Havoc
