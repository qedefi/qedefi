import Examples.Solmate.ERC4626.LowGas.Frames
import EvmLogic.AbsInt.Code
import Examples.Solmate.ERC4626.LowGas.Certify
import EvmLogic.Tactic.KernelRfl

/-!
# Low gas: the call targets of the Solmate vault and asset

Discharges `VaultCallsAsset` and `AssetCallsPrecompile` (`Frames.lean`) with the certified
abstract interpreter (`EvmLogic/AbsInt`): one kernel-checked certificate per code, for all
immutables (the vault's `asset` immutable is a symbolic value), shows every call goes to the
`asset` immutable or `0x01` (vault) / `0x01` only (asset). See `docs/erc4626/details.md` §9.
-/

namespace Examples.Solmate.ERC4626.LowGas
open Examples.Solmate.ERC20 QEDefi.ERC4626 QEDefi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open Examples.Solmate.Contracts EvmLogic.GasMono
open EvmLogic.AbsInt
open EvmLogic.Program.Nested (bump Reaches Danger InstrFrame exec_frame pushCall)
open EvmLogic.Program.Nested (precompilesOk_standard)
open QEDefi.Math QEDefi.ERC20 QEDefi.Trace.Lift
open Examples.Solmate.ERC4626.Nested Examples.Solmate.ERC4626.Invariants

/-! ## Targets -/

theorem toAddress_of_one {w : Word} (h : w.toNat = 1) : Word.toAddress w = 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [Word.toAddress, BitVec.toNat_setWidth, h]
  rfl

theorem toAddress_ofAddress (a : Address) : Word.toAddress (Word.ofAddress a) = a := by
  apply BitVec.eq_of_toNat_eq
  simp only [Word.toAddress, Word.ofAddress, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by omega) (by omega))),
    Nat.mod_eq_of_lt a.isLt]

theorem isPrecompile_one (fork : Fork) : Precompile.isPrecompile fork 1 = true := by
  cases fork <;> rfl

theorem precompileOf_one {ctx : Context} {msg : Message} (hca : msg.codeAddress = some 1)
    (hdis : msg.disablePrecompiles = false) :
    precompileOf (PrecompileImpl.standard ctx) msg = some 1 := by
  have h1 : (PrecompileImpl.standard ctx).isPrecompile 1 = true := isPrecompile_one ctx.fork
  simp only [precompileOf, hdis, hca, h1, Bool.false_eq_true, ↓reduceIte]

theorem call_one_precompile {m m' : Machine} {b : UInt8} {req : CallRequest} {tw : Word}
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m'))
    (hpre : m.precompiles = PrecompileImpl.standard m.ctx) (hnd : EcrecoverOk m)
    (htw : tw.toNat = 1)
    (hcall : (m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress tw)) = none) →
      req.msg.codeAddress = some (Word.toAddress tw) ∧
      req.msg.code = m.world.code (Word.toAddress tw) ∧ req.msg.disablePrecompiles = false) :
    precompileOf m'.precompiles req.msg ≠ none := by
  have hif : InstrFrame m m' := ((exec_frame _ m).of_run he).1
  rw [toAddress_of_one htw] at hcall
  obtain ⟨hca, -, hdis⟩ := hcall hnd
  rw [hif.same.precompiles, hpre, precompileOf_one hca hdis]
  simp

/-! ## The asset's frames -/

/-- An asset frame from its start, without a gas bound. -/
structure AssetRun (ia : SolmateAsset.Immutables) (mh : Machine) : Prop where
  code : mh.frame.code = SolmateAsset.runtimeCodeWith ia
  pc : mh.frame.pc = 0
  stack : mh.frame.stack = []
  pre : mh.precompiles = PrecompileImpl.standard mh.ctx
  ecrecover : EcrecoverOk mh

def AssetInv (ia : SolmateAsset.Immutables) (t : Tree) (mh m : Machine) : Prop :=
  SameFrame mh m ∧ m.frame.code = SolmateAsset.runtimeCodeWith ia ∧ InCert (fun _ => 0) t m ∧
    SameCode mh.world m.world

theorem asset_call_answered {ia : SolmateAsset.Immutables} {t : Tree}
    (hc : Cert (fun _ => 0) assetTargets (SolmateAsset.runtimeCodeWith ia) [] t) {mh m m' : Machine}
    (hA : AssetRun ia mh) (hI : AssetInv ia t mh m) {b : UInt8} {req : CallRequest}
    (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m')) :
    precompileOf m'.precompiles req.msg ≠ none := by
  obtain ⟨hs, hcm, hQ, hcd⟩ := hI
  obtain ⟨tw, a, -, ha, hat, hcall⟩ := inCert_call hc hcm hQ hb he
  have hpre : m.precompiles = PrecompileImpl.standard m.ctx := by
    rw [hs.precompiles, hs.ctx]; exact hA.pre
  have hnd : EcrecoverOk m := by
    unfold EcrecoverOk; rw [hs.ctx, hcd 1]; exact hA.ecrecover
  cases a with
  | const n =>
    simp only [assetTargets, beq_iff_eq] at ha
    subst ha
    exact call_one_precompile he hpre hnd hat hcall
  | sym _ => simp [assetTargets] at ha
  | top => simp [assetTargets] at ha

/-- **An asset frame up to its exit**: it stays described by the certificate, keeps the code
of every account, and every call it makes is answered by the precompile. -/
theorem asset_run {ia : SolmateAsset.Immutables} {t : Tree}
    (hc : Cert (fun _ => 0) assetTargets (SolmateAsset.runtimeCodeWith ia) [] t) {mh : Machine}
    (hA : AssetRun ia mh) {N : Nat} {mfh : Machine} {oh : Outcome} (hex : Exit mh N mfh oh) :
    ∀ k ≤ N, ∀ m, stepN k mh = .running m → SameFrame mh m → AssetInv ia t mh m := by
  have h0 : AssetInv ia t mh mh := by
    refine ⟨.refl mh, hA.code, ⟨[], ?_, ?_⟩, SameCode.refl _⟩
    · rw [hA.pc]; exact hc.init
    · rw [hA.stack]; trivial
  intro k hk m hm hs
  refine exit_frame_ind (AssetInv ia t mh) ?_ ?_ N mh mfh oh hex h0 k hk m hm hs
  · intro m b a m' m₁ hI hb he hw hs₁
    obtain ⟨hsm, hcm, hQ, hcd⟩ := hI
    obtain ⟨hcm₁, hQ₁⟩ := inCert_within hc hcm hQ hb he hw
    exact ⟨hsm.trans hs₁, hcm₁, hQ₁, hcd.trans (within_code he hw)⟩
  · intro m b a m' mc nc mfc oc hI hb he hp _ _
    exfalso
    rcases hp with ⟨req, rfl, hpre, -⟩ | ⟨msg, rfl, -⟩
    · exact asset_call_answered hc hA hI hb he hpre
    · exact inCert_no_create hc hI.2.1 hI.2.2.1 hb he

theorem asset_exit_code {ia : SolmateAsset.Immutables} {mh : Machine} (hA : AssetRun ia mh)
    {N : Nat} {mfh : Machine} {oh : Outcome} (hex : Exit mh N mfh oh) :
    SameCode mh.world mfh.world := by
  obtain ⟨t, hc⟩ := asset_cert ia
  obtain ⟨m, hm, hs, hx⟩ := hex.last
  obtain ⟨-, -, -, hcd⟩ := asset_run hc hA hex N (le_refl _) m hm hs
  rcases exitOf_cases hx with rfl | ⟨b, a, -, he⟩
  · exact hcd
  · exact hcd.trans ((exec_code _ m).of_run he)

/-- **Every call of an asset frame is answered by the `ECRECOVER` precompile.** -/
theorem asset_callsTo {ia : SolmateAsset.Immutables} {mh : Machine} (hA : AssetRun ia mh)
    {N : Nat} {mfh : Machine} {oh : Outcome} (hex : Exit mh N mfh oh) :
    CallsTo (fun _ => False) mh N := by
  obtain ⟨t, hc⟩ := asset_cert ia
  intro k hk m' b req m'' hm hs hb he hpre
  exact asset_call_answered hc hA (asset_run hc hA hex k (Nat.le_of_lt hk) m' hm hs) hb he hpre

theorem AssetHigh.run {ia : SolmateAsset.Immutables} {mh : Machine} (h : AssetHigh ia mh) :
    AssetRun ia mh :=
  ⟨h.code, h.pc, h.stack, h.pre, h.ecrecover⟩

/-- **`AssetCallsPrecompile` holds.** -/
theorem assetCallsPrecompile : AssetCallsPrecompile :=
  fun _ _ _ _ _ hA hex => asset_callsTo hA.run hex

/-! ## The vault's frames -/

def VaultInv (i : SolmateVault.Immutables) (t : Tree) (mh m : Machine) : Prop :=
  SameFrame mh m ∧ m.frame.code = SolmateVault.runtimeCodeWith i ∧
    InCert (fun _ => i.asset) t m ∧ SameCode mh.world m.world

theorem vault_child {vault asset : Address} {i : SolmateVault.Immutables} {t : Tree}
    (hc : Cert (fun _ => i.asset) vaultTargets (SolmateVault.runtimeCodeWith i) [] t)
    {mh m m' : Machine} (hV : VaultHigh vault asset i mh) (hI : VaultInv i t mh m) {b : UInt8}
    {req : CallRequest} (hb : m.frame.code[m.frame.pc]? = some b)
    (he : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.call req, m'))
    (hpre : precompileOf m'.precompiles req.msg = none) :
    ∃ ia, AssetRun ia (pushCall m' req) ∧
      (pushCall m' req).frame.jumpDests = validJumpDests (pushCall m' req).frame.code := by
  obtain ⟨hs, hcm, hQ, hcd⟩ := hI
  have hif : InstrFrame m m' := ((exec_frame _ m).of_run he).1
  obtain ⟨tw, a, -, ha, hat, hcall⟩ := inCert_call hc hcm hQ hb he
  have hpre' : m.precompiles = PrecompileImpl.standard m.ctx := by
    rw [hs.precompiles, hs.ctx]; exact hV.pre
  have hnd : EcrecoverOk m := by
    unfold EcrecoverOk; rw [hs.ctx, hcd 1]; exact hV.ecrecover
  cases a with
  | const n =>
    simp only [vaultTargets, beq_iff_eq] at ha
    subst ha
    exact absurd hpre (call_one_precompile he hpre' hnd hat hcall)
  | top => simp [vaultTargets] at ha
  | sym k =>
    simp only [AVal.Holds] at hat
    subst hat
    rw [toAddress_ofAddress, hV.assetEq] at hcall
    obtain ⟨ia, hia⟩ := hV.dep.assetCode
    have hca : m.world.code asset = SolmateAsset.runtimeCodeWith ia := by rw [hcd]; exact hia
    obtain ⟨-, hcode, -⟩ := hcall (.inr (by rw [hca]; exact delegatedAddress?_assetCode ia))
    refine ⟨ia, ⟨?_, rfl, rfl, ?_, ?_⟩, rfl⟩
    · show req.msg.code = _
      rw [hcode, hca]
    · show m'.precompiles = PrecompileImpl.standard m'.ctx
      rw [hif.same.precompiles, hif.same.ctx]; exact hpre'
    · unfold EcrecoverOk
      show m'.ctx.fork < .prague ∨ delegatedAddress? ((transferValue m'.world req.msg).code 1) = none
      rw [hif.same.ctx, code_transferValue m'.world req.msg 1, ((exec_code _ m).of_run he) 1]
      exact hnd

/-- **A vault frame up to its exit**: it stays described by the certificate and keeps the code
of every account. -/
theorem vault_run {vault asset : Address} {i : SolmateVault.Immutables} {t : Tree}
    (hc : Cert (fun _ => i.asset) vaultTargets (SolmateVault.runtimeCodeWith i) [] t)
    {mh : Machine} (hV : VaultHigh vault asset i mh) {N : Nat} {mfh : Machine} {oh : Outcome}
    (hex : Exit mh N mfh oh) :
    ∀ k ≤ N, ∀ m, stepN k mh = .running m → SameFrame mh m → VaultInv i t mh m := by
  have h0 : VaultInv i t mh mh := by
    refine ⟨.refl mh, hV.code, ⟨[], ?_, ?_⟩, SameCode.refl _⟩
    · rw [hV.pc]; exact hc.init
    · rw [hV.stack]; trivial
  intro k hk m hm hs
  refine exit_frame_ind (VaultInv i t mh) ?_ ?_ N mh mfh oh hex h0 k hk m hm hs
  · intro m b a m' m₁ hI hb he hw hs₁
    obtain ⟨hsm, hcm, hQ, hcd⟩ := hI
    obtain ⟨hcm₁, hQ₁⟩ := inCert_within hc hcm hQ hb he hw
    exact ⟨hsm.trans hs₁, hcm₁, hQ₁, hcd.trans (within_code he hw)⟩
  · intro m b a m' mc nc mfc oc hI hb he hp hexc hsR
    rcases hp with ⟨req, rfl, hpre, rfl⟩ | ⟨msg, rfl, -⟩
    · obtain ⟨ia, hrun, -⟩ := vault_child hc hV hI hb he hpre
      obtain ⟨hsm, hcm, hQ, hcd⟩ := hI
      obtain ⟨hcmR, hQR⟩ := inCert_pushed hc hcm hQ hb he (.inl ⟨req, rfl, hpre, rfl⟩) mfc oc
      refine ⟨hsm.trans hsR, hcmR, hQR, ?_⟩
      have hm' : SameCode m.world m'.world := (exec_code _ m).of_run he
      have hfin := hexc.finish.2
      have hk : mfc.frame.kind = .call req.retOffset req.retSize := hfin.kind
      rcases resumeAfter_world (p := m'.frame) (ps := m.parents) (o := oc) hk with hw | hw <;>
        rw [hw]
      · exact (hcd.trans hm').trans ((pushCall_code m' req).trans (asset_exit_code hrun hexc))
      · rw [hfin.snapshot]
        exact hcd.trans hm'
    · exact (inCert_no_create hc hI.2.1 hI.2.2.1 hb he).elim

/-- **Every call of a vault frame not answered by a precompile starts an asset frame.** -/
theorem vault_callsTo {vault asset : Address} {i : SolmateVault.Immutables} {mh : Machine}
    (hV : VaultHigh vault asset i mh) {N : Nat} {mfh : Machine} {oh : Outcome}
    (hex : Exit mh N mfh oh) : CallsTo (fun mc => ∃ ia, AssetHigh ia mc) mh N := by
  obtain ⟨t, hc⟩ := vault_cert i
  intro k hk m b req m' hm hs hb he hpre
  have hI := vault_run hc hV hex k (Nat.le_of_lt hk) m hm hs
  obtain ⟨ia, hrun, hjd⟩ := vault_child hc hV hI hb he hpre
  have hif : InstrFrame m m' := ((exec_frame _ m).of_run he).1
  have hok : Nested.CallOk m m' req := ((exec_frame _ m).of_run he).2
  have hg : m.frame.gasLeft ≤ mh.frame.gasLeft :=
    gas_le_of_stepN (by rw [hV.pre]; exact precompilesOk_standard _) hm hs.parents
  refine ⟨ia, hrun.code, hjd, hrun.pc, ?_, hrun.pre, hrun.stack, hrun.ecrecover⟩
  show req.msg.gas < 2 ^ 256
  have := hok.gas
  have := hV.gasLt
  omega

/-- **`VaultCallsAsset` holds.** -/
theorem vaultCallsAsset (vault asset : Address) : VaultCallsAsset vault asset :=
  fun _ _ _ _ _ hV hex => vault_callsTo hV hex

end Examples.Solmate.ERC4626.LowGas
