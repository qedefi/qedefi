import Verified.Solmate.ERC20.Spec.SubCert
import Verified.Solmate.ERC20.Spec.LowGas
import Verified.Solmate.ERC4626.LowGas.Certify
import Verified.Solmate.Contracts.SolmateAsset

/-!
# The asset reads no gas outside `permit`

The asset's only instructions reading the gas are `GAS` and `STATICCALL` at pcs 1630 and 1631
(`ecrecover` in `permit`). A frame that passes through one of the *targets* (the entries of the
other functions, and the dispatcher's `REVERT`s) never executes them before its exit
(`noGasRead_of_steps`), whatever the code at the precompile address `0x01` (an EIP-7702
delegation there would make the `STATICCALL` start a child, which `AssetHigh`'s
`EcrecoverOk` excludes; here it needs no exclusion):

* every machine of the frame is described by the whole code's table `t0` (`asset_certify`), at
  pcs whose bytes read no gas except 1630 and 1631 (`t0_check`);
* from the table's states at 1630 and 1631, no target is reachable (`tP_check`); so a frame at
  1630 or 1631 before its target cannot reach the target;
* from the table's states at the targets, neither 1630 nor 1631 is reachable (`tT_check`).
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested EvmLogic.GasMono
open EvmLogic.AbsInt Verified.Solmate.Contracts Verified.Solmate.ERC4626.LowGas

/-- The whole code's table (from pc `0`). -/
def t0 : Tree := (certify assetTargets SolmateAsset.runtimeCode [] [] certFuel).getD .leaf

/-- The function entries and dispatcher `REVERT`s the frames below pass through: `transfer`
515, `transferFrom` 321, `approve` 263, `balanceOf` 426, `allowance` 553, `totalSupply` 298,
`mint` 405, `burn` 496; the `REVERT`s of a call with value (14), and of unknown selectors and
short calldata (98, 135, 194, 232). -/
def targets : List Nat := [515, 321, 263, 426, 553, 298, 405, 496, 14, 98, 135, 194, 232]

/-- The pcs reading the gas. -/
def gasPcs : List Nat := [1630, 1631]

/-- The table explored from `t0`'s states at the pcs reading the gas. -/
def tP : Tree := (subcert SolmateAsset.runtimeCode t0 gasPcs certFuel).getD .leaf

/-- The table explored from `t0`'s states at the targets. -/
def tT : Tree := (subcert SolmateAsset.runtimeCode t0 targets certFuel).getD .leaf

/-- A byte whose instruction may read the gas. -/
def readsGasByte (b : UInt8) : Bool := b == 0x5a || isCallByteB b

/-- `q` lies in an immutable's window of the code. -/
def inWindow (q : Nat) : Bool := [1063, 1116, 345].any fun o => o ≤ q && q < o + 32

/-- The byte of the canonical code at `q`, through its kernel table. -/
noncomputable def tbyte (q : Nat) : UInt8 :=
  (SolmateAsset.runtimeCode.codeTable.bytes.get SolmateAsset.runtimeCode.codeTable.depth q).getD 0

theorem tbyte_eq (q : Nat) : tbyte q = Bytes.getD SolmateAsset.runtimeCode q :=
  (EvmLogic.Program.CodeTable.getD_eq SolmateAsset.runtimeCode.codeTable_ok q).symm

theorem tP_some : (subcert SolmateAsset.runtimeCode t0 gasPcs certFuel).isSome = true := by
  kernel_decide

theorem tT_some : (subcert SolmateAsset.runtimeCode t0 targets certFuel).isSome = true := by
  kernel_decide

/-- `t0`'s pcs lie outside the immutables, and read no gas except at 1630 and 1631. -/
theorem t0_check : (recorded t0).all (fun q => !inWindow q &&
    (gasPcs.contains q || !readsGasByte (tbyte q))) = true := by
  kernel_decide

/-- No target is reachable from the pcs reading the gas. -/
theorem tP_check : targets.all (fun q => !(recorded tP).contains q) = true := by
  kernel_decide

/-- The pcs reading the gas are not reachable from the targets. -/
theorem tT_check : gasPcs.all (fun q => !(recorded tT).contains q) = true := by
  kernel_decide

/-! ## For all immutables -/

variable {ia : SolmateAsset.Immutables}

theorem certify_code : certify assetTargets (SolmateAsset.runtimeCodeWith ia) [] [] certFuel =
    some t0 := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 asset_certify
  have h0 : t0 = t := by unfold t0; rw [ht]; rfl
  rw [h0]
  unfold certify table at ht ⊢
  rw [ascan_asset]
  exact ht

theorem subcert_code {Q : List Nat} {t : Tree}
    (h : (subcert SolmateAsset.runtimeCode t0 Q certFuel).isSome = true)
    (ht : t = (subcert SolmateAsset.runtimeCode t0 Q certFuel).getD .leaf) :
    subcert (SolmateAsset.runtimeCodeWith ia) t0 Q certFuel = some t := by
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.1 h
  rw [ht, ht']
  unfold subcert table at ht' ⊢
  rw [ascan_asset]
  exact ht'

theorem t0_cert : Cert (fun _ => 0) assetTargets (SolmateAsset.runtimeCodeWith ia) [] t0 :=
  certify_sound certify_code (fun q k h => by cases h)

/-- Outside the immutables' windows, the code of any deployment is the canonical one. -/
theorem getElem?_code {q : Nat} (hq : inWindow q = false) :
    (SolmateAsset.runtimeCodeWith ia)[q]? = SolmateAsset.runtimeCode[q]? := by
  refine EvmLogic.Solidity.getElem?_patchWords_of_offsets _ _ q [1063, 1116, 345] rfl ?_
  simp only [inWindow, List.any_eq_false, List.mem_cons, List.not_mem_nil, or_false,
    Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_lt] at hq
  intro o ho
  have := hq o (by simpa using ho)
  omega

theorem readsGasByte_of {fork : Fork} {b : UInt8}
    (h : readsGasB (Opcode.decode fork b) = true) : readsGasByte b = true := by
  rcases readsGas_decode fork b h with h | h | h | h | h | h | h <;> subst h <;> rfl

/-- **An asset frame passing through a target reads no gas** before its exit, under a parent
with empty code. -/
theorem noGasRead_of_steps {mh : Machine} {p0 : Frame} (hp : mh.parents = [p0])
    (hc0 : p0.code.size = 0) (hcode : mh.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hpc : mh.frame.pc = 0) (hst : mh.frame.stack = []) {mT : Machine} (hT : Steps mh mT)
    (hTpc : mT.frame.pc ∈ targets) :
    ∀ N mfh oh, Exit mh N mfh oh → NoGasRead mh N := by
  intro N mfh oh hex j hj m' b hj' hs' hb
  have hc0cert := t0_cert (ia := ia)
  have h0 : InCert (fun _ => 0) t0 mh := ⟨[], by rw [hpc]; exact hc0cert.init, by rw [hst]; trivial⟩
  have hall := absint_frame hc0cert hex hcode h0
  obtain ⟨n0, hn0, hsT⟩ := hT
  have hn0N : n0 ≤ N := by
    rcases Nat.lt_or_ge N n0 with hlt | hle
    · exfalso
      have hfin := hex.finish
      have hR := hfin.1
      rw [finishFrame_of_parents oh (hfin.2.parents.trans hp)] at hR
      obtain ⟨r, hr⟩ := step_resumeAfter_empty hc0 mfh oh
      by_cases h : n0 = N + 1
      · subst h
        rw [hR] at hn0
        have := congrArg Machine.parents (StepResult.running.inj hn0)
        rw [hsT.parents, hp] at this
        simp [resumeAfter] at this
      · have := stepN_add_of_running hR (n0 - (N + 1))
        rw [show N + 1 + (n0 - (N + 1)) = n0 by omega, hn0,
          show n0 - (N + 1) = (n0 - (N + 2)) + 1 by omega, stepN_succ_of_done hr] at this
        cases this
    · exact hle
  cases hrg : readsGasB (Opcode.decode m'.ctx.fork b)
  · rfl
  exfalso
  have hrg' : readsGasB (Opcode.decode m'.ctx.fork b) = true := hrg
  have hin := hall j hj m' hj' hs'
  have hchk := List.all_eq_true.1 t0_check _ (inCert_recorded hin)
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at hchk
  obtain ⟨hw, hg⟩ := hchk
  have hcode' : m'.frame.code = SolmateAsset.runtimeCodeWith ia := hs'.code.trans hcode
  rw [hcode', getElem?_code hw] at hb
  have hbyte : tbyte m'.frame.pc = b := by
    rw [tbyte_eq]; unfold Bytes.getD
    rw [getElem?_eq_some_iff] at hb
    obtain ⟨hlt, hb⟩ := hb
    simp only [hlt, ↓reduceDIte, hb]
  have hgp : m'.frame.pc ∈ gasPcs := by
    rcases hg with hg | hg
    · simpa using hg
    · rw [hbyte, readsGasByte_of hrg'] at hg; cases hg
  obtain ⟨s, hinT, hstk⟩ := hin
  rcases Nat.lt_or_ge j n0 with hjn | hjn
  · obtain ⟨hcP, hsubP⟩ := subcert_sound (ρ := fun _ => 0)
      (subcert_code (ia := ia) tP_some rfl)
    have hinP : InCert (fun _ => 0) tP m' := ⟨s, hsubP _ _ hinT hgp, hstk⟩
    have hexm := hex.shift hj' hs' hj
    have hstepT : stepN (n0 - j) m' = .running mT := by
      rw [← stepN_add_of_running hj', show j + (n0 - j) = n0 by omega]; exact hn0
    have hinT' := absintT_frame hcP hexm hcode' hinP (n0 - j) (by omega) mT hstepT
      (hs'.symm.trans hsT)
    have := List.all_eq_true.1 tP_check _ hTpc
    simp only [Bool.not_eq_true'] at this
    have h2 : (recorded tP).contains mT.frame.pc = true := by
      simpa using inCert_recorded (t := tP) hinT'
    rw [h2] at this; cases this
  · obtain ⟨hcT, hsubT⟩ := subcert_sound (ρ := fun _ => 0)
      (subcert_code (ia := ia) tT_some rfl)
    obtain ⟨sT, hinTT, hstkT⟩ := hall n0 hn0N mT hn0 hsT
    have hinT : InCert (fun _ => 0) tT mT := ⟨sT, hsubT _ _ hinTT hTpc, hstkT⟩
    have hexT := hex.shift hn0 hsT hn0N
    have hstep : stepN (j - n0) mT = .running m' := by
      rw [← stepN_add_of_running hn0, show n0 + (j - n0) = j by omega]; exact hj'
    have hin' := absintT_frame hcT hexT (hsT.code.trans hcode) hinT (j - n0) (by omega) m'
      hstep (hsT.symm.trans hs')
    have := List.all_eq_true.1 tT_check _ hgp
    simp only [Bool.not_eq_true'] at this
    have h2 : (recorded tT).contains m'.frame.pc = true := by
      simpa using inCert_recorded (t := tT) hin'
    rw [h2] at this; cases this

end Verified.Solmate.ERC20.Spec
