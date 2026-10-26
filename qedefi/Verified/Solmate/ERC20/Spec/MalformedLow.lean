import Verified.Solmate.ERC20.Spec.Obligations
import Verified.Common.Malformed.Region

/-!
# Solmate's asset at low gas: more targets, and its getters as a read-only region

`Obligations.lean` lifts a low frame to high gas (`low`) when it passes through one of the
`targets` (the entries of the spec's functions and the dispatcher's `REVERT`s), from which the
gas-reading pcs of `permit` (`gasPcs`) are unreachable and which they cannot reach. Here the
same argument for the frames `MalformedSpec` adds (`targets2`): the entries of `name`,
`symbol`, `decimals`, `DOMAIN_SEPARATOR` and `nonces`, and the `REVERT`s of the ABI decoders
(short `permit` calldata 2430, a dirty `address` 2273, a dirty `uint8` 2488). `low2` is `low`
for them (`noGasRead_of_steps2`, the proof of `noGasRead_of_steps` with `targets2`).

`solGetters`: the getters (those five and `balanceOf`, `allowance`, `totalSupply`) are a
read-only region from their entries, for every choice of immutables (`solGetters_cert`,
`solGetters_pure`).
-/

namespace Verified.Solmate.ERC20.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.GasMono
open EvmLogic.Program.Nested EvmLogic.AbsInt
open QEDefi.ERC20 QEDefi.ERC20.Spec
open Verified.Solmate.Contracts Verified.Solmate.ERC20 Verified.Solmate.ERC4626
open Verified.Solmate.ERC4626.LowGas Verified.Solmate.ERC20.Spec Verified.Common.Malformed

/-! ## More targets -/

/-- The entries of `name` 233, `symbol` 488, `decimals` 340, `DOMAIN_SEPARATOR` 397, `nonces`
457, and the decoder `REVERT`s 2430 (short `permit`), 2273 (dirty `address`), 2488 (dirty
`uint8`). -/
def targets2 : List Nat := [233, 488, 340, 397, 457, 2430, 2273, 2488]

/-- The table explored from `t0`'s states at `targets2`. -/
def tT2 : Tree := (subcert SolmateAsset.runtimeCode t0 targets2 certFuel).getD .leaf

theorem tT2_some : (subcert SolmateAsset.runtimeCode t0 targets2 certFuel).isSome = true := by
  kernel_decide

/-- No new target is reachable from the pcs reading the gas. -/
theorem tP_check2 : targets2.all (fun q => !(recorded tP).contains q) = true := by
  kernel_decide

/-- The pcs reading the gas are not reachable from the new targets. -/
theorem tT2_check : gasPcs.all (fun q => !(recorded tT2).contains q) = true := by
  kernel_decide

variable {ia : SolmateAsset.Immutables}

/-- **An asset frame passing through a new target reads no gas** before its exit, under a
parent with empty code (`noGasRead_of_steps` with `targets2`). -/
theorem noGasRead_of_steps2 {mh : Machine} {p0 : Frame} (hp : mh.parents = [p0])
    (hc0 : p0.code.size = 0) (hcode : mh.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hpc : mh.frame.pc = 0) (hst : mh.frame.stack = []) {mT : Machine} (hT : Steps mh mT)
    (hTpc : mT.frame.pc ∈ targets2) :
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
    have := List.all_eq_true.1 tP_check2 _ hTpc
    simp only [Bool.not_eq_true'] at this
    have h2 : (recorded tP).contains mT.frame.pc = true := by
      simpa using inCert_recorded (t := tP) hinT'
    rw [h2] at this; cases this
  · obtain ⟨hcT, hsubT⟩ := subcert_sound (ρ := fun _ => 0)
      (subcert_code (ia := ia) tT2_some rfl)
    obtain ⟨sT, hinTT, hstkT⟩ := hall n0 hn0N mT hn0 hsT
    have hinT : InCert (fun _ => 0) tT2 mT := ⟨sT, hsubT _ _ hinTT hTpc, hstkT⟩
    have hexT := hex.shift hn0 hsT hn0N
    have hstep : stepN (j - n0) mT = .running m' := by
      rw [← stepN_add_of_running hn0, show n0 + (j - n0) = j by omega]; exact hj'
    have hin' := absintT_frame hcT hexT (hsT.code.trans hcode) hinT (j - n0) (by omega) m'
      hstep (hsT.symm.trans hs')
    have := List.all_eq_true.1 tT2_check _ hgp
    simp only [Bool.not_eq_true'] at this
    have h2 : (recorded tT2).contains m'.frame.pc = true := by
      simpa using inCert_recorded (t := tT2) hin'
    rw [h2] at this; cases this

/-- **A frame of the asset whose lift passes through a new target ends as its lift does, or
fails** (`low` for `targets2`). -/
theorem low2 {m : Machine} (hf : Fresh (code ia) m) {G : Nat} (hG : m.frame.gasLeft ≤ G)
    (hT : ∃ mT, Steps (hi G m) mT ∧ mT.frame.pc ∈ targets2)
    {P : ByteArray → Machine → Prop}
    (hP : ∀ out mf mf', mf'.world = mf.world → mf'.transient = mf.transient →
      mf'.createdAccounts = mf.createdAccounts → mf'.frame.sub.logs = mf.frame.sub.logs →
      P out mf → P out mf')
    (hhigh : Halts (hi G m) fun mf o => ∀ out, o = .success out → P out mf) :
    Halts m fun mf o => Fails o ∨ ∃ out, o = .success out ∧ P out mf := by
  have hf' := hi_fresh hf hG
  obtain ⟨hcode, -, hpc, hst, -, -, -⟩ := hf'.frame
  obtain ⟨mT, hT, hTpc⟩ := hT
  refine (lowGas (p0 := p0 m) (by rfl) hP hhigh fun N mfh oh hex =>
    noGasRead_of_steps2 rfl (by rfl) hcode hpc hst hT hTpc N mfh oh hex).mono
    fun mf o _ h => ?_
  rcases h with h | h
  · exact .inl (failed_fails h)
  · exact .inr h

/-! ## The getters' region -/

/-- The getters' selectors and entry pcs. -/
def getterEntries : List (Nat × Nat) :=
  [(0x06fdde03, 233), (0x95d89b41, 488), (0x313ce567, 340), (0x3644e515, 397),
    (0x7ecebe00, 457), (0x70a08231, 426), (0xdd62ed3e, 553), (0x18160ddd, 298)]

/-- The exploration seeds: each getter entry with a one-word stack. -/
def getterSeeds : List (Nat × AStack) := getterEntries.map fun p => (p.2, [.top])

/-- The read-only region of the getters. -/
def solGetters : Tree := (regionCert SolmateAsset.runtimeCode getterSeeds certFuel).getD .leaf

theorem solGetters_some :
    (regionCert SolmateAsset.runtimeCode getterSeeds certFuel).isSome = true := by
  kernel_decide

theorem solGetters_eq :
    regionCert (SolmateAsset.runtimeCodeWith ia) getterSeeds certFuel = some solGetters := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 solGetters_some
  have h0 : solGetters = t := by unfold solGetters; rw [ht]; rfl
  rw [h0]
  unfold regionCert table at ht ⊢
  rw [ascan_asset]
  exact ht

theorem solGetters_eq0 :
    regionCert SolmateAsset.runtimeCode getterSeeds certFuel = some solGetters := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 solGetters_some
  rw [solGetters, ht]; rfl

set_option maxRecDepth 100000 in
/-- The getters' pcs lie outside the immutables and hold pure instructions. -/
theorem solGetters_check :
    (recorded solGetters).all (fun q => !inWindow q && pureByte (tbyte q)) = true := by
  kernel_decide

theorem getD_congr {c c' : ByteArray} {q : Nat} (h : c[q]? = c'[q]?) :
    Bytes.getD c q = Bytes.getD c' q := by
  unfold Bytes.getD
  by_cases h1 : q < c.size <;> by_cases h2 : q < c'.size
  · simp only [h1, h2, ↓reduceDIte]
    rw [getElem?_pos c q h1, getElem?_pos c' q h2] at h
    exact Option.some.inj h
  · rw [getElem?_pos c q h1, getElem?_neg c' q h2] at h; cases h
  · rw [getElem?_neg c q h1, getElem?_pos c' q h2] at h; cases h
  · simp only [h1, h2, ↓reduceDIte]

theorem solGetters_pure :
    ∀ q ∈ recorded solGetters, pureByte (Bytes.getD (SolmateAsset.runtimeCodeWith ia) q) = true :=
  fun q hq => by
    have := List.all_eq_true.1 solGetters_check q hq
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    obtain ⟨hw, hp⟩ := this
    have h1 := getD_congr (getElem?_code (ia := ia) hw)
    rw [h1, ← tbyte_eq]; exact hp

theorem solGetters_cert : CertT (fun _ => 0) (fun _ => true) (SolmateAsset.runtimeCodeWith ia)
    solGetters :=
  (regionCert_sound solGetters_eq).1

theorem solGetters_seed {q : Nat} (h : (q, [AVal.top]) ∈ getterSeeds) :
    InT solGetters q [.top] :=
  (regionCert_sound (ρ := fun _ => 0) (t := solGetters) solGetters_eq0).2 (q, [.top]) h

end Verified.Solmate.ERC20.Spec.Malformed
