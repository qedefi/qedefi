import Verified.Solmate.ERC20.Spec.Reframe
import Verified.Solmate.ERC20.Spec.Obligations
import Verified.Solmate.ERC4626.LowGas.Frames
import Verified.Solmate.ERC4626.LowGas.Targets

/-!
# Lower gas for frames that call `ecrecover`

`low_ecrecover`: a summary of an asset frame lifted to more gas (`hi G m`, a call under a parent
with empty code) transfers to the frame itself, at any gas and of any kind, when `ecrecover`
runs the precompile: the frame fails, or succeeds with the summary's observable post. The chain:
the frame runs as its re-kinded copy `m₁` (`lockstepK`), `m₁` as the lifted frame with less
gas (the gas lockstep of `EvmLogic.GasMono`, `assetHigh_mono`), and both summaries are read at
the real exits (`pin`).
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested EvmLogic.GasMono
open EvmLogic.AbsInt Verified.Solmate.Contracts Verified.Solmate.ERC4626.LowGas
open QEDefi.ERC20.Spec

variable {ia : SolmateAsset.Immutables} {Act : Finset Address} {m : Machine}

set_option maxHeartbeats 2000000 in
/-- **A frame summary at more gas transfers to the frame**, for an asset frame whose
`ecrecover` runs the precompile. -/
theorem low_ecrecover (hS : Start (code ia) solmateAbs M Act m) (hep : EcrecoverPlain m)
    {G : Nat} (hG : m.frame.gasLeft ≤ G) (hG' : G < 2 ^ 256)
    {P : ByteArray → Machine → Prop}
    (hP : ∀ out mf mf', mf'.world = mf.world → mf'.transient = mf.transient →
      mf'.createdAccounts = mf.createdAccounts → mf'.frame.sub.logs = mf.frame.sub.logs →
      P out mf → P out mf')
    (hhigh : Halts (hi G m) fun mf o => ∀ out, o = .success out → P out mf) :
    Halts m fun mf o => Fails o ∨ ∃ out, o = .success out ∧ P out mf := by
  let p := p0 m
  let m₁ := reframe (.call 0 0) [p] m
  have hc0 : p.code.size = 0 := rfl
  have hmh : hi G m = bump (G - m.frame.gasLeft) G [p] m₁ := rfl
  -- the high frame's exit
  obtain ⟨N, mfh, oh, hex, mf', o', hQ, hs', heq⟩ := pin (mh := hi G m) rfl hc0 hhigh
  have hf := hi_fresh hS.fresh hG
  obtain ⟨hcode, hjd, hpc, hst, -, -, -⟩ := hf.frame
  have hAH : AssetHigh ia (hi G m) :=
    { code := hcode, jd := by rw [hjd, hcode], pc := hpc, gasLt := by rw [hi_gas hG]; exact hG',
      pre := hS.precompiles, stack := hst, ecrecover := hep }
  -- the re-kinded frame against the high one
  have hlow : Halts m₁ (Post mfh oh) := by
    have := assetHigh_mono assetCallsPrecompile m₁ (hi G m) N mfh oh ⟨ia, hAH⟩
      (by rw [hmh]; exact bumpOf_bump _ _ _ _) hex
    exact this
  obtain ⟨N₁, mf₁, o₁, hex₁, mfl, ol, hpost, hsl, heq₁⟩ := pin (mh := m₁) rfl hc0 hlow
  -- the frame against the re-kinded one
  have hA₁ : AssetRun ia m₁ := ⟨hS.fresh.frame.1, hS.fresh.frame.2.2.1, hS.fresh.frame.2.2.2.1,
    hS.precompiles, hep⟩
  obtain ⟨t, hcert⟩ := asset_cert ia
  have honly : OnlyPrecompiles m₁ N₁ := by
    intro j hj m' b a m'' hj' hs'' hb hr
    have hI := asset_run hcert hA₁ hex₁ j hj m' hj' hs''
    refine ⟨fun req h => ?_, fun msg h => ?_⟩
    · subst h; exact asset_call_answered hcert hA₁ hI hb hr
    · subst h; exact inCert_no_create hcert hI.2.1 hI.2.2.1 hb hr
  refine (lockstepK N₁ m (.call 0 0) [p] mf₁ o₁ hex₁ honly).mono fun mfm om _ hk => ?_
  rcases hk with hk | ⟨rfl, hmf⟩
  · exact .inl (failed_fails hk)
  · cases om with
    | success out =>
      have hk₁ : mf₁.frame.kind = .call 0 0 := hex₁.finish.2.kind
      have hkl : mfl.frame.kind = .call 0 0 := hsl.kind
      obtain ⟨hol, hw₁, ht₁, hc₁, hl₁⟩ := resumeAfter_success hk₁ hkl heq₁
      rcases hpost with hfl | ⟨hoh, d, x, ps, hmfh⟩
      · exact absurd hol (fun h => hfl out h)
      · rw [hol] at hoh
        subst hoh
        have hkh : mfh.frame.kind = .call 0 0 := hex.finish.2.kind
        have hk' : mf'.frame.kind = .call 0 0 := hs'.kind
        obtain ⟨ho', hw, ht, hc, hl⟩ := resumeAfter_success hkh hk' heq
        have h1 := hQ out ho'
        refine .inr ⟨out, rfl, ?_⟩
        refine hP out mf' mfm ?_ ?_ ?_ ?_ h1
        · rw [hw, hmfh]; show mfm.world = mfl.world; rw [hw₁, hmf]; rfl
        · rw [ht, hmfh]; show mfm.transient = mfl.transient; rw [ht₁, hmf]; rfl
        · rw [hc, hmfh]; show mfm.createdAccounts = mfl.createdAccounts; rw [hc₁, hmf]; rfl
        · have e1 := (Array.append_right_inj _).1 hl
          have e2 := (Array.append_right_inj _).1 hl₁
          rw [e1, hmfh]; show mfm.frame.sub.logs = mfl.frame.sub.logs; rw [e2, hmf]; rfl
    | revert out => exact .inl trivial
    | halt e => exact .inl trivial

end Verified.Solmate.ERC20.Spec
