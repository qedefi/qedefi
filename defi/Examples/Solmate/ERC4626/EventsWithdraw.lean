import Examples.Solmate.ERC4626.Withdraw
import Examples.Solmate.ERC4626.EventsInternal
import Examples.Solmate.ERC4626.EventsConvert

/-!
# Logs of `withdraw`, at the bytecode level

`withdraw_halts_events`: the companion of `withdraw_halts` (`Withdraw.lean`) that also determines the frame's
logs (`OutPostLogs`), composing the log-tracking summaries of `EventsWithdrawInternal` and
`EventsConvert` and the inline `Withdraw` event.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Refinement.Out

set_option maxHeartbeats 0 in
/-- **`withdraw(uint256,address,address)`** of the vault, in any frame: ends as
`withdrawWorld?` prescribes. -/
theorem withdraw_halts_events {i : SolmateVault.Immutables} (m : Machine) (h : OutPre i m)
    {assets : Word} {receiver owner : Address}
    (hd : ThreeWordCall m.frame.msg.data 0xb460af94 assets (Word.ofAddress receiver)
      (Word.ofAddress owner)) :
    Halts m (OutPostLogs (fun v => ((m.frame.sub.logs.push (transferLog m.frame.msg.currentTarget owner 0 v)).push
        (withdrawLog m.frame.msg.currentTarget m.frame.msg.caller receiver owner assets v)).push
        (transferLog i.asset m.frame.msg.currentTarget receiver assets))
      (withdrawWorld? m.ctx.crypto m.world m.frame.msg.currentTarget i.asset
      m.frame.msg.caller assets receiver owner)) := by
  obtain ⟨hsel, hsize, harg0, harg1, harg2⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  out_intro
  pwp_run_to 0x62b [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
  -- `previewWithdraw(assets)`
  refine WP.bind_mono (previewWithdraw_wp_gas_logs _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    dsimp only [supplyOf, assetsOf] at hnone
    simp only [OutPostLogs, withdrawWorld?, hnone, Option.bind_none]
    exact ⟨_, hrev.1⟩
  rintro m1 - ⟨v, mem1, g1, rd1, sub1, hv, rfl, hmem1, hg1, hg1u, hl1⟩
  dsimp only [supplyOf, assetsOf] at hv
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 hg1u ⊢
  -- the allowance step
  refine WP.bind_mono (withdrawSpend_wp_logs _ rfl hj rfl rfl (by simp) hstatic hmem1
    (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    simp only [OutPostLogs, withdrawWorld?, hv, Option.bind_some, hnone, Option.bind_none]
    exact hrev
  rintro m2 - ⟨w₁, hw₁, mem2, g2, sub2, rfl, hm2a, hm2b, hg2, hg2u, hl2⟩
  simp only [resumeWorld, Machine.resumeWith] at hg2 hg2u ⊢
  have hmem2 : FmpOk mem2 := by
    rcases hmem1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact .inl ⟨hm2a.trans a, hm2b.trans b⟩
    · exact .inr ⟨hm2a.trans a, hm2b.trans b⟩
  clear hm2a hm2b
  -- `beforeWithdraw`
  pwp_run_to 0x104b
  refine WP.bind_mono (bump_wp_logs _ rfl hj rfl rfl (by simp) (by pjumpdest_disch) hstatic hmem2
    (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    simp only [OutPostLogs, withdrawWorld?, hv, Option.bind_some, hw₁, hnone, Option.bind_none]
    exact hrev
  rintro m3 - ⟨w₂, hw₂, g3, sub3, rfl, hg3, hg3u, hl3⟩
  simp only [resumeWorld, Machine.resumeWith, BitVec.reduceToNat] at hg3 hg3u ⊢
  -- `_burn(owner, shares)`
  pwp_run_to 0x105a
  refine WP.bind_mono (burn_wp_logs _ rfl hj rfl rfl (by simp) (by pjumpdest_disch) hstatic hmem2
    (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    simp only [OutPostLogs, withdrawWorld?, hv, Option.bind_some, hw₁, hw₂, hnone, Option.bind_none]
    exact hrev
  rintro m4 - ⟨w₃, hw₃, mem4, g4, rd4, sub4, rfl, hmem4, hg4, hg4u, hl4⟩
  simp only [resumeWorld, Machine.resumeWith, BitVec.reduceToNat] at hg4 hg4u ⊢
  have hcode₃ : ∃ ia, w₃.code i.asset = SolmateAsset.runtimeCodeWith ia := by
    obtain ⟨ia, h⟩ := hcode
    exact ⟨ia, by rw [code_of_burnStep hw₃, code_of_bumpStep hw₂, code_of_spendStep hw₁, h]⟩
  -- the `Withdraw` event, then `safeTransfer(asset, receiver, assets)`
  rcases hmem4 with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
  all_goals
    pwp_run_to 0x10b9 [hfmp, hsize, readBytes_code_asset2668, ofAddress_and_addressMask,
      addressMask_and_ofAddress]
    refine WP.bind_mono (safeTransfer_wp_logs _ ⟨rfl, hj, hcode₃, hpre, hdepth⟩ rfl rfl (by simp)
      (by pjumpdest_disch) hstatic hane ?_ (by evm_gas) (by evm_gas)) ?_ ?_
    · first
        | exact .inl ⟨by simp only [Memory.loadWord_expand,
              Memory.loadWord_storeWord_of_disjoint _ 128 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 160 64 _ (by decide), hfmp],
            by simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter,
              Memory.words, hsize]; decide⟩
        | exact .inr ⟨by simp only [Memory.loadWord_expand,
              Memory.loadWord_storeWord_of_disjoint _ 160 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 192 64 _ (by decide), hfmp],
            by simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter,
              Memory.words, hsize]; decide⟩
    · rintro mf o - ⟨hlt, hrev⟩
      dsimp only [assetsOf] at hlt
      simp only [OutPostLogs, withdrawWorld?, hv, Option.bind_some, hw₁, hw₂, hw₃, payStep, hlt,
        ↓reduceIte, Option.map_none]
      exact hrev
    rintro m5 - ⟨hbal, mem5, g5, rd5, sub5, rfl, hm5a, hm5b, hg5, hl5⟩
    dsimp only [assetsOf] at hbal
    simp only [resumeWorld, Machine.resumeWith, BitVec.reduceToNat] at hg5 hm5a hm5b ⊢
    simp only [Memory.loadWord_expand, loadWord_64_storeWord, Nat.reduceLeDiff, hfmp] at hm5a
    simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
      hsize, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.max_def,
      Nat.reduceLeDiff, ↓reduceIte] at hm5b
    have hW : withdrawWorld? m_ctx.crypto m_world m_msg.currentTarget i.asset m_msg.caller assets
        receiver owner = some (EvmLean.Solidity.Erc20.transferWorld m_ctx.crypto w₃ i.asset
          m_msg.currentTarget receiver assets, BitVec.ofNat 256 v) := by
      simp only [withdrawWorld?, hv, Option.bind_some, hw₁, hw₂, hw₃, payStep,
        Nat.not_lt.2 hbal, ↓reduceIte, Option.map_some]
    rw [hW]
    clear hW hcode₃ hcode hpre
    pwp_steps [hm5a, hm5b]
    refine ⟨rfl, rfl, ?_⟩
    dsimp only [outputMachine]
    logs_simp [hl1, hl2, hl3, hl4, hl5]
    event_log [assets, BitVec.ofNat 256 v]

end EvmLeanSpecs.Refinement
