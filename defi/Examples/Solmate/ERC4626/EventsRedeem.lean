import Examples.Solmate.ERC4626.Redeem
import Examples.Solmate.ERC4626.EventsInternal
import Examples.Solmate.ERC4626.EventsConvert

/-!
# Logs of `redeem`, at the bytecode level

`redeem_halts_events`: the companion of `redeem_halts` (`Redeem.lean`) that also determines the frame's
logs (`OutPostLogs`), composing the log-tracking summaries of `EventsWithdrawInternal` and
`EventsConvert` and the inline `Withdraw` event.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Refinement.Out

set_option maxHeartbeats 0 in
/-- **`redeem(uint256,address,address)` with its logs**, in any frame: as `redeem_halts`, and on
success the frame's logs gain the vault's `Transfer(owner, 0, shares)`, then
`Withdraw(caller, receiver, owner, assets, shares)`, then the asset's `Transfer(vault,
receiver, assets)`. -/
theorem redeem_halts_events {i : SolmateVault.Immutables} (m : Machine) (h : OutPre i m)
    {shares : Word} {receiver owner : Address}
    (hd : ThreeWordCall m.frame.msg.data 0xba087652 shares (Word.ofAddress receiver)
      (Word.ofAddress owner)) :
    Halts m (OutPostLogs (fun v => ((m.frame.sub.logs.push (transferLog m.frame.msg.currentTarget owner 0 shares)).push
        (withdrawLog m.frame.msg.currentTarget m.frame.msg.caller receiver owner v shares)).push
        (transferLog i.asset m.frame.msg.currentTarget receiver v))
      (redeemWorld? m.ctx.crypto m.world m.frame.msg.currentTarget i.asset
      m.frame.msg.caller shares receiver owner)) := by
  obtain ⟨hsel, hsize, harg0, harg1, harg2⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  out_intro
  pwp_run_to 0xa93 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
  -- the allowance step
  refine WP.bind_mono (redeemSpend_wp_logs _ rfl hj rfl rfl (by simp) hstatic
    (.inl initMemory_fmpInit) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    simp only [OutPostLogs, redeemWorld?, hnone, Option.bind_none]
    exact hrev
  rintro m2 - ⟨w₁, hw₁, mem2, g2, sub2, rfl, hm2a, hm2b, hg2, hg2u, hl2⟩
  simp only [resumeWorld, Machine.resumeWith] at hg2 hg2u ⊢
  have hmem2 : FmpInit mem2 := ⟨hm2a.trans initMemory_fmpInit.1, hm2b.trans initMemory_fmpInit.2⟩
  clear hm2a hm2b
  have hcode₁ : ∃ ia, w₁.code i.asset = SolmateAsset.runtimeCodeWith ia := by
    obtain ⟨ia, h⟩ := hcode
    exact ⟨ia, by rw [code_of_spendStep hw₁, h]⟩
  -- `previewRedeem(shares)` = `convertToAssets(shares)`
  pwp_run_to 0x593
  refine WP.bind_mono (convertToAssets_wp_gas_logs _ ⟨rfl, hj, hcode₁, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) hmem2 (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    dsimp only [supplyOf, assetsOf] at hnone
    simp only [OutPostLogs, redeemWorld?, hw₁, Option.bind_some, hnone, Option.bind_none]
    exact ⟨_, hrev.1⟩
  rintro m3 - ⟨v, mem3, g3, rd3, sub3, hv, rfl, hmem3, hg3, hg3u, hl3⟩
  dsimp only [supplyOf, assetsOf] at hv
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg3 hg3u ⊢
  have hvlt : v < 2 ^ 256 := convertToAssetsN_lt shares.isLt hv
  -- `ZERO_ASSETS`
  by_cases hv0 : v = 0
  · subst hv0
    have hR : redeemWorld? m_ctx.crypto m_world m_msg.currentTarget i.asset m_msg.caller shares
        receiver owner = none := by
      simp [redeemWorld?, hw₁, hv]
    rw [hR]
    rcases hmem3 with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hfmp, hsize]
      exact ⟨_, rfl⟩
  · have hnz : 0#256 - BitVec.ofNat 256 v ≠ 0#256 := by
      intro h
      apply hv0
      have h2 : BitVec.ofNat 256 v = 0#256 := by bv_omega
      have := congrArg BitVec.toNat h2
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt] at this
    have hnz' : 0#256 - BitVec.ofNat 256 v ≠ 0 := hnz
    -- `beforeWithdraw`
    pwp_run_to 0x104b
    refine WP.bind_mono (bump_wp_logs _ rfl hj rfl rfl (by simp) (by pjumpdest_disch) hstatic hmem3
      (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hnone, hrev⟩
      simp only [OutPostLogs, redeemWorld?, hw₁, Option.bind_some, hv, hv0, ↓reduceIte, hnone,
        Option.bind_none]
      exact hrev
    rintro m4 - ⟨w₂, hw₂, g4, sub4, rfl, hg4, hg4u, hl4⟩
    simp only [resumeWorld, Machine.resumeWith, BitVec.reduceToNat] at hg4 hg4u ⊢
    -- `_burn(owner, shares)`
    pwp_run_to 0x105a
    refine WP.bind_mono (burn_wp_logs _ rfl hj rfl rfl (by simp) (by pjumpdest_disch) hstatic hmem3
      (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hnone, hrev⟩
      simp only [OutPostLogs, redeemWorld?, hw₁, Option.bind_some, hv, hv0, ↓reduceIte, hw₂, hnone,
        Option.bind_none]
      exact hrev
    rintro m5 - ⟨w₃, hw₃, mem5, g5, rd5, sub5, rfl, hmem5, hg5, hg5u, hl5⟩
    simp only [resumeWorld, Machine.resumeWith, BitVec.reduceToNat] at hg5 hg5u ⊢
    have hcode₃ : ∃ ia, w₃.code i.asset = SolmateAsset.runtimeCodeWith ia := by
      obtain ⟨ia, h⟩ := hcode₁
      exact ⟨ia, by rw [code_of_burnStep hw₃, code_of_bumpStep hw₂, h]⟩
    -- the `Withdraw` event, then `safeTransfer(asset, receiver, assets)`
    rcases hmem5 with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_run_to 0x10b9 [hfmp, hsize, readBytes_code_asset2995, ofAddress_and_addressMask,
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
        simp only [OutPostLogs, redeemWorld?, hw₁, Option.bind_some, hv, hv0, ↓reduceIte, hw₂, hw₃,
          payStep, hlt, Option.map_none]
        exact hrev
      rintro m6 - ⟨hbal, mem6, g6, rd6, sub6, rfl, hm6a, hm6b, hg6, hl6⟩
      dsimp only [assetsOf] at hbal
      simp only [resumeWorld, Machine.resumeWith, BitVec.reduceToNat] at hg6 hm6a hm6b ⊢
      simp only [Memory.loadWord_expand, loadWord_64_storeWord, Nat.reduceLeDiff, hfmp] at hm6a
      simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
        hsize, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.max_def,
        Nat.reduceLeDiff, ↓reduceIte] at hm6b
      have hR : redeemWorld? m_ctx.crypto m_world m_msg.currentTarget i.asset m_msg.caller shares
          receiver owner = some (EvmLean.Solidity.Erc20.transferWorld m_ctx.crypto w₃
            i.asset m_msg.currentTarget receiver (BitVec.ofNat 256 v), BitVec.ofNat 256 v) := by
        simp only [redeemWorld?, hw₁, Option.bind_some, hv, hv0, ↓reduceIte, hw₂, hw₃, payStep,
          Nat.not_lt.2 hbal, Option.map_some]
      rw [hR]
      clear hR hcode₃ hcode₁ hcode hpre
      pwp_steps [hm6a, hm6b]
      refine ⟨rfl, rfl, ?_⟩
      dsimp only [outputMachine]
      logs_simp [hl2, hl3, hl4, hl5, hl6]
      event_log [BitVec.ofNat 256 v, shares]

end EvmLeanSpecs.Refinement
