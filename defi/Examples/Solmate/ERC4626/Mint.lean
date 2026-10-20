import Examples.Solmate.ERC4626.Deposit

/-!
# `mint(shares, receiver)` refines the model, in any frame

`mint_refines`: as `deposit_refines`, for `mint(shares, receiver)`: `previewMint_wp_gas`
(rounding up; no zero check), `safeTransferFrom_wp` of the previewed assets, `mintShares_wp` of
`shares`, the `Deposit` event, `afterDeposit_wp`. On the model's `some (s', assets)` the call
returns the ABI word of `assets`, the world is `depositWorld` and represents `s'`; on `none`
it reverts. Same hypotheses as `deposit_refines`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault Shares

set_option maxHeartbeats 0 in
/-- **`mint(shares, receiver)` refines `Solmate.mint`**, in any frame. -/
theorem mint_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m)
    (hstatic : m.frame.msg.isStatic = false) (hgas : 250000 ≤ m.frame.gasLeft)
    {shares : Word} {receiver : Address}
    (hd : TwoWordCall m.frame.msg.data 0x94bf804d shares (Word.ofAddress receiver))
    (hne : m.frame.msg.currentTarget ≠ i.asset)
    (hk : KeccakAvoids m.ctx.crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller)
    (hbv : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate m.frame.msg.currentTarget)
    (hbr : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate receiver)
    (ha : Erc20.AllowanceSlotOk m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller
      m.frame.msg.currentTarget)
    (hinv : Solmate.Inv (absOf i.asset m)) :
    Halts m (EntryPost m i.asset (DepositAllowances m.ctx.crypto receiver)
      (TransferFromAllowances m.ctx.crypto m.frame.msg.currentTarget m.frame.msg.caller
        m.frame.msg.currentTarget)
      (fun v => depositWorld m.ctx.crypto m.world m.frame.msg.currentTarget i.asset
        m.frame.msg.caller receiver (BitVec.ofNat 256 v) shares)
      (Solmate.mint (absOf i.asset m) m.frame.msg.caller shares.toNat receiver)) := by
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  have hprev : (absOf i.asset m).previewMint shares.toNat =
      previewMintN (supplyOf m).toNat (assetsOf i.asset m).toNat shares.toNat :=
    absOf_previewMint _ _ _
  have hshares : shares.toNat < 2 ^ 256 := shares.isLt
  obtain ⟨h2, h6, h7⟩ := balanceSlot_ne_fixed hk receiver
  generalize hr : Solmate.mint (absOf i.asset m) m.frame.msg.caller shares.toNat receiver = res
  view_intro
  simp only [absOf] at hr hprev hinv
  pwp_run_to 0x96b [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
  refine WP.bind_mono (previewMint_wp_gas _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    rw [mint_none_preview (hprev.trans hnone)] at hr
    subst hr
    exact ⟨_, hrev.1⟩
  rintro m' - ⟨v, mem, g, rd, sub, hv, rfl, hmem', hg1, hg1u⟩
  have hpv := hprev.trans hv
  have hvlt := previewMintN_lt hshares hv
  have hvn : (BitVec.ofNat 256 v).toNat = v := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  clear hv hprev
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 hg1u ⊢
  pwp_run_to 0xf38 [readBytes_code_asset2169, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  refine WP.bind_mono (safeTransferFrom_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ hstatic rfl rfl
    (by simp) (by pjumpdest_disch) hmem' (by dsimp only; omega) (by dsimp only; omega)
    hbc hbv ha hinv.1) ?_ ?_
  · rintro mf o - ⟨hT, out, ho⟩
    rw [hvn] at hT
    rw [mint_none_transfer hpv hT] at hr
    subst hr
    exact ⟨_, ho⟩
  rintro m2 - ⟨t', hT, hrepA, mem2, g2, rd2, sub2, rfl, hmem2, hg2⟩
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg2 ⊢
  rw [hvn] at hT
  pwp_run_to 0xfdc
  have hS : (Erc20.transferFromWorld m_ctx.crypto m_world i.asset m_msg.currentTarget m_msg.caller
      m_msg.currentTarget (BitVec.ofNat 256 v)).sload m_msg.currentTarget 2#256 =
      m_world.sload m_msg.currentTarget 2#256 := sload_transferFromWorld_ne hne _
  refine WP.bind_mono (mintShares_wp _ rfl hj hstatic rfl rfl (by simp) (by pjumpdest_disch)
    hmem2 (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hov, out, ho⟩
    rw [mint_none_mint hpv (token_mint_none_iff.2 ?_)] at hr
    · subst hr
      exact ⟨_, ho⟩
    · dsimp only at hov
      rw [hS] at hov
      exact hov
  rintro m3 - ⟨hov, mem3, g3, rd3, sub3, rfl, hmem3, hg3⟩
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg3 hov ⊢
  rw [hS] at hov
  rcases hmem3 with ⟨hfmp3, hsz3⟩ | ⟨hfmp3, hsz3⟩ <;>
  · pwp_run_to 0x1033 [hfmp3, hsz3]
    have h7w : (mintWorld m_ctx.crypto (Erc20.transferFromWorld m_ctx.crypto m_world i.asset
        m_msg.currentTarget m_msg.caller m_msg.currentTarget (BitVec.ofNat 256 v)) m_msg.currentTarget
        receiver shares).sload m_msg.currentTarget 7#256 =
        m_world.sload m_msg.currentTarget 7#256 := by
      rw [sload_mintWorld (.inr ⟨by decide, fun e => h7 e.symm⟩), sload_transferFromWorld_ne hne]
    refine WP.bind_mono (afterDeposit_wp _ rfl hj hstatic rfl rfl (by simp) (by pjumpdest_disch)
      ?_ (by evm_gas)) ?_ ?_
    · unfold FmpAfterTransfer
      simp (disch := decide) only [Memory.loadWord_storeWord_of_disjoint,
        Memory.loadWord_expand, hfmp3, Memory.size_storeWord, Memory.size_expand, hsz3,
        Memory.wordsAfter, Memory.words, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
        Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.max_def, ↓reduceIte]
      decide
    · rintro mf o - ⟨hov7, out, ho⟩
      dsimp only at hov7
      rw [h7w] at hov7
      rw [mint_none_bump hpv (bump_none_iff.2 (.inl hov7))] at hr
      subst hr
      exact ⟨_, ho⟩
    rintro m4 - ⟨hov7, g4, sub4, rfl, hg4⟩
    simp only [Machine.resumeWith, BitVec.reduceToNat] at hg4 hov7 ⊢
    rw [h7w] at hov7
    pwp_steps [hfmp3, hsz3]
    obtain ⟨s', hdep', hR⟩ := mint_post_some (crypto := m_ctx.crypto) (w := m_world)
      (vault := m_msg.currentTarget) (asset := i.asset) (caller := m_msg.caller)
      (receiver := receiver) hne hk hbc hbv hbr ha hinv hpv hvlt hT hov hov7
    rw [hdep'] at hr
    subst hr
    exact ⟨rfl, rfl, hR⟩


end EvmLeanSpecs.Refinement
