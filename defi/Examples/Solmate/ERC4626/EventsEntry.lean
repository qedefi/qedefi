import Examples.Solmate.ERC4626.Deposit
import Examples.Solmate.ERC4626.EventsInternal
import Examples.Solmate.ERC4626.EventsConvert
import Examples.Solmate.ERC4626.Events
import Examples.Solmate.ERC4626.Withdraw

/-!
# Events of `deposit`

`deposit_events`: the companion of `deposit_refines` (`Deposit.lean`) that also
determines the frame's logs — the same proof, composing the log-tracking summaries
(`*_wp_gas_logs`, `safeTransferFrom_wp_logs`, `mintShares_wp_logs`, `afterDeposit_wp_logs`) and the inline
`Deposit` event.
-/

section

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.ERC4626 Defi.Math Defi.ERC20 Examples.Solmate.ERC4626.Shares

set_option maxHeartbeats 0 in
/-- **`deposit` emits the model's events**, in any frame: as `deposit_refines`, and the frame
ends as `EventsPost` with the encoded events of the model — on success the asset's
`Transfer(caller, vault, assets)` (inside `safeTransferFrom`), the shares' `Transfer(0,
receiver, shares)` and `Deposit(caller, receiver, assets, shares)`, in this order. -/
theorem deposit_events {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m)
    (hstatic : m.frame.msg.isStatic = false) (hgas : 250000 ≤ m.frame.gasLeft)
    {assets : Word} {receiver : Address}
    (hd : TwoWordCall m.frame.msg.data 0x6e553f65 assets (Word.ofAddress receiver))
    (hne : m.frame.msg.currentTarget ≠ i.asset)
    (hk : KeccakAvoids m.ctx.crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)
    (hbv : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate m.frame.msg.currentTarget)
    (hbr : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate receiver)
    (ha : ERC20.AllowanceSlotOk m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller
      m.frame.msg.currentTarget)
    (hinv : Solmate.Inv (absOf i.asset m)) :
    Halts m (fun mf o => EntryPost m i.asset (DepositAllowances m.ctx.crypto receiver)
      (TransferFromAllowances m.ctx.crypto m.frame.msg.currentTarget m.frame.msg.caller
        m.frame.msg.currentTarget)
      (fun v => depositWorld m.ctx.crypto m.world m.frame.msg.currentTarget i.asset
        m.frame.msg.caller receiver assets (BitVec.ofNat 256 v))
      (Solmate.deposit (absOf i.asset m) m.frame.msg.caller assets.toNat receiver) mf o ∧
      EventsPost m (encode m.frame.msg.currentTarget i.asset
        (Solmate.Events.deposit m.frame.msg.currentTarget m.frame.msg.caller receiver assets.toNat
          (Solmate.deposit (absOf i.asset m) m.frame.msg.caller assets.toNat receiver))) mf o) := by
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hsz4 : 4 ≤ m.frame.msg.data.size := by omega
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by have := h.sizeLt; omega)
  have hprev : (absOf i.asset m).previewDeposit assets.toNat =
      convertToSharesN (supplyOf m).toNat (assetsOf i.asset m).toNat assets.toNat :=
    absOf_convertToShares _ _ _
  have hassets : assets.toNat < 2 ^ 256 := assets.isLt
  obtain ⟨h2, h6, h7⟩ := balanceSlot_ne_fixed hk receiver
  generalize hr : Solmate.deposit (absOf i.asset m) m.frame.msg.caller assets.toNat receiver = res
  view_intro
  simp only [absOf] at hr hprev hinv
  pwp_run_to 0xbda [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
  refine WP.bind_mono (convertToShares_wp_gas_logs _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    rw [deposit_none_preview (hprev.trans hnone)] at hr
    subst hr
    exact ⟨⟨_, hrev.1⟩, eventsPost_revert ⟨_, hrev.1⟩⟩
  rintro m' - ⟨v, mem, g, rd, sub, hv, rfl, hmem', hg1, hg1u, hl1⟩
  have hpv := hprev.trans hv
  have hvlt := convertToSharesN_lt hassets hv
  clear hv hprev
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 hg1u ⊢
  pwp_steps
  by_cases hv0 : v = 0
  · subst hv0
    rw [deposit_none_zero hpv] at hr
    subst hr
    rcases hmem' with ⟨hfmp, hsz⟩ | ⟨hfmp, hsz⟩ <;>
    · pwp_steps [hfmp, hsz]
      exact ⟨⟨_, rfl⟩, eventsPost_revert ⟨_, rfl⟩⟩
  · have hne0 : (0#256 - BitVec.ofNat 256 v) ≠ 0#256 := by
      intro he
      apply hv0
      have := congrArg BitVec.toNat (sub_eq_zero.1 he).symm
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt] at this
      simpa using this
    pwp_run_to 0xf38 [readBytes_code_asset2014, ofAddress_and_addressMask,
      addressMask_and_ofAddress]
    refine WP.bind_mono (safeTransferFrom_wp_logs _ ⟨rfl, hj, hcode, hpre, hdepth⟩ hstatic rfl rfl
      (by simp) (by pjumpdest_disch) hmem' (by dsimp only; omega) (by dsimp only; omega)
      hbc hbv ha hinv.1) ?_ ?_
    · rintro mf o - ⟨hT, out, ho⟩
      rw [deposit_none_transfer hpv hT] at hr
      subst hr
      exact ⟨⟨_, ho⟩, eventsPost_revert ⟨_, ho⟩⟩
    rintro m2 - ⟨t', hT, hrepA, mem2, g2, rd2, sub2, rfl, hmem2, hg2, hl2⟩
    simp only [Machine.resumeWith, BitVec.reduceToNat] at hg2 ⊢
    pwp_run_to 0xfdc
    have hS : (ERC20.transferFromWorld m_ctx.crypto m_world i.asset m_msg.currentTarget m_msg.caller
        m_msg.currentTarget assets).sload m_msg.currentTarget 2#256 =
        m_world.sload m_msg.currentTarget 2#256 := sload_transferFromWorld_ne hne _
    have hvn : (BitVec.ofNat 256 v).toNat = v := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
    refine WP.bind_mono (mintShares_wp_logs _ rfl hj hstatic rfl rfl (by simp) (by pjumpdest_disch)
      hmem2 (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hov, out, ho⟩
      rw [deposit_none_mint hpv hv0 hT (token_mint_none_iff.2 ?_)] at hr
      · subst hr
        exact ⟨⟨_, ho⟩, eventsPost_revert ⟨_, ho⟩⟩
      · dsimp only at hov
        rw [hS, hvn] at hov
        exact hov
    rintro m3 - ⟨hov, mem3, g3, rd3, sub3, rfl, hmem3, hg3, hl3⟩
    simp only [Machine.resumeWith, BitVec.reduceToNat] at hg3 hov ⊢
    rw [hS, hvn] at hov
    rcases hmem3 with ⟨hfmp3, hsz3⟩ | ⟨hfmp3, hsz3⟩ <;>
    · pwp_run_to 0x1033 [hfmp3, hsz3]
      have h7w : (mintWorld m_ctx.crypto (ERC20.transferFromWorld m_ctx.crypto m_world i.asset
          m_msg.currentTarget m_msg.caller m_msg.currentTarget assets) m_msg.currentTarget receiver
          (BitVec.ofNat 256 v)).sload m_msg.currentTarget 7#256 =
          m_world.sload m_msg.currentTarget 7#256 := by
        rw [sload_mintWorld (.inr ⟨by decide, fun e => h7 e.symm⟩), sload_transferFromWorld_ne hne]
      refine WP.bind_mono (afterDeposit_wp_logs _ rfl hj hstatic rfl rfl (by simp) (by pjumpdest_disch)
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
        rw [deposit_none_bump hpv hT (bump_none_iff.2 (.inl hov7))] at hr
        subst hr
        exact ⟨⟨_, ho⟩, eventsPost_revert ⟨_, ho⟩⟩
      rintro m4 - ⟨hov7, g4, sub4, rfl, hg4, hl4⟩
      simp only [Machine.resumeWith, BitVec.reduceToNat] at hg4 hov7 ⊢
      rw [h7w] at hov7
      pwp_steps [hfmp3, hsz3]
      obtain ⟨s', hdep', hR⟩ := deposit_post_some (crypto := m_ctx.crypto) (w := m_world)
        (vault := m_msg.currentTarget) (asset := i.asset) (caller := m_msg.caller)
        (receiver := receiver) hne hk hbc hbv hbr ha hinv hpv hv0 hvlt hT hov hov7
      rw [hdep'] at hr
      subst hr
      refine ⟨⟨rfl, rfl, hR⟩, ?_⟩
      show _ = _
      dsimp only [outputMachine]
      rw [encode_deposit, append_three]
      logs_simp [hl1, hl2, hl3, hl4]
      simp only [ofAddress_and_addressMask]
      event_log [assets, BitVec.ofNat 256 v]

end Examples.Solmate.ERC4626

end

section

/-!
## Events of `mint`

`mint_events`: the companion of `mint_refines` (`Mint.lean`) that also
determines the frame's logs — the same proof, composing the log-tracking summaries
(`*_wp_gas_logs`, `safeTransferFrom_wp_logs`, `mintShares_wp_logs`, `afterDeposit_wp_logs`) and the inline
`Deposit` event.
-/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.ERC4626 Defi.Math Defi.ERC20 Examples.Solmate.ERC4626.Shares

set_option maxHeartbeats 0 in
/-- **`mint` emits the model's events**, in any frame: as `mint_refines`, and the frame
ends as `EventsPost` with the encoded events of the model — on success the asset's
`Transfer(caller, vault, assets)` (inside `safeTransferFrom`), the shares' `Transfer(0,
receiver, shares)` and `Deposit(caller, receiver, assets, shares)`, in this order. -/
theorem mint_events {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m)
    (hstatic : m.frame.msg.isStatic = false) (hgas : 250000 ≤ m.frame.gasLeft)
    {shares : Word} {receiver : Address}
    (hd : TwoWordCall m.frame.msg.data 0x94bf804d shares (Word.ofAddress receiver))
    (hne : m.frame.msg.currentTarget ≠ i.asset)
    (hk : KeccakAvoids m.ctx.crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)
    (hbv : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate m.frame.msg.currentTarget)
    (hbr : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate receiver)
    (ha : ERC20.AllowanceSlotOk m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller
      m.frame.msg.currentTarget)
    (hinv : Solmate.Inv (absOf i.asset m)) :
    Halts m (fun mf o => EntryPost m i.asset (DepositAllowances m.ctx.crypto receiver)
      (TransferFromAllowances m.ctx.crypto m.frame.msg.currentTarget m.frame.msg.caller
        m.frame.msg.currentTarget)
      (fun v => depositWorld m.ctx.crypto m.world m.frame.msg.currentTarget i.asset
        m.frame.msg.caller receiver (BitVec.ofNat 256 v) shares)
      (Solmate.mint (absOf i.asset m) m.frame.msg.caller shares.toNat receiver) mf o ∧
      EventsPost m (encode m.frame.msg.currentTarget i.asset
        (Solmate.Events.mint4626 m.frame.msg.currentTarget m.frame.msg.caller receiver shares.toNat
          (Solmate.mint (absOf i.asset m) m.frame.msg.caller shares.toNat receiver))) mf o) := by
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
  refine WP.bind_mono (previewMint_wp_gas_logs _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    rw [mint_none_preview (hprev.trans hnone)] at hr
    subst hr
    exact ⟨⟨_, hrev.1⟩, eventsPost_revert ⟨_, hrev.1⟩⟩
  rintro m' - ⟨v, mem, g, rd, sub, hv, rfl, hmem', hg1, hg1u, hl1⟩
  have hpv := hprev.trans hv
  have hvlt := previewMintN_lt hshares hv
  have hvn : (BitVec.ofNat 256 v).toNat = v := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  clear hv hprev
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 hg1u ⊢
  pwp_run_to 0xf38 [readBytes_code_asset2169, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  refine WP.bind_mono (safeTransferFrom_wp_logs _ ⟨rfl, hj, hcode, hpre, hdepth⟩ hstatic rfl rfl
    (by simp) (by pjumpdest_disch) hmem' (by dsimp only; omega) (by dsimp only; omega)
    hbc hbv ha hinv.1) ?_ ?_
  · rintro mf o - ⟨hT, out, ho⟩
    rw [hvn] at hT
    rw [mint_none_transfer hpv hT] at hr
    subst hr
    exact ⟨⟨_, ho⟩, eventsPost_revert ⟨_, ho⟩⟩
  rintro m2 - ⟨t', hT, hrepA, mem2, g2, rd2, sub2, rfl, hmem2, hg2, hl2⟩
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg2 ⊢
  rw [hvn] at hT
  pwp_run_to 0xfdc
  have hS : (ERC20.transferFromWorld m_ctx.crypto m_world i.asset m_msg.currentTarget m_msg.caller
      m_msg.currentTarget (BitVec.ofNat 256 v)).sload m_msg.currentTarget 2#256 =
      m_world.sload m_msg.currentTarget 2#256 := sload_transferFromWorld_ne hne _
  refine WP.bind_mono (mintShares_wp_logs _ rfl hj hstatic rfl rfl (by simp) (by pjumpdest_disch)
    hmem2 (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hov, out, ho⟩
    rw [mint_none_mint hpv (token_mint_none_iff.2 ?_)] at hr
    · subst hr
      exact ⟨⟨_, ho⟩, eventsPost_revert ⟨_, ho⟩⟩
    · dsimp only at hov
      rw [hS] at hov
      exact hov
  rintro m3 - ⟨hov, mem3, g3, rd3, sub3, rfl, hmem3, hg3, hl3⟩
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg3 hov ⊢
  rw [hS] at hov
  rcases hmem3 with ⟨hfmp3, hsz3⟩ | ⟨hfmp3, hsz3⟩ <;>
  · pwp_run_to 0x1033 [hfmp3, hsz3]
    have h7w : (mintWorld m_ctx.crypto (ERC20.transferFromWorld m_ctx.crypto m_world i.asset
        m_msg.currentTarget m_msg.caller m_msg.currentTarget (BitVec.ofNat 256 v)) m_msg.currentTarget
        receiver shares).sload m_msg.currentTarget 7#256 =
        m_world.sload m_msg.currentTarget 7#256 := by
      rw [sload_mintWorld (.inr ⟨by decide, fun e => h7 e.symm⟩), sload_transferFromWorld_ne hne]
    refine WP.bind_mono (afterDeposit_wp_logs _ rfl hj hstatic rfl rfl (by simp) (by pjumpdest_disch)
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
      exact ⟨⟨_, ho⟩, eventsPost_revert ⟨_, ho⟩⟩
    rintro m4 - ⟨hov7, g4, sub4, rfl, hg4, hl4⟩
    simp only [Machine.resumeWith, BitVec.reduceToNat] at hg4 hov7 ⊢
    rw [h7w] at hov7
    pwp_steps [hfmp3, hsz3]
    obtain ⟨s', hdep', hR⟩ := mint_post_some (crypto := m_ctx.crypto) (w := m_world)
      (vault := m_msg.currentTarget) (asset := i.asset) (caller := m_msg.caller)
      (receiver := receiver) hne hk hbc hbv hbr ha hinv hpv hvlt hT hov hov7
    rw [hdep'] at hr
    subst hr
    refine ⟨⟨rfl, rfl, hR⟩, ?_⟩
    show _ = _
    dsimp only [outputMachine]
    rw [encode_mint4626, append_three]
    logs_simp [hl1, hl2, hl3, hl4]
    simp only [ofAddress_and_addressMask]
    event_log [BitVec.ofNat 256 v, shares]

end Examples.Solmate.ERC4626

end

section

/-!
## Logs of `withdraw`, at the bytecode level

`withdraw_halts_events`: the companion of `withdraw_halts` (`Withdraw.lean`) that also determines the frame's
logs (`OutPostLogs`), composing the log-tracking summaries of `Examples.Solmate.ERC4626.EventsInternal` and
`EventsConvert` and the inline `Withdraw` event.
-/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts
open Examples.Solmate.ERC4626.Out

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
        receiver owner = some (EvmLogic.Solidity.ERC20.transferWorld m_ctx.crypto w₃ i.asset
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

end Examples.Solmate.ERC4626

end

section

/-!
## Logs of `redeem`, at the bytecode level

`redeem_halts_events`: the companion of `redeem_halts` (`Redeem.lean`) that also determines the frame's
logs (`OutPostLogs`), composing the log-tracking summaries of `Examples.Solmate.ERC4626.EventsInternal` and
`EventsConvert` and the inline `Withdraw` event.
-/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts
open Examples.Solmate.ERC4626.Out

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
          receiver owner = some (EvmLogic.Solidity.ERC20.transferWorld m_ctx.crypto w₃
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

end Examples.Solmate.ERC4626

end

section

/-!
## Events of the ERC-4626 entry points against the model

For the compiled vault (any immutables, any asset address):

* **Frame form.** `deposit_events`, `mint_events` (`Examples.Solmate.ERC4626.EventsEntry`, `Examples.Solmate.ERC4626.EventsEntry`) and
  `withdraw_events`, `redeem_events` (here, from the bytecode-level `withdraw_halts_events` /
  `redeem_halts_events` and the model-level `Out.withdrawWorld?_refines` /
  `Out.redeemWorld?_refines`): in any frame (top level or called by another contract), with the
  hypotheses of `deposit_refines` / `withdraw_refines`, the frame ends as the refinement
  theorem says **and** as `EventsPost` with the encoded events of the model (`Events.deposit`,
  …): on success it appended exactly the asset's and the vault's logs, in emission order —
  for `deposit` / `mint` the asset's `Transfer(caller, vault, assets)` (emitted by the asset's
  frame, inside `safeTransferFrom`, and merged into the vault's on return), the shares'
  `Transfer(0, receiver, shares)`, `Deposit(caller, receiver, assets, shares)`; for `withdraw` /
  `redeem` the shares' `Transfer(owner, 0, shares)`, `Withdraw(caller, receiver, owner, assets,
  shares)`, the asset's `Transfer(vault, receiver, assets)`; on revert the model emits nothing
  (and the caller drops the frame's logs, `resumeAfter_eventsPost`).
* **Top-level form.** `deposit_events_call`, …: a top-level call of the `Deployed` vault returns a
  result whose `logs` are `encode vault asset (events (abs ctx.crypto w vault asset) op)`.
-/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.ERC4626 Defi.Math Defi.ERC20 Defi.ERC4626.Solmate Examples.Solmate.ERC4626.Out

/-- **`withdraw(assets, receiver, owner)` emits the model's events**, in any frame: as
`withdraw_refines`, and the frame ends as `EventsPost` with the encoded `Events.withdraw`. -/
theorem withdraw_events {i : SolmateVault.Immutables} (m : Machine) (h : OutPre i m)
    {assets : Word} {receiver owner : Address}
    (hd : ThreeWordCall m.frame.msg.data 0xb460af94 assets (Word.ofAddress receiver)
      (Word.ofAddress owner))
    (hk : OutSlots m.ctx.crypto m.frame.msg.currentTarget m.frame.msg.caller owner receiver)
    (hinv : Solmate.Inv (absOf i.asset m)) :
    Halts m (fun mf o => OutRefPost m.ctx.crypto m.world m.frame.msg.currentTarget i.asset
      m.frame.msg.caller receiver owner (Solmate.withdraw (absOf i.asset m) m.frame.msg.caller
        assets.toNat receiver owner) mf o ∧
      EventsPost m (encode m.frame.msg.currentTarget i.asset
        (Events.withdraw m.frame.msg.currentTarget m.frame.msg.caller receiver owner assets.toNat
          (Solmate.withdraw (absOf i.asset m) m.frame.msg.caller assets.toNat receiver owner)))
        mf o) := by
  have hW := withdrawWorld?_refines (refines_iff.2 rfl) hinv h.assetNe hk assets
  refine (withdraw_halts_events m h hd).mono fun mf o _ hp => ?_
  revert hW
  generalize Solmate.withdraw (absOf i.asset m) m.frame.msg.caller assets.toNat receiver owner = r
  intro hW
  rcases r with _ | ⟨s', v⟩
  · simp only at hW
    rw [hW] at hp
    exact ⟨hp, eventsPost_revert hp⟩
  · obtain ⟨w', hrw, hR⟩ := hW
    rw [hrw] at hp
    obtain ⟨ho, hw, hl⟩ := hp
    refine ⟨⟨ho, hw ▸ hR, hw ▸ fun b => code_of_withdrawWorld? hrw b⟩, ?_⟩
    rw [ho]
    exact eventsPost_success (by rw [hl, encode_withdraw, append_three])

/-- **`redeem(shares, receiver, owner)` emits the model's events**, in any frame: as
`redeem_refines`, and the frame ends as `EventsPost` with the encoded `Events.redeem`. -/
theorem redeem_events {i : SolmateVault.Immutables} (m : Machine) (h : OutPre i m)
    {shares : Word} {receiver owner : Address}
    (hd : ThreeWordCall m.frame.msg.data 0xba087652 shares (Word.ofAddress receiver)
      (Word.ofAddress owner))
    (hk : OutSlots m.ctx.crypto m.frame.msg.currentTarget m.frame.msg.caller owner receiver)
    (hinv : Solmate.Inv (absOf i.asset m)) :
    Halts m (fun mf o => OutRefPost m.ctx.crypto m.world m.frame.msg.currentTarget i.asset
      m.frame.msg.caller receiver owner (Solmate.redeem (absOf i.asset m) m.frame.msg.caller
        shares.toNat receiver owner) mf o ∧
      EventsPost m (encode m.frame.msg.currentTarget i.asset
        (Events.redeem m.frame.msg.currentTarget m.frame.msg.caller receiver owner shares.toNat
          (Solmate.redeem (absOf i.asset m) m.frame.msg.caller shares.toNat receiver owner)))
        mf o) := by
  have hW := redeemWorld?_refines (refines_iff.2 rfl) hinv h.assetNe hk shares
  refine (redeem_halts_events m h hd).mono fun mf o _ hp => ?_
  revert hW
  generalize Solmate.redeem (absOf i.asset m) m.frame.msg.caller shares.toNat receiver owner = r
  intro hW
  rcases r with _ | ⟨s', v⟩
  · simp only at hW
    rw [hW] at hp
    exact ⟨hp, eventsPost_revert hp⟩
  · obtain ⟨w', hrw, hR⟩ := hW
    rw [hrw] at hp
    obtain ⟨ho, hw, hl⟩ := hp
    refine ⟨⟨ho, hw ▸ hR, hw ▸ fun b => code_of_redeemWorld? hrw b⟩, ?_⟩
    rw [ho]
    exact eventsPost_success (by rw [hl, encode_redeem, append_three])

/-! ## Top-level transactions -/

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

/-- **`deposit(assets, receiver)` at the top level**: the result's logs are the model's events,
encoded. Hypotheses of `deposit_call`. -/
theorem deposit_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 250000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver : Address}
    (hk : KeccakAvoids ctx.crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : ERC20.BalanceSlotOk ctx.crypto ERC20.Layout.solmate caller)
    (hbv : ERC20.BalanceSlotOk ctx.crypto ERC20.Layout.solmate vault)
    (hbr : ERC20.BalanceSlotOk ctx.crypto ERC20.Layout.solmate receiver)
    (ha : ERC20.AllowanceSlotOk ctx.crypto ERC20.Layout.solmate caller vault)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (assets : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0x6e553f65 [assets, Word.ofAddress receiver]) gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.deposit caller assets.toNat receiver)) := by
  have hne := hdep.asset_ne
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := deposit_events _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile (by omega) hgas' (by rw [Abi.size_encodeCall]; simp))
    rfl hgas (twoWordCall_encodeCall' (by decide) assets _) hne.symm hk hbc hbv hbr ha hinv
  exact events_call hdeleg (Shares.delegatedAddress?_code i) (hdep.vaultNotPrecompile _)
    (hm.mono fun _ _ _ h => h.2)

/-- **`mint(shares, receiver)` at the top level**: the result's logs are the model's events,
encoded. Hypotheses of `mint_call`. -/
theorem mint_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 250000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver : Address}
    (hk : KeccakAvoids ctx.crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : ERC20.BalanceSlotOk ctx.crypto ERC20.Layout.solmate caller)
    (hbv : ERC20.BalanceSlotOk ctx.crypto ERC20.Layout.solmate vault)
    (hbr : ERC20.BalanceSlotOk ctx.crypto ERC20.Layout.solmate receiver)
    (ha : ERC20.AllowanceSlotOk ctx.crypto ERC20.Layout.solmate caller vault)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (shares : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0x94bf804d [shares, Word.ofAddress receiver]) gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.mint caller shares.toNat receiver)) := by
  have hne := hdep.asset_ne
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := mint_events _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile (by omega) hgas' (by rw [Abi.size_encodeCall]; simp))
    rfl hgas (twoWordCall_encodeCall' (by decide) shares _) hne.symm hk hbc hbv hbr ha hinv
  exact events_call hdeleg (Shares.delegatedAddress?_code i) (hdep.vaultNotPrecompile _)
    (hm.mono fun _ _ _ h => h.2)

/-- **`withdraw(assets, receiver, owner)` at the top level**: the result's logs are the model's
events, encoded. Hypotheses of `withdraw_call`. -/
theorem withdraw_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 200000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver owner : Address}
    (hk : OutSlots ctx.crypto vault caller owner receiver)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (assets : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0xb460af94 [assets, Word.ofAddress receiver, Word.ofAddress owner])
          gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.withdraw caller assets.toNat receiver owner)) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := withdraw_events _ (outPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas'
    (by rw [Abi.size_encodeCall]; simp))
    (threeWordCall_encodeCall' (by decide) assets _ _) hk hinv
  exact events_call hdeleg (Shares.delegatedAddress?_code i) (hdep.vaultNotPrecompile _)
    (hm.mono fun _ _ _ h => h.2)

/-- **`redeem(shares, receiver, owner)` at the top level**: the result's logs are the model's
events, encoded. Hypotheses of `redeem_call`. -/
theorem redeem_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 200000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver owner : Address}
    (hk : OutSlots ctx.crypto vault caller owner receiver)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (shares : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0xba087652 [shares, Word.ofAddress receiver, Word.ofAddress owner])
          gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.redeem caller shares.toNat receiver owner)) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := redeem_events _ (outPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas'
    (by rw [Abi.size_encodeCall]; simp))
    (threeWordCall_encodeCall' (by decide) shares _ _) hk hinv
  exact events_call hdeleg (Shares.delegatedAddress?_code i) (hdep.vaultNotPrecompile _)
    (hm.mono fun _ _ _ h => h.2)

end Examples.Solmate.ERC4626

end
