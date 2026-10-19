import EvmLeanSpecs.Refinement.DepositModel
import EvmLeanSpecs.Refinement.DepositConvert
import EvmLeanSpecs.Refinement.VaultViewsSpec

/-!
# `deposit(assets, receiver)` refines the model, in any frame

`deposit_refines`: the compiled vault (any immutables `i`), run in any frame satisfying
`ViewPre i` that is non-static and has at least 250000 gas (top level or called by another
contract), on calldata `deposit(assets, receiver)` (`TwoWordCall`, so also calldata assembled
by a calling contract), ends as the model's `Solmate.deposit` of `absOf i.asset m` says
(`EntryPost`): on `some (s', shares)` it returns the ABI word of `shares`, the world is
`depositWorld` and represents `s'`; on `none` it reverts (and the frame's rollback restores
the world).

The proof composes, by `WP.bind_mono`, the dispatcher and ABI decoder (symbolic execution),
`convertToShares_wp_gas` (`previewDeposit`), the `ZERO_SHARES` check, `safeTransferFrom_wp`
(the `CALL` into the asset), `mintShares_wp`, the `Deposit` event, `afterDeposit_wp` and the
return encoder; each revert point is matched with the model step that fails
(`deposit_none_*`), and the success case with `deposit_post_some`.

Hypotheses beyond `ViewPre`: the vault is not the asset; the hash hypotheses of
`DepositModel` (fresh balance slots of caller, vault, receiver; fresh `allowance[caller][vault]`
of the asset; no balance slot is 2, 6 or 7); `Solmate.Inv` of the model state.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault Shares

/-- How a call of `deposit` / `mint` ends, by cases on the model's result `r`: on `some (s', v)`
it returns the ABI word of `v`, the world is `W v`, and the world represents `s'` (allowances of
the shares on `P`, of the asset on `Q`); on `none` it reverts. -/
def EntryPost (m : Machine) (asset : Address) (P Q : Address → Address → Prop)
    (W : ℕ → World) (r : Option (Solmate.State Address × ℕ)) (mf : Machine) (o : Outcome) :
    Prop :=
  match r with
  | some (s', v) => o = .success (Bytes.ofWord (BitVec.ofNat 256 v)) ∧ mf.world = W v ∧
      Out.RefinesOn P Q m.ctx.crypto mf.world m.frame.msg.currentTarget asset s'
  | none => ∃ out, o = .revert out

set_option maxHeartbeats 0 in
/-- **`deposit(assets, receiver)` refines `Solmate.deposit`**, in any frame. -/
theorem deposit_refines {i : SolmateVault.Immutables} (m : Machine) (h : ViewPre i m)
    (hstatic : m.frame.msg.isStatic = false) (hgas : 250000 ≤ m.frame.gasLeft)
    {assets : Word} {receiver : Address}
    (hd : TwoWordCall m.frame.msg.data 0x6e553f65 assets (Word.ofAddress receiver))
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
        m.frame.msg.caller receiver assets (BitVec.ofNat 256 v))
      (Solmate.deposit (absOf i.asset m) m.frame.msg.caller assets.toNat receiver)) := by
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
  refine WP.bind_mono (convertToShares_wp_gas _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    rw [deposit_none_preview (hprev.trans hnone)] at hr
    subst hr
    exact ⟨_, hrev.1⟩
  rintro m' - ⟨v, mem, g, rd, sub, hv, rfl, hmem', hg1, hg1u⟩
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
      exact ⟨_, rfl⟩
  · have hne0 : (0#256 - BitVec.ofNat 256 v) ≠ 0#256 := by
      intro he
      apply hv0
      have := congrArg BitVec.toNat (sub_eq_zero.1 he).symm
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt] at this
      simpa using this
    pwp_run_to 0xf38 [readBytes_code_asset2014, ofAddress_and_addressMask,
      addressMask_and_ofAddress]
    refine WP.bind_mono (safeTransferFrom_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ hstatic rfl rfl
      (by simp) (by pjumpdest_disch) hmem' (by dsimp only; omega) (by dsimp only; omega)
      hbc hbv ha hinv.1) ?_ ?_
    · rintro mf o - ⟨hT, out, ho⟩
      rw [deposit_none_transfer hpv hT] at hr
      subst hr
      exact ⟨_, ho⟩
    rintro m2 - ⟨t', hT, hrepA, mem2, g2, rd2, sub2, rfl, hmem2, hg2⟩
    simp only [Machine.resumeWith, BitVec.reduceToNat] at hg2 ⊢
    pwp_run_to 0xfdc
    have hS : (Erc20.transferFromWorld m_ctx.crypto m_world i.asset m_msg.currentTarget m_msg.caller
        m_msg.currentTarget assets).sload m_msg.currentTarget 2#256 =
        m_world.sload m_msg.currentTarget 2#256 := sload_transferFromWorld_ne hne _
    have hvn : (BitVec.ofNat 256 v).toNat = v := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
    refine WP.bind_mono (mintShares_wp _ rfl hj hstatic rfl rfl (by simp) (by pjumpdest_disch)
      hmem2 (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hov, out, ho⟩
      rw [deposit_none_mint hpv hv0 hT (token_mint_none_iff.2 ?_)] at hr
      · subst hr
        exact ⟨_, ho⟩
      · dsimp only at hov
        rw [hS, hvn] at hov
        exact hov
    rintro m3 - ⟨hov, mem3, g3, rd3, sub3, rfl, hmem3, hg3⟩
    simp only [Machine.resumeWith, BitVec.reduceToNat] at hg3 hov ⊢
    rw [hS, hvn] at hov
    rcases hmem3 with ⟨hfmp3, hsz3⟩ | ⟨hfmp3, hsz3⟩ <;>
    · pwp_run_to 0x1033 [hfmp3, hsz3]
      have h7w : (mintWorld m_ctx.crypto (Erc20.transferFromWorld m_ctx.crypto m_world i.asset
          m_msg.currentTarget m_msg.caller m_msg.currentTarget assets) m_msg.currentTarget receiver
          (BitVec.ofNat 256 v)).sload m_msg.currentTarget 7#256 =
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
        rw [deposit_none_bump hpv hT (bump_none_iff.2 (.inl hov7))] at hr
        subst hr
        exact ⟨_, ho⟩
      rintro m4 - ⟨hov7, g4, sub4, rfl, hg4⟩
      simp only [Machine.resumeWith, BitVec.reduceToNat] at hg4 hov7 ⊢
      rw [h7w] at hov7
      pwp_steps [hfmp3, hsz3]
      obtain ⟨s', hdep', hR⟩ := deposit_post_some (crypto := m_ctx.crypto) (w := m_world)
        (vault := m_msg.currentTarget) (asset := i.asset) (caller := m_msg.caller)
        (receiver := receiver) hne hk hbc hbv hbr ha hinv hpv hv0 hvlt hT hov hov7
      rw [hdep'] at hr
      subst hr
      exact ⟨rfl, rfl, hR⟩

end EvmLeanSpecs.Refinement
