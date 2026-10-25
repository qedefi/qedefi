import Verified.Solmate.ERC4626.WithdrawInternal
import Verified.Solmate.ERC4626.ConvertGas
import Verified.Solmate.ERC4626.Views

/-!
# `withdraw` and `redeem` of the compiled vault

`withdraw_halts` / `redeem_halts`: in any fresh frame of the vault's code that `OutPre i`
describes, the function ends as `Out.withdrawWorld?` / `Out.redeemWorld?` prescribes.
`withdraw_refines` / `redeem_refines` (any frame) and `*_call` (top level) lift this to the
model's `Solmate.withdraw` / `Solmate.redeem` (`docs/erc4626/details.md` §2).
-/

section

namespace Verified.Solmate.ERC4626
open Verified.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts
open Verified.Solmate.ERC4626.Out

/-- A fresh, non-static, value-free frame of the vault's code that can run `withdraw` / `redeem`:
the asset deployed at `i.asset` (not a precompile, not the vault), room for the asset call,
`200000 ≤ gas < 2⁶⁴`, calldata shorter than `2⁶⁴` bytes. -/
structure OutPre (i : SolmateVault.Immutables) (m : Machine) : Prop where
  fresh : Fresh (SolmateVault.runtimeCodeWith i) m
  value : m.frame.msg.value = 0
  static : m.frame.msg.isStatic = false
  assetCode : ∃ ia, m.world.code i.asset = SolmateAsset.runtimeCodeWith ia
  assetNotPrecompile : m.precompiles.isPrecompile i.asset = false
  assetNe : i.asset ≠ m.frame.msg.currentTarget
  depth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit
  gas : 200000 ≤ m.frame.gasLeft
  gasLt : m.frame.gasLeft < 2 ^ 64
  sizeLt : m.frame.msg.data.size < 2 ^ 64

/-- How `withdraw` / `redeem` end, given the bytecode-level result `r`: success with the ABI
word and the world, or a revert. -/
def OutPost (r : Option (World × Word)) (mf : Machine) (o : Outcome) : Prop :=
  match r with
  | some (w', v) => o = .success (Bytes.ofWord v) ∧ mf.world = w'
  | none => ∃ out, o = .revert out

theorem code_of_spendStep {crypto : Crypto} {w w' : World} {vault owner caller : Address}
    {v : Word} (h : spendStep crypto w vault owner caller v = some w') (b : Address) :
    w'.code b = w.code b := by
  unfold spendStep at h
  split at h
  · cases h; rfl
  · dsimp only at h
    split at h
    · cases h
    · cases h
      unfold ERC20.spendWorld
      dsimp only
      split <;> simp

theorem code_of_bumpStep {w w' : World} {vault : Address} (h : bumpStep w vault = some w')
    (b : Address) : w'.code b = w.code b := by
  unfold bumpStep at h
  split at h
  · cases h
  · cases h; simp

theorem code_of_burnStep {crypto : Crypto} {w w' : World} {vault src : Address} {v : Word}
    (h : burnStep crypto w vault src v = some w') (b : Address) : w'.code b = w.code b := by
  unfold burnStep at h
  dsimp only at h
  split at h
  · cases h
  · cases h; simp

set_option hygiene false in
/-- Start of a `withdraw` / `redeem` proof: unpacks `OutPre` into `hval`, `hstatic`, `hcode`,
`hpre`, `hane`, `hdepth`, `hg`, `hg'`, `hsz'`. -/
macro "out_intro" : tactic => `(tactic| (
  apply WP.halts_of_false
  obtain ⟨hf, hval, hstatic, hcode, hpre, hane, hdepth, hg, hg', hsz'⟩ := h
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  clear hf
  have hagree := Shares.jumpDestsAgree i
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsz4 (by omega)
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  wp_hide_jump_tables
  subst hs hpc hc hmem))

set_option maxHeartbeats 0 in
/-- **`withdraw(uint256,address,address)`** in any frame: ends as `withdrawWorld?` prescribes. -/
theorem withdraw_halts {i : SolmateVault.Immutables} (m : Machine) (h : OutPre i m)
    {assets : Word} {receiver owner : Address}
    (hd : ThreeWordCall m.frame.msg.data 0xb460af94 assets (Word.ofAddress receiver)
      (Word.ofAddress owner)) :
    Halts m (OutPost (withdrawWorld? m.ctx.crypto m.world m.frame.msg.currentTarget i.asset
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
  refine WP.bind_mono (previewWithdraw_wp_gas _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) initMemory_fmpInit (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    dsimp only [supplyOf, assetsOf] at hnone
    simp only [OutPost, withdrawWorld?, hnone, Option.bind_none]
    exact ⟨_, hrev.1⟩
  rintro m1 - ⟨v, mem1, g1, rd1, sub1, hv, rfl, hmem1, hg1, hg1u⟩
  dsimp only [supplyOf, assetsOf] at hv
  simp only [Machine.resumeWith, BitVec.reduceToNat] at hg1 hg1u ⊢
  -- the allowance step
  refine WP.bind_mono (withdrawSpend_wp _ rfl hj rfl rfl (by simp) hstatic hmem1
    (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    simp only [OutPost, withdrawWorld?, hv, Option.bind_some, hnone, Option.bind_none]
    exact hrev
  rintro m2 - ⟨w₁, hw₁, mem2, g2, sub2, rfl, hm2a, hm2b, hg2, hg2u⟩
  simp only [resumeWorld, Machine.resumeWith] at hg2 hg2u ⊢
  have hmem2 : FmpOk mem2 := by
    rcases hmem1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact .inl ⟨hm2a.trans a, hm2b.trans b⟩
    · exact .inr ⟨hm2a.trans a, hm2b.trans b⟩
  clear hm2a hm2b
  -- `beforeWithdraw`
  pwp_run_to 0x104b
  refine WP.bind_mono (bump_wp _ rfl hj rfl rfl (by simp) (by pjumpdest_disch) hstatic hmem2
    (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    simp only [OutPost, withdrawWorld?, hv, Option.bind_some, hw₁, hnone, Option.bind_none]
    exact hrev
  rintro m3 - ⟨w₂, hw₂, g3, sub3, rfl, hg3, hg3u⟩
  simp only [resumeWorld, Machine.resumeWith, BitVec.reduceToNat] at hg3 hg3u ⊢
  -- `_burn(owner, shares)`
  pwp_run_to 0x105a
  refine WP.bind_mono (burn_wp _ rfl hj rfl rfl (by simp) (by pjumpdest_disch) hstatic hmem2
    (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    simp only [OutPost, withdrawWorld?, hv, Option.bind_some, hw₁, hw₂, hnone, Option.bind_none]
    exact hrev
  rintro m4 - ⟨w₃, hw₃, mem4, g4, rd4, sub4, rfl, hmem4, hg4, hg4u⟩
  simp only [resumeWorld, Machine.resumeWith, BitVec.reduceToNat] at hg4 hg4u ⊢
  have hcode₃ : ∃ ia, w₃.code i.asset = SolmateAsset.runtimeCodeWith ia := by
    obtain ⟨ia, h⟩ := hcode
    exact ⟨ia, by rw [code_of_burnStep hw₃, code_of_bumpStep hw₂, code_of_spendStep hw₁, h]⟩
  -- the `Withdraw` event, then `safeTransfer(asset, receiver, assets)`
  rcases hmem4 with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
  all_goals
    pwp_run_to 0x10b9 [hfmp, hsize, readBytes_code_asset2668, ofAddress_and_addressMask,
      addressMask_and_ofAddress]
    refine WP.bind_mono (safeTransfer_wp _ ⟨rfl, hj, hcode₃, hpre, hdepth⟩ rfl rfl (by simp)
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
      simp only [OutPost, withdrawWorld?, hv, Option.bind_some, hw₁, hw₂, hw₃, payStep, hlt,
        ↓reduceIte, Option.map_none]
      exact hrev
    rintro m5 - ⟨hbal, mem5, g5, rd5, sub5, rfl, hm5a, hm5b, hg5⟩
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
    exact ⟨rfl, rfl⟩

end Verified.Solmate.ERC4626

end

section

/-! ## `redeem`: as `withdraw`, with the allowance step first and a `ZERO_ASSETS` check -/

namespace Verified.Solmate.ERC4626
open Verified.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts
open Verified.Solmate.ERC4626.Out

set_option maxHeartbeats 0 in
/-- **`redeem(uint256,address,address)`** in any frame: ends as `redeemWorld?` prescribes. -/
theorem redeem_halts {i : SolmateVault.Immutables} (m : Machine) (h : OutPre i m)
    {shares : Word} {receiver owner : Address}
    (hd : ThreeWordCall m.frame.msg.data 0xba087652 shares (Word.ofAddress receiver)
      (Word.ofAddress owner)) :
    Halts m (OutPost (redeemWorld? m.ctx.crypto m.world m.frame.msg.currentTarget i.asset
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
  refine WP.bind_mono (redeemSpend_wp _ rfl hj rfl rfl (by simp) hstatic
    (.inl initMemory_fmpInit) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    simp only [OutPost, redeemWorld?, hnone, Option.bind_none]
    exact hrev
  rintro m2 - ⟨w₁, hw₁, mem2, g2, sub2, rfl, hm2a, hm2b, hg2, hg2u⟩
  simp only [resumeWorld, Machine.resumeWith] at hg2 hg2u ⊢
  have hmem2 : FmpInit mem2 := ⟨hm2a.trans initMemory_fmpInit.1, hm2b.trans initMemory_fmpInit.2⟩
  clear hm2a hm2b
  have hcode₁ : ∃ ia, w₁.code i.asset = SolmateAsset.runtimeCodeWith ia := by
    obtain ⟨ia, h⟩ := hcode
    exact ⟨ia, by rw [code_of_spendStep hw₁, h]⟩
  -- `previewRedeem(shares)` = `convertToAssets(shares)`
  pwp_run_to 0x593
  refine WP.bind_mono (convertToAssets_wp_gas _ ⟨rfl, hj, hcode₁, hpre, hdepth⟩ rfl rfl (by simp)
    (by pjumpdest_disch) hmem2 (by dsimp only; omega) (by dsimp only; omega)) ?_ ?_
  · rintro mf o - ⟨hnone, hrev⟩
    dsimp only [supplyOf, assetsOf] at hnone
    simp only [OutPost, redeemWorld?, hw₁, Option.bind_some, hnone, Option.bind_none]
    exact ⟨_, hrev.1⟩
  rintro m3 - ⟨v, mem3, g3, rd3, sub3, hv, rfl, hmem3, hg3, hg3u⟩
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
    refine WP.bind_mono (bump_wp _ rfl hj rfl rfl (by simp) (by pjumpdest_disch) hstatic hmem3
      (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hnone, hrev⟩
      simp only [OutPost, redeemWorld?, hw₁, Option.bind_some, hv, hv0, ↓reduceIte, hnone,
        Option.bind_none]
      exact hrev
    rintro m4 - ⟨w₂, hw₂, g4, sub4, rfl, hg4, hg4u⟩
    simp only [resumeWorld, Machine.resumeWith, BitVec.reduceToNat] at hg4 hg4u ⊢
    -- `_burn(owner, shares)`
    pwp_run_to 0x105a
    refine WP.bind_mono (burn_wp _ rfl hj rfl rfl (by simp) (by pjumpdest_disch) hstatic hmem3
      (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hnone, hrev⟩
      simp only [OutPost, redeemWorld?, hw₁, Option.bind_some, hv, hv0, ↓reduceIte, hw₂, hnone,
        Option.bind_none]
      exact hrev
    rintro m5 - ⟨w₃, hw₃, mem5, g5, rd5, sub5, rfl, hmem5, hg5, hg5u⟩
    simp only [resumeWorld, Machine.resumeWith, BitVec.reduceToNat] at hg5 hg5u ⊢
    have hcode₃ : ∃ ia, w₃.code i.asset = SolmateAsset.runtimeCodeWith ia := by
      obtain ⟨ia, h⟩ := hcode₁
      exact ⟨ia, by rw [code_of_burnStep hw₃, code_of_bumpStep hw₂, h]⟩
    -- the `Withdraw` event, then `safeTransfer(asset, receiver, assets)`
    rcases hmem5 with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_run_to 0x10b9 [hfmp, hsize, readBytes_code_asset2995, ofAddress_and_addressMask,
        addressMask_and_ofAddress]
      refine WP.bind_mono (safeTransfer_wp _ ⟨rfl, hj, hcode₃, hpre, hdepth⟩ rfl rfl (by simp)
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
        simp only [OutPost, redeemWorld?, hw₁, Option.bind_some, hv, hv0, ↓reduceIte, hw₂, hw₃,
          payStep, hlt, Option.map_none]
        exact hrev
      rintro m6 - ⟨hbal, mem6, g6, rd6, sub6, rfl, hm6a, hm6b, hg6⟩
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
      exact ⟨rfl, rfl⟩

end Verified.Solmate.ERC4626

end

section

/-! ## `withdraw` and `redeem` refine the model -/

namespace Verified.Solmate.ERC4626
open Verified.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts
open Verified.Solmate.ERC4626.Out
open QEDefi.Math QEDefi.ERC20

/-- How `withdraw` / `redeem` end against the model's result `r`: success with the ABI word and
a world refining the model's state, or a revert. -/
def OutRefPost (crypto : Crypto) (w₀ : World) (vault asset caller receiver owner : Address)
    (r : Option (Solmate.State Address × ℕ)) (mf : Machine) (o : Outcome) : Prop :=
  match r with
  | some (s', v) => o = .success (Bytes.ofWord (BitVec.ofNat 256 v)) ∧
      RefinesOn (OutAllowances crypto caller owner) (TransferAllowances crypto vault receiver)
        crypto mf.world vault asset s' ∧ ∀ b, mf.world.code b = w₀.code b
  | none => ∃ out, o = .revert out

theorem code_of_payStep {crypto : Crypto} {w w' : World} {asset vault dst : Address} {v : Word}
    (h : payStep crypto w asset vault dst v = some w') (b : Address) : w'.code b = w.code b := by
  unfold payStep at h
  split at h
  · cases h
  · cases h; simp [EvmLogic.Solidity.ERC20.transferWorld]

theorem code_of_withdrawWorld? {crypto : Crypto} {w w' : World}
    {vault asset caller receiver owner : Address} {assets v : Word}
    (h : withdrawWorld? crypto w vault asset caller assets receiver owner = some (w', v))
    (b : Address) : w'.code b = w.code b := by
  simp only [withdrawWorld?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, -, w₁, h₁, w₂, h₂, w₃, h₃, w₄, h₄, he⟩ := h
  cases he
  rw [code_of_payStep h₄, code_of_burnStep h₃, code_of_bumpStep h₂, code_of_spendStep h₁]

theorem code_of_redeemWorld? {crypto : Crypto} {w w' : World}
    {vault asset caller receiver owner : Address} {shares v : Word}
    (h : redeemWorld? crypto w vault asset caller shares receiver owner = some (w', v))
    (b : Address) : w'.code b = w.code b := by
  simp only [redeemWorld?, Option.bind_eq_some_iff] at h
  obtain ⟨w₁, h₁, x, -, h⟩ := h
  split at h
  · cases h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨w₂, h₂, w₃, h₃, w₄, h₄, he⟩ := h
    cases he
    rw [code_of_payStep h₄, code_of_burnStep h₃, code_of_bumpStep h₂, code_of_spendStep h₁]

theorem outRefPost_of {crypto : Crypto} {vault asset caller receiver owner : Address}
    {r : Option (Solmate.State Address × ℕ)} {rw : Option (World × Word)}
    (hW : match r with
      | some (s', v) => ∃ w', rw = some (w', BitVec.ofNat 256 v) ∧
          RefinesOn (OutAllowances crypto caller owner) (TransferAllowances crypto vault receiver)
            crypto w' vault asset s'
      | none => rw = none)
    {w₀ : World} (hc : ∀ w' v, rw = some (w', v) → ∀ b, w'.code b = w₀.code b)
    {mf : Machine} {o : Outcome} (h : OutPost rw mf o) :
    OutRefPost crypto w₀ vault asset caller receiver owner r mf o := by
  unfold OutRefPost
  split at hW
  · obtain ⟨w', rfl, hR⟩ := hW
    obtain ⟨ho, hw⟩ := h
    exact ⟨ho, hw ▸ hR, hw ▸ hc _ _ rfl⟩
  · subst hW
    exact h

/-- **`withdraw(assets, receiver, owner)` refines `Solmate.withdraw`**, in any frame: under
`OutPre`, the Keccak hypotheses `OutSlots` and `Solmate.Inv`, `some (s', v)` returns `v` with a
world refining `s'`; `none` reverts. -/
theorem withdraw_refines {i : SolmateVault.Immutables} (m : Machine) (h : OutPre i m)
    {assets : Word} {receiver owner : Address}
    (hd : ThreeWordCall m.frame.msg.data 0xb460af94 assets (Word.ofAddress receiver)
      (Word.ofAddress owner))
    (hk : OutSlots m.ctx.crypto m.frame.msg.currentTarget m.frame.msg.caller owner receiver)
    (hinv : Solmate.Inv (absOf i.asset m)) :
    Halts m (OutRefPost m.ctx.crypto m.world m.frame.msg.currentTarget i.asset m.frame.msg.caller
      receiver owner (Solmate.withdraw (absOf i.asset m) m.frame.msg.caller assets.toNat
        receiver owner)) :=
  (withdraw_halts m h hd).mono fun _ _ _ hp =>
    outRefPost_of (withdrawWorld?_refines (refines_iff.2 rfl) hinv h.assetNe hk assets)
      (fun _ _ he => code_of_withdrawWorld? he) hp

/-- **`redeem(shares, receiver, owner)` refines `Solmate.redeem`**, in any frame (hypotheses as
`withdraw_refines`). -/
theorem redeem_refines {i : SolmateVault.Immutables} (m : Machine) (h : OutPre i m)
    {shares : Word} {receiver owner : Address}
    (hd : ThreeWordCall m.frame.msg.data 0xba087652 shares (Word.ofAddress receiver)
      (Word.ofAddress owner))
    (hk : OutSlots m.ctx.crypto m.frame.msg.currentTarget m.frame.msg.caller owner receiver)
    (hinv : Solmate.Inv (absOf i.asset m)) :
    Halts m (OutRefPost m.ctx.crypto m.world m.frame.msg.currentTarget i.asset m.frame.msg.caller
      receiver owner (Solmate.redeem (absOf i.asset m) m.frame.msg.caller shares.toNat
        receiver owner)) :=
  (redeem_halts m h hd).mono fun _ _ _ hp =>
    outRefPost_of (redeemWorld?_refines (refines_iff.2 rfl) hinv h.assetNe hk shares)
      (fun _ _ he => code_of_redeemWorld? he) hp

/-! ## Top-level transactions -/

/-- What a top-level `withdraw` / `redeem` returns, against the model's result `r`. -/
def OutResult (crypto : Crypto) (w : World) (vault asset caller receiver owner : Address)
    (res : MessageResult) (r : Option (Solmate.State Address × ℕ)) : Prop :=
  match r with
  | some (s', v) => res.success = true ∧ res.output = Bytes.ofWord (BitVec.ofNat 256 v) ∧
      RefinesOn (OutAllowances crypto caller owner) (TransferAllowances crypto vault receiver)
        crypto res.world vault asset s' ∧ ∀ b, res.world.code b = w.code b
  | none => res.success = false ∧ res.reverted = true ∧ res.world = w

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {data : ByteArray} {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

theorem outPre_start {i : SolmateVault.Immutables} (hdep : Deployed w vault i.asset)
    (hgas : 200000 ≤ gas) (hgas' : gas < 2 ^ 64) (hsize : data.size < 2 ^ 64) :
    OutPre i (startMachine ctx w tr
      (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk)) where
  fresh := fresh_startMachine ctx w tr
    (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk)
  value := rfl
  static := rfl
  assetCode := hdep.assetCode
  assetNotPrecompile := hdep.assetNotPrecompile ctx.fork
  assetNe := hdep.asset_ne
  depth := by simp [startMachine, callMsg, Frame.init, Gas.stackDepthLimit]
  gas := hgas
  gasLt := hgas'
  sizeLt := hsize

theorem threeWordCall_encodeCall' {sel : Nat} (hsel : sel < 2 ^ 32) (x y z : Word) :
    ThreeWordCall (Abi.encodeCall sel [x, y, z]) sel x y z :=
  ⟨by rw [Abi.selectorOf_encodeCall, Nat.mod_eq_of_lt hsel],
   by rw [Abi.size_encodeCall]; simp, Abi.calldataload_encodeCall_0 _ _ _,
   Abi.calldataload_encodeCall_1 _ _ _ _, Abi.calldataload_encodeCall_2 _ _ _ _ _⟩

set_option maxHeartbeats 1000000 in
theorem out_call {i : SolmateVault.Immutables} {receiver owner : Address}
    {r : Option (Solmate.State Address × ℕ)}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false)
    (h : Halts (startMachine ctx w tr
        (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk))
      (OutRefPost ctx.crypto w vault i.asset caller receiver owner r)) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk) = .ok res ∧
      OutResult ctx.crypto w vault i.asset caller receiver owner res r := by
  have hdel : delegatedAddress?
      (callMsg (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk).code = none :=
    Shares.delegatedAddress?_code i
  obtain ⟨n, hn⟩ := processMessageCall_of_halts (a := vault) hdeleg hdel rfl rfl hpre rfl rfl h
  refine ⟨n, fun fuel hle => ?_⟩
  obtain ⟨mf, o, hH, hs, hrun⟩ := hn fuel hle
  have hk : mf.frame.kind = .call 0 0 := hs.kind
  refine ⟨_, hrun, ?_⟩
  unfold OutRefPost at hH
  unfold OutResult
  split at hH
  · obtain ⟨ho, hR, hC⟩ := hH
    subst ho
    obtain ⟨h1, h2, h3, -⟩ := topLevelResult_success_call (t := (callMsg
      (SolmateVault.runtimeCodeWith i) vault caller data gas wa wk).target)
      (out := Bytes.ofWord _) hk
    exact ⟨h1, h2, h3 ▸ hR, h3 ▸ hC⟩
  · obtain ⟨out, ho⟩ := hH
    subst ho
    have hsnap : mf.frame.snapshot.1 = w := by rw [hs.snapshot]; rfl
    simp only [frameResult_revert, topLevelResult_world, topLevelResult_success,
      topLevelResult_reverted, ChildResult.success, hsnap]
    decide

/-- **`withdraw(assets, receiver, owner)` as a top-level transaction** on the deployed vault:
refines `Solmate.withdraw` of the model state read from the world. -/
theorem withdraw_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 200000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver owner : Address}
    (hk : OutSlots ctx.crypto vault caller owner receiver)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (assets : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0xb460af94 [assets, Word.ofAddress receiver, Word.ofAddress owner])
          gas wa wk) = .ok res ∧
      OutResult ctx.crypto w vault asset caller receiver owner res
        (Solmate.withdraw (abs ctx.crypto w vault asset) caller assets.toNat receiver owner) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := withdraw_refines _ (outPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas'
    (by rw [Abi.size_encodeCall]; simp))
    (threeWordCall_encodeCall' (by decide) assets _ _) hk hinv
  exact out_call hdeleg (hdep.vaultNotPrecompile _) hm

/-- **`redeem(shares, receiver, owner)` as a top-level transaction** on the deployed vault:
refines `Solmate.redeem` of the model state read from the world. -/
theorem redeem_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 200000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver owner : Address}
    (hk : OutSlots ctx.crypto vault caller owner receiver)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (shares : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0xba087652 [shares, Word.ofAddress receiver, Word.ofAddress owner])
          gas wa wk) = .ok res ∧
      OutResult ctx.crypto w vault asset caller receiver owner res
        (Solmate.redeem (abs ctx.crypto w vault asset) caller shares.toNat receiver owner) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := redeem_refines _ (outPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas'
    (by rw [Abi.size_encodeCall]; simp))
    (threeWordCall_encodeCall' (by decide) shares _ _) hk hinv
  exact out_call hdeleg (hdep.vaultNotPrecompile _) hm

end Verified.Solmate.ERC4626

end
