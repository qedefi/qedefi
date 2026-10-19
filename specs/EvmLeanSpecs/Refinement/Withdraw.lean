import EvmLeanSpecs.Refinement.WithdrawSpend
import EvmLeanSpecs.Refinement.AssetCallOutGas
import EvmLeanSpecs.Refinement.VaultViews

/-!
# `withdraw(assets, receiver, owner)` of the compiled vault, at the bytecode level

`withdraw_halts`: run in **any** fresh frame of the vault's code (deployed with any immutables
`i`) that `OutPre i` describes — top level or called by another contract, any `Crypto`, any
world with the asset deployed — `withdraw` ends the frame exactly as `Out.withdrawWorld?`
prescribes (`OutPost`): on `some (w', v)` it returns the ABI word `v` (the shares burnt) with
world `w'`; on `none` it reverts.

The proof runs the dispatcher and the ABI decoder symbolically (`pwp_run_to`), then composes
the summaries: `previewWithdraw_wp` (`VaultConvert`), `withdrawSpend_wp`, `bump_wp`, `burn_wp`
(`WithdrawCode`), the `Withdraw` event (symbolically), `safeTransfer_wp` (`AssetCallOut`, the
`CALL` into the asset), and the return encoder.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Refinement.Out

/-- The start of a call frame of the vault deployed with immutables `i` that can run `withdraw`
or `redeem`: fresh frame of the vault's code, no value, non-static (the functions write
storage), the asset deployed at `i.asset` (any immutables, not a precompile, not the vault
itself), room for the asset call, enough gas (`200000 ≤ gas < 2⁶⁴`), calldata shorter than
`2⁶⁴` bytes. -/
structure OutPre (i : SolmateVault.Immutables) (m : Machine) : Prop where
  /-- A fresh frame of the vault's code. -/
  fresh : Fresh (SolmateVault.runtimeCodeWith i) m
  /-- No value is sent (the functions are not payable). -/
  value : m.frame.msg.value = 0
  /-- A non-static frame. -/
  static : m.frame.msg.isStatic = false
  /-- The asset is deployed. -/
  assetCode : ∃ ia, m.world.code i.asset = SolmateAsset.runtimeCodeWith ia
  /-- The asset is not a precompile. -/
  assetNotPrecompile : m.precompiles.isPrecompile i.asset = false
  /-- The asset is not the executing account. -/
  assetNe : i.asset ≠ m.frame.msg.currentTarget
  /-- A call from this frame does not exceed the depth limit. -/
  depth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit
  /-- Enough gas. -/
  gas : 200000 ≤ m.frame.gasLeft
  /-- Gas fits 64 bits (as it does in every transaction). -/
  gasLt : m.frame.gasLeft < 2 ^ 64
  /-- Calldata length fits 64 bits. -/
  sizeLt : m.frame.msg.data.size < 2 ^ 64

/-- How `withdraw` / `redeem` end, given the bytecode-level result `r` (`withdrawWorld?` …):
success with the ABI word and the world, or a revert. -/
def OutPost (r : Option (World × Word)) (mf : Machine) (o : Outcome) : Prop :=
  match r with
  | some (w', v) => o = .success (Bytes.ofWord v) ∧ mf.world = w'
  | none => ∃ out, o = .revert out

/-- The allowance step keeps every account's code. -/
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
      unfold Erc20.spendWorld
      dsimp only
      split <;> simp

/-- The hook step keeps every account's code. -/
theorem code_of_bumpStep {w w' : World} {vault : Address} (h : bumpStep w vault = some w')
    (b : Address) : w'.code b = w.code b := by
  unfold bumpStep at h
  split at h
  · cases h
  · cases h; simp

/-- The burn step keeps every account's code. -/
theorem code_of_burnStep {crypto : Crypto} {w w' : World} {vault src : Address} {v : Word}
    (h : burnStep crypto w vault src v = some w') (b : Address) : w'.code b = w.code b := by
  unfold burnStep at h
  dsimp only at h
  split at h
  · cases h
  · cases h; simp

set_option hygiene false in
/-- The start of a `withdraw` / `redeem` proof: as `view_intro`, for `OutPre` (unpacked into
`hval`, `hstatic`, `hcode`, `hpre`, `hane`, `hdepth`, `hg`, `hg'`, `hsz'`). -/
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
/-- **`withdraw(uint256,address,address)`** of the vault, in any frame: ends as
`withdrawWorld?` prescribes. -/
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
        receiver owner = some (Examples.SolmateAssetTransfer.transferWorld m_ctx.crypto w₃ i.asset
          m_msg.currentTarget receiver assets, BitVec.ofNat 256 v) := by
      simp only [withdrawWorld?, hv, Option.bind_some, hw₁, hw₂, hw₃, payStep,
        Nat.not_lt.2 hbal, ↓reduceIte, Option.map_some]
    rw [hW]
    clear hW hcode₃ hcode hpre
    pwp_steps [hm5a, hm5b]
    exact ⟨rfl, rfl⟩

end EvmLeanSpecs.Refinement
