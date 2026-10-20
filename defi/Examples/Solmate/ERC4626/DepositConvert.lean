import Examples.Solmate.ERC4626.ConvertGas

/-!
# Conversions with an upper bound on the gas left

`deposit` and `mint` make a second external call (the asset's `transferFrom`, with
`call(gas(), …)`) after the conversion (`convertToShares` / `previewMint`), which may itself
call the asset (`balanceOf`). The amount of gas forwarded by `gas()` is the word
`gasLeft − 2`, so the second call's summary needs `gasLeft < 2²⁵⁶` (here `< 2⁶⁴`) *after*
the conversion: the gas left must not have grown. The summaries `balanceOf_halts`,
`totalAssets_wp`, `convertToShares_wp`, `previewMint_wp` only bound the gas used from above;
the `_gas` versions (`balanceOf_halts_gas`, `totalAssets_wp_gas` of `AssetCallOutGas`, and
`convertToShares_wp_gas`, `previewMint_wp_gas` here) are the same proofs with the extra
conclusion that the gas left at the end is at most the gas at the start (the callee returns at
most what it was forwarded).
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

set_option maxHeartbeats 0 in
/-- `convertToShares_wp`, with the gas left at the end bounded by the gas at the start. -/
theorem convertToShares_wp_gas {i : SolmateVault.Immutables} (m : Machine) {x r : Word} {rest : List Word}
    (hv : VaultFrame i m)
    (hpc : m.frame.pc = 0xbda) (hs : m.frame.stack = x :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpInit m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ v mem g rd sub,
        convertToSharesN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = some v ∧
        m' = m.resumeWith r.toNat (BitVec.ofNat 256 v :: rest) mem g rd sub ∧
        FmpOk mem ∧ m.frame.gasLeft ≤ g + 12000 ∧ g ≤ m.frame.gasLeft)
      (fun mf o => convertToSharesN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = none ∧
        MulDivRevert m mf o) := by
  obtain ⟨hc, hj, hcode, hpre, hdepth⟩ := hv
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨hfmp, hsize⟩ := hmem
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [supplyOf, assetsOf]
  pwp_steps
  by_cases hS : m_world.sload m_msg.currentTarget 2#256 = 0#256
  · simp only [hS, iszero_zero]
    pwp_steps
    refine WP.ret ⟨x.toNat, m_memory, _, m_returnData, _,
      by simp only [convertToSharesN]; rfl,
      by rw [Machine.resumeWith, ofNat_toNat_word], .inl ⟨hfmp, hsize⟩, ?_, ?_⟩
    · evm_gas
    · omega
  · have hS' : (m_world.sload m_msg.currentTarget 2#256).toNat ≠ 0 :=
      fun h => hS (BitVec.eq_of_toNat_eq (by simpa using h))
    simp only [iszero_of_ne hS]
    pwp_run_to 0x47b
    wp_generalize_gas g0 hg0
    have hg0' : m_gasLeft ≤ g0 + 2300 := by subst hg0; evm_gas
    have hg0'' : g0 ≤ m_gasLeft := by subst hg0; omega
    clear hg0
    refine WP.bind_mono (totalAssets_wp_gas _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl
      (by simp only [List.length_cons]; omega) (by pjumpdest_disch) hfmp hsize (by dsimp only; omega)
      (by dsimp only; omega)) (fun _ _ _ h => h.elim) ?_
    rintro m1 - ⟨mem, g, rd, sub, rfl, ⟨hfmp1, hsize1⟩, hg1, hg1u⟩
    simp only [Machine.resumeWith, assetsOf, BitVec.reduceToNat] at hg1 hg1u ⊢
    pwp_run_to 0xe62
    refine WP.bind_mono (mulDivDown_wp _ rfl hj rfl rfl (by simp only [List.length_cons]; omega)
      (by pjumpdest_disch) (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hnone, hrev⟩
      exact ⟨by simp only [convertToSharesN, hS', ↓reduceIte]; exact hnone, hrev⟩
    rintro m2 - ⟨v, hv, rfl⟩
    simp only [Machine.resumeAt, BitVec.reduceToNat]
    pwp_steps
    exact WP.ret ⟨v, mem, _, rd, sub, by simp only [convertToSharesN, hS', ↓reduceIte, hv], rfl,
      .inr ⟨hfmp1, hsize1⟩, by omega, by omega⟩

set_option maxHeartbeats 0 in
/-- `previewMint_wp`, with the gas left at the end bounded by the gas at the start. -/
theorem previewMint_wp_gas {i : SolmateVault.Immutables} (m : Machine) {x r : Word} {rest : List Word}
    (hv : VaultFrame i m)
    (hpc : m.frame.pc = 0x96b) (hs : m.frame.stack = x :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpInit m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ v mem g rd sub,
        previewMintN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = some v ∧
        m' = m.resumeWith r.toNat (BitVec.ofNat 256 v :: rest) mem g rd sub ∧
        FmpOk mem ∧ m.frame.gasLeft ≤ g + 12000 ∧ g ≤ m.frame.gasLeft)
      (fun mf o => previewMintN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = none ∧
        MulDivRevert m mf o) := by
  obtain ⟨hc, hj, hcode, hpre, hdepth⟩ := hv
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨hfmp, hsize⟩ := hmem
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [supplyOf, assetsOf]
  pwp_steps
  by_cases hS : m_world.sload m_msg.currentTarget 2#256 = 0#256
  · simp only [hS, iszero_zero]
    pwp_steps
    refine WP.ret ⟨x.toNat, m_memory, _, m_returnData, _,
      by simp only [previewMintN]; rfl,
      by rw [Machine.resumeWith, ofNat_toNat_word], .inl ⟨hfmp, hsize⟩, ?_, ?_⟩
    · evm_gas
    · omega
  · have hS' : (m_world.sload m_msg.currentTarget 2#256).toNat ≠ 0 :=
      fun h => hS (BitVec.eq_of_toNat_eq (by simpa using h))
    simp only [iszero_of_ne hS]
    pwp_run_to 0x47b
    wp_generalize_gas g0 hg0
    have hg0' : m_gasLeft ≤ g0 + 2300 := by subst hg0; evm_gas
    have hg0'' : g0 ≤ m_gasLeft := by subst hg0; omega
    clear hg0
    refine WP.bind_mono (totalAssets_wp_gas _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl
      (by simp only [List.length_cons]; omega) (by pjumpdest_disch) hfmp hsize (by dsimp only; omega)
      (by dsimp only; omega)) (fun _ _ _ h => h.elim) ?_
    rintro m1 - ⟨mem, g, rd, sub, rfl, ⟨hfmp1, hsize1⟩, hg1, hg1u⟩
    simp only [Machine.resumeWith, assetsOf, BitVec.reduceToNat] at hg1 hg1u ⊢
    pwp_run_to 0xe7d
    refine WP.bind_mono (mulDivUp_wp _ rfl hj rfl rfl (by simp only [List.length_cons]; omega)
      (by pjumpdest_disch) (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hnone, hrev⟩
      exact ⟨by simp only [previewMintN, hS', ↓reduceIte]; exact hnone, hrev⟩
    rintro m2 - ⟨v, hv, rfl⟩
    simp only [Machine.resumeAt, BitVec.reduceToNat]
    pwp_steps
    exact WP.ret ⟨v, mem, _, rd, sub, by simp only [previewMintN, hS', ↓reduceIte, hv], rfl,
      .inr ⟨hfmp1, hsize1⟩, by omega, by omega⟩

end EvmLeanSpecs.Refinement
