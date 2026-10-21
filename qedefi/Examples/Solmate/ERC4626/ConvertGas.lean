import Examples.Solmate.ERC4626.Convert

/-!
# Conversions with an upper bound on the gas left

`*_gas`: `balanceOf_halts`, `totalAssets_wp` and the conversions, by the same proofs, with the
extra conclusion that the gas left at the end is at most the gas at the start. Needed because
`deposit`/`mint`/`withdraw`/`redeem` make a second call after a conversion, forwarding the
word `GAS - 2`, whose summary needs the gas left to still be `< 2⁶⁴`.
-/

section

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

set_option maxHeartbeats 0 in
theorem balanceOf_halts_gas {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (a : Address)
    (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = balanceOfSelector)
    (hsize : 36 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress a)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (fun mf o => BalanceOfPost a m mf o ∧ mf.frame.gasLeft ≤ m.frame.gasLeft) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg,
    ofAddress_and_addressMask, Solidity.eq_self, Memory.read_64, balanceOfSelector]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
  · dsimp only [outputMachine]
    evm_gas
  · dsimp only [outputMachine]
    evm_gas

set_option maxHeartbeats 0 in
theorem totalAssets_wp_gas {i : SolmateVault.Immutables} (m : Machine) {r : Word} {rest : List Word}
    (hv : VaultFrame i m)
    (hpc : m.frame.pc = 0x47b) (hs : m.frame.stack = r :: rest)
    (hlen : rest.length ≤ 1010) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hfmp : m.frame.memory.loadWord 64 = 128#256) (hsize : m.frame.memory.size = 96)
    (hg : 20000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ mem g rd sub,
        m' = m.resumeWith r.toNat (assetsOf i.asset m :: rest) mem g rd sub ∧
        FmpAfterCall mem ∧ m.frame.gasLeft ≤ g + 8000 ∧ g ≤ m.frame.gasLeft)
      (fun _ _ => False) := by
  obtain ⟨hc, hj, ⟨ia, hcode⟩, hpre, hdepth⟩ := hv
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  pwp_run_to 0x4d0 [hfmp, hsize, readBytes_code_asset1170, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  have hacc := accessCost_le (m_sub.accessedAddresses.contains i.asset)
  have hmod : (m_gasLeft - 112) % 2 ^ 256 = m_gasLeft - 112 := Nat.mod_eq_of_lt (by omega)
  have hto : Word.toAddress (Word.ofAddress i.asset) = i.asset := Word.toAddress_ofAddress _
  have hdel := delegatedAddress?_assetCode ia
  refine WP.staticcall (by pcode_fact) rfl ?_ ?_ ?_ ?_
    (balanceOf_halts_gas (ia := ia) _ ?_ m_msg.currentTarget rfl ?_ ?_ ?_ ?_ ?_) ?_
  · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
  · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, hmod,
      Nat.reducePow, Nat.reduceMod]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    evm_gas
  · exact hdepth
  · rw [hto]; exact hpre
  · exact ⟨_, _, _, rfl, by dsimp only [childMsg]; rw [hto, hcode]⟩
  · dsimp only [Frame.init, childMsg, callMemory]
    simp only [BitVec.reduceToNat, readBytes_bytes, Abi.selectorOf]
    rw [Memory.readBytes_read _ 128 36 0 4 (by decide)]
    simp only [Memory.read_expand, Nat.add_zero,
      Memory.read_storeWord_of_disjoint _ 132 128 4 _ (by decide),
      Memory.read_storeWord_prefix _ _ 4 _ (by decide)]
    kernel_decide
  · dsimp only [Frame.init, childMsg, callMemory]
    simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
    decide
  · dsimp only [Frame.init, childMsg, callMemory]
    simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
    decide
  · dsimp only [Frame.init, childMsg, callMemory]
    simp only [BitVec.reduceToNat, readBytes_bytes]
    rw [Memory.readBytes_read _ 128 36 4 32 (by decide), Memory.read_expand, Memory.read_expand,
      Memory.read_expand, Memory.read_storeWord, Bytes.toWord_ofWord]
  · dsimp only [Frame.init, childMsg]
    simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, hmod, Nat.reducePow,
      Nat.reduceMod]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    evm_gas
  · intro mf o ⟨⟨ho, hw, ht, hca, hlogs, hgasB⟩, hgasU⟩ hsame
    have hk : mf.frame.kind = .call 128 32 := hsame.kind
    subst ho
    rw [resumeAfter_success hk]
    dsimp only at hw ht hca hgasB hlogs hgasU
    have hs1 : mf.ctx = m_ctx := hsame.ctx
    have hs2 : mf.precompiles = m_pre := hsame.precompiles
    have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
    simp only [hw, ht, hca, hs1, hs2, hs3]
    dsimp only [callerFrame, callMemory, Frame.init, childMsg] at hgasB hgasU ⊢
    simp only [hto, returnMemory_ofWord, callCost, callGas, callExt, ofNat,
      BitVec.toNat_ofNat, hmod, Nat.reducePow, Nat.reduceMod] at hgasB hgasU ⊢
    rw [messageCallGas_zero (by evm_gas)] at hgasB hgasU ⊢
    simp only [Gas.maxMessageCallGas] at hgasB hgasU ⊢
    wp_generalize_gas g1 hg1
    have hg1' : m_gasLeft ≤ g1 + 6000 := by
      subst hg1
      generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses i.asset) = acc
        at hacc hgasB ⊢
      evm_gas
    have hg1'' : g1 ≤ m_gasLeft := by
      subst hg1
      generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses i.asset) = acc
        at hacc hgasU ⊢
      evm_gas
    clear hg1 hgasB hgasU hdel hto hcode hpre
    pwp_steps [hfmp, hsize, Bytes.size_ofWord]
    apply WP.ret
    refine ⟨_, _, _, _, by simp only [Machine.resumeWith, assetsOf]; rfl, ⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [Memory.loadWord_expand, Memory.loadWord_storeWord]
    · rw_mem_sizes
      evm_gas_norm
      rw_mem_sizes
      evm_gas_norm
    · omega
    · omega


set_option maxHeartbeats 0 in
theorem convertToAssets_wp_gas {i : SolmateVault.Immutables} (m : Machine) {x r : Word} {rest : List Word}
    (hv : VaultFrame i m)
    (hpc : m.frame.pc = 0x593) (hs : m.frame.stack = x :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpInit m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ v mem g rd sub,
        convertToAssetsN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = some v ∧
        m' = m.resumeWith r.toNat (BitVec.ofNat 256 v :: rest) mem g rd sub ∧
        FmpOk mem ∧ m.frame.gasLeft ≤ g + 12000 ∧ g ≤ m.frame.gasLeft)
      (fun mf o => convertToAssetsN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = none ∧
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
      by simp only [convertToAssetsN]; rfl,
      by rw [Machine.resumeWith, ofNat_toNat_word], .inl ⟨hfmp, hsize⟩, ?_, ?_⟩
    · evm_gas
    · evm_gas
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
      exact ⟨by simp only [convertToAssetsN, hS', ↓reduceIte]; exact hnone, hrev⟩
    rintro m2 - ⟨v, hv, rfl⟩
    simp only [Machine.resumeAt, BitVec.reduceToNat]
    pwp_steps
    exact WP.ret ⟨v, mem, _, rd, sub, by simp only [convertToAssetsN, hS', ↓reduceIte, hv], rfl,
      .inr ⟨hfmp1, hsize1⟩, by omega, by omega⟩

set_option maxHeartbeats 0 in
theorem previewWithdraw_wp_gas {i : SolmateVault.Immutables} (m : Machine) {x r : Word} {rest : List Word}
    (hv : VaultFrame i m)
    (hpc : m.frame.pc = 0x62b) (hs : m.frame.stack = x :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpInit m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ v mem g rd sub,
        previewWithdrawN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = some v ∧
        m' = m.resumeWith r.toNat (BitVec.ofNat 256 v :: rest) mem g rd sub ∧
        FmpOk mem ∧ m.frame.gasLeft ≤ g + 12000 ∧ g ≤ m.frame.gasLeft)
      (fun mf o => previewWithdrawN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = none ∧
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
      by simp only [previewWithdrawN]; rfl,
      by rw [Machine.resumeWith, ofNat_toNat_word], .inl ⟨hfmp, hsize⟩, ?_, ?_⟩
    · evm_gas
    · evm_gas
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
      exact ⟨by simp only [previewWithdrawN, hS', ↓reduceIte]; exact hnone, hrev⟩
    rintro m2 - ⟨v, hv, rfl⟩
    simp only [Machine.resumeAt, BitVec.reduceToNat]
    pwp_steps
    exact WP.ret ⟨v, mem, _, rd, sub, by simp only [previewWithdrawN, hS', ↓reduceIte, hv], rfl,
      .inr ⟨hfmp1, hsize1⟩, by omega, by omega⟩

end Examples.Solmate.ERC4626

end

section

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

set_option maxHeartbeats 0 in
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

end Examples.Solmate.ERC4626

end
