import Verified.Solmate.ERC20.Spec.PermitNormal

/-!
# Solmate's `permit` at the call-depth limit

A frame at depth 1024 cannot start the `STATICCALL` to `0x01` (`step_staticcall_limit`: the
call pushes `0` at once), so `permit` reverts there (`permit_halts_limit`), as `solmateRec`
(`0` at the limit) makes the model say.
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity

variable {m : Machine} {gas toW inOff inSize outOff outSize : Word} {rest : List Word}

/-- **`STATICCALL` at the depth limit** pushes `0` and continues, the forwarded gas refunded. -/
theorem step_staticcall_limit (hcode : m.frame.code[m.frame.pc]? = some 0xfa)
    (hstk : m.frame.stack = gas :: toW :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hdepth : Gas.stackDepthLimit < m.frame.msg.depth + 1) (hlen : rest.length < 1024) :
    step m = .running { m with frame := { callerFrame m rest (callCost m gas 0 (Word.toAddress toW)
        0 0 inOff inSize outOff outSize) (Word.toAddress toW) inOff inSize outOff outSize with
      gasLeft := m.frame.gasLeft - callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
          outSize + (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall
      stack := 0 :: rest
      pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
      outSize := Nat.not_lt.mpr hgas
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0xfa = .staticcall by
    cases m.ctx.fork <;> rfl]
  simp only [exec, execCall, popNat, popAddress, pop, getFrame, modifyFrame, StateT.run_bind,
    hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, memoryExpansion]
  rw [run_accessAddress]
  simp only [pure_bind]
  rw [run_accessDelegation _ _ ?hd]
  case hd => exact hdel
  simp only [callCost, callGas, callExt, Nat.add_zero] at hg
  simp only [pure_bind, charge, getFrame, StateT.run_bind, StateT.run_get, StateT.run_pure,
    ite_true, Nat.add_zero, hg, ite_false, modifyFrame, StateT.run_modify,
    reduceCtorEq, decide_false, Bool.false_and, Bool.false_eq_true, expandMemory, genericCall,
    setReturnData, hdepth, List.foldl, readMemory, refundGas, push, advance]
  have hl : ¬ rest.length ≥ Gas.stackLimit := by simp only [Gas.stackLimit]; omega
  simp only [hl, ite_false, StateT.run_modify, pure_bind]
  rfl

/-- **`RETURNDATACOPY(0, 0, 0)`**: nothing copied, three gas. -/
theorem step_returndatacopy_zero (hcode : m.frame.code[m.frame.pc]? = some 0x3e)
    (hstk : m.frame.stack = 0 :: 0 :: 0 :: rest) (hg : 3 ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - 3, memory := m.frame.memory.expand 0 0,
      pc := m.frame.pc + 1 } } := by
  have hg' : ¬ m.frame.gasLeft < 3 := by omega
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x3e = .returndatacopy by
    cases m.ctx.fork <;> rfl]
  simp [exec, popNat, pop, getFrame, modifyFrame, hstk, memoryExpansion, charge, expandMemory,
    writeMemory, advance, Gas.extendMemory, Gas.copyCost, Gas.veryLow, Gas.words, hg']
  rfl

end Verified.Solmate.ERC20.Spec

namespace Verified.Solmate.ERC20.Spec
open QEDefi.ERC4626 Verified.Solmate.ERC20.Permit

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

set_option maxHeartbeats 0 in
/-- From the `STATICCALL` of `permit` at the depth limit: the call fails at once and `permit`
reverts. -/
theorem permit_tail_limit {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {F : Nat}
    {v r s deadline value : Word} {owner spender : Address}
    (hF : F = 128 ∨ F = 320)
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1631)
    (hs : m.frame.stack = [ofNat m.frame.gasLeft, 1#256, BitVec.ofNat 256 (F + 354), 128#256,
      BitVec.ofNat 256 (F + 322), 32#256, BitVec.ofNat 256 (F + 482), 1#256, 0#256,
      s, r, v, deadline, value, Word.ofAddress spender, Word.ofAddress owner, 424#256,
      3573918927#256])
    (hmem : m.frame.memory = M) (hM64 : M.loadWord 64 = BitVec.ofNat 256 (F + 354))
    (hMs : M.size = F + 512)
    (hg : 40000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : Gas.stackDepthLimit < m.frame.msg.depth + 1) :
    WP m (fun _ => False) (fun _ o => ∃ out, o = .revert out) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs hmem
  have hmod : m_gasLeft % 2 ^ 256 = m_gasLeft := Nat.mod_eq_of_lt (by omega)
  have hacc := accessCost_le (m_sub.accessedAddresses.contains 1)
  have hto : Word.toAddress (1#256) = 1 := by decide
  rcases hF with rfl | rfl <;>
  · simp only [Nat.reduceAdd] at hM64 hMs ⊢
    refine WP.of_step (step_staticcall_limit (by pcode_fact) rfl (by rw [hto]; exact hdel1) ?_
      hdepth (by simp)) (by same_frame) ?_
    · simp only [callCost, callGas, callExt, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod, hto]
      rw [messageCallGas_zero (by evm_gas)]
      simp only [Gas.maxMessageCallGas]
      evm_gas
    simp only [callMemory, callCost, callGas, callExt, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, callerFrame, hto]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    wp_generalize_gas g1 hg1
    have hg1'' : 30000 ≤ g1 := by
      subst hg1
      generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses 1) = acc at hacc ⊢
      evm_gas
    clear hg1
    pwp_steps [hM64, hMs, permit_norm, Memory.read_64]
    refine WP.of_step (step_returndatacopy_zero (by pcode_fact) rfl (by evm_gas)) (by same_frame) ?_
    dsimp only
    pwp_steps
    exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
theorem permit_body_limit {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {F S : Nat}
    {ds deadline value v r s : Word} {owner spender : Address}
    (hFS : (F = 128 ∧ S = 96) ∨ (F = 320 ∧ S = 320))
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1382)
    (hs : m.frame.stack = [ds, 1#256, 0#256, s, r, v, deadline, value, Word.ofAddress spender,
      Word.ofAddress owner, 424#256, 3573918927#256])
    (hmem : m.frame.memory = M) (hM64 : M.loadWord 64 = BitVec.ofNat 256 F) (hMs : M.size = S)
    (hv : v &&& 255#256 = v)
    (hg : 90000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : Gas.stackDepthLimit < m.frame.msg.depth + 1)
    (hstatic : m.frame.msg.isStatic = false) :
    WP m (fun _ => False) (fun _ o => ∃ out, o = .revert out) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs hmem hstd
  rcases hFS with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · pwp_run_to 1420 [hM64, hMs, permit_norm, ofAddress_and_addressMask, addressMask_and_ofAddress,
      Memory.read_64, hstatic]
    generalize hN : m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 5#256)) = nonce
    wp_generalize_gas g1 hg1
    have hg1' : m_gasLeft ≤ g1 + 30000 := by subst hg1; evm_gas
    have hg1'' : 60000 ≤ g1 := by subst hg1; evm_gas
    have hg1u : g1 ≤ m_gasLeft := by subst hg1; omega
    clear hg1
    -- the struct hash
    wp_generalize_mem M1 hM1
    have hM1a := congrArg (Memory.loadWord · 64) hM1
    have hM1b := congrArg Memory.size hM1
    simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
      hM64] at hM1a
    simp only [permit_norm, hMs] at hM1b
    clear hM1
    replace hM1a := hM1a.symm
    replace hM1b := hM1b.symm
    pwp_run_to 1522 [hM1a, hM1b, permit_norm, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_192]
    -- the digest
    wp_generalize_mem M2 hM2
    have hM2a := congrArg (Memory.loadWord · 64) hM2
    have hM2b := congrArg Memory.size hM2
    simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord] at hM2a
    simp only [permit_norm, hM1b] at hM2b
    clear hM2
    replace hM2a := hM2a.symm
    replace hM2b := hM2b.symm
    pwp_run_to 1580 [hM2a, hM2b, permit_norm, Memory.read_66, Memory.read_storeWord_two,
      prefix_eq]
    -- the input of `ecrecover`
    wp_generalize_mem M3 hM3
    have hM3a := congrArg (Memory.loadWord · 64) hM3
    have hM3b := congrArg Memory.size hM3
    simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord] at hM3a
    simp only [permit_norm, hM2b] at hM3b
    clear hM3
    replace hM3a := hM3a.symm
    replace hM3b := hM3b.symm
    pwp_run_to 1631 [hM3a, hM3b, permit_norm, hv]
    refine permit_tail_limit _ (by decide) rfl hj rfl rfl rfl ?_ ?_ ?_ ?_
      (by dsimp only; rw [World.code_sstore]; exact hdel1) hdepth
    · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
        Memory.loadWord_storeWord]
    · simp only [permit_norm, hM3b]
    · dsimp only; omega
    · dsimp only; omega

set_option maxHeartbeats 0 in
theorem permit_halts_limit {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    {owner spender : Address} {value deadline v r s : Word}
    (hd : PermitCall m.frame.msg.data owner spender value deadline v r s)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hcase : DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256))
    (hg : 100000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : Gas.stackDepthLimit < m.frame.msg.depth + 1) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2, harg3, harg4, harg5, harg6⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  subst hstd
  by_cases hv : v.toNat < 256
  swap
  · -- `v` is not a `uint8`: the decoder reverts
    have hne := eq_of_ne (Ne.symm (and_255_ne (x := v) (by omega)))
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hne, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    exact ⟨_, rfl⟩
  have hv' := and_255_of_lt hv
  by_cases hdl : (ofNat m_ctx.block.timestamp).toNat ≤ deadline.toNat
  swap
  · -- the deadline has passed
    have hlt' : Word.lt deadline (ofNat m_ctx.block.timestamp) = 1 :=
      (Word.lt_eq_one_iff _ _).2 (by omega)
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hv', hlt', ofAddress_and_addressMask, addressMask_and_ofAddress,
      Solidity.eq_self, iszero_one]
    exact ⟨_, rfl⟩
  have hge : Word.lt deadline (ofNat m_ctx.block.timestamp) = 0 := (Word.lt_eq_zero_iff _ _).2 hdl
  pwp_run_to 1060 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3,
    harg4, harg5, harg6, hv', hge, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Solidity.eq_self, iszero_zero]
  refine WP.bind_mono (asset_ds_wp _ rfl hj rfl rfl (by simp) (by pjumpdest_disch)
    (Memory.loadWord_storeWord _ _ _) (by simp [Memory.size_storeWord, Memory.size_expand,
      Memory.wordsAfter, Memory.words]) hcase (by dsimp only; omega) (by dsimp only; omega))
    (fun _ _ _ h => h.elim) ?_
  rintro _ - ⟨mem, g, sub, rfl, hmem, hgb, hgu, hlog⟩
  dsimp only [Machine.resumeWith] at hgb hgu hlog ⊢
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, dsOf]
  generalize domainSeparator m_ctx.crypto _ _ _ _ _ = ds
  rcases hmem with ⟨h64, hs⟩ | ⟨h64, hs⟩
  · exact permit_body_limit _ (F := 128) (S := 96) (.inl ⟨rfl, rfl⟩) rfl hj rfl rfl rfl
      h64 hs hv' (by dsimp only; omega) (by dsimp only; omega) rfl hdel1 hdepth hstatic
  · exact permit_body_limit _ (F := 320) (S := 320) (.inr ⟨rfl, rfl⟩) rfl hj rfl rfl rfl
      h64 hs hv' (by dsimp only; omega) (by dsimp only; omega) rfl hdel1 hdepth hstatic

end Verified.Solmate.ERC20.Spec
