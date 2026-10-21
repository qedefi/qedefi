import Examples.AaveV3.AToken.Burn.Basic

/-!
# `AToken.burn` by the Pool: success

`burn_halts_ok`: in any fresh non-static frame, the Pool's `burn(u, r, amount, amt, idx)` with
`r` other than the token succeeds, returns whether `u`'s scaled balance becomes zero, and
leaves the executing account's storage as `burnWorld`, provided the checks of `_burnScaled` /
`_burn` pass and both external calls behave as assumed (`HandleActionOkCode`, `TransferOk`).
Both event branches (`Mint` when the accrued interest exceeds the burnt amount, `Burn`
otherwise) are covered; they share the tail through `safeTransfer`, which is replayed in each.
-/

namespace Examples.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Examples.AaveV3.Contracts
open Examples.Solmate.ERC20 (lt_size_four)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- **`burn` by the Pool, success.** Hypotheses: well-formed calldata for
`burn(u, r, amount, amt, idx)` with `r` not the executing account, the Pool as caller, no
value, a non-static frame, gas in `[5·10^6, 2^64)` (two calls each forward all but 1/64);
`u`'s slot is neither 54 nor 61; the checks pass: `amt ≠ 0`, `amt ≤ scaledBalance u`,
`amt ≤ scaledTotalSupply`, `idx < 2^128`, `scaledBalance u · idx < 2^256`, the accrued interest is
not negative; the rewards controller is deployed (code of size in `(0, 2^256)`, not a
precompile, not delegated) and behaves (`HandleActionOkCode`); the underlying (slot 61) is
not a precompile, not delegated, and its `transfer` behaves (`TransferOk`); depth < 1024. -/
theorem burn_halts_ok (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xb18d6afd)
    (hsize : 164 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    {u r : Address} {amount amt idx : Word}
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress u)
    (harg1 : Bytes.toWord (readBytes m.frame.msg.data 36 32) = Word.ofAddress r)
    (harg2 : Bytes.toWord (readBytes m.frame.msg.data 68 32) = amount)
    (harg3 : Bytes.toWord (readBytes m.frame.msg.data 100 32) = amt)
    (harg4 : Bytes.toWord (readBytes m.frame.msg.data 132 32) = idx)
    (hc : m.frame.msg.caller = pool)
    (hg : 5000000 ≤ m.frame.gasLeft) (hgu : m.frame.gasLeft < 2 ^ 64)
    (hrcOk : HandleActionOkCode (m.world.code rewardsController) m.frame.msg.currentTarget)
    (hcs : (m.world.code rewardsController).size ≠ 0)
    (hcs2 : (m.world.code rewardsController).size < 2 ^ 256)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code rewardsController) = none)
    (hpre : m.precompiles.isPrecompile rewardsController = false)
    (hdepth : m.frame.msg.depth < 1024)
    (hr : r ≠ m.frame.msg.currentTarget)
    (hslot61 : userStateSlot m.ctx.crypto u ≠ 61#256)
    (hTok : TransferOk (underlyingAddress m.world m.frame.msg.currentTarget)
      m.frame.msg.currentTarget)
    (hdelU : m.ctx.fork < .prague ∨ delegatedAddress?
      (m.world.code (underlyingAddress m.world m.frame.msg.currentTarget)) = none)
    (hpreU : m.precompiles.isPrecompile (underlyingAddress m.world m.frame.msg.currentTarget) =
      false)
    (hamt : amt ≠ 0) (hslot : userStateSlot m.ctx.crypto u ≠ 54#256)
    (hle : amt.toNat ≤ (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat)
    (hsupLe : amt.toNat ≤ (scaledTotalSupply m.world m.frame.msg.currentTarget).toNat)
    (hidx : idx.toNat < 2 ^ 128)
    (hmul : (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat * idx.toNat <
      2 ^ 256)
    (hinc : (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat *
        (previousIndex m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat /
          1000000000000000000000000000 ≤
      (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat * idx.toNat /
        1000000000000000000000000000) :
    Halts m (BurnOk u amt idx m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
      (BitVec.ofNat 256 160)) = 1 := iszero_slt_calldatasize (by omega) (by omega)
  have hc' : Word.eq 773725381719276160229242488166406195640368342242#256
      (Word.ofAddress m.frame.msg.caller) = 1#256 := by rw [hc]; exact poolWord_eq_pool
  have hneg : 0#256 - amt ≠ 0#256 := by
    intro h; apply hamt; have := congrArg (· + amt) h; simpa using this.symm
  obtain ⟨W, hW⟩ : ∃ W, m.world.sload m.frame.msg.currentTarget
      (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress u) ++ Bytes.ofWord 52#256)) = W :=
    ⟨_, rfl⟩
  obtain ⟨bal, hbal⟩ : ∃ b, 1329227995784915872903807060280344575#256 &&& W = b := ⟨_, rfl⟩
  obtain ⟨prev, hprev⟩ : ∃ p, 340282366920938463463374607431768211455#256 &&&
      W.div 340282366920938463463374607431768211456#256 = p := ⟨_, rfl⟩
  have hbal120 : bal.toNat < 2 ^ 120 := by
    rw [← hbal, mask120_and, BitVec.toNat_ofNat]; omega
  have hprev128 : prev.toNat < 2 ^ 128 := by
    rw [← hprev, mask128_and_div, BitVec.toNat_ofNat]
    have := W.isLt
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hbal2 : scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u = bal := by
    rw [← hbal, mask120_and, ← hW]; rfl
  have hprev2 : previousIndex m.ctx.crypto m.world m.frame.msg.currentTarget u = prev := by
    rw [← hprev, mask128_and_div, ← hW]; rfl
  rw [hbal2] at hle hmul hinc
  rw [hprev2] at hinc
  have hsub0 := gt_sub_self_of_le (x := bal) (y := amt) hle
  have hba : (bal - amt).toNat = bal.toNat - amt.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]
  have hr1 := rayGuard_eq_one (x := bal - amt) (y := idx) (by
    rw [hba]
    have := Nat.mul_le_mul_right idx.toNat (Nat.sub_le bal.toNat amt.toNat); omega)
  have hBP : bal.toNat * prev.toNat < 2 ^ 256 := by
    have := Nat.mul_le_mul (Nat.le_of_lt hbal120) (Nat.le_of_lt hprev128)
    simp only [Nat.reducePow, Nat.reduceMul] at this ⊢; omega
  have hr2 := rayGuard_eq_one hBP
  have hr3 := rayGuard_eq_one hmul
  have hsub1 := gt_sub_self_of_le (x := Word.div (bal * idx) 1000000000000000000000000000#256)
    (y := Word.div (bal * prev) 1000000000000000000000000000#256)
    (by rw [toNat_rayMul hmul, toNat_rayMul hBP]; exact hinc)
  have hc128 := gt_eq_zero_of_le (x := idx) (n := 2 ^ 128 - 1) (by omega) (by decide)
  have hc120 := gt_eq_zero_of_le (x := amt) (n := 2 ^ 120 - 1) (by omega) (by decide)
  simp only [Nat.reducePow, Nat.reduceSub] at hc128 hc120
  simp only [userStateSlot] at hslot61
  obtain ⟨U, hU⟩ : ∃ U, m.world.sload m.frame.msg.currentTarget 61#256 = U := ⟨_, rfl⟩
  simp only [underlyingAddress, hU] at hTok hdelU hpreU
  obtain ⟨T, hT⟩ : ∃ T, m.world.sload m.frame.msg.currentTarget 54#256 = T := ⟨_, rfl⟩
  simp only [scaledTotalSupply, hT] at hsupLe
  have hS : ∀ (w : World) a v, (w.sstore a (m.ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress u) ++ Bytes.ofWord 52#256)) v).sload a 54#256 = w.sload a 54#256 :=
    fun w a v => World.sload_sstore_ne_key _ _ _ (fun e => hslot e.symm)
  have hS2 : ∀ (w : World) a v, (w.sstore a 54#256 v).sload a (m.ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress u) ++ Bytes.ofWord 52#256)) = w.sload a (m.ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress u) ++ Bytes.ofWord 52#256)) :=
    fun w a v => World.sload_sstore_ne_key _ _ _ hslot
  have hsub2 := gt_sub_self_of_le (x := T) (y := amt) hsupLe
  have hlow := low120_userWordIndexed W idx
  rw [hbal] at hlow
  simp only [userWordIndexed] at hlow
  have ham := and_mask120_of_lt (show amt.toNat < 2 ^ 120 by omega)
  have hm1 := mask120_and_of_lt (show amt.toNat < 2 ^ 120 by omega)
  have hm2 := mask120_and_of_lt hbal120
  have hc120b := gt_eq_zero_of_le (x := bal - amt) (n := 2 ^ 120 - 1) (by rw [hba]; omega)
    (by decide)
  simp only [Nat.reducePow, Nat.reduceSub] at hc120b
  fresh_intro
  pwp_run_to 8307 [hc120b, hT, hS, hS2, hsub2, World.sload_sstore_self, hlow, ham, hm1, hm2, hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
    hc', hW, hbal, hprev, hsub0, iszero_zero, hr1, hr2, hr3, hsub1, hc128, hc120, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self,
    Memory.read_64]
  wp_abstract gas g2 hgas2
  have hg3 : 4900000 ≤ g2 := by rw [← hgas2]; evm_gas
  have hgu3 : g2 ≤ m_gasLeft := by rw [← hgas2]; omega
  clear hgas2
  have hrc : Word.toAddress 738707689404430392569646267577155488893963911115#256 = rewardsController := by
    decide
  have hcs' : Word.iszero (ofNat (m_world.code rewardsController).size) = 0#256 := by
    apply iszero_of_ne
    intro h
    have := congrArg BitVec.toNat h
    simp only [ofNat, BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt hcs2] at this
    exact hcs this
  have hacc := accessCost_le (m_sub.accessedAddresses.contains rewardsController)
  apply WP.of_step
  case h =>
    refine step_extcodesize (by pcode_fact) rfl (by simp) ?_
    access_bounds
    evm_gas
  case hs => same_frame
  pwp_norm [hrc, hcs', World.code_sstore]
  wp_abstract gas g3 hgas3
  have hg4 : 4890000 ≤ g3 := by
    rw [← hgas3]
    access_bounds
    evm_gas
  have hgu4 : g3 ≤ g2 := by rw [← hgas3]; omega
  clear hgas3
  pwp_run_to 8321 [hrc, hcs', World.code_sstore, hm2, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  wp_abstract memory M3 hM3
  have hM3s : M3.size = 256 := by
    rw [← hM3]
    simp only [Memory.size_storeWord, Memory.size_expand,
      Memory.wordsAfter, Memory.words, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
      Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.max_def, ↓reduceIte,
      Memory.size_empty]
  have hM3f : M3.loadWord 64 = 128#256 := by
    rw [← hM3]
    simp only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint _ 128 64 _ (by decide),
      Memory.loadWord_storeWord_of_disjoint _ 132 64 _ (by decide),
      Memory.loadWord_storeWord_of_disjoint _ 164 64 _ (by decide),
      Memory.loadWord_storeWord_of_disjoint _ 196 64 _ (by decide),
      Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
      Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide), Memory.loadWord_storeWord]
  refine WP.call0 (by pcode_fact) rfl ?_ ?_ ?_ ?_ (hrcOk _ u T bal ?_ rfl rfl ?_ ?_ ?_ ?_ ?_) ?_
  · simp only [World.code_sstore, hrc]; exact hdel
  · simp only [callCost, callGas, callExt, hrc, ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show g3 - 27 < 2 ^ 256 by omega)]
    simp only [Nat.reducePow, Nat.reduceMod]
    access_bounds
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    evm_gas
  · simp only [Gas.stackDepthLimit]; omega
  · rw [hrc]; exact hpre
  · exact ⟨_, _, _, rfl, by simp only [childMsg, World.code_sstore, hrc]⟩
  · dsimp only [Frame.init, childMsg, callMemory]
    rw [← hM3]
    simp only [BitVec.reduceToNat, readBytes_bytes, Abi.selectorOf]
    rw [Memory.readBytes_read _ 128 100 0 4 (by decide)]
    simp only [Memory.read_expand, Nat.add_zero,
      Memory.read_storeWord_of_disjoint _ 196 128 4 _ (by decide),
      Memory.read_storeWord_of_disjoint _ 164 128 4 _ (by decide),
      Memory.read_storeWord_of_disjoint _ 132 128 4 _ (by decide),
      Memory.read_storeWord_prefix _ _ 4 _ (by decide)]
    kernel_decide
  · dsimp only [Frame.init, childMsg, callMemory]
    rw [← hM3]
    simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
  · dsimp only [Frame.init, childMsg, callMemory]
    rw [← hM3]
    simp only [BitVec.reduceToNat, readBytes_bytes]
    rw [Memory.readBytes_read _ 128 100 4 32 (by decide)]
    simp only [Nat.reduceAdd, Memory.read_expand,
      Memory.read_storeWord_of_disjoint _ 196 132 32 _ (by decide),
      Memory.read_storeWord_of_disjoint _ 164 132 32 _ (by decide), Memory.read_storeWord,
      Bytes.toWord_ofWord]
  · dsimp only [Frame.init, childMsg, callMemory]
    rw [← hM3]
    simp only [BitVec.reduceToNat, readBytes_bytes]
    rw [Memory.readBytes_read _ 128 100 36 32 (by decide)]
    simp only [Nat.reduceAdd, Memory.read_expand,
      Memory.read_storeWord_of_disjoint _ 196 164 32 _ (by decide), Memory.read_storeWord,
      Bytes.toWord_ofWord]
  · dsimp only [Frame.init, childMsg, callMemory]
    rw [← hM3]
    simp only [BitVec.reduceToNat, readBytes_bytes]
    rw [Memory.readBytes_read _ 128 100 68 32 (by decide)]
    simp only [Nat.reduceAdd, Memory.read_expand, Memory.read_storeWord, Bytes.toWord_ofWord]
  · intro mf o ⟨⟨out, ho⟩, hst, hcode⟩ hsame
    have hk : mf.frame.kind = .call 128 0 := hsame.kind
    subst ho
    rw [resumeAfter_success hk]
    have hs1 : mf.ctx = m_ctx := hsame.ctx
    have hs2 : mf.precompiles = m_pre := hsame.precompiles
    have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
    clear hsame
    simp only [hs1, hs2, hs3]
    dsimp only [call0Caller, callerFrame, callMemory, Frame.init, childMsg] at hst ⊢
    wp_abstract memory M4 hM4
    have hM4s : M4.size = 256 := by
      rw [← hM4]
      simp only [returnMemory, ByteArray.size_extract, Nat.sub_zero,
        Nat.zero_le, Nat.min_eq_left, ↓reduceIte, Memory.size_expand, Memory.wordsAfter, Memory.words,
        hM3s, BitVec.reduceToNat]
      decide
    have hM4f : M4.loadWord 64 = 128#256 := by
      rw [← hM4]
      simp only [returnMemory, ByteArray.size_extract, Nat.sub_zero,
        Nat.zero_le, Nat.min_eq_left, ↓reduceIte, Memory.loadWord_expand, hM3f]
    clear hM4
    wp_abstract gas g5 hgas5
    have hg5 : 75000 ≤ g5 := by
      rw [← hgas5]
      simp only [callCost, callGas, callExt, hrc, ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show g3 - 27 < 2 ^ 256 by omega), Nat.reducePow, Nat.reduceMod]
      access_bounds
      rw [messageCallGas_zero (by evm_gas)]
      simp only [Gas.maxMessageCallGas]
      evm_gas
    clear hgas5
    wp_abstract sub sub5 hsub5
    clear hsub5
    pwp_steps [hM4s, hM4f]
    have hBA : (bal - amt).toNat * idx.toNat < 2 ^ 256 := by
      rw [hba]
      have := Nat.mul_le_mul_right idx.toNat (Nat.sub_le bal.toNat amt.toNat); omega
    have hrne : Word.eq (Word.ofAddress m_msg.currentTarget) (Word.ofAddress r) = 0#256 :=
      eq_of_ne fun e => hr (Word.ofAddress_injective e).symm
    have h61 : mf.world.sload m_msg.currentTarget 61#256 = U := by
      rw [hst, World.sload_sstore_ne_key _ _ _ (fun e => hslot61 e.symm),
        World.sload_sstore_ne_key _ _ _ (by decide), World.sload_sstore_ne_key _ _ _
        (fun e => hslot61 e.symm), hU]
    by_cases hNP : (Word.div (bal * prev) 1000000000000000000000000000#256).toNat <
        (Word.div ((bal - amt) * idx) 1000000000000000000000000000#256).toNat
    · simp only [gt_eq_ofBool, decide_eq_true hNP, Word.ofBool, ↓reduceIte]
      have hsubN := gt_sub_self_of_le (x := Word.div ((bal - amt) * idx) 1000000000000000000000000000#256)
        (y := Word.div (bal * prev) 1000000000000000000000000000#256) (Nat.le_of_lt hNP)
      pwp_steps [hM4s, hM4f, hsubN, iszero_zero]
      pwp_codecopy
      pwp_steps [hM4s, hM4f, ofAddress_and_addressMask, addressMask_and_ofAddress]
      pwp_codecopy
      pwp_run_to 5982 [hM4s, hM4f, ofAddress_and_addressMask, addressMask_and_ofAddress, hsub0,
        iszero_zero, hrne, h61]
      wp_abstract gas g6 hgas6
      have hg6 : 60000 ≤ g6 := by rw [← hgas6]; evm_gas
      have hgu6 : g6 ≤ g5 := by rw [← hgas6]; omega
      clear hgas6
      wp_abstract memory M6 hM6
      have hM6s : M6.size = 256 := by
        rw [← hM6]
        simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
          Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceLeDiff, Nat.reduceEqDiff,
          Nat.max_def, ↓reduceIte, hM4s]
      have hM6f : M6.loadWord 64 = 128#256 := by
        rw [← hM6]
        simp only [Memory.loadWord_expand,
          Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 128 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 132 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 160 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 164 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 192 64 _ (by decide), hM4f]
      have htoU : Word.toAddress (1461501637330902918203684832716283019655932542975#256 &&& U) =
          Word.toAddress U := toAddress_mask160_and U
      pwp_steps 1 [hM6s]
      refine WP.call0 (by pcode_fact) rfl ?_ ?_ ?_ ?_ (hTok _ r amount ?_ rfl rfl ?_ ?_ ?_ ?_) ?_
      · rw [htoU, hcode]; simp only [World.code_sstore]; exact hdelU
      · simp only [callCost, callGas, callExt, htoU, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod]
        access_bounds
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · simp only [Gas.stackDepthLimit]; omega
      · rw [htoU]; exact hpreU
      · exact ⟨_, _, _, rfl, by simp only [childMsg, htoU]⟩
      · dsimp only [Frame.init, childMsg, callMemory]
        rw [← hM6]
        simp only [BitVec.reduceToNat, readBytes_bytes, Abi.selectorOf]
        rw [Memory.readBytes_read _ 128 68 0 4 (by decide)]
        simp only [Memory.read_expand, Nat.add_zero,
          Memory.read_storeWord_of_disjoint _ 164 128 4 _ (by decide),
          Memory.read_storeWord_of_disjoint _ 132 128 4 _ (by decide),
          Memory.read_storeWord_prefix _ _ 4 _ (by decide)]
        kernel_decide
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
      · dsimp only [Frame.init, childMsg, callMemory]
        rw [← hM6]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 128 68 4 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand,
          Memory.read_storeWord_of_disjoint _ 164 132 32 _ (by decide), Memory.read_storeWord,
          Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        rw [← hM6]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 128 68 36 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand, Memory.read_storeWord, Bytes.toWord_ofWord]
      · intro mf2 o2 ⟨ho2, hst2⟩ hsame2
        have hk2 : mf2.frame.kind = .call 0 0 := hsame2.kind
        subst ho2
        rw [resumeAfter_success hk2]
        have h21 : mf2.ctx = m_ctx := hsame2.ctx
        have h22 : mf2.precompiles = m_pre := hsame2.precompiles
        have h23 : mf2.originalWorld = m_originalWorld := hsame2.originalWorld
        clear hsame2
        simp only [h21, h22, h23]
        dsimp only [call0Caller, callerFrame, callMemory, Frame.init, childMsg] at hst2 ⊢
        wp_abstract memory M7 hM7
        have hM7s : M7.size = 256 := by
          rw [← hM7]
          simp only [returnMemory, ByteArray.size_extract, Nat.sub_zero,
            Nat.zero_le, Nat.min_eq_left, ↓reduceIte, Memory.size_expand, Memory.wordsAfter,
            Memory.words, hM6s, BitVec.reduceToNat]
          decide
        have hM7f : M7.loadWord 64 = 128#256 := by
          rw [← hM7]
          simp only [returnMemory, ByteArray.size_extract, Nat.sub_zero,
            Nat.zero_le, Nat.min_eq_left, ↓reduceIte, Memory.loadWord_expand, hM6f]
        clear hM7
        wp_abstract gas g7 hgas7
        have hg7 : 800 ≤ g7 := by
          rw [← hgas7]
          simp only [callCost, callGas, callExt, htoU, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
            Nat.reduceMod]
          access_bounds
          rw [messageCallGas_zero (by evm_gas)]
          simp only [Gas.maxMessageCallGas]
          evm_gas
        clear hgas7
        pwp_steps [hM7s, hM7f, Bytes.size_ofWord]
        have hext : (Bytes.ofWord (1 : Word)).extract 0 (0 + 32) = Bytes.ofWord 1 := by
          rw [Nat.zero_add, ← Bytes.size_ofWord (1 : Word), ByteArray.extract_zero_size]
        apply WP.of_step
        case h =>
          refine step_returndatacopy (by pcode_fact) rfl (by decide)
            (by rw [Bytes.size_ofWord]; decide) ?_
          simp only [memoryCost]
          evm_gas
        case hs => same_frame
        pwp_norm [hext, Memory.write_ofWord, hM7s, hM7f]
        pwp_steps [hext, Memory.write_ofWord, hM7s, hM7f, Memory.loadWord_storeWord,
          Memory.loadWord_expand]
        refine ⟨?_, fun slot => ?_⟩
        · dsimp only
          rw [iszero_iszero_iszero, hbal2]
        · dsimp only [outputMachine]
          rw [hst2, hst]
          simp only [burnWorld, userWordIndexed, userWordMinted, userStateSlot, hW, hT, hbal2]
    · simp only [gt_eq_ofBool, decide_eq_false hNP, Word.ofBool, Bool.false_eq_true,
        ↓reduceIte]
      have hsubP := gt_sub_self_of_le (x := Word.div (bal * prev) 1000000000000000000000000000#256)
        (y := Word.div ((bal - amt) * idx) 1000000000000000000000000000#256) (Nat.le_of_not_lt hNP)
      pwp_steps [hM4s, hM4f, hsubP, iszero_zero]
      pwp_codecopy
      pwp_run_to 5982 [hM4s, hM4f, ofAddress_and_addressMask, addressMask_and_ofAddress, hsub0,
        iszero_zero, hrne, h61]
      wp_abstract gas g6 hgas6
      have hg6 : 60000 ≤ g6 := by rw [← hgas6]; evm_gas
      have hgu6 : g6 ≤ g5 := by rw [← hgas6]; omega
      clear hgas6
      wp_abstract memory M6 hM6
      have hM6s : M6.size = 256 := by
        rw [← hM6]
        simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
          Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceLeDiff, Nat.reduceEqDiff,
          Nat.max_def, ↓reduceIte, hM4s]
      have hM6f : M6.loadWord 64 = 128#256 := by
        rw [← hM6]
        simp only [Memory.loadWord_expand,
          Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 128 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 132 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 160 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 164 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 192 64 _ (by decide), hM4f]
      have htoU : Word.toAddress (1461501637330902918203684832716283019655932542975#256 &&& U) =
          Word.toAddress U := toAddress_mask160_and U
      pwp_steps 1 [hM6s]
      refine WP.call0 (by pcode_fact) rfl ?_ ?_ ?_ ?_ (hTok _ r amount ?_ rfl rfl ?_ ?_ ?_ ?_) ?_
      · rw [htoU, hcode]; simp only [World.code_sstore]; exact hdelU
      · simp only [callCost, callGas, callExt, htoU, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod]
        access_bounds
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · simp only [Gas.stackDepthLimit]; omega
      · rw [htoU]; exact hpreU
      · exact ⟨_, _, _, rfl, by simp only [childMsg, htoU]⟩
      · dsimp only [Frame.init, childMsg, callMemory]
        rw [← hM6]
        simp only [BitVec.reduceToNat, readBytes_bytes, Abi.selectorOf]
        rw [Memory.readBytes_read _ 128 68 0 4 (by decide)]
        simp only [Memory.read_expand, Nat.add_zero,
          Memory.read_storeWord_of_disjoint _ 164 128 4 _ (by decide),
          Memory.read_storeWord_of_disjoint _ 132 128 4 _ (by decide),
          Memory.read_storeWord_prefix _ _ 4 _ (by decide)]
        kernel_decide
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
      · dsimp only [Frame.init, childMsg, callMemory]
        rw [← hM6]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 128 68 4 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand,
          Memory.read_storeWord_of_disjoint _ 164 132 32 _ (by decide), Memory.read_storeWord,
          Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        rw [← hM6]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 128 68 36 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand, Memory.read_storeWord, Bytes.toWord_ofWord]
      · intro mf2 o2 ⟨ho2, hst2⟩ hsame2
        have hk2 : mf2.frame.kind = .call 0 0 := hsame2.kind
        subst ho2
        rw [resumeAfter_success hk2]
        have h21 : mf2.ctx = m_ctx := hsame2.ctx
        have h22 : mf2.precompiles = m_pre := hsame2.precompiles
        have h23 : mf2.originalWorld = m_originalWorld := hsame2.originalWorld
        clear hsame2
        simp only [h21, h22, h23]
        dsimp only [call0Caller, callerFrame, callMemory, Frame.init, childMsg] at hst2 ⊢
        wp_abstract memory M7 hM7
        have hM7s : M7.size = 256 := by
          rw [← hM7]
          simp only [returnMemory, ByteArray.size_extract, Nat.sub_zero,
            Nat.zero_le, Nat.min_eq_left, ↓reduceIte, Memory.size_expand, Memory.wordsAfter,
            Memory.words, hM6s, BitVec.reduceToNat]
          decide
        have hM7f : M7.loadWord 64 = 128#256 := by
          rw [← hM7]
          simp only [returnMemory, ByteArray.size_extract, Nat.sub_zero,
            Nat.zero_le, Nat.min_eq_left, ↓reduceIte, Memory.loadWord_expand, hM6f]
        clear hM7
        wp_abstract gas g7 hgas7
        have hg7 : 800 ≤ g7 := by
          rw [← hgas7]
          simp only [callCost, callGas, callExt, htoU, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
            Nat.reduceMod]
          access_bounds
          rw [messageCallGas_zero (by evm_gas)]
          simp only [Gas.maxMessageCallGas]
          evm_gas
        clear hgas7
        pwp_steps [hM7s, hM7f, Bytes.size_ofWord]
        have hext : (Bytes.ofWord (1 : Word)).extract 0 (0 + 32) = Bytes.ofWord 1 := by
          rw [Nat.zero_add, ← Bytes.size_ofWord (1 : Word), ByteArray.extract_zero_size]
        apply WP.of_step
        case h =>
          refine step_returndatacopy (by pcode_fact) rfl (by decide)
            (by rw [Bytes.size_ofWord]; decide) ?_
          simp only [memoryCost]
          evm_gas
        case hs => same_frame
        pwp_norm [hext, Memory.write_ofWord, hM7s, hM7f]
        pwp_steps [hext, Memory.write_ofWord, hM7s, hM7f, Memory.loadWord_storeWord,
          Memory.loadWord_expand]
        refine ⟨?_, fun slot => ?_⟩
        · dsimp only
          rw [iszero_iszero_iszero, hbal2]
        · dsimp only [outputMachine]
          rw [hst2, hst]
          simp only [burnWorld, userWordIndexed, userWordMinted, userStateSlot, hW, hT, hbal2]


end Examples.AaveV3.AToken
