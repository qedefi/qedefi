import Examples.AaveV3.AToken.Burn.Basic

/-!
# `AToken.burn` by the Pool: success

`burn_halts_ok`: in any fresh non-static frame, the Pool's `burn(u, r, amount, amt, idx)` with
`r` other than the token succeeds, returns whether `u`'s scaled balance becomes zero, and
leaves the executing account's storage as `burnWorld`, provided the checks of `_burnScaled` /
`_burn` pass and both external calls behave as assumed (`HandleActionOkCode`, `TransferOk`).
Both event branches (`Mint` when the accrued interest exceeds the burnt amount, `Burn`
otherwise) are covered; they reach `safeTransfer`'s call in the same state up to memory, gas and
logs, and share that tail (`wp_join`: proved once). No upper bound on the gas is needed (the
caller keeps 1/64 of its gas at each call, whatever it requests).
-/

namespace Examples.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Examples.AaveV3.Contracts
open Examples.Solmate.ERC20 (lt_size_four)

/-- **`burn` by the Pool, success.** Hypotheses: well-formed calldata for
`burn(u, r, amount, amt, idx)` with `r` not the executing account, the Pool as caller, no
value, a non-static frame, gas at least 5·10^6 (two calls each forward all but 1/64);
`u`'s slot is neither 54 nor 61; the checks pass: `amt ≠ 0`, `amt ≤ scaledBalance u`,
`amt ≤ scaledTotalSupply`, `idx < 2^128`, `scaledBalance u · idx < 2^256`, the accrued
interest is not negative; the rewards controller is deployed (code of size in `(0, 2^256)`, not a
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
    (hg : 5000000 ≤ m.frame.gasLeft)
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
  pwp_run_to 8307 [hc120b, hT, hS, hS2, hsub2, World.sload_sstore_self, hlow, ham, hm1, hm2, hval,
    hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4, hc', hW, hbal,
    hprev, hsub0, iszero_zero, hr1, hr2, hr3, hsub1, hc128, hc120, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  wp_abstract gas g2 hgas2
  have hg3 : 4900000 ≤ g2 := by rw [← hgas2]; evm_gas
  clear hgas2
  have hrc : Word.toAddress 738707689404430392569646267577155488893963911115#256 =
      rewardsController := by decide
  have hcs' : Word.iszero (ofNat (m_world.code rewardsController).size) = 0#256 := by
    apply iszero_of_ne
    intro h
    have := congrArg BitVec.toNat h
    simp only [ofNat, BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt hcs2] at this
    exact hcs this
  -- \`extcodesize(REWARDS_CONTROLLER)\` and the arguments of \`handleAction\`
  pwp_xrun_to 8321 [World.code_sstore, hrc, hcs', hm2, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  wp_abstract_mem M3 with hM3
  wp_abstract gas g3 hgas3
  have hg4 : 4880000 ≤ g3 := by rw [← hgas3]; evm_gas
  clear hgas3
  -- the call's memory windows \`[128, 228)\` and \`[128, 128)\` are inside memory: no expansion
  have hext : (Gas.extendMemory 256 [((128#256 : Word).toNat, (100#256 : Word).toNat),
      ((128#256 : Word).toNat, (0#256 : Word).toNat)]).cost = 0 := by decide
  have hext' : (Gas.extendMemory 256 [(128, 100), (128, 0)]).cost = 0 := by decide
  refine WP.call0 (by pcode_fact) rfl ?_ ?_ ?_ ?_ (hrcOk _ u T bal ?_ rfl rfl ?_ ?_ ?_ ?_ ?_) ?_
  · simp only [World.code_sstore, hrc]; exact hdel
  · exact callCost_le_gasLeft (c := 0)
      (by simp only [callExt, M3_size, hext]; exact Nat.le_refl 0)
      (by evm_gas)
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
      Memory.read_storeWord_of_disjoint _ 132 128 4 _ (by decide), reduceErrorSelector,
      Abi.selectorBytes, Bytes.toNat_ofNatBE]
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
    clear hM3
    dsimp only [call0Caller, callerFrame, callMemory, Frame.init, childMsg] at hst ⊢
    wp_abstract_mem M4
    wp_abstract gas g5 hgas5
    -- the caller keeps 1/64 of its gas, whatever gas the \`GAS\` word asked for
    have hg5 : 75000 ≤ g5 := by
      rw [← hgas5]
      simp only [callCost, callGas, callExt, hrc, ofNat, BitVec.toNat_ofNat, M3_size,
        Nat.reducePow, Nat.reduceMod, hext']
      rw [messageCallGas_zero (by evm_gas)]
      simp only [Gas.maxMessageCallGas]
      evm_gas
    clear hgas5
    wp_abstract sub sub5 hsub5
    clear hsub5
    pwp_steps
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
    case' pos =>
      -- \`Mint\` event (the interest exceeds the burnt amount), up to \`safeTransfer\`'s call
      simp only [gt_eq_ofBool, decide_eq_true hNP, Word.ofBool, ↓reduceIte]
      have hsubN := gt_sub_self_of_le
        (x := Word.div ((bal - amt) * idx) 1000000000000000000000000000#256)
        (y := Word.div (bal * prev) 1000000000000000000000000000#256) (Nat.le_of_lt hNP)
      pwp_xrun_to 5982 [hsubN, iszero_zero, ofAddress_and_addressMask,
        addressMask_and_ofAddress, hsub0, hrne, h61]
      wp_abstract gas g6 hgas6
      have hg6 : 60000 ≤ g6 := by rw [← hgas6]; evm_gas
      clear hgas6
      wp_abstract_mem M6 with hM6
      have hc0 : M6.read 128 4 = Abi.selectorBytes 0xa9059cbb := by
        rw [← hM6]; simp (disch := decide) only [Memory.read_expand,
          Memory.read_storeWord_of_disjoint, reduceErrorSelector]
      have hc1 : M6.read 132 32 = Bytes.ofWord (Word.ofAddress r) := by
        rw [← hM6]; simp (disch := decide) only [Memory.read_expand,
          Memory.read_storeWord_of_disjoint, Memory.read_storeWord]
      have hc2 : M6.read 164 32 = Bytes.ofWord amount := by
        rw [← hM6]; simp (disch := decide) only [Memory.read_storeWord]
      clear hM6
      wp_abstract sub sub6 hsub6
      clear hsub6
    case' neg =>
      -- \`Burn\` event
      simp only [gt_eq_ofBool, decide_eq_false hNP, Word.ofBool, Bool.false_eq_true,
        ↓reduceIte]
      have hsubP := gt_sub_self_of_le
        (x := Word.div (bal * prev) 1000000000000000000000000000#256)
        (y := Word.div ((bal - amt) * idx) 1000000000000000000000000000#256)
        (Nat.le_of_not_lt hNP)
      pwp_xrun_to 5982 [hsubP, iszero_zero, ofAddress_and_addressMask,
        addressMask_and_ofAddress, hsub0, hrne, h61]
      wp_abstract gas g6 hgas6
      have hg6 : 60000 ≤ g6 := by rw [← hgas6]; evm_gas
      clear hgas6
      wp_abstract_mem M6 with hM6
      have hc0 : M6.read 128 4 = Abi.selectorBytes 0xa9059cbb := by
        rw [← hM6]; simp (disch := decide) only [Memory.read_expand,
          Memory.read_storeWord_of_disjoint, reduceErrorSelector]
      have hc1 : M6.read 132 32 = Bytes.ofWord (Word.ofAddress r) := by
        rw [← hM6]; simp (disch := decide) only [Memory.read_expand,
          Memory.read_storeWord_of_disjoint, Memory.read_storeWord]
      have hc2 : M6.read 164 32 = Bytes.ofWord amount := by
        rw [← hM6]; simp (disch := decide) only [Memory.read_storeWord]
      clear hM6
      wp_abstract sub sub6 hsub6
      clear hsub6
    -- both branches reach pc 5982 in the same state up to memory (event data), gas and logs:
    -- the tail (\`safeTransfer\`) is proved once
    wp_join [M6, M6_size, M6_fp, hc0, hc1, hc2, g6, hg6, sub6]
    have htoU : Word.toAddress (1461501637330902918203684832716283019655932542975#256 &&& U) =
        Word.toAddress U := toAddress_mask160_and U
    have hext6 : (Gas.extendMemory 256 [((128#256 : Word).toNat, (68#256 : Word).toNat),
        ((0#256 : Word).toNat, (0#256 : Word).toNat)]).cost = 0 := by decide
    have hext6' : (Gas.extendMemory 256 [(128, 68), (0, 0)]).cost = 0 := by decide
    pwp_steps 1
    refine WP.call0 (by pcode_fact) rfl ?_ ?_ ?_ ?_ (hTok _ r amount ?_ rfl rfl ?_ ?_ ?_ ?_) ?_
    · rw [htoU, hcode]; simp only [World.code_sstore]; exact hdelU
    · exact callCost_le_gasLeft (c := 0)
        (by simp only [callExt, M6_size, hext6]; exact Nat.le_refl 0)
        (by evm_gas)
    · simp only [Gas.stackDepthLimit]; omega
    · rw [htoU]; exact hpreU
    · exact ⟨_, _, _, rfl, by simp only [childMsg, htoU]⟩
    · dsimp only [Frame.init, childMsg, callMemory]
      simp only [BitVec.reduceToNat, readBytes_bytes, Abi.selectorOf]
      rw [Memory.readBytes_read _ 128 68 0 4 (by decide)]
      simp only [Memory.read_expand, Nat.add_zero, hc0, Abi.selectorBytes, Bytes.toNat_ofNatBE]
    · dsimp only [Frame.init, childMsg, callMemory]
      simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
    · dsimp only [Frame.init, childMsg, callMemory]
      simp only [BitVec.reduceToNat, readBytes_bytes]
      rw [Memory.readBytes_read _ 128 68 4 32 (by decide)]
      simp only [Nat.reduceAdd, Memory.read_expand, hc1, Bytes.toWord_ofWord]
    · dsimp only [Frame.init, childMsg, callMemory]
      simp only [BitVec.reduceToNat, readBytes_bytes]
      rw [Memory.readBytes_read _ 128 68 36 32 (by decide)]
      simp only [Nat.reduceAdd, Memory.read_expand, hc2, Bytes.toWord_ofWord]
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
      wp_abstract_mem M7
      wp_abstract gas g7 hgas7
      have hg7 : 800 ≤ g7 := by
        rw [← hgas7]
        simp only [callCost, callGas, callExt, htoU, ofNat, BitVec.toNat_ofNat, M6_size,
          Nat.reducePow, Nat.reduceMod, hext6']
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      clear hgas7
      -- \`returndatacopy\` of the returned word (\`pwp_xsteps\`), its check, \`return\`
      pwp_xsteps [Bytes.size_ofWord, Memory.write_ofWord, Memory.loadWord_storeWord,
        Memory.loadWord_expand]
      refine ⟨?_, fun slot => ?_⟩
      · dsimp only
        rw [iszero_iszero_iszero, hbal2]
      · dsimp only [outputMachine]
        rw [hst2, hst]
        simp only [burnWorld, userWordIndexed, userWordMinted, userStateSlot, hW, hT, hbal2]

end Examples.AaveV3.AToken
