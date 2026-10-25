import Examples.AaveV3.AToken.Mint.Basic

/-!
# `AToken.mint` by the Pool: success

`mint_halts_ok`: in any fresh non-static frame (the proxy's `DELEGATECALL`), the Pool's call
`mint(caller, u, amt, idx)` succeeds, returns whether `u`'s scaled balance was zero, and leaves
the executing account's storage as `mintWorld` (the user's packed word with the new index and
balance, `_totalSupply + amt`), provided the arithmetic checks of `_mintScaled`/`_mint` pass
and the rewards controller behaves as `HandleActionOk` says.

The run crosses `EXTCODESIZE`, one external `CALL` (`WP.call0` with the assumed callee summary)
and two `CODECOPY`s of event topics, all stepped by `pwp_xrun_to`/`pwp_xsteps`; memory and gas
are abstracted at the phase boundaries (`wp_abstract_mem`, which keeps the memory's size and free
pointer, and `wp_abstract gas`). No upper bound on the gas is needed: the caller keeps at least
1/64 of its gas whatever gas it requests (`callCost_le_gasLeft`, `messageCallGas_zero`).
-/

namespace Examples.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Examples.AaveV3.Contracts
open Examples.Solmate.ERC20 (lt_size_four)

/-- **`mint` by the Pool, success.** Hypotheses: well-formed calldata for
`mint(c, u, amt, idx)`, the Pool as caller, no value, a non-static frame, enough gas
(≥ 10^6, the rewards controller gets all but 1/64 of it; no upper bound); the user's slot is
not slot 54; the checks of the code pass: `amt ≠ 0`, the new balance fits 120 bits, `idx` fits
128 bits, `(balance + amt) * idx` does not overflow, the accrued interest `rayMul(balance, idx) -
rayMul(balance, previousIndex)` is not negative, the new supply does not overflow; and the
rewards controller is deployed (code of size in `(0, 2^256)`, not a precompile, no EIP-7702
delegation), depth allows the call, and its `handleAction` behaves (`HandleActionOk`). -/
theorem mint_halts_ok (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xb3f1c93d)
    (hsize : 132 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    {c u : Address} {amt idx : Word}
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress c)
    (harg1 : Bytes.toWord (readBytes m.frame.msg.data 36 32) = Word.ofAddress u)
    (harg2 : Bytes.toWord (readBytes m.frame.msg.data 68 32) = amt)
    (harg3 : Bytes.toWord (readBytes m.frame.msg.data 100 32) = idx)
    (hc : m.frame.msg.caller = pool)
    (hg : 1000000 ≤ m.frame.gasLeft)
    (hslot : userStateSlot m.ctx.crypto u ≠ 54#256)
    (hamt : amt ≠ 0)
    (hnb : (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat + amt.toNat <
      2 ^ 120)
    (hidx : idx.toNat < 2 ^ 128)
    (hmul : ((scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat + amt.toNat) *
      idx.toNat < 2 ^ 256)
    (hinc : (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat *
        (previousIndex m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat /
          1000000000000000000000000000 ≤
      (scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u).toNat * idx.toNat /
        1000000000000000000000000000)
    (hsup : (scaledTotalSupply m.world m.frame.msg.currentTarget).toNat + amt.toNat < 2 ^ 256)
    (hrcOk : HandleActionOk (m.world.code rewardsController) m.frame.msg.currentTarget)
    (hcs : (m.world.code rewardsController).size ≠ 0)
    (hcs2 : (m.world.code rewardsController).size < 2 ^ 256)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code rewardsController) = none)
    (hpre : m.precompiles.isPrecompile rewardsController = false)
    (hdepth : m.frame.msg.depth < 1024) :
    Halts m (MintOk u amt idx m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
      (BitVec.ofNat 256 128)) = 1 := iszero_slt_calldatasize (by omega) (by omega)
  have hc' : Word.eq 773725381719276160229242488166406195640368342242#256
      (Word.ofAddress m.frame.msg.caller) = 1#256 := by rw [hc]; exact poolWord_eq_pool
  have hneg : 0#256 - amt ≠ 0#256 := by
    intro h; apply hamt; have := congrArg (· + amt) h; simpa using this.symm
  obtain ⟨W, hW⟩ : ∃ W, m.world.sload m.frame.msg.currentTarget
      (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress u) ++ Bytes.ofWord 52#256)) = W :=
    ⟨_, rfl⟩
  obtain ⟨bal, hbal⟩ : ∃ b, 1329227995784915872903807060280344575#256 &&& W = b := ⟨_, rfl⟩
  have hbal2 : scaledBalance m.ctx.crypto m.world m.frame.msg.currentTarget u = bal := by
    rw [← hbal, mask120_and, ← hW]; rfl
  have hprev2 : previousIndex m.ctx.crypto m.world m.frame.msg.currentTarget u =
      340282366920938463463374607431768211455#256 &&&
        W.div 340282366920938463463374607431768211456#256 := by
    rw [mask128_and_div, ← hW]; rfl
  rw [hbal2] at hnb hmul hinc
  rw [hprev2] at hinc
  have hamt' : amt.toNat < 2 ^ 120 := by omega
  obtain ⟨T, hT⟩ : ∃ T, m.world.sload m.frame.msg.currentTarget 54#256 = T := ⟨_, rfl⟩
  simp only [scaledTotalSupply, hT] at hsup
  have hS : ∀ (w : World) a v, (w.sstore a (m.ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress u) ++ Bytes.ofWord 52#256)) v).sload a 54#256 = w.sload a 54#256 :=
    fun w a v => World.sload_sstore_ne_key _ _ _ (fun e => hslot e.symm)
  obtain ⟨prev, hprev⟩ : ∃ p, 340282366920938463463374607431768211455#256 &&&
      W.div 340282366920938463463374607431768211456#256 = p := ⟨_, rfl⟩
  rw [hprev] at hinc
  have hbal120 : bal.toNat < 2 ^ 120 := by
    rw [← hbal, mask120_and, BitVec.toNat_ofNat]; omega
  have hadd1 := ERC20.gt_add_self_eq_zero (x := amt) (y := bal) (by omega)
  have hprev128 : prev.toNat < 2 ^ 128 := by
    rw [← hprev, mask128_and_div, BitVec.toNat_ofNat]
    have := W.isLt
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hr2 := rayGuard_eq_one (x := bal) (y := prev) (by
    have := Nat.mul_le_mul (Nat.le_of_lt hbal120) (Nat.le_of_lt hprev128)
    simp only [Nat.reducePow, Nat.reduceMul] at this ⊢; omega)
  have hr3 := rayGuard_eq_one (x := bal) (y := idx) (by
    have := Nat.mul_le_mul_right idx.toNat (Nat.le_add_right bal.toNat amt.toNat); omega)
  have hBP : bal.toNat * prev.toNat < 2 ^ 256 := by
    have := Nat.mul_le_mul (Nat.le_of_lt hbal120) (Nat.le_of_lt hprev128)
    simp only [Nat.reducePow, Nat.reduceMul] at this ⊢; omega
  have hBI : bal.toNat * idx.toNat < 2 ^ 256 := by
    have := Nat.mul_le_mul_right idx.toNat (Nat.le_add_right bal.toNat amt.toNat); omega
  have hsub1 := gt_sub_self_of_le (x := Word.div (bal * idx) 1000000000000000000000000000#256)
    (y := Word.div (bal * prev) 1000000000000000000000000000#256)
    (by rw [toNat_rayMul hBI, toNat_rayMul hBP]; exact hinc)
  have hc128 := gt_eq_zero_of_le (x := idx) (n := 2 ^ 128 - 1) (by omega) (by decide)
  have hc120 := gt_eq_zero_of_le (x := amt) (n := 2 ^ 120 - 1) (by omega) (by decide)
  simp only [Nat.reducePow, Nat.reduceSub] at hc128 hc120
  have hr1 := rayGuard_eq_one (x := bal + amt) (y := idx) (by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; exact hmul)
  fresh_intro
  -- through the dispatcher, `onlyPool`, the checks and `rayMul`s, to the index write
  pwp_run_to 6240 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3,
    hc', hW, hbal, hadd1, iszero_zero, hr1, hprev, hr2, hr3, hsub1, hc128, hc120,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  wp_abstract_mem M
  wp_abstract gas g hgas
  have hg2 : 990000 ≤ g := by rw [← hgas]; evm_gas
  clear hgas
  have ham := and_mask120_of_lt hamt'
  have hadd2 := ERC20.gt_add_self_eq_zero (x := T) (y := amt) (by omega)
  have hS2 : ∀ (w : World) a v, (w.sstore a 54#256 v).sload a (m_ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress u) ++ Bytes.ofWord 52#256)) = w.sload a (m_ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress u) ++ Bytes.ofWord 52#256)) :=
    fun w a v => World.sload_sstore_ne_key _ _ _ hslot
  have hlow := low120_userWordIndexed W idx
  rw [hbal] at hlow
  simp only [userWordIndexed] at hlow
  have hm1 := mask120_and_of_lt hamt'
  have hm2 := mask120_and_of_lt hbal120
  have hc120b := gt_eq_zero_of_le (x := amt + bal) (n := 2 ^ 120 - 1)
    (by rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega) (by decide)
  simp only [Nat.reducePow, Nat.reduceSub] at hc120b
  -- the three writes (`_userState[u]` index, `_totalSupply`, `_userState[u]` balance)
  pwp_run_to 8177 [hW, hT, hS, hc120, iszero_zero, ham, hadd2, hS2,
    World.sload_sstore_self, hlow, hm1, hm2, hc120b, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64]
  wp_abstract_mem M2
  wp_abstract gas g2 hgas2
  have hg3 : 900000 ≤ g2 := by rw [← hgas2]; evm_gas
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
  -- `extcodesize(REWARDS_CONTROLLER)` (`pwp_xrun_to` steps it) and the call's arguments
  pwp_xrun_to 8321 [World.code_sstore, hrc, hcs', hm2, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  wp_abstract_mem M3 with hM3
  wp_abstract gas g3 hgas3
  have hg4 : 880000 ≤ g3 := by rw [← hgas3]; evm_gas
  clear hgas3
  -- the call's memory windows `[128, 228)` and `[128, 128)` are inside memory: no expansion
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
  · -- the selector, read back from the stored word (`reduceErrorSelector`)
    dsimp only [Frame.init, childMsg, callMemory]
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
  · intro mf o ⟨⟨out, ho⟩, hst⟩ hsame
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
    -- the caller keeps 1/64 of its gas, whatever gas the `GAS` word asked for
    have hg5 : 13000 ≤ g5 := by
      rw [← hgas5]
      simp only [callCost, callGas, callExt, hrc, ofNat, BitVec.toNat_ofNat, M3_size,
        Nat.reducePow, Nat.reduceMod, hext']
      rw [messageCallGas_zero (by evm_gas)]
      simp only [Gas.maxMessageCallGas]
      evm_gas
    clear hgas5
    have hBA : (bal + amt).toNat * idx.toNat < 2 ^ 256 := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; exact hmul
    have hsub2 := gt_sub_self_of_le (x := Word.div ((bal + amt) * idx) 1000000000000000000000000000#256)
      (y := Word.div (bal * prev) 1000000000000000000000000000#256)
      (by
        rw [toNat_rayMul hBA, toNat_rayMul hBP, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
        exact Nat.le_trans hinc (Nat.div_le_div_right
          (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))))
    -- the `Mint` event (two `CODECOPY`s of topics, stepped by `pwp_xsteps`) and the return
    pwp_xsteps [hsub2, iszero_zero, ofAddress_and_addressMask, addressMask_and_ofAddress]
    refine ⟨?_, ?_⟩
    · rw [iszero_iszero_iszero, hbal2]
    · intro slot
      dsimp only [outputMachine]
      rw [hst slot]
      simp only [mintWorld, userWordIndexed, userWordMinted, userStateSlot, hW, hT, hbal2]

end Examples.AaveV3.AToken
