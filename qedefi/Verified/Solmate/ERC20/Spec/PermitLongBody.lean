import Verified.Solmate.ERC20.Spec.PermitLongGas

/-!
# Solmate's `permit` body over any memory, at any gas below `2²⁵⁶`

`Permit.asset_permit_body` runs `permit` from `0x0566` (after `DOMAIN_SEPARATOR()`) with the
memory `DOMAIN_SEPARATOR()` leaves on the deployment chain or for a short `name` (free pointer
`0x80` or `0x140`, size `96` or `320`) and less than `2⁶⁴` gas. Off the deployment chain with a
long `name` the copied name stays in memory, which then has any size `S ≥ 320` (a multiple of
32), with free pointer `0x140`. `pl_body` is the same run for every such size and any gas below
`2²⁵⁶` (a frame lifted to the gas bound of `permit` may have more than `2⁶⁴`): the sizes below
`832` (the end of what the body writes) one by one, the larger ones as `832 + 32 t`
(`PermitLongGas`).
-/

namespace Verified.Solmate.ERC20.Spec
open QEDefi.ERC4626 Verified.Solmate.ERC20.Permit
open Verified.Solmate.ERC20.Spec.PermitLongGas

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

set_option maxHeartbeats 0 in
/-- `Permit.asset_permit_tail` (from the `STATICCALL` to `ecrecover`) for a memory of size
`832 + 32 t` and gas below `2²⁵⁶`. -/
theorem pl_tail {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {t : Nat}
    {dg v r s deadline value : Word} {owner spender : Address}
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1631)
    (hs : m.frame.stack = [ofNat m.frame.gasLeft, 1#256, BitVec.ofNat 256 (320 + 354), 128#256,
      BitVec.ofNat 256 (320 + 322), 32#256, BitVec.ofNat 256 (320 + 482), 1#256, 0#256,
      s, r, v, deadline, value, Word.ofAddress spender, Word.ofAddress owner, 424#256,
      3573918927#256])
    (hmem : m.frame.memory = M) (hM64 : M.loadWord 64 = BitVec.ofNat 256 (320 + 354))
    (hMout : M.loadWord (320 + 322) = 0#256)
    (hMin : M.read (320 + 354) 128 =
      Bytes.ofWord dg ++ (Bytes.ofWord v ++ (Bytes.ofWord r ++ Bytes.ofWord s)))
    (hMsz : M.size = 832 + 32 * t)
    (hg : 40000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 256)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hstatic : m.frame.msg.isStatic = false) :
    WP m (fun _ => False) (TailPost owner spender value dg v r s m) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs hmem hstd
  cases m_msg
  dsimp only at hstatic hdepth
  subst hstatic
  have hmod : m_gasLeft % 2 ^ 256 = m_gasLeft := Nat.mod_eq_of_lt (by omega)
  have hacc := accessCost_le (m_sub.accessedAddresses.contains 1)
  simp only [Nat.reduceAdd] at hM64 hMout hMin ⊢
  have hext : Gas.extendMemory m_memory.size [(674, 128), (642, 32)] =
      { cost := 0, newSize := 832 + 32 * t } := by
    rw [hMsz]; exact bg_ext2 (by decide) (by omega) (by omega)
  have hx1 : m_memory.expand 674 128 = m_memory := bg_expand hMsz (by decide) (by omega)
  have hx2 : m_memory.expand 642 32 = m_memory := bg_expand hMsz (by decide) (by omega)
  refine WP.staticcall_ecrecover (hash := dg) (v := v) (r := r) (s := s) (by pcode_fact) rfl rfl
    hdel1 ?_ hdepth hMin ?_ ?_
  · simp only [callCost, callGas, callExt, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, hext]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    evm_gas
  · simp only [callGas, callExt, ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hext]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    evm_gas
  simp only [returnMemory_ecrecoverOutput, callMemory, callCost, callGas, callExt, ofNat,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, callerFrame, hext, hx1, hx2]
  rw [messageCallGas_zero (by evm_gas)]
  simp only [Gas.maxMessageCallGas]
  wp_generalize_gas g1 hg1
  have hg1' : m_gasLeft ≤ g1 + 6000 := by
    subst hg1
    generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses 1) = acc at hacc ⊢
    evm_gas
  have hg1'' : 30000 ≤ g1 := by
    subst hg1
    generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses 1) = acc at hacc ⊢
    evm_gas
  clear hg1
  generalize ecrecoverOutput m_ctx.crypto dg v r s = rd
  have hxm := fun off len => bg_expand (off := off) (len := len) hMsz (by decide)
  cases hrec : ecrecoverAddress? m_ctx.crypto dg v r s with
  | none =>
    plwp_steps [hM64, hMout, ofAddress_and_addressMask, addressMask_and_ofAddress,
      Solidity.eq_self, iszero_zero, iszero_one, hMsz, Memory.read_64, hxm]
    unfold TailPost RecoversTo
    refine ⟨fun h => absurd h.2 (by rw [hrec]; simp), fun _ => ⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]; pl_gas
  | some a =>
    have hMs' : (m_memory.storeWord 642 (Word.ofAddress a)).size = 832 + 32 * t := by
      rw [Memory.size_storeWord, hMsz]; omega
    by_cases ha0 : a = 0
    · subst ha0
      plwp_steps [hM64, hMout, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Solidity.eq_self, iszero_zero, iszero_one, hMsz, hMs', Memory.read_64, hxm]
      unfold TailPost RecoversTo
      refine ⟨fun h => (h.1 (Option.some.inj (h.2.symm.trans hrec))).elim, fun _ => ⟨_, rfl⟩,
        ?_⟩
      dsimp only [outputMachine]; pl_gas
    · have hz := iszero_ofAddress ha0
      by_cases hao : a = owner
      · subst hao
        plwp_steps [hM64, hz, ofAddress_and_addressMask, addressMask_and_ofAddress,
          Solidity.eq_self, iszero_zero, iszero_one, hMsz, hMs', Memory.read_64, hxm]
        apply WP.halt_of_step (step_stop (by pcode_fact)) (SameFrame.refl _)
        unfold TailPost RecoversTo
        refine ⟨fun _ => ⟨rfl, ?_, rfl, rfl, ?_⟩, fun h => absurd ⟨ha0, hrec⟩ h, ?_⟩
        · rfl
        · dsimp only
          logs_simp []
          event_log [value]
        · pl_gas
      · have hne := eq_ofAddress_ne hao
        plwp_steps [hM64, hz, hne, ofAddress_and_addressMask, addressMask_and_ofAddress,
          Solidity.eq_self, iszero_zero, iszero_one, hMsz, hMs', Memory.read_64, hxm]
        unfold TailPost RecoversTo
        refine ⟨fun h => (hao (Option.some.inj (hrec.symm.trans h.2))).elim, fun _ => ⟨_, rfl⟩,
          ?_⟩
        dsimp only [outputMachine]; pl_gas


set_option maxHeartbeats 0 in
/-- `Permit.asset_permit_body` with free pointer `0x140`, a memory of size `832 + 32 t` and gas
below `2²⁵⁶`. -/
theorem pl_body_big {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {t : Nat}
    {ds deadline value v r s : Word} {owner spender : Address}
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1382)
    (hs : m.frame.stack = [ds, 1#256, 0#256, s, r, v, deadline, value, Word.ofAddress spender,
      Word.ofAddress owner, 424#256, 3573918927#256])
    (hmem : m.frame.memory = M) (hM64 : M.loadWord 64 = 320#256)
    (hMsz : M.size = 832 + 32 * t)
    (hv : v &&& 255#256 = v)
    (hg : 90000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 256)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hstatic : m.frame.msg.isStatic = false) :
    WP m (fun _ => False) (BodyPost ds owner spender value deadline v r s m) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs hmem hstd
  have hxm := fun off len => bg_expand (off := off) (len := len) hMsz (by decide)
  plwp_run_to 1420 [hM64, hMsz, hxm, ofAddress_and_addressMask, addressMask_and_ofAddress,
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
  simp only [Memory.size_storeWord, hMsz, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul] at hM1b
  clear hM1 hxm
  replace hM1a := hM1a.symm
  have hMsz : M1.size = 832 + 32 * t := by omega
  have hxm : ∀ off len, off + len ≤ 832 → M1.expand off len = M1 :=
    fun _ _ h => bg_expand hMsz (by decide) h
  plwp_run_to 1522 [hM1a, hMsz, hxm, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_192]
  -- the digest
  wp_generalize_mem M2 hM2
  have hM2a := congrArg (Memory.loadWord · 64) hM2
  have hM2b := congrArg Memory.size hM2
  simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord] at hM2a
  simp only [Memory.size_storeWord, hMsz, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul] at hM2b
  clear hM2 hxm
  replace hM2a := hM2a.symm
  have hMsz : M2.size = 832 + 32 * t := by omega
  have hxm : ∀ off len, off + len ≤ 832 → M2.expand off len = M2 :=
    fun _ _ h => bg_expand hMsz (by decide) h
  plwp_run_to 1580 [hM2a, hMsz, hxm, Memory.read_66, Memory.read_storeWord_two, prefix_eq]
  -- the input of `ecrecover`
  wp_generalize_mem M3 hM3
  have hM3a := congrArg (Memory.loadWord · 64) hM3
  have hM3b := congrArg Memory.size hM3
  simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord] at hM3a
  simp only [Memory.size_storeWord, hMsz, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul] at hM3b
  clear hM3 hxm
  replace hM3a := hM3a.symm
  have hMsz : M3.size = 832 + 32 * t := by omega
  have hxm : ∀ off len, off + len ≤ 832 → M3.expand off len = M3 :=
    fun _ _ h => bg_expand hMsz (by decide) h
  plwp_run_to 1631 [hM3a, hMsz, hxm, hv]
  refine WP.mono (pl_tail _ (t := t)
    (dg := digest m_ctx.crypto ds (structHash m_ctx.crypto owner spender value nonce deadline))
    rfl hj rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl
    (by dsimp only; rw [World.code_sstore]; exact hdel1) hdepth hstatic) (fun _ _ h => h) ?_
  · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
      Memory.loadWord_storeWord, hxm]
  · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
      Memory.loadWord_storeWord, hxm]
  · simp (disch := decide) only [Memory.read_128, Memory.read_expand, Memory.read_storeWord,
      Memory.read_storeWord_of_disjoint, hxm]
    rfl
  · simp only [Memory.size_storeWord, hMsz]; omega
  · dsimp only; omega
  · dsimp only; omega
  intro mf o _ ht
  obtain ⟨h1, h2, h3⟩ := ht
  subst hN
  refine ⟨fun hr => ?_, fun hr => h2 hr, ?_⟩
  · obtain ⟨ho, hw, ht, hc, hl⟩ := h1 hr
    exact ⟨ho, hw, ht, hc, hl⟩
  dsimp only at h3 ⊢
  omega


set_option maxHeartbeats 0 in
/-- `Permit.asset_permit_body` with free pointer `0x140`, a memory of size `S` from `320` to
`800` bytes and gas below `2²⁵⁶`. -/
theorem pl_body_small {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {S : Nat}
    {ds deadline value v r s : Word} {owner spender : Address}
    (hS : S = 320 ∨ S = 352 ∨ S = 384 ∨ S = 416 ∨ S = 448 ∨ S = 480 ∨ S = 512 ∨ S = 544 ∨ S = 576 ∨ S = 608 ∨ S = 640 ∨ S = 672 ∨ S = 704 ∨ S = 736 ∨ S = 768 ∨ S = 800)
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1382)
    (hs : m.frame.stack = [ds, 1#256, 0#256, s, r, v, deadline, value, Word.ofAddress spender,
      Word.ofAddress owner, 424#256, 3573918927#256])
    (hmem : m.frame.memory = M) (hM64 : M.loadWord 64 = 320#256) (hMs : M.size = S)
    (hv : v &&& 255#256 = v)
    (hg : 90000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 256)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hstatic : m.frame.msg.isStatic = false) :
    WP m (fun _ => False) (BodyPost ds owner spender value deadline v r s m) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs hmem hstd
  rcases hS with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  · pwp_run_to 1420 [hM64, hMs, permit_norm, ofAddress_and_addressMask, addressMask_and_ofAddress,
      Memory.read_64, hstatic]
    generalize hN : m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 5#256)) = nonce
    wp_generalize_gas g1 hg1
    have hg1' : m_gasLeft ≤ g1 + 30000 := by subst hg1; evm_gas
    have hg1'' : 60000 ≤ g1 := by subst hg1; evm_gas
    have hg1u : g1 ≤ m_gasLeft := by subst hg1; omega
    clear hg1
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
    wp_generalize_mem M3 hM3
    have hM3a := congrArg (Memory.loadWord · 64) hM3
    have hM3b := congrArg Memory.size hM3
    simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord] at hM3a
    simp only [permit_norm, hM2b] at hM3b
    clear hM3
    replace hM3a := hM3a.symm
    replace hM3b := hM3b.symm
    pwp_run_to 1631 [hM3a, hM3b, permit_norm, hv]
    refine WP.mono (pl_tail _ (t := 0)
      (dg := digest m_ctx.crypto ds (structHash m_ctx.crypto owner spender value nonce deadline))
      rfl hj rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl
      (by dsimp only; rw [World.code_sstore]; exact hdel1) hdepth hstatic) (fun _ _ h => h) ?_
    · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
        Memory.loadWord_storeWord]
    · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
        Memory.loadWord_storeWord]
    · simp (disch := decide) only [Memory.read_128, Memory.read_expand, Memory.read_storeWord,
        Memory.read_storeWord_of_disjoint]
      rfl
    · simp only [permit_norm, hM3b]
    · dsimp only; omega
    · dsimp only; omega
    intro mf o _ ht
    obtain ⟨h1, h2, h3⟩ := ht
    subst hN
    refine ⟨fun hr => ?_, fun hr => h2 hr, ?_⟩
    · obtain ⟨ho, hw, ht, hc, hl⟩ := h1 hr
      exact ⟨ho, hw, ht, hc, hl⟩
    dsimp only at h3 ⊢
    omega


/-- **`permit`'s body with free pointer `0x140` and any memory of `S ≥ 320` bytes** (a multiple
of 32), at any gas from `90000` below `2²⁵⁶`. -/
theorem pl_body {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {S : Nat}
    {ds deadline value v r s : Word} {owner spender : Address}
    (hS : 320 ≤ S) (hS32 : S % 32 = 0)
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1382)
    (hs : m.frame.stack = [ds, 1#256, 0#256, s, r, v, deadline, value, Word.ofAddress spender,
      Word.ofAddress owner, 424#256, 3573918927#256])
    (hmem : m.frame.memory = M) (hM64 : M.loadWord 64 = 320#256) (hMs : M.size = S)
    (hv : v &&& 255#256 = v)
    (hg : 90000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 256)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hstatic : m.frame.msg.isStatic = false) :
    WP m (fun _ => False) (BodyPost ds owner spender value deadline v r s m) := by
  by_cases hbig : 832 ≤ S
  · exact pl_body_big m (t := (S - 832) / 32) hc hj hpc hs hmem hM64 (by omega) hv hg hg' hstd
      hdel1 hdepth hstatic
  · refine pl_body_small m (S := S) ?_ hc hj hpc hs hmem hM64 hMs hv hg hg' hstd hdel1 hdepth
      hstatic
    omega

end Verified.Solmate.ERC20.Spec
