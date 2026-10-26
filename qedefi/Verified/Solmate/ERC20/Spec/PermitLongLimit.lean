import Verified.Solmate.ERC20.Spec.PermitLongBody
import Verified.Solmate.ERC20.Spec.PermitDepth

/-!
# Solmate's `permit` body over any memory: the call-depth limit and static frames

`pl_body_limit`: at the call-depth limit the `STATICCALL` to `ecrecover` fails at once and
`permit` reverts (`permit_body_limit` for the memory of `DOMAIN_SEPARATOR()` with a long
`name`, any size `S ≥ 320`, gas below `2²⁵⁶`); `pl_body_static`: in a static frame the nonce's
`SSTORE` halts.
-/

namespace Verified.Solmate.ERC20.Spec
open QEDefi.ERC4626 Verified.Solmate.ERC20.Permit
open Verified.Solmate.ERC20.Spec.PermitLongGas

open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts

set_option maxHeartbeats 0 in
/-- `permit_tail_limit` for a memory of size `832 + 32 t` and gas below `2²⁵⁶`. -/
theorem pl_tail_limit {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {t : Nat}
    {v r s deadline value : Word} {owner spender : Address}
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1631)
    (hs : m.frame.stack = [ofNat m.frame.gasLeft, 1#256, BitVec.ofNat 256 (320 + 354), 128#256,
      BitVec.ofNat 256 (320 + 322), 32#256, BitVec.ofNat 256 (320 + 482), 1#256, 0#256,
      s, r, v, deadline, value, Word.ofAddress spender, Word.ofAddress owner, 424#256,
      3573918927#256])
    (hmem : m.frame.memory = M) (hM64 : M.loadWord 64 = BitVec.ofNat 256 (320 + 354))
    (hMsz : M.size = 832 + 32 * t)
    (hg : 40000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 256)
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
  simp only [Nat.reduceAdd] at hM64 ⊢
  have hext : Gas.extendMemory m_memory.size [(674, 128), (642, 32)] =
      { cost := 0, newSize := 832 + 32 * t } := by
    rw [hMsz]; exact bg_ext2 (by decide) (by omega) (by omega)
  have hx1 : m_memory.expand 674 128 = m_memory := bg_expand hMsz (by decide) (by omega)
  have hx2 : m_memory.expand 642 32 = m_memory := bg_expand hMsz (by decide) (by omega)
  refine WP.of_step (step_staticcall_limit (by pcode_fact) rfl (by rw [hto]; exact hdel1) ?_
    hdepth (by simp)) (by same_frame) ?_
  · simp only [callCost, callGas, callExt, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, hto, hext]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    evm_gas
  simp only [callMemory, callCost, callGas, callExt, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, callerFrame, hto, hext, hx1, hx2]
  rw [messageCallGas_zero (by evm_gas)]
  simp only [Gas.maxMessageCallGas]
  wp_generalize_gas g1 hg1
  have hg1'' : 30000 ≤ g1 := by
    subst hg1
    generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses 1) = acc at hacc ⊢
    evm_gas
  clear hg1
  have hxm : ∀ off len, off + len ≤ 832 → m_memory.expand off len = m_memory :=
    fun _ _ h => bg_expand hMsz (by decide) h
  plwp_steps [hM64, hMsz, hxm, Memory.read_64]
  refine WP.of_step (step_returndatacopy_zero (by pcode_fact) rfl (by evm_gas)) (by same_frame) ?_
  dsimp only
  plwp_steps [hMsz, hxm]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- `Permit.asset_permit_body` with free pointer `0x140`, a memory of size `832 + 32 t` and gas
below `2²⁵⁶`. -/
theorem pl_body_big_limit {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {t : Nat}
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
    (hdepth : Gas.stackDepthLimit < m.frame.msg.depth + 1)
    (hstatic : m.frame.msg.isStatic = false) :
    WP m (fun _ => False) (fun _ o => ∃ out, o = .revert out) := by
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
  refine pl_tail_limit _ (t := t) rfl hj rfl rfl rfl ?_ ?_ ?_ ?_
    (by dsimp only; rw [World.code_sstore]; exact hdel1) hdepth
  · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
      Memory.loadWord_storeWord, hxm]
  · simp only [Memory.size_storeWord, hMsz]; omega
  · dsimp only; omega
  · dsimp only; omega

set_option maxHeartbeats 0 in
/-- `Permit.asset_permit_body` with free pointer `0x140`, a memory of size `S` from `320` to
`800` bytes and gas below `2²⁵⁶`. -/
theorem pl_body_small_limit {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {S : Nat}
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
    (hdepth : Gas.stackDepthLimit < m.frame.msg.depth + 1)
    (hstatic : m.frame.msg.isStatic = false) :
    WP m (fun _ => False) (fun _ o => ∃ out, o = .revert out) := by
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
    refine pl_tail_limit _ (t := 0) rfl hj rfl rfl rfl ?_ ?_ ?_ ?_
      (by dsimp only; rw [World.code_sstore]; exact hdel1) hdepth
    · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
        Memory.loadWord_storeWord]
    · simp only [permit_norm, hM3b]
    · dsimp only; omega
    · dsimp only; omega


set_option maxHeartbeats 0 in
/-- From `permit`'s body (`0x0566`) in a static frame, with free pointer `0x140` and any memory of
`S ≥ 320` bytes: the nonce's `SSTORE` halts. -/
theorem pl_body_static {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {S : Nat}
    {ds deadline value v r s : Word} {owner spender : Address}
    (hS : 320 ≤ S) (hS32 : S % 32 = 0)
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1382)
    (hs : m.frame.stack = [ds, 1#256, 0#256, s, r, v, deadline, value, Word.ofAddress spender,
      Word.ofAddress owner, 424#256, 3573918927#256])
    (hmem : m.frame.memory = M) (hM64 : M.loadWord 64 = 320#256) (hMs : M.size = S)
    (hg : 90000 ≤ m.frame.gasLeft) (hstatic : m.frame.msg.isStatic = true) :
    WP m (fun _ => False) (fun _ o => QEDefi.ERC20.Spec.Fails o) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs hmem
  have hMsz : m_memory.size = 320 + 32 * ((S - 320) / 32) := by omega
  have hxm : ∀ off len, off + len ≤ 320 → m_memory.expand off len = m_memory :=
    fun _ _ h => bg_expand hMsz (by decide) h
  plwp_run_to 1419 [hM64, hMsz, hxm, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  apply wp_sstore_static
  · pcode_fact
  · exact hstatic
  · intro e; trivial


/-- **`permit`'s body at the call-depth limit, with free pointer `0x140` and any memory of
`S ≥ 320` bytes**: it reverts. -/
theorem pl_body_limit {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {S : Nat}
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
    (hdepth : Gas.stackDepthLimit < m.frame.msg.depth + 1)
    (hstatic : m.frame.msg.isStatic = false) :
    WP m (fun _ => False) (fun _ o => ∃ out, o = .revert out) := by
  by_cases hbig : 832 ≤ S
  · exact pl_body_big_limit m (t := (S - 832) / 32) hc hj hpc hs hmem hM64 (by omega) hv hg hg'
      hstd hdel1 hdepth hstatic
  · refine pl_body_small_limit m (S := S) ?_ hc hj hpc hs hmem hM64 hMs hv hg hg' hstd hdel1
      hdepth hstatic
    omega

end Verified.Solmate.ERC20.Spec
