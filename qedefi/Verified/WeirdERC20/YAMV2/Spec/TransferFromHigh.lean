import Verified.WeirdERC20.YAMV2.Spec.TransferFrom

/-!
# YAMv2 under the spec: `transferFrom` with enough gas

The exact run of `transferFrom(src, dst, v)`: every revert (zero sender or recipient, amount
above the balance, overflowing credit, amount above the allowance, zero caller) and the success.
The memory is abstracted after each reason string is copied (`wp_abstract`), keeping only its
size, the free-memory pointer and the string's length.
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.YAMV2.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626
open Verified.WeirdERC20.AMPL.Spec (iszero_lt_size ampl_addr_ne')

set_option maxHeartbeats 0 in
theorem transferFrom_high (m : Machine) (src dst : Address) (v : Word)
    (hf : Fresh YAMV2.runtimeCode m)
    (hd : Args m.frame.msg.data 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (TransferFromPost m src dst v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  have harg2 := harg 2 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1 harg2
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 96) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hs0 : src = 0
  · subst hs0
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self,
      loadWord_write_of_disjoint, Memory.read_write_of_disjoint, size_readBytes, Memory.size_write]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun h => absurd rfl h⟩
  have hsw := ofAddress_ne_zero hs0
  by_cases hd0 : dst = 0
  · subst hd0
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hsw, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self,
      loadWord_write_of_disjoint, Memory.read_write_of_disjoint, size_readBytes, Memory.size_write]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ h => absurd rfl h⟩
  have hdw := ofAddress_ne_zero hd0
  pwp_xrun_to 2568 [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hsw, hdw,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
    Abi.shr_calldataload_zero, Solidity.eq_self, loadWord_write_of_disjoint,
    Memory.read_write_of_disjoint, size_readBytes, Memory.size_write]
  wp_abstract memory M hM
  have hMs : M.size = 224 := by
    subst hM; simp [Memory.size_write, Memory.size_expand, Memory.size_storeWord,
      Memory.wordsAfter, Memory.words]
  have hM64 : M.loadWord 64 = 224#256 := by
    subst hM; simp [loadWord_write_of_disjoint, Memory.loadWord_storeWord_of_disjoint,
      Memory.loadWord_storeWord]
  have hM128 : M.loadWord 128 = 38#256 := by
    subst hM; simp [loadWord_write_of_disjoint, Memory.loadWord_storeWord]
  clear hM
  by_cases hsb : v.toNat ≤ (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto src)).toNat
  swap
  · have hgt := Verified.Solady.Spec.iszero_gt_of_lt (v := v)
      (b := m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto src)) (by omega)
    simp only [balSlot, mappingSlot] at hgt
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hsw, hdw, hgt,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
      Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ _ h => absurd h hsb⟩
  have hgt := Verified.Solady.Spec.iszero_gt_of_le (v := v)
    (b := m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto src)) hsb
  simp only [balSlot, mappingSlot] at hgt
  by_cases hfit : ((debitWorld m_ctx.crypto m_world m_msg.currentTarget src v).sload
      m_msg.currentTarget (balSlot m_ctx.crypto dst)).toNat + v.toNat < 2 ^ 256
  swap
  · have h3 := Verified.WeirdERC20.AMPL.Spec.ampl_add_lt_zero (S := v)
      (v := (debitWorld m_ctx.crypto m_world m_msg.currentTarget src v).sload
        m_msg.currentTarget (balSlot m_ctx.crypto dst)) (by omega)
    simp only [debitWorld, balSlot, mappingSlot] at h3
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hsw, hdw, hgt, h3,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
      Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ _ _ h => absurd h hfit⟩
  have h3 := Verified.WeirdERC20.AMPL.Spec.ampl_add_lt_one (S := v)
    (v := (debitWorld m_ctx.crypto m_world m_msg.currentTarget src v).sload
      m_msg.currentTarget (balSlot m_ctx.crypto dst)) (by omega)
  simp only [debitWorld, balSlot, mappingSlot] at h3
  pwp_xrun_to 1248 [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hsw, hdw, hgt, h3,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
    Abi.shr_calldataload_zero, Solidity.eq_self, loadWord_write_of_disjoint,
    Memory.read_write_of_disjoint, size_readBytes, Memory.size_write]
  wp_abstract memory M2 hM2
  have hM2s : M2.size = 320 := by
    subst hM2; simp [Memory.size_write, Memory.size_expand, Memory.size_storeWord,
      Memory.wordsAfter, Memory.words, hMs]
  have hM264 : M2.loadWord 64 = 320#256 := by
    subst hM2; simp [loadWord_write_of_disjoint, Memory.loadWord_storeWord_of_disjoint,
      Memory.loadWord_storeWord]
  have hM2224 : M2.loadWord 224 = 40#256 := by
    subst hM2; simp [loadWord_write_of_disjoint, Memory.loadWord_storeWord_of_disjoint,
      Memory.loadWord_storeWord]
  clear hM2 hMs hM64 hM128
  by_cases hab : v.toNat ≤ ((moveWorld m_ctx.crypto m_world m_msg.currentTarget src dst v).sload
      m_msg.currentTarget (allowSlot m_ctx.crypto src m_msg.caller)).toNat
  swap
  · have hga := Verified.Solady.Spec.iszero_gt_of_lt (v := v)
      (b := (moveWorld m_ctx.crypto m_world m_msg.currentTarget src dst v).sload
        m_msg.currentTarget (allowSlot m_ctx.crypto src m_msg.caller)) (by omega)
    simp only [moveWorld, debitWorld, allowSlot, balSlot, mappingSlot2, mappingSlot] at hga
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hsw, hdw, hgt, h3, hga,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
      Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ _ _ _ =>
      ⟨fun _ => ⟨_, rfl⟩, fun h => absurd h hab⟩⟩
  have hga := Verified.Solady.Spec.iszero_gt_of_le (v := v)
    (b := (moveWorld m_ctx.crypto m_world m_msg.currentTarget src dst v).sload
      m_msg.currentTarget (allowSlot m_ctx.crypto src m_msg.caller)) hab
  simp only [moveWorld, debitWorld, allowSlot, balSlot, mappingSlot2, mappingSlot] at hga
  by_cases hc0 : m_msg.caller = 0
  · have hcw0 : Word.ofAddress m_msg.caller = 0 := by rw [hc0]; rfl
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hsw, hdw, hgt, h3, hga, hcw0,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
      Abi.shr_calldataload_zero, Solidity.eq_self, loadWord_write_of_disjoint,
      Memory.read_write_of_disjoint, size_readBytes, Memory.size_write]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ h => absurd hc0 h⟩
  have hcw := ofAddress_ne_zero hc0
  pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hsw, hdw, hgt, h3, hga, hcw,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
    Abi.shr_calldataload_zero, Solidity.eq_self]
  refine ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ _ =>
    ⟨fun h => absurd (Nat.lt_of_lt_of_le h hab) (Nat.lt_irrefl _),
     fun _ => ⟨hval, hst, rfl, ?_, rfl, rfl, ?_⟩⟩⟩
  · rcases h with h | h | h | h
    · exact absurd h hs0
    · exact absurd h hd0
    · exact absurd h hc0
    · exact absurd (Nat.lt_of_lt_of_le h hsb) (Nat.lt_irrefl _)
  · simp only [outputMachine]
    rfl
  · simp only [outputMachine]
    logs_simp []
    refine congrArg₂ Array.push ?_ ?_
    · event_log [v]
    · rw [approvalLog]
      refine logEntry_eq_eventLog ?_
      event_data
      try rfl

end Verified.WeirdERC20.YAMV2.Spec
