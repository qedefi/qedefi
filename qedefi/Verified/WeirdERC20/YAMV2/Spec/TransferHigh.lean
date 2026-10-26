import Verified.WeirdERC20.YAMV2.Spec.Transfer

/-!
# YAMv2 under the spec: `transfer` with enough gas

The exact run of `transfer(to, v)`: every revert (zero sender or recipient, amount above the
balance, overflowing credit) and the success.
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.YAMV2.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626
open Verified.WeirdERC20.AMPL.Spec (iszero_lt_size ampl_addr_ne')

set_option maxHeartbeats 0 in
theorem transfer_high (m : Machine) (dst : Address) (v : Word) (hf : Fresh YAMV2.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa9059cbb [Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (TransferPost m dst v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hc0 : m_msg.caller = 0
  · have hcw0 : Word.ofAddress m_msg.caller = 0 := by rw [hc0]; rfl
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hcw0, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self,
      loadWord_write_of_disjoint, Memory.read_write_of_disjoint, size_readBytes, Memory.size_write]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun h => absurd hc0 h⟩
  have hcw := ofAddress_ne_zero hc0
  by_cases hd0 : dst = 0
  · subst hd0
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hcw, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self,
      loadWord_write_of_disjoint, Memory.read_write_of_disjoint, size_readBytes, Memory.size_write]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ h => absurd rfl h⟩
  have hdw := ofAddress_ne_zero hd0
  pwp_xrun_to 2568 [hval, hst, hsel', hz, hl, harg0, harg1, hcw, hdw, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self,
    loadWord_write_of_disjoint, Memory.read_write_of_disjoint, size_readBytes, Memory.size_write]
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
  by_cases hsb : v.toNat ≤
      (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto m_msg.caller)).toNat
  swap
  · have hgt := Verified.Solady.Spec.iszero_gt_of_lt (v := v)
      (b := m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto m_msg.caller)) (by omega)
    simp only [balSlot, mappingSlot] at hgt
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hcw, hdw, hgt, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ h => absurd h hsb⟩
  have hgt := Verified.Solady.Spec.iszero_gt_of_le (v := v)
    (b := m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto m_msg.caller)) hsb
  simp only [balSlot, mappingSlot] at hgt
  by_cases hfit : ((debitWorld m_ctx.crypto m_world m_msg.currentTarget m_msg.caller v).sload
      m_msg.currentTarget (balSlot m_ctx.crypto dst)).toNat + v.toNat < 2 ^ 256
  swap
  · have h3 := Verified.WeirdERC20.AMPL.Spec.ampl_add_lt_zero (S := v)
      (v := (debitWorld m_ctx.crypto m_world m_msg.currentTarget m_msg.caller v).sload
        m_msg.currentTarget (balSlot m_ctx.crypto dst)) (by omega)
    simp only [debitWorld, balSlot, mappingSlot] at h3
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hcw, hdw, hgt, h3,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
      Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ _ h => absurd h hfit⟩
  have h3 := Verified.WeirdERC20.AMPL.Spec.ampl_add_lt_one (S := v)
    (v := (debitWorld m_ctx.crypto m_world m_msg.currentTarget m_msg.caller v).sload
      m_msg.currentTarget (balSlot m_ctx.crypto dst)) (by omega)
  simp only [debitWorld, balSlot, mappingSlot] at h3
  pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hcw, hdw, hgt, h3,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
    Abi.shr_calldataload_zero, Solidity.eq_self]
  refine ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ => ⟨hval, hst, rfl, ?_, rfl, rfl, ?_⟩⟩
  · rcases h with h | h | h
    · exact absurd h hc0
    · exact absurd h hd0
    · exact absurd (Nat.lt_of_lt_of_le h hsb) (Nat.lt_irrefl _)
  · simp only [outputMachine]
    rfl
  · simp only [outputMachine]
    logs_simp []
    event_log [v]

end Verified.WeirdERC20.YAMV2.Spec
