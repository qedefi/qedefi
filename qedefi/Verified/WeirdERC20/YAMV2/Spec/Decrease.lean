import Verified.WeirdERC20.YAMV2.Spec.Ops

/-!
# YAMv2 under the spec: `decreaseAllowance`, the bytecode runs

`decreaseAllowance(sp, x)`: `allowance[caller][sp].sub(x, reason)` (an amount above the
allowance reverts with the reason string), then `_approve(caller, sp, ·)` (a zero caller or
spender reverts). The memory is abstracted after the reason string is copied.
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.YAMV2.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626
open Verified.WeirdERC20.AMPL.Spec (iszero_lt_size ampl_addr_ne')

/-- `decreaseAllowance(sp, x)`'s code-level end. -/
def DecreasePost (m : Machine) (sp : Address) (x : Word) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.value ≠ 0 → ∃ out, o = .revert out) ∧
  (m.frame.msg.caller = 0 ∨ sp = 0 ∨
    (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat
      < x.toNat → ∃ out, o = .revert out) ∧
  (m.frame.msg.caller ≠ 0 → sp ≠ 0 → x.toNat ≤
    (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ (∃ out, o = .success out) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)
      (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp) - x) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem decrease_low (m : Machine) (sp : Address) (x : Word) (hf : Fresh YAMV2.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa457c2d7 [Word.ofAddress sp, x])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (DecreasePost m sp x) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps stop_at [1842] [hsel', hz, harg0, harg1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  wp_abstract memory M hM
  have hM64 : M.loadWord 64 = 224#256 := by
    subst hM; simp [loadWord_write_of_disjoint, Memory.loadWord_storeWord_of_disjoint,
      Memory.loadWord_storeWord]
  have hM128 : M.loadWord 128 = 37#256 := by
    subst hM; simp [loadWord_write_of_disjoint, Memory.loadWord_storeWord]
  clear hM
  hwp_steps [hsel', hz, harg0, harg1, hM64, hM128, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  have hc0 := ampl_addr_ne' (by with_reducible assumption : Word.ofAddress m_msg.caller ≠ 0)
  have hs0 := ampl_addr_ne' (by with_reducible assumption : Word.ofAddress sp ≠ 0)
  have hA0 : (x.gt (m_world.sload m_msg.currentTarget
      (allowSlot m_ctx.crypto m_msg.caller sp))).iszero ≠ 0 := by
    simp only [allowSlot, mappingSlot2, mappingSlot]; with_reducible assumption
  have hA := Verified.Solady.Spec.le_of_iszero_gt hA0
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
    ⟨fun h => absurd hv h, fun h => ?_, fun _ _ _ => ⟨hv, ‹_›, ⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  rcases h with h | h | h
  · exact absurd h hc0
  · exact absurd h hs0
  · dsimp only at h; omega

set_option maxHeartbeats 0 in
theorem decrease_high (m : Machine) (sp : Address) (x : Word) (hf : Fresh YAMV2.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa457c2d7 [Word.ofAddress sp, x])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (DecreasePost m sp x) := by
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
  pwp_xrun_to 1842 [hval, hst, hsel', hz, hl, harg0, harg1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self,
    loadWord_write_of_disjoint, Memory.read_write_of_disjoint, size_readBytes, Memory.size_write]
  wp_abstract memory M hM
  have hMs : M.size = 224 := by
    subst hM; simp [Memory.size_write, Memory.size_expand, Memory.size_storeWord,
      Memory.wordsAfter, Memory.words]
  have hM64 : M.loadWord 64 = 224#256 := by
    subst hM; simp [loadWord_write_of_disjoint, Memory.loadWord_storeWord_of_disjoint,
      Memory.loadWord_storeWord]
  have hM128 : M.loadWord 128 = 37#256 := by
    subst hM; simp [loadWord_write_of_disjoint, Memory.loadWord_storeWord]
  clear hM
  by_cases hA : x.toNat ≤
      (m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto m_msg.caller sp)).toNat
  swap
  · have hgt := Verified.Solady.Spec.iszero_gt_of_lt (v := x)
      (b := m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto m_msg.caller sp)) (by omega)
    simp only [allowSlot, mappingSlot2, mappingSlot] at hgt
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hgt, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ h => absurd h hA⟩
  have hgt := Verified.Solady.Spec.iszero_gt_of_le (v := x)
    (b := m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto m_msg.caller sp)) hA
  simp only [allowSlot, mappingSlot2, mappingSlot] at hgt
  by_cases hc0 : m_msg.caller = 0
  · have hcw0 : Word.ofAddress m_msg.caller = 0#256 := by rw [hc0]; rfl
    rw [hcw0] at hgt
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hgt, hcw0, hMs, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self,
      loadWord_write_of_disjoint, Memory.size_write, size_readBytes]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun h => absurd hc0 h⟩
  have hcw := ofAddress_ne_zero hc0
  by_cases hs0 : sp = 0
  · subst hs0
    rw [show Word.ofAddress (0 : Address) = 0#256 from rfl] at hgt
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hgt, hcw, hMs, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self,
      loadWord_write_of_disjoint, Memory.size_write, size_readBytes]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ h => absurd rfl h⟩
  have hsw := ofAddress_ne_zero hs0
  pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hgt, hcw, hsw, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  refine ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ => ⟨hval, hst, ⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  rcases h with h | h | h
  · exact absurd h hc0
  · exact absurd h hs0
  · dsimp only at h; omega

end Verified.WeirdERC20.YAMV2.Spec
