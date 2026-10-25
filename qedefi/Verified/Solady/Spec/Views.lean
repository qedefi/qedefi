import Verified.Solady.Spec.Common
import Verified.Solady.Spec.Rows

/-!
# Solady `ERC20` under the spec: the views
-/

namespace Verified.Solady.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open EvmLean.Interpreter EvmLogic.Tactic Verified.Solady.Contracts Verified.Solady.Spec.AnyGas

/-- A view's code-level end: success with the word `x`, nothing changed, no value. -/
def ViewPost (m : Machine) (x : Word) (mf : Machine) (o : Outcome) : Prop :=
  m.frame.msg.value = 0 ∧ o = .success (Bytes.ofWord x) ∧ mf.world = m.world ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs

set_option maxHeartbeats 0 in
theorem balanceOf_low (m : Machine) (a : Address)
    (hf : Fresh SoladyToken.runtimeCode m) (hd : Args m.frame.msg.data 0x70a08231 [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto a))) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at harg0
  hwp_steps [hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0,
    ofAddress_and_addressMask, Solidity.eq_self]
  rw [read_row _ a balSeed]
  rotate_left
  · decide
  · simp only [Memory.read_storeWord]
  · rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
      read_storeWord_slice' _ 12 20 12 32 _ (by omega) rfl]
    rfl
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
    ⟨eq_zero_of_iszero_ne (x := m_msg.value) ‹_›, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm [balSlot]

set_option maxHeartbeats 0 in
theorem allowance_low (m : Machine) (o sp : Address)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0xdd62ed3e [Word.ofAddress o, Word.ofAddress sp])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (if sp = PERMIT2 then BitVec.ofNat 256 QEDefi.Math.MAX else
      m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto o sp))) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0 harg1
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
    Nat.mul_one] at harg0 harg1
  hwp_steps [hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
    ofAddress_and_addressMask, Solidity.eq_self]
  · have hp := (permit2_test sp).mp ‹_›
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
    simp only [outputData, hp, ↓reduceIte]
    apwp_norm []
    rfl
  · have hp : sp ≠ PERMIT2 := fun h => ‹Word.ofAddress sp + _ ≠ 0› ((permit2_test sp).mpr h)
    rw [read_allowRow _ o sp allowSeed]
    rotate_left
    · decide
    · simp only [Memory.read_storeWord]
    · rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
        read_storeWord_slice' _ 12 20 12 32 _ (by omega) rfl]
      rfl
    · rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
        Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
        read_storeWord_slice' _ 32 12 20 44 _ (by omega) rfl]
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
    simp only [outputData, hp, ↓reduceIte]
    apwp_norm [allowSlot]

set_option maxHeartbeats 0 in
theorem totalSupply_low (m : Machine) (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0x18160ddd []) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (m.world.sload m.frame.msg.currentTarget supplySlot)) := by
  intro H hF hok
  obtain ⟨hsel, hsize, -⟩ := hd
  simp only [List.length_nil] at hsize
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm [supplySlot]
  rfl

set_option maxHeartbeats 0 in
theorem totalSupply_high (m : Machine) (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0x18160ddd []) (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ViewPost m (m.world.sload m.frame.msg.currentTarget supplySlot)) := by
  obtain ⟨hsel, hsize, -⟩ := hd
  simp only [List.length_nil] at hsize
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64]
  refine ⟨hval, ?_, rfl, rfl, rfl, rfl⟩
  rfl

set_option maxHeartbeats 0 in
theorem balanceOf_high (m : Machine) (a : Address)
    (hf : Fresh SoladyToken.runtimeCode m) (hd : Args m.frame.msg.data 0x70a08231 [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ViewPost m (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto a))) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at harg0
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, hok,
    ofAddress_and_addressMask, Solidity.eq_self]
  sorry

end Verified.Solady.Spec
