import Verified.Solady.Spec.Transfer

/-!
# Solady `ERC20` under the spec: `mint` and `burn` (`SoladyToken`'s open entry points)
-/

namespace Verified.Solady.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open EvmLean.Interpreter EvmLogic.Tactic Verified.Solady.Contracts Verified.Solady.Spec.AnyGas
open QEDefi.ERC4626

set_option maxHeartbeats 0 in
theorem mint_low (m : Machine) (dst : Address) (v : Word)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0x40c10f19 [Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) (P : Machine → Outcome → Prop) :
    LowHalts m P := by
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
  all_goals
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    try simp (disch := simp (disch := decide) only [Memory.read_expand,
      Memory.read_storeWord_of_disjoint, read_seed_tail]) only [read_balRow] at *
  trace_state
  all_goals sorry

set_option maxHeartbeats 0 in
theorem burn_low (m : Machine) (src : Address) (v : Word)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0x9dc29fac [Word.ofAddress src, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) (P : Machine → Outcome → Prop) :
    LowHalts m P := by
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
  all_goals
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    try simp (disch := simp (disch := decide) only [Memory.read_expand,
      Memory.read_storeWord_of_disjoint, read_seed_tail]) only [read_balRow] at *
  trace_state
  all_goals sorry

end Verified.Solady.Spec
