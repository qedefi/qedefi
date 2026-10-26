import Verified.OpenZeppelin.ERC20.Spec.Dispatch
import Verified.Solmate.ERC4626.UnknownSelectors

/-!
# `ERC20Mock`'s decoders reject malformed arguments

For each entry point of the deployed `ERC20Mock` that writes state (`transfer`, `approve`,
`mint`, `burn`: an `address` and a `uint256`; `transferFrom`: two `address`es and a
`uint256`): too few argument words (`short_halts`) or a dirty `address` argument after clean
ones (`dirty0_halts`, `dirty1_halts`) reverts in solc's ABI decoder, in any fresh frame
without value and with at least 2000 gas.
-/

namespace Verified.OpenZeppelin.ERC20.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.OpenZeppelin.Contracts
open Verified.Solmate.ERC20 (lt_size_four)
open Verified.Solmate.ERC4626 (argWord CleanAddr cleanAddr_lit eq_and_mask_zero iszero_slt_short)

/-- The writing entry points with their argument sizes (bytes after the selector). -/
def writeShapes : List (Nat × Nat) :=
  [(0xa9059cbb, 64), (0x095ea7b3, 64), (0x40c10f19, 64), (0x9dc29fac, 64), (0x23b872dd, 96)]

set_option maxHeartbeats 0 in
/-- **Too few argument words revert.** -/
theorem short_halts {sel n : Nat} (hsh : (sel, n) ∈ writeShapes) (m : Machine)
    (hf : Fresh OzAsset.runtimeCode m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (hsize : 4 ≤ m.frame.msg.data.size) (hshort : m.frame.msg.data.size < 4 + n)
    (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hsel' := Dispatch.selector_eq hsel
  simp only [writeShapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hsh
  rcases hsh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
    have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 _))
        = 0 := iszero_slt_short hsize hshort (by decide)
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
    exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- **A dirty first `address` argument reverts.** -/
theorem dirty0_halts {sel n : Nat} (hsh : (sel, n) ∈ writeShapes) (m : Machine)
    (hf : Fresh OzAsset.runtimeCode m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (hsize : 4 + n ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 0) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  simp only [writeShapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hsh
  rcases hsh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 _))
        = 1 := iszero_slt_calldatasize hsize (by omega)
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
    exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- **`transferFrom` with a clean first and a dirty second `address` argument reverts.** -/
theorem dirty1_halts (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd)
    (hsize : 100 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc0 : CleanAddr m.frame.msg.data 0) (hd : ¬ CleanAddr m.frame.msg.data 1)
    (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hc0' := cleanAddr_lit hc0
  simp only [argWord] at hc0'
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', hc0', Solidity.eq_self]
  exact ⟨_, rfl⟩

end Verified.OpenZeppelin.ERC20.Spec.Malformed
