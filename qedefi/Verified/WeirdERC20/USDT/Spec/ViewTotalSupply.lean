import Verified.WeirdERC20.USDT.Spec.ViewOut

/-!
# USDT `totalSupply()` on the lift
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.WeirdERC20.USDT.Contracts EvmLogic.Program.Nested EvmLogic.GasMono
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math


set_option maxHeartbeats 0 in
set_option pwp.chunk 0 in
/-- **`totalSupply()`** on the lift: slot 1. -/
theorem totalSupply_high (m : Machine) (hf : Fresh USDT.runtimeCode m) (d : Nat)
    (hg : g₀ ≤ m.frame.gasLeft + d) (hsel : Abi.selectorOf m.frame.msg.data = 0x18160ddd)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hdep : m.frame.msg.value = 0 →
      deprecatedField.get (m.world.sload m.frame.msg.currentTarget 10#256) = 0) :
    WP (lift patchedCode d m) (fun mh' => mh'.frame.pc ∉ patchPcs ∧
      ExitsWith (ViewOut (m.world.sload m.frame.msg.currentTarget supplySlot) m) mh')
      (fun _ _ => False) := by
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  simp only [deprecatedField_get] at hdep
  simp only [g₀] at hg
  by_cases hval : m.frame.msg.value = 0
  · have hdep := hdep hval
    lift_intro
    usdt_run [hval, hsel', hlt, Memory.read_64, div_selector, expCost_20, expCost_0]
    simp only [hdep]
    usdt_run []
    usdt_return
    exact .inl ⟨hval, rfl, rfl, rfl, rfl, rfl⟩
  · have hz := iszero_value hval
    lift_intro
    usdt_run [hz, hsel', hlt, Memory.read_64, div_selector]
    usdt_revert
    exact .inr ⟨hval, trivial⟩


end Verified.WeirdERC20.USDT.Spec
