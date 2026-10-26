import Verified.WeirdERC20.USDT.Spec.ViewOut

/-!
# USDT `allowance(o, sp)` on the lift
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.WeirdERC20.USDT.Contracts EvmLogic.Program.Nested EvmLogic.GasMono
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math


set_option maxHeartbeats 0 in
set_option pwp.chunk 0 in
/-- **`allowance(o, sp)`** on the lift: the `allowed[o][sp]` row. -/
theorem allowance_high (m : Machine) (hf : Fresh USDT.runtimeCode m) (d : Nat) (o sp : Address)
    (hg : g₀ ≤ m.frame.gasLeft + d) (hsel : Abi.selectorOf m.frame.msg.data = 0xdd62ed3e)
    (hsize : 68 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress o)
    (harg1 : Bytes.toWord (readBytes m.frame.msg.data 36 32) = Word.ofAddress sp)
    (hdep : m.frame.msg.value = 0 →
      deprecatedField.get (m.world.sload m.frame.msg.currentTarget 10#256) = 0) :
    WP (lift patchedCode d m) (fun mh' => mh'.frame.pc ∉ patchPcs ∧
      ExitsWith (ViewOut (m.world.sload m.frame.msg.currentTarget
        (mappingSlot2 m.ctx.crypto (Word.ofAddress o) (Word.ofAddress sp) allowedSlot)) m) mh')
      (fun _ _ => False) := by
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  simp only [deprecatedField_get] at hdep
  simp only [g₀] at hg
  by_cases hval : m.frame.msg.value = 0
  · have hdep := hdep hval
    lift_intro
    usdt_run [hval, hsel', hlt, Memory.read_64, div_selector, expCost_20, expCost_0, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress]
    simp only [hdep]
    usdt_run [ofAddress_and_addressMask, addressMask_and_ofAddress, expCost_20, expCost_0,
      Memory.read_64]
    usdt_return
    refine .inl ⟨hval, ?_, rfl, rfl, rfl, rfl⟩
    simp only [mappingSlot2, mappingSlot, allowedSlot]
    rfl
  · have hz := iszero_value hval
    lift_intro
    usdt_run [hz, hsel', hlt, Memory.read_64, div_selector]
    usdt_revert
    exact .inr ⟨hval, trivial⟩

end Verified.WeirdERC20.USDT.Spec
