import Verified.OpenZeppelin.ERC20.Callee
import EvmLogic.Tactic.Patched

/-!
# `OzAsset.approve` in any frame

`approve(spender, amount)` of the deployed `ERC20Mock` (`_approve(caller, spender, amount, true)`):
success with `allowanceWorld` and the `Approval` log, or the zero-address reverts.
-/

namespace Verified.OpenZeppelin.ERC20
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Solidity.ERC20
open EvmLean.Interpreter EvmLogic.Tactic QEDefi.ERC4626 Verified.OpenZeppelin.Contracts
open Verified.Solmate.ERC20 (TwoWordCall Reverts lt_size_four)

set_option maxHeartbeats 0 in
/-- **`approve(spender, amount)`, success**, in any non-static frame: nonzero caller and
`spender`. -/
theorem approve_halts_ok (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {spender : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x095ea7b3 (Word.ofAddress spender) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 40000 ≤ m.frame.gasLeft)
    (hc : m.frame.msg.caller ≠ 0) (hs : spender ≠ 0) :
    Halts m (ApproveOk spender amount m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hc' := ofAddress_ne_zero hc
  have hs' := ofAddress_ne_zero hs
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  refine ⟨rfl, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [outputMachine, allowanceWorld, allowanceSlot_oz]
  · dsimp only [outputMachine]
    event_log [amount]
  · dsimp only [outputMachine]
    evm_gas

set_option maxHeartbeats 0 in
/-- **`approve(spender, amount)`, revert**, in any frame, when `Model.ozApprove` fails
(`ERC20InvalidApprover`, `ERC20InvalidSpender`). -/
theorem approve_halts_revert (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) {spender : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x095ea7b3 (Word.ofAddress spender) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 10000 ≤ m.frame.gasLeft)
    (hm : Model.ozApprove (assetView m) m.frame.msg.caller spender amount = none) :
    Halts m (Reverts 10000 m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  unfold Model.ozApprove at hm
  by_cases hc : m.frame.msg.caller = 0
  · have hc' : Word.ofAddress m.frame.msg.caller = 0#256 := by rw [hc]; rfl
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, hc',
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    refine ⟨⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]
    evm_gas
  have hc' := ofAddress_ne_zero hc
  by_cases hs : spender = 0
  · subst hs
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, ofAddress_zero,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    refine ⟨⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]
    evm_gas
  simp only [hc, hs, ↓reduceIte, reduceCtorEq] at hm

end Verified.OpenZeppelin.ERC20
