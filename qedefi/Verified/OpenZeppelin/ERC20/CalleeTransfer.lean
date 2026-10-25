import Verified.OpenZeppelin.ERC20.Callee
import EvmLogic.Tactic.Patched

/-!
# `OzAsset.balanceOf` and `OzAsset.transfer` in any frame

Callee summaries (`Halts`, for `WP.call`/`WP.staticcall`) of `balanceOf(a)` and
`transfer(dst, amount)` of the deployed `ERC20Mock`, in any fresh frame.
-/

namespace Verified.OpenZeppelin.ERC20
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Solidity.ERC20
open EvmLean.Interpreter EvmLogic.Tactic QEDefi.ERC4626 Verified.OpenZeppelin.Contracts
open Verified.Solmate.ERC20 (TwoWordCall Reverts lt_size_four)

set_option maxHeartbeats 0 in
/-- **`balanceOf(a)`, in any frame.** -/
theorem balanceOf_halts (m : Machine) (hf : Fresh OzAsset.runtimeCode m) (a : Address)
    (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x70a08231)
    (hsize : 36 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress a)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (BalanceOfPost a m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only [outputMachine]
  evm_gas

set_option maxHeartbeats 0 in
/-- **`transfer(dst, amount)`, success**, in any non-static frame: nonzero caller and `dst`,
`amount ≤ balanceOf[caller]`. -/
theorem transfer_halts_ok (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {dst : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hc : m.frame.msg.caller ≠ 0) (hdst : dst ≠ 0)
    (hbal : amount.toNat ≤ ((assetView m).balanceOf m.frame.msg.caller).toNat) :
    Halts m (TransferOk dst amount m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hc' := ofAddress_ne_zero hc
  have hd' := ofAddress_ne_zero hdst
  simp only [view, balanceSlot_oz] at hbal
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [(Word.lt_eq_zero_iff _ _).2 hbal]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine ⟨rfl, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [outputMachine, moveWorld, balanceSlot_oz]
  · dsimp only [outputMachine]
    event_log [amount]
  · dsimp only [outputMachine]
    evm_gas

set_option maxHeartbeats 0 in
/-- **`transfer(dst, amount)`, revert**, in any frame, when `Model.ozTransfer` fails
(`ERC20InvalidSender`, `ERC20InvalidReceiver`, `ERC20InsufficientBalance`). -/
theorem transfer_halts_revert (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) {dst : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 10000 ≤ m.frame.gasLeft)
    (hm : Model.ozTransfer (assetView m) m.frame.msg.caller dst amount = none) :
    Halts m (Reverts 10000 m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  unfold Model.ozTransfer at hm
  by_cases hc : m.frame.msg.caller = 0
  · have hc' : Word.ofAddress m.frame.msg.caller = 0#256 := by rw [hc]; rfl
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, hc',
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    refine ⟨⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]
    evm_gas
  have hc' := ofAddress_ne_zero hc
  by_cases hdst : dst = 0
  · subst hdst
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, ofAddress_zero,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    refine ⟨⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]
    evm_gas
  have hd' := ofAddress_ne_zero hdst
  simp only [hc, hdst, ↓reduceIte] at hm
  have hbal : ((assetView m).balanceOf m.frame.msg.caller).toNat < amount.toNat := by
    unfold Model.transfer at hm
    split at hm
    · cases hm
    · omega
  simp only [view, balanceSlot_oz] at hbal
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [(Word.lt_eq_one_iff _ _).2 hbal]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine ⟨⟨_, rfl⟩, ?_⟩
  dsimp only [outputMachine]
  evm_gas

end Verified.OpenZeppelin.ERC20
