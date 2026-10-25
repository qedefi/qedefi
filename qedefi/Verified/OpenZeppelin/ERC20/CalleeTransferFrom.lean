import Verified.OpenZeppelin.ERC20.Callee
import Verified.Solmate.ERC20.TransferFrom
import EvmLogic.Tactic.Patched

/-!
# `OzAsset.transferFrom` in any frame

`transferFrom(src, dst, amount)` of the deployed `ERC20Mock` from the spender `caller`:
`_spendAllowance(src, caller, amount)` (nothing on an infinite allowance, otherwise a checked
subtraction written back by `_approve`, whose zero-address checks apply, without an event),
then `_transfer(src, dst, amount)`. `TransferFromCond` is the exact success condition, stated on
the storage (no hash hypothesis: the balance is read after the allowance write); success gives
`ozTransferFromWorld` and the single log `Transfer(src, dst, amount)`, otherwise it reverts.
-/

namespace Verified.OpenZeppelin.ERC20
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Solidity.ERC20
open EvmLean.Interpreter EvmLogic.Tactic QEDefi.ERC4626 Verified.OpenZeppelin.Contracts
open Verified.Solmate.ERC20 (ThreeWordCall Reverts lt_size_four)

/-- When `transferFrom(src, dst, amount)` from `m`'s caller succeeds: the allowance is
infinite, or covers `amount` with a nonzero spender (`_approve`); `src`, `dst` are nonzero;
the balance of `src` after the allowance step covers `amount`. -/
def TransferFromCond (m : Machine) (src dst : Address) (amount : Word) : Prop :=
  (m.world.sload m.frame.msg.currentTarget
      (allowanceSlot m.ctx.crypto Layout.oz src m.frame.msg.caller) = maxWord ∨
    (amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (allowanceSlot m.ctx.crypto Layout.oz src m.frame.msg.caller)).toNat ∧
      m.frame.msg.caller ≠ 0)) ∧
  src ≠ 0 ∧ dst ≠ 0 ∧
  amount.toNat ≤ ((ozSpendWorld m.ctx.crypto Layout.oz m.world m.frame.msg.currentTarget src
    m.frame.msg.caller amount).sload m.frame.msg.currentTarget
      (balanceSlot m.ctx.crypto Layout.oz src)).toNat

/-- `lt_maxWord_of_eq` with `type(uint256).max` as the literal symbolic execution leaves. -/
theorem lt_maxLit_of_eq {a : Word} (h : a = maxWord) :
    Word.lt a 115792089237316195423570985008687907853269984665640564039457584007913129639935#256 = 0#256 := lt_maxWord_of_eq h

/-- `lt_maxWord_of_ne` with `type(uint256).max` as the literal symbolic execution leaves. -/
theorem lt_maxLit_of_ne {a : Word} (h : a ≠ maxWord) :
    Word.lt a 115792089237316195423570985008687907853269984665640564039457584007913129639935#256 = 1#256 := lt_maxWord_of_ne h

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- **`transferFrom(src, dst, amount)`, success**, in any non-static frame. -/
theorem transferFrom_halts_ok (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src dst : Address}
    {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (h : TransferFromCond m src dst amount) :
    Halts m (TransferFromOk src dst amount m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  obtain ⟨hspend, hs, hdst, hbal⟩ := h
  have hs' := ofAddress_ne_zero hs
  have hd' := ofAddress_ne_zero hdst
  simp only [ozSpendWorld, allowanceWorld, allowanceSlot_oz, balanceSlot_oz] at hspend hbal
  by_cases hmax : m.world.sload m.frame.msg.currentTarget (m.ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress m.frame.msg.caller) ++ Bytes.ofWord (m.ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 1#256)))) = maxWord
  · simp only [hmax, ↓reduceIte] at hbal
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [lt_maxLit_of_eq hmax]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [(Word.lt_eq_zero_iff _ _).2 hbal]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine ⟨rfl, ?_, rfl, rfl, ?_, ?_⟩
    · simp only [outputMachine, ozTransferFromWorld, ozSpendWorld, moveWorld,
        allowanceSlot_oz, balanceSlot_oz, hmax, ↓reduceIte]
    · dsimp only [outputMachine]
      event_log [amount]
    · dsimp only [outputMachine]
      evm_gas
  · simp only [hmax, ↓reduceIte, false_or] at hbal hspend
    obtain ⟨hle, hc⟩ := hspend
    have hc' := ofAddress_ne_zero hc
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [lt_maxLit_of_ne hmax]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [(Word.lt_eq_zero_iff _ _).2 hle]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [(Word.lt_eq_zero_iff _ _).2 hbal]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine ⟨rfl, ?_, rfl, rfl, ?_, ?_⟩
    · simp only [outputMachine, ozTransferFromWorld, ozSpendWorld, allowanceWorld, moveWorld,
        allowanceSlot_oz, balanceSlot_oz, hmax, ↓reduceIte]
    · dsimp only [outputMachine]
      event_log [amount]
    · dsimp only [outputMachine]
      evm_gas

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- **`transferFrom(src, dst, amount)`, revert**, in any non-static frame, when
`TransferFromCond` fails (`ERC20InsufficientAllowance`, `ERC20InvalidApprover`,
`ERC20InvalidSpender`, `ERC20InvalidSender`, `ERC20InvalidReceiver`,
`ERC20InsufficientBalance`). -/
theorem transferFrom_halts_revert (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src dst : Address}
    {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (hfail : ¬ TransferFromCond m src dst amount) :
    Halts m (Reverts 80000 m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  unfold TransferFromCond at hfail
  simp only [ozSpendWorld, allowanceWorld, allowanceSlot_oz, balanceSlot_oz] at hfail
  by_cases hmax : m.world.sload m.frame.msg.currentTarget (m.ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress m.frame.msg.caller) ++ Bytes.ofWord (m.ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 1#256)))) = maxWord
  · simp only [hmax, true_or, true_and, ↓reduceIte] at hfail
    by_cases hs : src = 0
    · subst hs
      simp only [ofAddress_zero] at hmax
      fresh_intro
      pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, ofAddress_zero,
        ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
      simp only [lt_maxLit_of_eq hmax]
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64, ofAddress_zero]
      refine ⟨⟨_, rfl⟩, ?_⟩
      dsimp only [outputMachine]
      evm_gas
    have hs' := ofAddress_ne_zero hs
    by_cases hdst : dst = 0
    · subst hdst
      fresh_intro
      pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, ofAddress_zero,
        ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
      simp only [lt_maxLit_of_eq hmax]
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64, ofAddress_zero]
      refine ⟨⟨_, rfl⟩, ?_⟩
      dsimp only [outputMachine]
      evm_gas
    have hd' := ofAddress_ne_zero hdst
    have hbal := Nat.lt_of_not_le fun h => hfail ⟨hs, hdst, h⟩
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [lt_maxLit_of_eq hmax]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [(Word.lt_eq_one_iff _ _).2 hbal]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine ⟨⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]
    evm_gas
  simp only [hmax, false_or, ↓reduceIte] at hfail
  rcases Nat.lt_or_ge (m.world.sload m.frame.msg.currentTarget (m.ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress m.frame.msg.caller) ++ Bytes.ofWord (m.ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 1#256))))).toNat amount.toNat with
    hlt' | hle
  · fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [lt_maxLit_of_ne hmax]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [(Word.lt_eq_one_iff _ _).2 hlt']
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine ⟨⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]
    evm_gas
  by_cases hs : src = 0
  · subst hs
    simp only [ofAddress_zero] at hmax hle
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, ofAddress_zero,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [lt_maxLit_of_ne hmax]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64, ofAddress_zero]
    simp only [(Word.lt_eq_zero_iff _ _).2 hle]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64, ofAddress_zero]
    refine ⟨⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]
    evm_gas
  have hs' := ofAddress_ne_zero hs
  by_cases hc : m.frame.msg.caller = 0
  · have hc' : Word.ofAddress m.frame.msg.caller = 0#256 := by rw [hc]; rfl
    simp only [hc'] at hmax hle
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, hc',
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [lt_maxLit_of_ne hmax]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64, hc']
    simp only [(Word.lt_eq_zero_iff _ _).2 hle]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64, hc']
    refine ⟨⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]
    evm_gas
  have hc' := ofAddress_ne_zero hc
  by_cases hdst : dst = 0
  · subst hdst
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, ofAddress_zero,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [lt_maxLit_of_ne hmax]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64, ofAddress_zero]
    simp only [(Word.lt_eq_zero_iff _ _).2 hle]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64, ofAddress_zero]
    refine ⟨⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]
    evm_gas
  have hd' := ofAddress_ne_zero hdst
  have hbal := Nat.lt_of_not_le fun h => hfail ⟨⟨hle, hc⟩, hs, hdst, h⟩
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [lt_maxLit_of_ne hmax]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  simp only [(Word.lt_eq_zero_iff _ _).2 hle]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  simp only [(Word.lt_eq_one_iff _ _).2 hbal]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine ⟨⟨_, rfl⟩, ?_⟩
  dsimp only [outputMachine]
  evm_gas

end Verified.OpenZeppelin.ERC20
