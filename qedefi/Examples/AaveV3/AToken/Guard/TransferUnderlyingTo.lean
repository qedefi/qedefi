import Examples.AaveV3.AToken.Basic

/-!
# `AToken.transferUnderlyingTo`: only the Pool

`transferUnderlyingTo(address,uint256)` (selector `0x4efecaa5`) is `onlyPool`. solc decodes the arguments before the modifier,
so with a non-Pool caller the frame reverts with `CallerMustBePool()` when the calldata is
well formed (`transferUnderlyingTo_reverts_of_not_pool`), and with empty data when it is not (too short, a dirty
address word) or when value is sent (every AToken function is non-payable). In every case
nothing changes (`transferUnderlyingTo_noEffect_of_not_pool`, any calldata with the selector, any value).
-/

namespace Examples.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Examples.AaveV3.Contracts
open Examples.Solmate.ERC20 (lt_size_four)

set_option maxHeartbeats 0 in
/-- **`transferUnderlyingTo` from a non-Pool caller, well-formed calldata**: the frame reverts with
`CallerMustBePool()` and changes nothing. Calldata of at least 68 bytes with the selector and its address arguments clean (what the ABI decoder accepts);
no value. -/
theorem transferUnderlyingTo_reverts_of_not_pool (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0x4efecaa5)
    (hsize : 68 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    {a : Address}
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress a)
    (hc : m.frame.msg.caller ≠ pool) (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (RevertsWith callerMustBePool 3000 m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
      (BitVec.ofNat 256 64)) = 1 := iszero_slt_calldatasize (by omega) (by omega)
  have hc' := poolWord_eq_caller hc
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, hc',
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [read_callerMustBePool]
  · dsimp only [outputMachine]
    evm_gas

set_option maxHeartbeats 0 in
/-- **`transferUnderlyingTo` from a non-Pool caller, any calldata and value**: the frame reverts and changes
nothing (calldata with the selector `0x4efecaa5`). -/
theorem transferUnderlyingTo_noEffect_of_not_pool (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x4efecaa5) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc : m.frame.msg.caller ≠ pool) (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (NoEffect 3000 m) := by
  by_cases hval : m.frame.msg.value ≠ 0
  · apply WP.halts_of_false
    have hv := iszero_of_ne hval
    fresh_intro
    pwp_steps [hv]
    exact ⟨⟨_, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, by dsimp only [outputMachine]; evm_gas⟩
  replace hval : m.frame.msg.value = 0 := Classical.not_not.1 hval
  by_cases h4 : m.frame.msg.data.size < 4
  · apply WP.halts_of_false
    have hlt := lt_size_four_one h4
    fresh_intro
    pwp_steps [hval, hlt]
    exact ⟨⟨_, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, by dsimp only [outputMachine]; evm_gas⟩
  by_cases hs : m.frame.msg.data.size < 68
  · apply WP.halts_of_false
    have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
    have hsel' := Dispatch.selector_eq hsel
    have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
        (BitVec.ofNat 256 64)) = 0 := iszero_slt_calldatasize_short (by omega) (by omega) (by omega)
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
    exact ⟨⟨_, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, by dsimp only [outputMachine]; evm_gas⟩
  by_cases h0 : IsAddressArg m.frame.msg.data 4
  · obtain ⟨_, h0a⟩ := h0
    exact (transferUnderlyingTo_reverts_of_not_pool m hf hval hsel (by omega) hsize' h0a hc hg).mono
      fun _ _ _ h => h.noEffect
  · apply WP.halts_of_false
    have hx := eq_and_addressMask_of_not h0
    have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
    have hsel' := Dispatch.selector_eq hsel
    have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
        (BitVec.ofNat 256 64)) = 1 := iszero_slt_calldatasize (by omega) (by omega)
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hx,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    exact ⟨⟨_, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, by dsimp only [outputMachine]; evm_gas⟩

end Examples.AaveV3.AToken
