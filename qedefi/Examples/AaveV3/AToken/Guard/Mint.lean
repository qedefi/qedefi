import Examples.AaveV3.AToken.Basic

/-!
# `AToken.mint`: only the Pool

`mint(address,address,uint256,uint256)` (selector `0xb3f1c93d`) is `onlyPool`. solc decodes the
arguments before the modifier, so with a non-Pool caller the frame reverts with `CallerMustBePool()`
when the calldata is well formed (`mint_reverts_of_not_pool`), and with empty data when it is not
(too short, a dirty address word) or when value is sent (every AToken function is non-payable). In
every case nothing changes (`mint_noEffect_of_not_pool`, any calldata with the selector, any value).
-/

namespace Examples.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Examples.AaveV3.Contracts
open Examples.Solmate.ERC20 (lt_size_four)

/-- **`mint` from a non-Pool caller, well-formed calldata**: the frame reverts with
`CallerMustBePool()` and changes nothing. Calldata of at least 132 bytes with the selector and its
address arguments clean (what the ABI decoder accepts); no value. -/
theorem mint_reverts_of_not_pool (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0xb3f1c93d)
    (hsize : 132 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    {a b : Address}
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress a)
    (harg1 : Bytes.toWord (readBytes m.frame.msg.data 36 32) = Word.ofAddress b)
    (hc : m.frame.msg.caller ≠ pool) (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (RevertsWith callerMustBePool 3000 m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
      (BitVec.ofNat 256 128)) = 1 := iszero_slt_calldatasize (by omega) (by omega)
  have hc' := poolWord_eq_caller hc
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, hc',
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [read_callerMustBePool]
  · dsimp only [outputMachine]
    evm_gas

/-- **`mint` from a non-Pool caller, any calldata and value**: the frame reverts, with at most 4
bytes of data, and changes nothing (calldata with the selector `0xb3f1c93d`). -/
theorem mint_noEffectOut_of_not_pool (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xb3f1c93d) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc : m.frame.msg.caller ≠ pool) (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (NoEffectOut 3000 4 m) := by
  by_cases hval : m.frame.msg.value ≠ 0
  · apply WP.halts_of_false
    have hv := iszero_of_ne hval
    fresh_intro
    pwp_steps [hv]
    exact ⟨⟨_, rfl, by simp⟩, ⟨rfl, rfl, rfl, rfl⟩,
      by dsimp only [outputMachine]; evm_gas⟩
  replace hval : m.frame.msg.value = 0 := Classical.not_not.1 hval
  by_cases h4 : m.frame.msg.data.size < 4
  · apply WP.halts_of_false
    have hlt := lt_size_four_one h4
    fresh_intro
    pwp_steps [hval, hlt]
    exact ⟨⟨_, rfl, by simp⟩, ⟨rfl, rfl, rfl, rfl⟩,
      by dsimp only [outputMachine]; evm_gas⟩
  by_cases hs : m.frame.msg.data.size < 132
  · apply WP.halts_of_false
    have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
    have hsel' := Dispatch.selector_eq hsel
    have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
        (BitVec.ofNat 256 128)) = 0 := iszero_slt_calldatasize_short (by omega) (by omega) (by omega)
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
    exact ⟨⟨_, rfl, by simp⟩, ⟨rfl, rfl, rfl, rfl⟩,
      by dsimp only [outputMachine]; evm_gas⟩
  by_cases h0 : IsAddressArg m.frame.msg.data 4
  · obtain ⟨_, h0a⟩ := h0
    by_cases h1 : IsAddressArg m.frame.msg.data 36
    · obtain ⟨_, h1a⟩ := h1
      exact (mint_reverts_of_not_pool m hf hval hsel (by omega) hsize' h0a h1a hc hg).mono
        fun _ _ _ h => h.noEffectOut (by decide)
    · apply WP.halts_of_false
      have hx := eq_and_addressMask_of_not h1
      have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
      have hsel' := Dispatch.selector_eq hsel
      have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
          (BitVec.ofNat 256 128)) = 1 := iszero_slt_calldatasize (by omega) (by omega)
      fresh_intro
      pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, h0a, hx,
        ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
      exact ⟨⟨_, rfl, by simp⟩, ⟨rfl, rfl, rfl, rfl⟩,
        by dsimp only [outputMachine]; evm_gas⟩
  · apply WP.halts_of_false
    have hx := eq_and_addressMask_of_not h0
    have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
    have hsel' := Dispatch.selector_eq hsel
    have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
        (BitVec.ofNat 256 128)) = 1 := iszero_slt_calldatasize (by omega) (by omega)
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hx,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    exact ⟨⟨_, rfl, by simp⟩, ⟨rfl, rfl, rfl, rfl⟩,
      by dsimp only [outputMachine]; evm_gas⟩

/-- **`mint` from a non-Pool caller, any calldata and value**: the frame reverts and changes
nothing (calldata with the selector `0xb3f1c93d`). -/
theorem mint_noEffect_of_not_pool (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xb3f1c93d) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc : m.frame.msg.caller ≠ pool) (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (NoEffect 3000 m) :=
  (mint_noEffectOut_of_not_pool m hf hsel hsize' hc hg).mono fun _ _ _ h => h.noEffect

end Examples.AaveV3.AToken
