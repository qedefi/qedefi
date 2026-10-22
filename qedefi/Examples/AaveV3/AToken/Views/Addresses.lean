import Examples.AaveV3.AToken.State

/-!
# `AToken`: the address getters, and non-payability

In any fresh frame: `POOL()`, `TREASURY()`, `RESERVE_TREASURY_ADDRESS()`, `REWARDS_CONTROLLER()`
return the immutables, `UNDERLYING_ASSET_ADDRESS()` the low 160 bits of slot 61; nothing
changes. Every AToken function is non-payable: `noEffect_of_value` (any calldata, value ≠ 0:
revert with empty data, nothing changed).
-/

namespace Examples.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Examples.AaveV3.Contracts
open Examples.Solmate.ERC20 (lt_size_four)

/-! ## Non-payable -/

/-- **Every function is non-payable**: with value, any calldata reverts (empty data) and
changes nothing. -/
theorem noEffect_of_value (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value ≠ 0) (hg : 100 ≤ m.frame.gasLeft) :
    Halts m (NoEffect 100 m) := by
  apply WP.halts_of_false
  have hv := iszero_of_ne hval
  fresh_intro
  pwp_steps [hv]
  exact ⟨⟨_, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, by dsimp only [outputMachine]; evm_gas⟩

/-! ## Addresses -/

/-- **`POOL()`** returns the Pool proxy; nothing changes. -/
theorem POOL_halts (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0x7535d246)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 1000 ≤ m.frame.gasLeft) :
    Halts m (Returns (Bytes.ofWord (Word.ofAddress pool)) 1000 m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64]
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · rfl
  · dsimp only [outputMachine]
    evm_gas

/-- **`TREASURY()`** returns `treasury`; nothing changes. -/
theorem TREASURY_halts (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0x2d2c5565)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 1000 ≤ m.frame.gasLeft) :
    Halts m (Returns (Bytes.ofWord (Word.ofAddress treasury)) 1000 m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64]
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · rfl
  · dsimp only [outputMachine]
    evm_gas

/-- **`RESERVE_TREASURY_ADDRESS()`** returns `treasury`; nothing changes. -/
theorem RESERVE_TREASURY_ADDRESS_halts (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0xae167335)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 1000 ≤ m.frame.gasLeft) :
    Halts m (Returns (Bytes.ofWord (Word.ofAddress treasury)) 1000 m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64]
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · rfl
  · dsimp only [outputMachine]
    evm_gas

/-- **`REWARDS_CONTROLLER()`** returns `rewardsController`; nothing changes. -/
theorem REWARDS_CONTROLLER_halts (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0xcd086d45)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 1000 ≤ m.frame.gasLeft) :
    Halts m (Returns (Bytes.ofWord (Word.ofAddress rewardsController)) 1000 m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64]
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · rfl
  · dsimp only [outputMachine]
    evm_gas

/-- **`UNDERLYING_ASSET_ADDRESS()`** returns `underlyingAsset`; nothing changes. -/
theorem UNDERLYING_ASSET_ADDRESS_halts (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0xb16a19de)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (Returns (Bytes.ofWord (underlyingAsset m.world m.frame.msg.currentTarget)) 3000 m) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64]
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [mask160_and_and]; rfl
  · dsimp only [outputMachine]
    evm_gas

end Examples.AaveV3.AToken
