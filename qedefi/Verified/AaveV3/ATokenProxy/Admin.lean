import Verified.AaveV3.ATokenProxy.Basic

/-!
# Aave V3 aToken proxy: the admin's fallback reverts

`admin_reverts`: the admin (the PoolConfigurator) calling the proxy with calldata that selects
none of the proxy's functions gets `_willFallback`'s revert, so it never reaches the
implementation, and nothing changes.
-/

namespace Verified.AaveV3.ATokenProxy
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.AaveV3.Contracts

/-- **The admin cannot reach the implementation.** A fresh frame running the aToken proxy,
called by the admin with calldata that selects none of the proxy's own functions, reverts
(`"Cannot call fallback function from the proxy admin"`) and changes nothing. -/
theorem admin_reverts (m : Machine) (hf : Fresh ATokenProxy.runtimeCode m)
    (hsel : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ proxySelectors)
    (ha : m.frame.msg.caller = admin) (hsize : m.frame.msg.data.size < 2 ^ 64)
    (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (Reverted 2000 m) := by
  have hc' : Word.eq 574988636942314518095395226888196325637651086119#256
      (Word.ofAddress m.frame.msg.caller) = 1#256 := by rw [ha]; exact adminWord_eq_admin
  apply WP.halts_of_false
  by_cases h4 : m.frame.msg.data.size < 4
  · have hlt := lt_size_four_one h4
    fresh_intro
    pwp_steps [hlt, hc', iszero_one, Memory.read_64]
    exact ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl, by dsimp only [outputMachine]; evm_gas⟩
  · have hlt := Verified.Solmate.ERC20.lt_size_four (n := m.frame.msg.data.size) (by omega)
      (by omega)
    obtain ⟨e1, e2, e3, e4, e5⟩ := dispatch_facts (hsel.resolve_left h4)
    by_cases hgt : Abi.selectorOf m.frame.msg.data < 0x5c60da1b
    · have hg' := gt_selector_lt hgt
      fresh_intro
      pwp_steps [hlt, Abi.shr_calldataload_zero, hg', e1, e2, e3, e4, e5, hc', iszero_one,
        Memory.read_64]
      exact ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl, by dsimp only [outputMachine]; evm_gas⟩
    · have hg' := gt_selector_ge hgt
      fresh_intro
      pwp_steps [hlt, Abi.shr_calldataload_zero, hg', e1, e2, e3, e4, e5, hc', iszero_one,
        Memory.read_64]
      exact ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl, by dsimp only [outputMachine]; evm_gas⟩

end Verified.AaveV3.ATokenProxy
