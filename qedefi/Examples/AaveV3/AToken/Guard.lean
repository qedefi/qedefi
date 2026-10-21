import Examples.AaveV3.AToken.Guard.Mint
import Examples.AaveV3.AToken.Guard.Burn
import Examples.AaveV3.AToken.Guard.MintToTreasury
import Examples.AaveV3.AToken.Guard.TransferOnLiquidation
import Examples.AaveV3.AToken.Guard.TransferUnderlyingTo

/-!
# `AToken`: the Pool-only entry points have no effect for anyone else

The five `onlyPool` functions of the deployed AToken implementation are the only ones that
mint, burn or move scaled balances without an owner's consent (`mint`, `burn`, `mintToTreasury`,
`transferOnLiquidation`) or move the underlying out of the token (`transferUnderlyingTo`).
`poolOnly_noEffect`: called by anyone but the Pool, with any calldata carrying one of their
selectors and any value, in any frame, each reverts and leaves the world, the transient storage,
the created accounts and the logs as they were. In particular no storage slot of the executing
account changes (`poolOnly_sload_unchanged`), so neither the scaled supply `_totalSupply`
(slot 54) nor any `_userState` row.
-/

namespace Examples.AaveV3.AToken
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Examples.AaveV3.Contracts

/-- The selectors of the `onlyPool` functions: `mint`, `burn`, `mintToTreasury`,
`transferOnLiquidation`, `transferUnderlyingTo`. -/
def poolOnlySelectors : List Nat := [0xb3f1c93d, 0xb18d6afd, 0x7df5bd3b, 0x353b7b9a, 0x4efecaa5]

/-- The selectors are those of the verified ABI. -/
theorem poolOnlySelectors_abi :
    ("mint(address,address,uint256,uint256)", (0xb3f1c93d : UInt32)) ∈ AToken.selectors ∧
    ("burn(address,address,uint256,uint256,uint256)", (0xb18d6afd : UInt32)) ∈ AToken.selectors ∧
    ("mintToTreasury(uint256,uint256)", (0x7df5bd3b : UInt32)) ∈ AToken.selectors ∧
    ("transferOnLiquidation(address,address,uint256,uint256,uint256)", (0x353b7b9a : UInt32)) ∈
      AToken.selectors ∧
    ("transferUnderlyingTo(address,uint256)", (0x4efecaa5 : UInt32)) ∈ AToken.selectors := by
  decide

/-- **Access control.** A frame running the AToken implementation, called by anyone but the
Pool with one of the `onlyPool` selectors (any further calldata, any value, any world, any
depth), reverts and changes nothing. -/
theorem poolOnly_noEffect (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data ∈ poolOnlySelectors)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc : m.frame.msg.caller ≠ pool) (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (NoEffect 3000 m) := by
  simp only [poolOnlySelectors, List.mem_cons, List.not_mem_nil, or_false] at hsel
  rcases hsel with h | h | h | h | h
  · exact mint_noEffect_of_not_pool m hf h hsize' hc hg
  · exact burn_noEffect_of_not_pool m hf h hsize' hc hg
  · exact mintToTreasury_noEffect_of_not_pool m hf h hsize' hc hg
  · exact transferOnLiquidation_noEffect_of_not_pool m hf h hsize' hc hg
  · exact transferUnderlyingTo_noEffect_of_not_pool m hf h hsize' hc hg

/-- **No storage write by a non-Pool caller.** Under the hypotheses of `poolOnly_noEffect`, the
frame reverts and every storage slot of the executing account (the proxy, under
`DELEGATECALL`), among them `_totalSupply` (slot 54) and the `_userState` rows (slot 52), holds
its old value when the frame ends. -/
theorem poolOnly_sload_unchanged (m : Machine) (hf : Fresh AToken.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data ∈ poolOnlySelectors)
    (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc : m.frame.msg.caller ≠ pool) (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (fun mf o => (∃ out, o = .revert out) ∧
      ∀ slot, mf.world.sload m.frame.msg.currentTarget slot =
        m.world.sload m.frame.msg.currentTarget slot) :=
  (poolOnly_noEffect m hf hsel hsize' hc hg).mono fun _ _ _ h => ⟨h.1, fun _ => by rw [h.2.1.1]⟩

end Examples.AaveV3.AToken
