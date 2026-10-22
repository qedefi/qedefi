import Examples.AaveV3.AToken.Havoc.Run

/-!
# The views, and `transferUnderlyingTo`

Functions that write nothing: every path ends in a `REVERT`/`RETURN` of an unchanged world, or
goes through a static call of the Pool (`balanceOf`, `totalSupply`: any `Good` world after it,
`pwp_staticcall`) or, for `transferUnderlyingTo`, a call of the underlying (`pwp_call_any`).
-/

namespace Examples.AaveV3.AToken.Havoc
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Solidity Examples.AaveV3.Contracts

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `getScaledUserBalanceAndSupply`. -/
theorem body_scaledUserBalanceAndSupply : BodyOk 589 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `ATOKEN_REVISION`. -/
theorem body_atokenRevision : BodyOk 629 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `totalSupply (a static call of the Pool's index)`. -/
theorem body_totalSupply : BodyOk 651 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `scaledBalanceOf`. -/
theorem body_scaledBalanceOf : BodyOk 659 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `TREASURY`. -/
theorem body_treasury : BodyOk 697 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `PERMIT_TYPEHASH`. -/
theorem body_permitTypehash : BodyOk 760 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `decimals`. -/
theorem body_decimals : BodyOk 799 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `balanceOf (a static call of the Pool's index)`. -/
theorem body_balanceOf : BodyOk 887 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `POOL`. -/
theorem body_pool : BodyOk 906 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `getIncentivesController`. -/
theorem body_incentivesController : BodyOk 945 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `EIP712_REVISION`. -/
theorem body_eip712Revision : BodyOk 983 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `nonces`. -/
theorem body_nonces : BodyOk 1034 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `RESERVE_TREASURY_ADDRESS`. -/
theorem body_reserveTreasury : BodyOk 1118 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `UNDERLYING_ASSET_ADDRESS`. -/
theorem body_underlyingAsset : BodyOk 1175 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `scaledTotalSupply`. -/
theorem body_scaledTotalSupply : BodyOk 1211 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `REWARDS_CONTROLLER`. -/
theorem body_rewardsController : BodyOk 1238 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `allowance`. -/
theorem body_allowance : BodyOk 1315 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `getPreviousIndex`. -/
theorem body_previousIndex : BodyOk 1371 := by
  atok_run

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `transferUnderlyingTo(target, amount)`: `onlyPool`, then the underlying's `transfer`; no write
before the call. -/
theorem body_transferUnderlyingTo : BodyOk 868 := by
  atok_run

end Examples.AaveV3.AToken.Havoc
