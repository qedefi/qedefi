import Verified.AaveV3.AToken.Havoc.Run

/-!
# `approve`, `increaseAllowance`, `decreaseAllowance`, `renounceAllowance`

Each writes one `_allowances` entry and logs `Approval`: the write keeps `Good`
(`Good.sstore_allow`, under `SlotsOk`).
-/

namespace Verified.AaveV3.AToken.Havoc
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Solidity Verified.AaveV3.Contracts

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `approve(spender, amount)`. -/
theorem body_approve : BodyOk 554 := by
  atok_run
  all_goals exact Good.sstore_allow hK _ _ _ hw ht

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `increaseAllowance(spender, added)`. -/
theorem body_increaseAllowance : BodyOk 849 := by
  atok_run
  all_goals exact Good.sstore_allow hK _ _ _ hw ht

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `decreaseAllowance(spender, subtracted)`. -/
theorem body_decreaseAllowance : BodyOk 1080 := by
  atok_run
  all_goals exact Good.sstore_allow hK _ _ _ hw ht

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `renounceAllowance(owner)`. -/
theorem body_renounceAllowance : BodyOk 1156 := by
  atok_run
  all_goals exact Good.sstore_allow hK _ _ _ hw ht

end Verified.AaveV3.AToken.Havoc
