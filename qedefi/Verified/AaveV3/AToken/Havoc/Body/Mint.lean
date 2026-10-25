import Verified.AaveV3.AToken.Havoc.Run

/-!
# `mint` with any caller and any arguments

`mint(caller, onBehalfOf, scaledAmount, index)` is `onlyPool`, but the Pool is not trusted: any
arguments. The three writes before the rewards controller's `handleAction` (index, `_totalSupply
+ amount`, balance `+ amount`, both checked, the balance as `uint120`) move the ledger and the
supply together (`Good.writes3`).
-/

namespace Verified.AaveV3.AToken.Havoc
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Solidity Verified.AaveV3.Contracts

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `mint`. -/
theorem body_mint : BodyOk 1219 := by
  atok_run
  ledger_chain
  word_omega

end Verified.AaveV3.AToken.Havoc
