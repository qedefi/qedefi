import EvmLogic.Solidity.Dispatch
import EvmLogic.Solidity.Call
import EvmLogic.Solidity.ERC20Oz
import Examples.OpenZeppelin.Contracts.OzAsset

/-!
# `OzAsset`: facts shared by the function proofs

The runtime code is no EIP-7702 delegation designator (`delegatedAddress?_runtimeCode`), so a
top-level call runs it (`processMessageCall_callMsg`). Each function file imports only this, so
they build in parallel.
-/

namespace Examples.OpenZeppelin.ERC20
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity Examples.OpenZeppelin.Contracts

theorem delegatedAddress?_runtimeCode : delegatedAddress? OzAsset.runtimeCode = none :=
  delegatedAddress?_of_size (by rw [OzAsset.size_runtimeCode]; decide)

end Examples.OpenZeppelin.ERC20
