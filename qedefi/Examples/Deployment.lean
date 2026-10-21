import EvmLean

/-!
# The canonical deployment of the example contracts

Each compiled contract family (Solmate, OpenZeppelin) is deployed on its own chain from
`deployer`: the asset at nonce 0, the vault at nonce 1.
-/

namespace Examples.Deployment
open EvmLean

/-- The chain id of the canonical deployment. -/
def chainId : Nat := 1

/-- The deployer of the canonical deployment. -/
def deployer : Address := 0x1000000000000000000000000000000000000000

end Examples.Deployment
