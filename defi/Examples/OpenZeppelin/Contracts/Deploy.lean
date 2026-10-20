import Examples.OpenZeppelin.Contracts.OzAsset
import Examples.OpenZeppelin.Contracts.OzVault
import Examples.OpenZeppelin.Contracts.OzVaultOffset

/-!
# Runtime code of the OpenZeppelin contracts for arbitrary deployment parameters

`runtimeCodeFor` patches the vaults' immutables (`_asset`, `_underlyingDecimals`) into the
canonical code by position (`runtimeCodeWith`). `OzVaultOffset` is `OzVault` with
`_decimalsOffset() = 3`.
-/

namespace Examples.OpenZeppelin.Contracts
open EvmLean EvmLogic EvmLogic.Solidity

namespace OzAsset

/-- `ERC20Mock` has no immutables: its runtime code is the same everywhere. -/
def runtimeCodeFor : ByteArray := runtimeCode

end OzAsset

namespace OzVault

/-- The immutables of an `OzVault` over `asset` with `decimals` decimals. -/
def immutablesFor (asset : Address) (decimals : Nat := 18) : Immutables where
  asset := asset
  underlyingDecimals := BitVec.ofNat 256 decimals

/-- The runtime code of an `OzVault` over `asset` (18 decimals), wherever it is deployed. -/
def runtimeCodeFor (asset : Address) : ByteArray := runtimeCodeWith (immutablesFor asset)

end OzVault

namespace OzVaultOffset

/-- The immutables of an `OzVaultOffset` over `asset` with `decimals` decimals. -/
def immutablesFor (asset : Address) (decimals : Nat := 18) : Immutables where
  asset := asset
  underlyingDecimals := BitVec.ofNat 256 decimals

/-- The runtime code of an `OzVaultOffset` over `asset` (18 decimals), wherever it is
deployed. -/
def runtimeCodeFor (asset : Address) : ByteArray := runtimeCodeWith (immutablesFor asset)

end OzVaultOffset

end Examples.OpenZeppelin.Contracts
