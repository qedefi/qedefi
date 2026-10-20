import Examples.OpenZeppelin.Contracts.OzAsset
import Examples.OpenZeppelin.Contracts.OzVault

/-!
# Runtime code of the OpenZeppelin contracts for arbitrary deployment parameters

| Contract | Immutable | Value |
|---|---|---|
| OpenZeppelin `ERC4626` | `_asset` | constructor argument |
| | `_underlyingDecimals` | `asset.decimals()` at deployment (18 when the call fails) |

`runtimeCodeFor` patches these values into the canonical code by position
(`runtimeCodeWith`); see `Examples.Solmate.Contracts.Deploy` for the Solmate contracts.
-/

namespace EvmLean.Contracts

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

end EvmLean.Contracts
