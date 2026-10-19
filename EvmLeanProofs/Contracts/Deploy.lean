import EvmLeanProofs.Contracts.SolmateAsset
import EvmLeanProofs.Contracts.SolmateVault
import EvmLeanProofs.Contracts.OzAsset
import EvmLeanProofs.Contracts.OzVault

/-!
# Runtime code for arbitrary deployment parameters

The generated modules fix one canonical deployment. A contract deployed elsewhere (another
address, chain or asset) runs the same code with different immutables, which the
constructor computes as follows:

| Contract | Immutable | Value |
|---|---|---|
| Solmate `ERC20` (asset and vault) | `decimals` | constructor argument (vault: `asset.decimals()`) |
| | `INITIAL_CHAIN_ID` | `block.chainid` at deployment |
| | `INITIAL_DOMAIN_SEPARATOR` | `computeDomainSeparator()` at deployment (`solmateDomainSeparator`) |
| Solmate `ERC4626` | `asset` | constructor argument |
| OpenZeppelin `ERC4626` | `_asset` | constructor argument |
| | `_underlyingDecimals` | `asset.decimals()` at deployment (18 when the call fails) |

`runtimeCodeFor` patches these values into the canonical code by position
(`runtimeCodeWith`). `lake exe difftest` checks the result against code deployed by running
the creation code in evm-lean and in anvil.
-/

namespace EvmLean.Contracts

/-- Solmate's `ERC20.computeDomainSeparator()`: the EIP-712 domain separator of a token named
`name` (version `"1"`) deployed at `self` on chain `chainId`, for the given Keccak-256. -/
def solmateDomainSeparator (keccak256 : ByteArray → Word) (name : String) (chainId : Nat)
    (self : Address) : Word :=
  keccak256 <|
    Bytes.ofWord (keccak256
      "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)".toUTF8) ++
    Bytes.ofWord (keccak256 name.toUTF8) ++
    Bytes.ofWord (keccak256 "1".toUTF8) ++
    Bytes.ofWord (BitVec.ofNat 256 chainId) ++
    Bytes.ofWord (Word.ofAddress self)

namespace SolmateAsset

/-- The token name of the canonical deployment (constructor argument). -/
def name : String := "Solmate Asset"

/-- The immutables of a `MockERC20` named `name` with `decimals` decimals, deployed at
`self` on chain `chainId`. -/
def immutablesFor (keccak256 : ByteArray → Word) (chainId : Nat) (self : Address)
    (name : String := name) (decimals : Nat := 18) : Immutables where
  initialChainId := BitVec.ofNat 256 chainId
  initialDomainSeparator := solmateDomainSeparator keccak256 name chainId self
  decimals := BitVec.ofNat 256 decimals

/-- The runtime code of a `MockERC20` deployed at `self` on chain `chainId` (canonical name,
symbol and decimals). -/
def runtimeCodeFor (keccak256 : ByteArray → Word) (chainId : Nat) (self : Address) : ByteArray :=
  runtimeCodeWith (immutablesFor keccak256 chainId self)

end SolmateAsset

namespace SolmateVault

/-- The vault name of the canonical deployment (constructor argument). -/
def name : String := "Solmate Vault"

/-- The immutables of a `MockERC4626` named `name` over `asset` (which has `decimals`
decimals), deployed at `self` on chain `chainId`. -/
def immutablesFor (keccak256 : ByteArray → Word) (chainId : Nat) (asset self : Address)
    (name : String := name) (decimals : Nat := 18) : Immutables where
  initialChainId := BitVec.ofNat 256 chainId
  initialDomainSeparator := solmateDomainSeparator keccak256 name chainId self
  asset := asset
  decimals := BitVec.ofNat 256 decimals

/-- The runtime code of a `MockERC4626` over `asset` (18 decimals) deployed at `self` on
chain `chainId`, with the canonical name and symbol. -/
def runtimeCodeFor (keccak256 : ByteArray → Word) (chainId : Nat) (asset self : Address) :
    ByteArray :=
  runtimeCodeWith (immutablesFor keccak256 chainId asset self)

end SolmateVault

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
