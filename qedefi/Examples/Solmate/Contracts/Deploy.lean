import Examples.Solmate.Contracts.SolmateAssetData
import Examples.Solmate.Contracts.SolmateVaultData

/-!
# Runtime code for arbitrary deployment parameters

The generated modules fix one canonical deployment. Elsewhere the same code runs with other
immutables (`decimals`, `INITIAL_CHAIN_ID`, `INITIAL_DOMAIN_SEPARATOR`, and the vault's
`asset`), computed here as the constructor does; `runtimeCodeFor` patches them in
(`runtimeCodeWith`). `lake exe difftest` checks this against code deployed in anvil.
-/

namespace Examples.Solmate.Contracts
open EvmLean EvmLogic EvmLogic.Solidity

/-- Solmate's `computeDomainSeparator()`: the EIP-712 domain separator (version `"1"`). -/
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

def name : String := "Solmate Asset"

/-- The immutables of a `MockERC20` deployed at `self` on chain `chainId`. -/
def immutablesFor (keccak256 : ByteArray → Word) (chainId : Nat) (self : Address)
    (name : String := name) (decimals : Nat := 18) : Immutables where
  initialChainId := BitVec.ofNat 256 chainId
  initialDomainSeparator := solmateDomainSeparator keccak256 name chainId self
  decimals := BitVec.ofNat 256 decimals

/-- The runtime code of a canonical `MockERC20` deployed at `self` on chain `chainId`. -/
def runtimeCodeFor (keccak256 : ByteArray → Word) (chainId : Nat) (self : Address) : ByteArray :=
  runtimeCodeWith (immutablesFor keccak256 chainId self)

end SolmateAsset

namespace SolmateVault

def name : String := "Solmate Vault"

/-- The immutables of a `MockERC4626` over `asset` deployed at `self` on chain `chainId`. -/
def immutablesFor (keccak256 : ByteArray → Word) (chainId : Nat) (asset self : Address)
    (name : String := name) (decimals : Nat := 18) : Immutables where
  initialChainId := BitVec.ofNat 256 chainId
  initialDomainSeparator := solmateDomainSeparator keccak256 name chainId self
  asset := asset
  decimals := BitVec.ofNat 256 decimals

/-- The runtime code of a canonical `MockERC4626` over `asset` at `self` on chain `chainId`. -/
def runtimeCodeFor (keccak256 : ByteArray → Word) (chainId : Nat) (asset self : Address) :
    ByteArray :=
  runtimeCodeWith (immutablesFor keccak256 chainId asset self)

end SolmateVault

end Examples.Solmate.Contracts
