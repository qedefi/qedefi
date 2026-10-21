import Examples.Solmate.Contracts.Deploy
import Examples.OpenZeppelin.Contracts.Deploy
import Examples.Deployment

/-!
# Vault families under test

A *family* is an asset token and an ERC-4626 vault over it, with what the tester needs to
deploy them, encode calls and locate their ERC-20 storage.
-/

namespace Examples.Differential

open EvmLean EvmLogic EvmLogic.Solidity Examples.Deployment Examples.OpenZeppelin
open Examples.OpenZeppelin.Contracts Examples.Solmate Examples.Solmate.Contracts

/-- An asset/vault pair. -/
structure Family where
  /-- Name used in reports and on the command line. -/
  name : String
  /-- Asset creation code with constructor arguments. -/
  assetInit : ByteArray
  /-- Vault creation code with constructor arguments (for the canonical asset address). -/
  vaultInit : ByteArray
  /-- Vault creation code with constructor arguments for the asset at the given address. -/
  vaultInitFor : Address → ByteArray
  /-- Canonical asset address (deployer nonce 0). -/
  asset : Address
  /-- Canonical vault address (deployer nonce 1). -/
  vault : Address
  /-- Expected asset runtime code. -/
  assetCode : ByteArray
  /-- Expected vault runtime code. -/
  vaultCode : ByteArray
  /-- Expected runtime codes for a deployment by another deployer: `(asset, vault)` code for
  asset and vault addresses (`Contracts.Deploy`). -/
  codeFor : Address → Address → ByteArray × ByteArray
  /-- Asset selectors. -/
  assetSelectors : List (String × UInt32)
  /-- Vault selectors. -/
  vaultSelectors : List (String × UInt32)
  /-- Slot of the asset's balance mapping. -/
  assetBalances : Nat
  /-- Slot of the vault's share-balance mapping. -/
  vaultBalances : Nat
  /-- Slot of the vault's allowance mapping. -/
  vaultAllowances : Nat
  /-- Slot of the asset's allowance mapping. -/
  assetAllowances : Nat
  /-- Slot of the vault's `totalSupply`. -/
  vaultTotalSupply : Nat

/-- ABI-encoded constructor arguments with the first (static, address) argument replaced:
both vaults take the asset address first. -/
def withFirstArg (args : ByteArray) (a : Address) : ByteArray :=
  Bytes.ofWord (Word.ofAddress a) ++ args.extract 32 args.size

/-- The Solmate family: `MockERC20` and `MockERC4626`. -/
def solmate : Family where
  name := "solmate"
  assetInit := SolmateAsset.creationCode ++ SolmateAsset.constructorArgs
  vaultInit := SolmateVault.creationCode ++ SolmateVault.constructorArgs
  vaultInitFor a := SolmateVault.creationCode ++ withFirstArg SolmateVault.constructorArgs a
  asset := SolmateAsset.address
  vault := SolmateVault.address
  assetCode := SolmateAsset.runtimeCode
  vaultCode := SolmateVault.runtimeCode
  codeFor a v := (SolmateAsset.runtimeCodeFor Crypto.real.keccak256 chainId a,
                  SolmateVault.runtimeCodeFor Crypto.real.keccak256 chainId a v)
  assetSelectors := SolmateAsset.selectors
  vaultSelectors := SolmateVault.selectors
  assetBalances := (slotOf? SolmateAsset.storageLayout "balanceOf").getD 0
  assetAllowances := (slotOf? SolmateAsset.storageLayout "allowance").getD 0
  vaultBalances := (slotOf? SolmateVault.storageLayout "balanceOf").getD 0
  vaultAllowances := (slotOf? SolmateVault.storageLayout "allowance").getD 0
  vaultTotalSupply := (slotOf? SolmateVault.storageLayout "totalSupply").getD 0

/-- The OpenZeppelin family: `ERC20Mock` and `OzVault`. -/
def openzeppelin : Family where
  name := "oz"
  assetInit := OzAsset.creationCode ++ OzAsset.constructorArgs
  vaultInit := OzVault.creationCode ++ OzVault.constructorArgs
  vaultInitFor a := OzVault.creationCode ++ withFirstArg OzVault.constructorArgs a
  asset := OzAsset.address
  vault := OzVault.address
  assetCode := OzAsset.runtimeCode
  vaultCode := OzVault.runtimeCode
  codeFor a _ := (OzAsset.runtimeCodeFor, OzVault.runtimeCodeFor a)
  assetSelectors := OzAsset.selectors
  vaultSelectors := OzVault.selectors
  assetBalances := (slotOf? OzAsset.storageLayout "_balances").getD 0
  assetAllowances := (slotOf? OzAsset.storageLayout "_allowances").getD 0
  vaultBalances := (slotOf? OzVault.storageLayout "_balances").getD 0
  vaultAllowances := (slotOf? OzVault.storageLayout "_allowances").getD 0
  vaultTotalSupply := (slotOf? OzVault.storageLayout "_totalSupply").getD 0

/-- The OpenZeppelin family with decimals offset 3: `ERC20Mock` and `OzVaultOffset`. -/
def openzeppelinOffset : Family :=
  { openzeppelin with
    name := "oz3"
    vaultInit := OzVaultOffset.creationCode ++ OzVaultOffset.constructorArgs
    vaultInitFor a := OzVaultOffset.creationCode ++ withFirstArg OzVaultOffset.constructorArgs a
    vault := OzVaultOffset.address
    vaultCode := OzVaultOffset.runtimeCode
    codeFor a _ := (OzAsset.runtimeCodeFor, OzVaultOffset.runtimeCodeFor a)
    vaultSelectors := OzVaultOffset.selectors
    vaultBalances := (slotOf? OzVaultOffset.storageLayout "_balances").getD 0
    vaultAllowances := (slotOf? OzVaultOffset.storageLayout "_allowances").getD 0
    vaultTotalSupply := (slotOf? OzVaultOffset.storageLayout "_totalSupply").getD 0 }

/-- The storage slot of `m[k]` for a mapping at slot `slot` (`keccak(k ‖ slot)`). -/
def mappingSlot (k : Word) (slot : Word) : Word :=
  Crypto.real.keccak256 (Bytes.ofWord k ++ Bytes.ofWord slot)

/-- `balances[a]` of the token at `token` with the balance mapping at `slot`. -/
def balanceIn (w : World) (token : Address) (slot : Nat) (a : Address) : Word :=
  w.sload token (mappingSlot (Word.ofAddress a) (BitVec.ofNat 256 slot))

/-- `allowances[owner][spender]` of the token at `token` with the mapping at `slot`. -/
def allowanceIn (w : World) (token : Address) (slot : Nat) (owner spender : Address) : Word :=
  w.sload token (mappingSlot (Word.ofAddress spender)
    (mappingSlot (Word.ofAddress owner) (BitVec.ofNat 256 slot)))

end Examples.Differential
