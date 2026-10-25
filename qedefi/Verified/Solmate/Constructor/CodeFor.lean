import Verified.Solmate.Constructor.AssetDefs
import Verified.Solmate.Constructor.VaultDefs

/-!
# The deposited code is `runtimeCodeFor`, for a Keccak that hashes the constants right

The constructors push `keccak256("EIP712Domain(…)")` and `keccak256("1")` as literals of the
code (`Asset.domainTypehash`, `Asset.versionHash`). `Deploy.lean`'s `runtimeCodeFor` computes
them with the hash function. For a `Crypto` whose `keccak256` agrees with the code on these two
strings (`ConstHashes`; real Keccak-256 does, which `difftest` checks), the immutables the
constructors store are `immutablesFor` (`asset_immutables_eq`, `vault_immutables_eq`), so the
deployed code is `runtimeCodeFor`.
-/

namespace Verified.Solmate.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity Verified.Solmate.Contracts

/-- `keccak256` agrees with the two hashes the constructors use as literals. -/
structure ConstHashes (crypto : Crypto) : Prop where
  domain : crypto.keccak256
    "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)".toUTF8 =
      Asset.domainTypehash
  version : crypto.keccak256 "1".toUTF8 = Asset.versionHash

theorem asset_name_bytes : (Bytes.ofWord Asset.nameWord).extract 0 13 = SolmateAsset.name.toUTF8 :=
  eq_of_data_toList_eq (by decide +kernel)

theorem vault_name_bytes :
    (Bytes.ofWord SolmateVault.nameWord).extract 0 13 = SolmateVault.name.toUTF8 :=
  eq_of_data_toList_eq (by decide +kernel)

theorem asset_domainSeparator_eq {crypto : Crypto} (h : ConstHashes crypto) (chainId : Nat)
    (self : Address) : Asset.domainSeparator crypto chainId self =
      solmateDomainSeparator crypto.keccak256 SolmateAsset.name chainId self := by
  simp only [Asset.domainSeparator, solmateDomainSeparator, h.domain, h.version, asset_name_bytes,
    ByteArray.append_assoc]
  rfl

theorem vault_domainSeparator_eq {crypto : Crypto} (h : ConstHashes crypto) (chainId : Nat)
    (self : Address) : Vault.domainSeparator crypto chainId self =
      solmateDomainSeparator crypto.keccak256 SolmateVault.name chainId self := by
  simp only [Vault.domainSeparator, solmateDomainSeparator, h.domain, h.version, vault_name_bytes,
    ByteArray.append_assoc]
  rfl

/-- The asset's constructor stores `immutablesFor`. -/
theorem asset_immutables_eq {crypto : Crypto} (h : ConstHashes crypto) (chainId : Nat)
    (self : Address) : Asset.immutables crypto chainId self =
      SolmateAsset.immutablesFor crypto.keccak256 chainId self := by
  simp only [Asset.immutables, SolmateAsset.immutablesFor, asset_domainSeparator_eq h]
  rfl

/-- The vault's constructor stores `immutablesFor` when the asset has 18 decimals. -/
theorem vault_immutables_eq {crypto : Crypto} (h : ConstHashes crypto) (chainId : Nat)
    (self asset : Address) : Vault.immutables crypto chainId self asset 18#256 =
      SolmateVault.immutablesFor crypto.keccak256 chainId asset self := by
  simp only [Vault.immutables, SolmateVault.immutablesFor, vault_domainSeparator_eq h]
  rfl

end Verified.Solmate.Constructor
