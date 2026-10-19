import EvmLeanProofs.Contracts.Deploy

/-!
# Tests for the compiled-contract constants

Cross-checks of the generated tables in `EvmLeanProofs/Contracts/` against the pure-Lean
Keccak-256 (selectors and event topics are hashes of their signatures), of the immutables
patching (`runtimeCodeFor` recomputes the canonical immutables, including Solmate's EIP-712
domain separator) and of the storage layouts the proofs rely on. Execution of the code
itself is tested against anvil by `lake exe difftest`.
-/

namespace EvmLeanTest.Contracts

open EvmLean EvmLean.Contracts

/-- The 4-byte selector of a function signature. -/
def selectorOf (sig : String) : UInt32 :=
  (Crypto.real.keccak256 sig.toUTF8 >>> 224).toNat.toUInt32

/-- Every entry of a selector table is the hash of its signature. -/
def selectorsOk (t : List (String × UInt32)) : Bool := t.all fun (s, v) => selectorOf s == v

/-- Every event topic is the hash of its signature. -/
def eventsOk (t : List (String × Word)) : Bool :=
  t.all fun (s, v) => Crypto.real.keccak256 s.toUTF8 == v

#guard selectorsOk SolmateAsset.selectors && selectorsOk SolmateVault.selectors
#guard selectorsOk OzAsset.selectors && selectorsOk OzVault.selectors
#guard selectorsOk OzAsset.errors && selectorsOk OzVault.errors
#guard eventsOk SolmateAsset.events && eventsOk SolmateVault.events
#guard eventsOk OzAsset.events && eventsOk OzVault.events

#guard selector? SolmateVault.selectors "deposit(uint256,address)" == some 0x6e553f65
#guard selector? OzVault.selectors "redeem(uint256,address,address)" == some 0xba087652
#guard SolmateVault.selectors.length == 30 && OzVault.selectors.length == 25

-- Code sizes (bytes).
#guard SolmateAsset.runtimeCode.size == 2870 && SolmateAsset.creationCode.size == 3885
#guard SolmateVault.runtimeCode.size == 5248 && SolmateVault.creationCode.size == 6474
#guard OzAsset.runtimeCode.size == 1900 && OzAsset.creationCode.size == 2366
#guard OzVault.runtimeCode.size == 4408 && OzVault.creationCode.size == 5098

-- Canonical addresses: `CREATE` from the deployer at nonces 0 and 1.
#guard Interpreter.createAddress Crypto.real.keccak256 deployer 0 == SolmateAsset.address
#guard Interpreter.createAddress Crypto.real.keccak256 deployer 1 == SolmateVault.address
#guard OzAsset.address == SolmateAsset.address && OzVault.address == SolmateVault.address

-- The immutables recomputed from the deployment parameters reproduce the deployed code.
#guard SolmateAsset.immutablesFor Crypto.real.keccak256 chainId SolmateAsset.address ==
  SolmateAsset.deployment
#guard SolmateVault.immutablesFor Crypto.real.keccak256 chainId SolmateAsset.address
  SolmateVault.address == SolmateVault.deployment
#guard OzVault.immutablesFor OzAsset.address == OzVault.deployment
#guard SolmateVault.runtimeCodeFor Crypto.real.keccak256 chainId SolmateAsset.address
  SolmateVault.address == SolmateVault.runtimeCode
#guard OzVault.runtimeCodeFor OzAsset.address == OzVault.runtimeCode
-- A different asset changes the 20 address bytes of each of the six `asset` placeholders.
#guard
  let a := SolmateVault.runtimeCodeFor Crypto.real.keccak256 chainId 0xabcd SolmateVault.address
  let b := SolmateVault.runtimeCode
  a.size == b.size &&
    ((List.range a.size).filter fun i => a.data[i]? != b.data[i]?).length == 6 * 20

-- Storage layouts (Solmate: `name`, `symbol`, `totalSupply`, `balanceOf`, `allowance`,
-- `nonces`; OpenZeppelin: `_balances`, `_allowances`, `_totalSupply`, `_name`, `_symbol`).
#guard slotOf? SolmateVault.storageLayout "totalSupply" == some 2
#guard slotOf? SolmateVault.storageLayout "balanceOf" == some 3
#guard slotOf? SolmateVault.storageLayout "allowance" == some 4
#guard slotOf? SolmateVault.storageLayout "afterDepositHookCalledCounter" == some 7
#guard slotOf? SolmateAsset.storageLayout "balanceOf" == some 3
#guard slotOf? OzVault.storageLayout "_balances" == some 0
#guard slotOf? OzVault.storageLayout "_allowances" == some 1
#guard slotOf? OzVault.storageLayout "_totalSupply" == some 2
#guard slotOf? OzAsset.storageLayout "_balances" == some 0
#guard SolmateVault.immutableRefs.map (·.name) ==
  ["INITIAL_CHAIN_ID", "INITIAL_DOMAIN_SEPARATOR", "asset", "decimals"]
#guard OzAsset.immutableRefs.isEmpty

end EvmLeanTest.Contracts
