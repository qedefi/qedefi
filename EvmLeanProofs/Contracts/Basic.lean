import EvmLean

/-!
# Compiled contracts: shared definitions

The verification targets (`contracts/`, see `contracts/README.md`) are compiled by
`scripts/build-contracts.sh`, which generates one Lean module per contract:

| Module | Solidity contract | Role |
|---|---|---|
| `Contracts.SolmateAsset` | Solmate `MockERC20` | asset of the Solmate vault |
| `Contracts.SolmateVault` | Solmate `MockERC4626` | Solmate ERC-4626 vault |
| `Contracts.OzAsset` | OpenZeppelin `ERC20Mock` | asset of the OpenZeppelin vault |
| `Contracts.OzVault` | `OzVault` (OpenZeppelin `ERC4626`, nothing overridden) | OpenZeppelin vault |

Each module defines `creationCode`, `constructorArgs`, `runtimeCode` (the code deployed in
the canonical deployment, `Deployment`), `address`, `selectors`, `events`, `errors`,
`storageLayout`, `immutableRefs` and, for contracts with immutables, `Immutables`,
`runtimeCodeWith` and `deployment`.

This file holds the types those modules use and the canonical deployment parameters.

## Immutables

solc compiles a Solidity `immutable` into 32-byte `PUSH32` placeholders in the runtime code;
the constructor writes the value into each placeholder before returning the code. The
positions are part of the compiler output (`immutableReferences`), so the runtime code for
other deployment parameters is `runtimeCodeWith` (the canonical code patched by position).
`Contracts.Deploy` computes the immutables from the deployment parameters.
-/

namespace EvmLean.Contracts

/-- A Solidity storage type, as described by solc's `storageLayout.types` table. -/
inductive StorageType where
  /-- A value stored in place (elementary types), with its solc label and its size in bytes. -/
  | inplace (label : String) (numberOfBytes : Nat)
  /-- A `string` or `bytes` value (short strings in place, long ones at `keccak(slot)`). -/
  | bytes (label : String)
  /-- `mapping(key => value)`: the value of `k` lives at `keccak(k ‖ slot)`. -/
  | mapping (key value : StorageType)
  /-- A dynamic array of elements, stored from `keccak(slot)`. -/
  | dynamicArray (elem : StorageType)
  deriving Repr, DecidableEq, Inhabited

/-- A state variable: its slot, byte offset within the slot and type. -/
structure StorageVar where
  /-- The variable name. -/
  label : String
  /-- The storage slot. -/
  slot : Nat
  /-- Byte offset within the slot (from the least significant end), for packed variables. -/
  offset : Nat
  /-- The variable's type. -/
  type : StorageType
  deriving Repr, DecidableEq, Inhabited

/-- The slot of the state variable `label`, if any. -/
def slotOf? (layout : List StorageVar) (label : String) : Option Nat :=
  (layout.find? (·.label == label)).map (·.slot)

/-- An immutable variable and the byte offsets of its 32-byte placeholders in the runtime code. -/
structure ImmutableRef where
  /-- The Solidity name of the immutable. -/
  name : String
  /-- Offsets of the 32-byte slots holding its value. -/
  offsets : List Nat
  deriving Repr, DecidableEq, Inhabited

/-- Overwrite `l` from position `off` with `src` (truncated at the end of `l`). Structural on
lists, so it reduces in the kernel (`ByteArray.copySlice` does not, usefully). -/
def writeList : List UInt8 → Nat → List UInt8 → List UInt8
  | l, _, [] => l
  | [], _, _ => []
  | _ :: xs, 0, y :: ys => y :: writeList xs 0 ys
  | x :: xs, n + 1, ys => x :: writeList xs n ys

/-- Overwrite the 32 bytes at each offset with the corresponding word (big-endian). -/
def patchWords (code : ByteArray) (ps : List (Nat × Word)) : ByteArray :=
  ⟨⟨ps.foldl (fun l p => writeList l p.1 (Bytes.ofWord p.2).data.toList) code.data.toList⟩⟩

/-- Byte arrays with the same bytes are equal. Kernel checks of code equality should compare
`.data.toList` (structural) rather than use `ByteArray`'s `DecidableEq`, which does not
reduce well in the kernel. -/
theorem eq_of_data_toList_eq {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  rcases a with ⟨⟨a⟩⟩
  rcases b with ⟨⟨b⟩⟩
  simp_all

/-- The chain id of the canonical deployment. -/
def chainId : Nat := 1

/-- The deployer of the canonical deployment. Each family (Solmate, OpenZeppelin) is deployed
on its own chain from this account: the asset at nonce 0, the vault at nonce 1. -/
def deployer : Address := 0x1000000000000000000000000000000000000000

/-- Look up a selector by signature, e.g. `selector? selectors "deposit(uint256,address)"`. -/
def selector? (table : List (String × UInt32)) (sig : String) : Option UInt32 :=
  table.lookup sig

end EvmLean.Contracts
