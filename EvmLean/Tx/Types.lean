import EvmLean.Prelude.Rlp
import EvmLean.Machine.Types

/-!
# Transaction types

The five transaction formats (four in Cancun, plus Prague's set-code transaction), mirroring
the dataclasses in `ethereum/execution-specs` (`src/ethereum/forks/prague/transactions.py`):

| Lean            | execution-specs          | EIP          |
|-----------------|--------------------------|--------------|
| `LegacyTx`      | `LegacyTransaction`      | pre-2718     |
| `AccessListTx`  | `AccessListTransaction`  | EIP-2930     |
| `FeeMarketTx`   | `FeeMarketTransaction`   | EIP-1559     |
| `BlobTx`        | `BlobTransaction`        | EIP-4844     |
| `SetCodeTx`     | `SetCodeTransaction`     | EIP-7702     |

All integer fields are `Nat`. The bounds of the reference types (`U64`, `U256`) are enforced
when transactions are decoded (`EvmLean.Tx.Codec`), so values built from the wire always
respect them; `Uint` fields (gas, gas prices) are unbounded, exactly as in the reference.
Fee and balance arithmetic is therefore done in `Nat`, with no wrap-around.

A blob or set-code transaction's `to` is an `Address`, not an `Option`: as in the reference,
these transactions cannot create a contract, and an empty `to` fails to decode. Which types
a fork accepts is decided by `Tx.validate` (set-code transactions only from Prague).
-/

namespace EvmLean

/-- One access-list entry (EIP-2930): an address and storage keys to pre-warm. Mirrors
`Access` in `cancun/transactions.py`. -/
structure AccessListItem where
  /-- The account to pre-warm. -/
  address : Address
  /-- Storage keys of `address` to pre-warm. -/
  storageKeys : List Word
  deriving DecidableEq, Inhabited

/-- A legacy (pre-EIP-2718) transaction. Mirrors `LegacyTransaction`. -/
structure LegacyTx where
  /-- Sender nonce (`U256`). -/
  nonce : Nat
  /-- Gas price in wei (`Uint`). -/
  gasPrice : Nat
  /-- Gas limit (`Uint`). -/
  gas : Nat
  /-- Recipient, or `none` for a contract creation. -/
  to : Option Address
  /-- Value in wei (`U256`). -/
  value : Nat
  /-- Calldata, or init code for a creation. -/
  data : ByteArray
  /-- Signature `v` (27/28, or EIP-155 `chainId * 2 + 35/36`). -/
  v : Nat
  /-- Signature `r`. -/
  r : Nat
  /-- Signature `s`. -/
  s : Nat
  deriving DecidableEq, Inhabited

/-- An EIP-2930 access-list transaction (type `0x01`). Mirrors `AccessListTransaction`. -/
structure AccessListTx where
  /-- Chain id (`U64`). -/
  chainId : Nat
  /-- Sender nonce (`U256`). -/
  nonce : Nat
  /-- Gas price in wei (`Uint`). -/
  gasPrice : Nat
  /-- Gas limit (`Uint`). -/
  gas : Nat
  /-- Recipient, or `none` for a contract creation. -/
  to : Option Address
  /-- Value in wei (`U256`). -/
  value : Nat
  /-- Calldata, or init code for a creation. -/
  data : ByteArray
  /-- Addresses and storage keys to pre-warm. -/
  accessList : List AccessListItem
  /-- Signature y-parity (must be 0 or 1). -/
  yParity : Nat
  /-- Signature `r`. -/
  r : Nat
  /-- Signature `s`. -/
  s : Nat
  deriving DecidableEq, Inhabited

/-- An EIP-1559 fee-market transaction (type `0x02`). Mirrors `FeeMarketTransaction`. -/
structure FeeMarketTx where
  /-- Chain id (`U64`). -/
  chainId : Nat
  /-- Sender nonce (`U256`). -/
  nonce : Nat
  /-- Maximum priority fee (tip) per gas (`Uint`). -/
  maxPriorityFeePerGas : Nat
  /-- Maximum total fee per gas (`Uint`). -/
  maxFeePerGas : Nat
  /-- Gas limit (`Uint`). -/
  gas : Nat
  /-- Recipient, or `none` for a contract creation. -/
  to : Option Address
  /-- Value in wei (`U256`). -/
  value : Nat
  /-- Calldata, or init code for a creation. -/
  data : ByteArray
  /-- Addresses and storage keys to pre-warm. -/
  accessList : List AccessListItem
  /-- Signature y-parity (must be 0 or 1). -/
  yParity : Nat
  /-- Signature `r`. -/
  r : Nat
  /-- Signature `s`. -/
  s : Nat
  deriving DecidableEq, Inhabited

/-- An EIP-4844 blob transaction (type `0x03`). Mirrors `BlobTransaction`. -/
structure BlobTx where
  /-- Chain id (`U64`). -/
  chainId : Nat
  /-- Sender nonce (`U256`). -/
  nonce : Nat
  /-- Maximum priority fee (tip) per gas (`Uint`). -/
  maxPriorityFeePerGas : Nat
  /-- Maximum total fee per gas (`Uint`). -/
  maxFeePerGas : Nat
  /-- Gas limit (`Uint`). -/
  gas : Nat
  /-- Recipient. Blob transactions cannot create contracts. -/
  to : Address
  /-- Value in wei (`U256`). -/
  value : Nat
  /-- Calldata. -/
  data : ByteArray
  /-- Addresses and storage keys to pre-warm. -/
  accessList : List AccessListItem
  /-- Maximum fee per unit of blob gas (`U256`). -/
  maxFeePerBlobGas : Nat
  /-- Versioned hashes of the blobs (first byte is the version, `0x01` for KZG). -/
  blobVersionedHashes : List Word
  /-- Signature y-parity (must be 0 or 1). -/
  yParity : Nat
  /-- Signature `r`. -/
  r : Nat
  /-- Signature `s`. -/
  s : Nat
  deriving DecidableEq, Inhabited

/-- An EIP-7702 set-code transaction (type `0x04`, Prague). Mirrors `SetCodeTransaction`. -/
structure SetCodeTx where
  /-- Chain id (`U64`). -/
  chainId : Nat
  /-- Sender nonce (`U64`). -/
  nonce : Nat
  /-- Maximum priority fee (tip) per gas (`Uint`). -/
  maxPriorityFeePerGas : Nat
  /-- Maximum total fee per gas (`Uint`). -/
  maxFeePerGas : Nat
  /-- Gas limit (`Uint`). -/
  gas : Nat
  /-- Recipient. Set-code transactions cannot create contracts. -/
  to : Address
  /-- Value in wei (`U256`). -/
  value : Nat
  /-- Calldata. -/
  data : ByteArray
  /-- Addresses and storage keys to pre-warm. -/
  accessList : List AccessListItem
  /-- Authorization tuples, processed in order before execution. -/
  authorizations : List Authorization
  /-- Signature y-parity (must be 0 or 1). -/
  yParity : Nat
  /-- Signature `r`. -/
  r : Nat
  /-- Signature `s`. -/
  s : Nat
  deriving DecidableEq, Inhabited

/-- A transaction of any type. Mirrors the `Transaction` union in
`prague/transactions.py`. -/
inductive Transaction where
  /-- Legacy transaction. -/
  | legacy (tx : LegacyTx)
  /-- EIP-2930 transaction. -/
  | eip2930 (tx : AccessListTx)
  /-- EIP-1559 transaction. -/
  | eip1559 (tx : FeeMarketTx)
  /-- EIP-4844 transaction. -/
  | eip4844 (tx : BlobTx)
  /-- EIP-7702 transaction (Prague). -/
  | eip7702 (tx : SetCodeTx)
  deriving DecidableEq, Inhabited

namespace Transaction

/-- The EIP-2718 type byte (`0` for legacy transactions). -/
def typeByte : Transaction → Nat
  | .legacy _ => 0
  | .eip2930 _ => 1
  | .eip1559 _ => 2
  | .eip4844 _ => 3
  | .eip7702 _ => 4

/-- Sender nonce. -/
def nonce : Transaction → Nat
  | .legacy t => t.nonce
  | .eip2930 t => t.nonce
  | .eip1559 t => t.nonce
  | .eip4844 t => t.nonce
  | .eip7702 t => t.nonce

/-- Gas limit. -/
def gas : Transaction → Nat
  | .legacy t => t.gas
  | .eip2930 t => t.gas
  | .eip1559 t => t.gas
  | .eip4844 t => t.gas
  | .eip7702 t => t.gas

/-- Recipient (`none` for a contract creation). -/
def to : Transaction → Option Address
  | .legacy t => t.to
  | .eip2930 t => t.to
  | .eip1559 t => t.to
  | .eip4844 t => some t.to
  | .eip7702 t => some t.to

/-- Value in wei. -/
def value : Transaction → Nat
  | .legacy t => t.value
  | .eip2930 t => t.value
  | .eip1559 t => t.value
  | .eip4844 t => t.value
  | .eip7702 t => t.value

/-- Calldata or init code. -/
def data : Transaction → ByteArray
  | .legacy t => t.data
  | .eip2930 t => t.data
  | .eip1559 t => t.data
  | .eip4844 t => t.data
  | .eip7702 t => t.data

/-- Access list (empty for legacy transactions). -/
def accessList : Transaction → List AccessListItem
  | .legacy _ => []
  | .eip2930 t => t.accessList
  | .eip1559 t => t.accessList
  | .eip4844 t => t.accessList
  | .eip7702 t => t.accessList

/-- Signature `r`. -/
def r : Transaction → Nat
  | .legacy t => t.r
  | .eip2930 t => t.r
  | .eip1559 t => t.r
  | .eip4844 t => t.r
  | .eip7702 t => t.r

/-- Signature `s`. -/
def s : Transaction → Nat
  | .legacy t => t.s
  | .eip2930 t => t.s
  | .eip1559 t => t.s
  | .eip4844 t => t.s
  | .eip7702 t => t.s

/-- Blob versioned hashes (empty for non-blob transactions). -/
def blobVersionedHashes : Transaction → List Word
  | .legacy _ => []
  | .eip2930 _ => []
  | .eip1559 _ => []
  | .eip4844 t => t.blobVersionedHashes
  | .eip7702 _ => []

/-- EIP-7702 authorizations (empty for other types). -/
def authorizations : Transaction → List Authorization
  | .legacy _ | .eip2930 _ | .eip1559 _ | .eip4844 _ => []
  | .eip7702 t => t.authorizations

/-- Is this a contract creation? -/
def isCreate (tx : Transaction) : Bool := tx.to.isNone

end Transaction

end EvmLean
