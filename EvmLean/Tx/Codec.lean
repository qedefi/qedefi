import EvmLean.Tx.Types
import EvmLean.Tx.RlpDecode

/-!
# Transaction encoding, decoding and signing hashes

Canonical encoding (`encode_transaction`), block-body decoding (`decode_transaction`) and
signing preimages (`signing_hash_*`). Hashing is left to the caller's `Crypto`.
-/

namespace EvmLean

namespace Transaction

/-- An address as a 20-byte RLP string. -/
def addressRlp (a : Address) : Rlp := .bytes (Bytes.ofAddress a)

/-- A word as a 32-byte RLP string (hashes, storage keys). -/
def wordRlp (w : Word) : Rlp := .bytes (Bytes.ofWord w)

/-- A recipient field: empty for a contract creation. -/
def toRlp : Option Address → Rlp
  | none => .bytes .empty
  | some a => addressRlp a

/-- An access list, as `[[address, [key, …]], …]`. -/
def accessListRlp (l : List AccessListItem) : Rlp :=
  .list (l.map fun i => .list [addressRlp i.address, .list (i.storageKeys.map wordRlp)])

/-- An EIP-7702 authorization list, as `[[chainId, address, nonce, yParity, r, s], …]`. -/
def authorizationsRlp (l : List Authorization) : Rlp :=
  .list (l.map fun a => .list [.nat a.chainId, addressRlp a.address, .nat a.nonce,
    .nat a.yParity, .nat a.r, .nat a.s])

/-- The RLP list of all fields, signature included, in reference field order. -/
def fieldsRlp : Transaction → Rlp
  | .legacy t => .list [.nat t.nonce, .nat t.gasPrice, .nat t.gas, toRlp t.to, .nat t.value,
      .bytes t.data, .nat t.v, .nat t.r, .nat t.s]
  | .eip2930 t => .list [.nat t.chainId, .nat t.nonce, .nat t.gasPrice, .nat t.gas,
      toRlp t.to, .nat t.value, .bytes t.data, accessListRlp t.accessList, .nat t.yParity,
      .nat t.r, .nat t.s]
  | .eip1559 t => .list [.nat t.chainId, .nat t.nonce, .nat t.maxPriorityFeePerGas,
      .nat t.maxFeePerGas, .nat t.gas, toRlp t.to, .nat t.value, .bytes t.data,
      accessListRlp t.accessList, .nat t.yParity, .nat t.r, .nat t.s]
  | .eip4844 t => .list [.nat t.chainId, .nat t.nonce, .nat t.maxPriorityFeePerGas,
      .nat t.maxFeePerGas, .nat t.gas, addressRlp t.to, .nat t.value, .bytes t.data,
      accessListRlp t.accessList, .nat t.maxFeePerBlobGas,
      .list (t.blobVersionedHashes.map wordRlp), .nat t.yParity, .nat t.r, .nat t.s]
  | .eip7702 t => .list [.nat t.chainId, .nat t.nonce, .nat t.maxPriorityFeePerGas,
      .nat t.maxFeePerGas, .nat t.gas, addressRlp t.to, .nat t.value, .bytes t.data,
      accessListRlp t.accessList, authorizationsRlp t.authorizations, .nat t.yParity,
      .nat t.r, .nat t.s]

/-- `type ‖ payload` for a typed transaction. -/
def typed (ty : UInt8) (payload : ByteArray) : ByteArray := ⟨#[ty]⟩ ++ payload

/-- `encode_transaction`: RLP for legacy, `type ‖ rlp(fields)` otherwise; Keccak is the tx hash. -/
def encode (tx : Transaction) : ByteArray :=
  match tx with
  | .legacy _ => tx.fieldsRlp.encode
  | .eip2930 _ => typed 1 tx.fieldsRlp.encode
  | .eip1559 _ => typed 2 tx.fieldsRlp.encode
  | .eip4844 _ => typed 3 tx.fieldsRlp.encode
  | .eip7702 _ => typed 4 tx.fieldsRlp.encode

/-- Block-body form: a list for legacy, an opaque byte string for typed transactions. -/
def bodyRlp (tx : Transaction) : Rlp :=
  match tx with
  | .legacy _ => tx.fieldsRlp
  | .eip2930 _ | .eip1559 _ | .eip4844 _ | .eip7702 _ => .bytes tx.encode

/-- The EIP-155 chain id encoded in a legacy `v ≥ 35`. -/
def legacyChainId (v : Nat) : Nat := (v - 35) / 2

/-- Signing preimage; legacy `v ∈ {27, 28}` is pre-EIP-155, any other `v` is EIP-155. -/
def signingMessage : Transaction → ByteArray
  | .legacy t =>
    let base := [Rlp.nat t.nonce, .nat t.gasPrice, .nat t.gas, toRlp t.to, .nat t.value,
      .bytes t.data]
    if t.v = 27 ∨ t.v = 28 then (Rlp.list base).encode
    else (Rlp.list (base ++ [.nat (legacyChainId t.v), .nat 0, .nat 0])).encode
  | .eip2930 t => typed 1 (Rlp.list [.nat t.chainId, .nat t.nonce, .nat t.gasPrice,
      .nat t.gas, toRlp t.to, .nat t.value, .bytes t.data,
      accessListRlp t.accessList]).encode
  | .eip1559 t => typed 2 (Rlp.list [.nat t.chainId, .nat t.nonce,
      .nat t.maxPriorityFeePerGas, .nat t.maxFeePerGas, .nat t.gas, toRlp t.to, .nat t.value,
      .bytes t.data, accessListRlp t.accessList]).encode
  | .eip4844 t => typed 3 (Rlp.list [.nat t.chainId, .nat t.nonce, .nat t.maxPriorityFeePerGas,
      .nat t.maxFeePerGas, .nat t.gas, addressRlp t.to, .nat t.value, .bytes t.data,
      accessListRlp t.accessList, .nat t.maxFeePerBlobGas,
      .list (t.blobVersionedHashes.map wordRlp)]).encode
  | .eip7702 t => typed 4 (Rlp.list [.nat t.chainId, .nat t.nonce, .nat t.maxPriorityFeePerGas,
      .nat t.maxFeePerGas, .nat t.gas, addressRlp t.to, .nat t.value, .bytes t.data,
      accessListRlp t.accessList, authorizationsRlp t.authorizations]).encode

/-! ## Decoding -/

open Rlp in
/-- Decode an access list `[[address, [key, …]], …]`. -/
def decodeAccessList (r : Rlp) : Except DecodeError (List AccessListItem) := do
  let items ← asList "accessList" r
  items.mapM fun item => do
    match ← asList "accessList entry" item with
    | [a, keys] =>
      let address ← asAddress "accessList address" a
      let keys ← asList "accessList storage keys" keys
      let storageKeys ← keys.mapM (asWord "accessList storage key")
      return { address, storageKeys }
    | _ => throw (.unexpected "accessList entry must have 2 fields")

open Rlp in
/-- Decode an EIP-7702 authorization list with the reference field widths. -/
def decodeAuthorizations (r : Rlp) : Except DecodeError (List Authorization) := do
  let items ← asList "authorizationList" r
  items.mapM fun item => do
    match ← asList "authorization" item with
    | [chainId, address, nonce, yParity, r, s] =>
      return { chainId := ← asU256 "authorization chainId" chainId,
               address := ← asAddress "authorization address" address,
               nonce := ← asU64 "authorization nonce" nonce,
               yParity := ← asNat "authorization yParity" 1 yParity,
               r := ← asU256 "authorization r" r, s := ← asU256 "authorization s" s }
    | _ => throw (.unexpected "authorization must have 6 fields")

open Rlp in
/-- Decode the fields of a legacy transaction. -/
def decodeLegacy (items : List Rlp) : Except DecodeError Transaction :=
  match items with
  | [nonce, gasPrice, gas, to, value, data, v, r, s] => do
    return .legacy {
      nonce := ← asU256 "nonce" nonce, gasPrice := ← asUint "gasPrice" gasPrice,
      gas := ← asUint "gas" gas, to := ← asTo "to" to, value := ← asU256 "value" value,
      data := ← asBytes "data" data, v := ← asU256 "v" v, r := ← asU256 "r" r,
      s := ← asU256 "s" s }
  | _ => throw (.unexpected s!"legacy transaction must have 9 fields, got {items.length}")

open Rlp in
/-- Decode the payload of a typed transaction of type `ty` (`decode_transaction`). -/
def decodeTyped (ty : Nat) (payload : ByteArray) : Except DecodeError Transaction := do
  let items ← asList "typed transaction" (← Rlp.decode payload)
  match ty, items with
  | 1, [chainId, nonce, gasPrice, gas, to, value, data, al, yParity, r, s] =>
    return .eip2930 {
      chainId := ← asU64 "chainId" chainId, nonce := ← asU256 "nonce" nonce,
      gasPrice := ← asUint "gasPrice" gasPrice, gas := ← asUint "gas" gas,
      to := ← asTo "to" to, value := ← asU256 "value" value, data := ← asBytes "data" data,
      accessList := ← decodeAccessList al, yParity := ← asU256 "yParity" yParity,
      r := ← asU256 "r" r, s := ← asU256 "s" s }
  | 2, [chainId, nonce, maxPrio, maxFee, gas, to, value, data, al, yParity, r, s] =>
    return .eip1559 {
      chainId := ← asU64 "chainId" chainId, nonce := ← asU256 "nonce" nonce,
      maxPriorityFeePerGas := ← asUint "maxPriorityFeePerGas" maxPrio,
      maxFeePerGas := ← asUint "maxFeePerGas" maxFee, gas := ← asUint "gas" gas,
      to := ← asTo "to" to, value := ← asU256 "value" value, data := ← asBytes "data" data,
      accessList := ← decodeAccessList al, yParity := ← asU256 "yParity" yParity,
      r := ← asU256 "r" r, s := ← asU256 "s" s }
  | 3, [chainId, nonce, maxPrio, maxFee, gas, to, value, data, al, maxBlobFee, hashes,
        yParity, r, s] =>
    return .eip4844 {
      chainId := ← asU64 "chainId" chainId, nonce := ← asU256 "nonce" nonce,
      maxPriorityFeePerGas := ← asUint "maxPriorityFeePerGas" maxPrio,
      maxFeePerGas := ← asUint "maxFeePerGas" maxFee, gas := ← asUint "gas" gas,
      to := ← asAddress "to" to, value := ← asU256 "value" value,
      data := ← asBytes "data" data, accessList := ← decodeAccessList al,
      maxFeePerBlobGas := ← asU256 "maxFeePerBlobGas" maxBlobFee,
      blobVersionedHashes := ← (← asList "blobVersionedHashes" hashes).mapM
        (asWord "blob versioned hash"),
      yParity := ← asU256 "yParity" yParity, r := ← asU256 "r" r, s := ← asU256 "s" s }
  | 4, [chainId, nonce, maxPrio, maxFee, gas, to, value, data, al, auths, yParity, r, s] =>
    return .eip7702 {
      chainId := ← asU64 "chainId" chainId, nonce := ← asU64 "nonce" nonce,
      maxPriorityFeePerGas := ← asUint "maxPriorityFeePerGas" maxPrio,
      maxFeePerGas := ← asUint "maxFeePerGas" maxFee, gas := ← asUint "gas" gas,
      to := ← asAddress "to" to, value := ← asU256 "value" value,
      data := ← asBytes "data" data, accessList := ← decodeAccessList al,
      authorizations := ← decodeAuthorizations auths,
      yParity := ← asU256 "yParity" yParity, r := ← asU256 "r" r, s := ← asU256 "s" s }
  | 1, _ | 2, _ | 3, _ | 4, _ =>
    throw (.unexpected s!"type-{ty} transaction has wrong field count {items.length}")
  | _, _ => throw (.unexpected s!"unsupported transaction type {ty}")

/-- Decode a typed envelope `type ‖ rlp(fields)`. -/
def decodeEnvelope (b : ByteArray) : Except Rlp.DecodeError Transaction :=
  match Rlp.byteAt? b 0 with
  | none => .error (.unexpected "empty typed transaction")
  | some ty => decodeTyped ty.toNat (b.extract 1 b.size)

/-- Decode a block-body transaction item (`decode_transaction`). -/
def ofRlp : Rlp → Except Rlp.DecodeError Transaction
  | .list items => decodeLegacy items
  | .bytes b => decodeEnvelope b

/-- Decode a canonical encoding (inverse of `encode`). -/
def decode (b : ByteArray) : Except Rlp.DecodeError Transaction :=
  match Rlp.byteAt? b 0 with
  | some p => if p ≥ 0xc0 then do decodeLegacy (← Rlp.asList "transaction" (← Rlp.decode b))
              else decodeEnvelope b
  | none => .error .truncated

end Transaction

end EvmLean
