import Std.Data.ExtTreeSet
import EvmLean.Fork
import EvmLean.State.Account

/-!
# Execution environment and message interface

These types are the boundary between the interpreter (`EvmLean.Interpreter`) and the
transaction layer (`EvmLean.Tx`). Field names follow `ethereum/execution-specs`.
-/

namespace EvmLean

/-- Block-level environment, constant during a block. -/
structure BlockEnv where
  /-- Chain id (`CHAINID`). -/
  chainId : Nat := 1
  /-- Fee recipient (`COINBASE`). -/
  coinbase : Address := 0
  /-- Block number (`NUMBER`). -/
  number : Nat := 0
  /-- Timestamp (`TIMESTAMP`). -/
  timestamp : Nat := 0
  /-- Block gas limit (`GASLIMIT`). -/
  gasLimit : Nat := 0
  /-- EIP-1559 base fee (`BASEFEE`). -/
  baseFee : Nat := 0
  /-- Beacon-chain randomness (`PREVRANDAO`). -/
  prevRandao : Word := 0
  /-- EIP-4844 excess blob gas of this block, from which `BLOBBASEFEE` is derived. -/
  excessBlobGas : Nat := 0
  /-- Ancestor block hashes, most recent first: `blockHashes[0]` is block `number - 1`. -/
  blockHashes : List Word := []
  /-- EIP-4788 parent beacon block root. -/
  parentBeaconBlockRoot : Word := 0
  deriving Inhabited

/-- An EIP-7702 authorization tuple; integer widths are enforced when decoding. -/
structure Authorization where
  /-- Chain id the authorization is valid on (`0` for every chain). -/
  chainId : Nat
  /-- The delegation target (the zero address clears the delegation). -/
  address : Address
  /-- The authority's nonce the authorization is valid for. -/
  nonce : Nat
  /-- Signature y-parity. -/
  yParity : Nat
  /-- Signature `r`. -/
  r : Nat
  /-- Signature `s`. -/
  s : Nat
  deriving DecidableEq, Inhabited

/-- Transaction-level environment, constant during a transaction. -/
structure TxEnv where
  /-- Transaction sender (`ORIGIN`). -/
  origin : Address := 0
  /-- Effective gas price (`GASPRICE`). -/
  gasPrice : Nat := 0
  /-- EIP-4844 blob versioned hashes (`BLOBHASH`). -/
  blobVersionedHashes : Array Word := #[]
  /-- EIP-7702 authorizations, applied before the top-level message runs. -/
  authorizations : List Authorization := []
  deriving Inhabited

/-- The cryptographic primitives, kept abstract for proofs. Not `Inhabited`: a default would
be a fake hash. -/
structure Crypto where
  /-- Keccak-256. -/
  keccak256 : ByteArray → Word
  /-- SHA-256 (32-byte digest). -/
  sha256 : ByteArray → ByteArray
  /-- RIPEMD-160 (20-byte digest). -/
  ripemd160 : ByteArray → ByteArray
  /-- BLAKE2b compression `F(rounds, h, m, t₀, t₁, final)`. -/
  blake2f : Nat → Vector UInt64 8 → Vector UInt64 16 → UInt64 → UInt64 → Bool → Vector UInt64 8
  /-- secp256k1 public-key recovery `(hash, recId, r, s) ↦ 64-byte key`. -/
  ecrecover : ByteArray → Nat → Nat → Nat → Option ByteArray
  /-- BN254 point addition (EIP-196). -/
  bn254Add : ByteArray → Option ByteArray
  /-- BN254 scalar multiplication (EIP-196). -/
  bn254Mul : ByteArray → Option ByteArray
  /-- BN254 pairing check (EIP-197). -/
  bn254Pairing : ByteArray → Option Bool
  /-- KZG proof verification `(commitment, z, y, proof)` (EIP-4844). -/
  kzgVerify : ByteArray → ByteArray → ByteArray → ByteArray → Option Bool
  /-- BLS12-381 `G1` addition on two 128-byte points (EIP-2537); `none` if invalid. -/
  bls12G1Add : ByteArray → Option ByteArray
  /-- BLS12-381 `G1` multi-scalar multiplication on `k · 160` bytes (EIP-2537). -/
  bls12G1Msm : ByteArray → Option ByteArray
  /-- BLS12-381 `G2` addition on two 256-byte points (EIP-2537). -/
  bls12G2Add : ByteArray → Option ByteArray
  /-- BLS12-381 `G2` multi-scalar multiplication on `k · 288` bytes (EIP-2537). -/
  bls12G2Msm : ByteArray → Option ByteArray
  /-- BLS12-381 pairing check on `k · 384` bytes of `(G1, G2)` pairs (EIP-2537). -/
  bls12Pairing : ByteArray → Option Bool
  /-- Map a 64-byte `𝔽ₚ` element to `G1` (EIP-2537, RFC 9380 SSWU + cofactor clearing). -/
  bls12MapFpToG1 : ByteArray → Option ByteArray
  /-- Map a 128-byte `𝔽ₚ²` element to `G2` (EIP-2537). -/
  bls12MapFp2ToG2 : ByteArray → Option ByteArray
  /-- P-256 ECDSA verification `(hash, r, s, qx, qy)` with EIP-7951's checks. -/
  p256Verify : ByteArray → Nat → Nat → Nat → Nat → Bool

/-- Everything constant during a transaction. -/
structure Context where
  /-- Cryptographic primitives. -/
  crypto : Crypto
  /-- The active fork. -/
  fork : Fork := .cancun
  /-- Block environment. -/
  block : BlockEnv := {}
  /-- Transaction environment. -/
  tx : TxEnv := {}

/-- A log entry (`LOG0`–`LOG4`). -/
structure Log where
  /-- Emitting contract. -/
  address : Address
  /-- Indexed topics (at most four). -/
  topics : Array Word
  /-- Unindexed data. -/
  data : ByteArray
  deriving Inhabited, DecidableEq

/-- Set of addresses. -/
abbrev AddressSet := Std.ExtTreeSet Address compare

/-- Set of storage keys, per address. -/
abbrev StorageKeySet := Std.ExtTreeMap Address (Std.ExtTreeSet Word compare) compare

/-- Transient storage (EIP-1153): address ↦ slot ↦ value, cleared after each transaction. -/
abbrev TransientStorage := Std.ExtTreeMap Address Storage compare

/-- A message call or contract creation, as passed to the interpreter. -/
structure Message where
  /-- Sender of the message (`CALLER`). -/
  caller : Address
  /-- `some a` for a call to `a`; `none` for a contract creation. -/
  target : Option Address
  /-- The account whose storage and balance are in use (`ADDRESS`); the new contract on create. -/
  currentTarget : Address
  /-- Gas available to the message. -/
  gas : Nat
  /-- Value (`CALLVALUE`). -/
  value : Word
  /-- Calldata, or init code for a creation. -/
  data : ByteArray
  /-- The account whose code runs (differs from `currentTarget` for `CALLCODE`/`DELEGATECALL`). -/
  codeAddress : Option Address
  /-- Code to execute. -/
  code : ByteArray
  /-- Call depth (0 for the transaction's top-level message). -/
  depth : Nat
  /-- Whether `value` is moved from `caller` to `currentTarget`. -/
  shouldTransferValue : Bool
  /-- Static context: state modifications halt exceptionally. -/
  isStatic : Bool
  /-- Warm addresses (EIP-2929) at message start. -/
  accessedAddresses : AddressSet
  /-- Warm storage keys at message start. -/
  accessedStorageKeys : StorageKeySet
  /-- Reached through an EIP-7702 delegation: a precompile at `codeAddress` is not run. -/
  disablePrecompiles : Bool := false
  deriving Inhabited

set_option linter.missingDocs false in
/-- Why execution halted exceptionally. Exceptional halts consume all gas and revert. -/
inductive ExceptionalHalt where
  | outOfGas
  | invalidOpcode
  | stackUnderflow
  | stackOverflow
  | invalidJumpDestination
  | writeInStaticContext
  | returnDataOutOfBounds
  | callDepthExceeded
  | insufficientFunds
  | addressCollision
  | invalidContractPrefix
  | contractSizeExceeded
  | initCodeSizeExceeded
  | nonceOverflow
  | precompileFailure
  deriving DecidableEq, Repr, Inhabited

/-- Outcome of executing a message to completion. -/
structure MessageResult where
  /-- Gas left over (zero after an exceptional halt). -/
  gasLeft : Nat
  /-- Accumulated refund counter (EIP-3529; may be negative before clamping). -/
  refundCounter : Int
  /-- Logs emitted (empty unless successful). -/
  logs : Array Log
  /-- Accounts scheduled for deletion by `SELFDESTRUCT`. -/
  accountsToDelete : AddressSet
  /-- EIP-161 touched accounts (deleted at the end of the transaction if empty). -/
  touchedAccounts : AddressSet
  /-- `none` on success or `REVERT`; the reason on exceptional halt. -/
  error : Option ExceptionalHalt
  /-- `true` iff the message ended in `REVERT`. -/
  reverted : Bool
  /-- Return data (or revert data). -/
  output : ByteArray
  /-- World state after the message (rolled back on failure). -/
  world : World
  /-- Transient storage after the message. -/
  transientStorage : TransientStorage
  deriving Inhabited

namespace MessageResult

/-- Did the message succeed (no exceptional halt, no revert)? -/
def success (r : MessageResult) : Bool := r.error.isNone && !r.reverted

end MessageResult

end EvmLean
