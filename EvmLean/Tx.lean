import EvmLean.Interpreter
import EvmLean.Crypto.Secp256k1
import EvmLean.Tx.Types
import EvmLean.Tx.Codec

/-!
# Transactions

Validation, intrinsic gas and execution of a single transaction, following
`ethereum/execution-specs` (`src/ethereum/forks/{cancun,prague,osaka}/`). Fork differences:

* Prague: set-code transactions (EIP-7702: authorization cost, empty-list check, delegated
  senders allowed by EIP-3607), the calldata floor (EIP-7623), blob parameters (EIP-7691).
* Osaka: the transaction gas limit cap `2²⁴` (EIP-7825) and at most six blobs per
  transaction (`BLOB_COUNT_LIMIT`, EIP-7594).

The table maps definitions to the reference:

| Lean                 | execution-specs                                      |
|----------------------|------------------------------------------------------|
| `intrinsicGas`       | `calculate_intrinsic_cost` (`transactions.py`)       |
| `validate`           | `validate_transaction` (`transactions.py`)           |
| `chainIdOf`          | `chain_id` (`transactions.py`)                       |
| `resolveSender`      | `recover_sender` (`transactions.py`)                 |
| `check`              | `check_transaction` (`fork.py`)                      |
| `process`            | `process_transaction` + `prepare_message` (`fork.py`, `utils/message.py`) |

Every rejection is a constructor of `InvalidTx`; fee arithmetic is in `Nat`, so a huge
`gas * maxFeePerGas` is simply a large number that fails the balance check, never a
wrapped-around one. State changes use the interpreter's `modify_state` helpers
(`Interpreter.modifyState` …), so an account left empty by a change is deleted (EIP-161).
-/

namespace EvmLean.Tx

/-! ## Constants (`GasCosts` in `cancun/vm/gas.py`) -/

/-- `TX_BASE`: base cost of every transaction. -/
def txBase : Nat := 21000
/-- `TX_DATA_TOKEN_STANDARD`: gas per calldata token (a zero byte is one token, a non-zero
byte four, so this is Cancun's 4 per zero / 16 per non-zero byte). -/
def txDataTokenStandard : Nat := 4
/-- `TX_DATA_TOKEN_FLOOR` (EIP-7623, Prague): floor gas per calldata token. -/
def txDataTokenFloor : Nat := 10
/-- `TX_MAX_GAS_LIMIT` (EIP-7825, Osaka): maximum gas limit of a transaction. -/
def txMaxGasLimit : Nat := 2 ^ 24
/-- `BLOB_COUNT_LIMIT` (Osaka): maximum number of blobs per transaction. -/
def blobCountLimit : Nat := 6
/-- `TX_ACCESS_LIST_ADDRESS`. -/
def txAccessListAddress : Nat := 2400
/-- `TX_ACCESS_LIST_STORAGE_KEY`. -/
def txAccessListStorageKey : Nat := 1900
/-- `GasCosts.PER_BLOB`: blob gas per blob (EIP-4844). -/
def gasPerBlob : Nat := 2 ^ 17
/-- `VERSIONED_HASH_VERSION_KZG`: required first byte of a blob versioned hash. -/
def versionedHashVersionKzg : Nat := 0x01
/-- Per-fork blob parameters (EIP-4844; EIP-7691 raised them in Prague). -/
structure BlobParams where
  /-- `BLOB_TARGET_GAS_PER_BLOCK`. -/
  targetGasPerBlock : Nat
  /-- `MAX_BLOB_GAS_PER_BLOCK`. -/
  maxGasPerBlock : Nat

/-- Blob parameters of `fork`. Cancun: target 3 blobs, max 6 (`cancun/vm/gas.py`,
`cancun/fork.py`). Prague and Osaka: target 6, max 9 (EIP-7691). -/
def blobParams : Fork → BlobParams
  | .cancun => { targetGasPerBlock := 393216, maxGasPerBlock := 786432 }
  | .prague => { targetGasPerBlock := 786432, maxGasPerBlock := 1179648 }
  | .osaka => { targetGasPerBlock := 786432, maxGasPerBlock := 1179648 }

/-! ## Intrinsic gas and blob fees -/

/-- Number of zero bytes in `b`. -/
def zeroBytes (b : ByteArray) : Nat := b.foldl (fun n x => if x = 0 then n + 1 else n) 0

/-- Number of calldata tokens: one per zero byte, four per non-zero byte (EIP-7623). -/
def calldataTokens (data : ByteArray) : Nat :=
  let zeros := zeroBytes data
  zeros + (data.size - zeros) * 4

/-- The two intrinsic costs of a transaction (`IntrinsicGasCost`). -/
structure IntrinsicGas where
  /-- Charged before execution: base, calldata, creation, access list, authorizations. -/
  regular : Nat
  /-- EIP-7623 floor (Prague): the minimum gas a transaction is charged. -/
  calldataFloor : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Gas charged before execution starts. Mirrors `calculate_intrinsic_cost`: base cost,
calldata (4 per token, i.e. 4 per zero byte and 16 per non-zero byte), creation (32000 plus
the EIP-3860 init-code charge), access list (2400 per address, 1900 per storage key) and
EIP-7702 authorizations (25000 each); plus the EIP-7623 floor `21000 + 10 · tokens`, which
`validate` and `process` only use from Prague. -/
def intrinsicGas (tx : Transaction) : IntrinsicGas :=
  let tokens := calldataTokens tx.data
  let dataCost := tokens * txDataTokenStandard
  let createCost := if tx.isCreate then Gas.createCost tx.data.size else 0
  let accessListCost := tx.accessList.foldl
    (fun c i => c + txAccessListAddress + i.storageKeys.length * txAccessListStorageKey) 0
  let authCost := Interpreter.authPerEmptyAccount * tx.authorizations.length
  { regular := txBase + dataCost + createCost + accessListCost + authCost
    calldataFloor := tokens * txDataTokenFloor + txBase }

/-- `calculate_total_blob_gas`: blob gas consumed by `tx`. -/
def totalBlobGas (tx : Transaction) : Nat := gasPerBlob * tx.blobVersionedHashes.length

/-! ## Errors -/

/-- Why a signature is malformed (`InvalidSignatureError` in the reference). -/
inductive SignatureError where
  /-- `r` is zero or not below the curve order. -/
  | badR
  /-- `s` is zero or above half the curve order (EIP-2). -/
  | badS
  /-- Legacy `v` is neither 27/28 nor a valid EIP-155 value. -/
  | badV
  /-- Typed-transaction y-parity is not 0 or 1. -/
  | badYParity
  /-- Public-key recovery failed. -/
  | recoveryFailed
  deriving DecidableEq, Repr, Inhabited

/-- Why a transaction is invalid, i.e. cannot be included in a block. Constructor names
follow the reference's exception classes. -/
inductive InvalidTx where
  /-- `TransactionTypeError`: a transaction type the fork does not know. -/
  | unsupportedType (ty : Nat)
  /-- `TransactionGasLimitExceededError` (EIP-7825, Osaka): gas limit above `2²⁴`. -/
  | gasLimitAboveCap (gasLimit : Nat)
  /-- `BlobCountExceededError` (Osaka): more than six blobs. -/
  | blobCountExceeded (count : Nat)
  /-- `EmptyAuthorizationListError` (EIP-7702). -/
  | emptyAuthorizationList
  /-- `InsufficientTransactionGasError`: gas limit below the intrinsic cost. -/
  | intrinsicGasTooLow (intrinsic gasLimit : Nat)
  /-- `InitCodeTooLargeError` (EIP-3860). -/
  | initCodeSizeExceeded (size : Nat)
  /-- `NonceOverflowError` (EIP-2681): nonce ≥ 2⁶⁴ - 1. -/
  | nonceOverflow (nonce : Nat)
  /-- `PriorityFeeGreaterThanMaxFeeError`. -/
  | priorityFeeGreaterThanMaxFee (priority max : Nat)
  /-- `GasUsedExceedsLimitError`: gas limit above the gas left in the block. -/
  | gasAllowanceExceeded (gasLimit available : Nat)
  /-- `BlobGasLimitExceededError`: blob gas above the blob gas left in the block. -/
  | blobGasLimitExceeded (blobGas available : Nat)
  /-- `WrongChainIdError`. -/
  | wrongChainId (expected actual : Nat)
  /-- `InvalidSignatureError`. -/
  | invalidSignature (e : SignatureError)
  /-- `InsufficientMaxFeePerGasError`: max fee per gas below the base fee. -/
  | insufficientMaxFeePerGas (maxFee baseFee : Nat)
  /-- Legacy/EIP-2930 gas price below the base fee (a bare `InvalidBlock` in the
  reference). -/
  | gasPriceBelowBaseFee (gasPrice baseFee : Nat)
  /-- `NoBlobDataError`: blob transaction without blobs. -/
  | noBlobData
  /-- `InvalidBlobVersionedHashError`: a versioned hash with the wrong version byte. -/
  | invalidBlobVersionedHash
  /-- `InsufficientMaxFeePerBlobGasError`. -/
  | insufficientMaxFeePerBlobGas (maxFee blobGasPrice : Nat)
  /-- `NonceMismatchError("nonce too low")`. -/
  | nonceTooLow (accountNonce txNonce : Nat)
  /-- `NonceMismatchError("nonce too high")`. -/
  | nonceTooHigh (accountNonce txNonce : Nat)
  /-- `InsufficientBalanceError`: balance below `maxGasFee + value`. -/
  | insufficientBalance (balance required : Nat)
  /-- `InvalidSenderError("not EOA")` (EIP-3607): the sender has code. -/
  | senderNotEOA
  deriving DecidableEq, Repr, Inhabited

/-- Human-readable description of an invalid-transaction reason. -/
def InvalidTx.toString : InvalidTx → String
  | .unsupportedType t => s!"transaction type {t} not supported by this fork"
  | .gasLimitAboveCap g => s!"gas limit {g} above the transaction cap 2^24"
  | .blobCountExceeded n => s!"{n} blobs exceed the per-transaction limit"
  | .emptyAuthorizationList => "set-code transaction with empty authorization list"
  | .intrinsicGasTooLow i g => s!"intrinsic gas too low ({i} > gas limit {g})"
  | .initCodeSizeExceeded n => s!"init code size {n} exceeds limit"
  | .nonceOverflow n => s!"nonce {n} ≥ 2^64-1"
  | .priorityFeeGreaterThanMaxFee p m => s!"priority fee {p} > max fee {m}"
  | .gasAllowanceExceeded g a => s!"gas limit {g} exceeds block gas left {a}"
  | .blobGasLimitExceeded g a => s!"blob gas {g} exceeds block blob gas left {a}"
  | .wrongChainId e a => s!"wrong chain id {a}, expected {e}"
  | .invalidSignature e => s!"invalid signature ({repr e})"
  | .insufficientMaxFeePerGas m b => s!"max fee per gas {m} < base fee {b}"
  | .gasPriceBelowBaseFee p b => s!"gas price {p} < base fee {b}"
  | .noBlobData => "blob transaction without blobs"
  | .invalidBlobVersionedHash => "invalid blob versioned hash version"
  | .insufficientMaxFeePerBlobGas m p => s!"max fee per blob gas {m} < blob gas price {p}"
  | .nonceTooLow a t => s!"nonce too low (account {a}, tx {t})"
  | .nonceTooHigh a t => s!"nonce too high (account {a}, tx {t})"
  | .insufficientBalance b r => s!"insufficient balance {b} < {r}"
  | .senderNotEOA => "sender has code (EIP-3607)"

instance : ToString InvalidTx := ⟨InvalidTx.toString⟩

/-! ## Validation -/

/-- Max fee and max priority fee of an EIP-1559-style transaction
(`FeeMarketCapableTransaction`), if it is one. -/
def feeCaps? : Transaction → Option (Nat × Nat)
  | .legacy _ => none
  | .eip2930 _ => none
  | .eip1559 t => some (t.maxFeePerGas, t.maxPriorityFeePerGas)
  | .eip4844 t => some (t.maxFeePerGas, t.maxPriorityFeePerGas)
  | .eip7702 t => some (t.maxFeePerGas, t.maxPriorityFeePerGas)

/-- Is the transaction's type known to `fork`? Set-code transactions start in Prague (before
it, `decode_transaction` raises `TransactionTypeError`). -/
def typeSupported (fork : Fork) : Transaction → Bool
  | .legacy _ | .eip2930 _ | .eip1559 _ | .eip4844 _ => true
  | .eip7702 _ => fork ≥ .prague

/-- Stateless validity; returns the intrinsic gas. Mirrors `validate_transaction`: the gas
limit must cover the intrinsic cost (and, from Prague, the calldata floor); from Osaka it
must not exceed `2²⁴`. -/
def validate (fork : Fork) (tx : Transaction) : Except InvalidTx IntrinsicGas := do
  if !typeSupported fork tx then throw (.unsupportedType tx.typeByte)
  let intrinsic := intrinsicGas tx
  let required :=
    if fork ≥ .prague then max intrinsic.regular intrinsic.calldataFloor else intrinsic.regular
  if required > tx.gas then throw (.intrinsicGasTooLow required tx.gas)
  if tx.isCreate && tx.data.size > Gas.maxInitCodeSize fork then
    throw (.initCodeSizeExceeded tx.data.size)
  if fork ≥ .osaka && tx.gas > txMaxGasLimit then throw (.gasLimitAboveCap tx.gas)
  if tx.nonce ≥ Gas.maxNonce then throw (.nonceOverflow tx.nonce)
  match feeCaps? tx with
  | some (maxFee, maxPrio) =>
    if maxFee < maxPrio then throw (.priorityFeeGreaterThanMaxFee maxPrio maxFee)
  | none => pure ()
  return intrinsic

/-- The chain id a transaction commits to, if any. Mirrors `chain_id`: legacy transactions
with `v ∈ {27, 28}` predate EIP-155 and commit to none. -/
def chainIdOf : Transaction → Except InvalidTx (Option Nat)
  | .legacy t =>
    if t.v = 27 ∨ t.v = 28 then .ok none
    else if t.v < 35 then .error (.invalidSignature .badV)
    else
      let c := Transaction.legacyChainId t.v
      if c > 2 ^ 64 - 1 then .error (.invalidSignature .badV) else .ok (some c)
  | .eip2930 t => .ok (some t.chainId)
  | .eip1559 t => .ok (some t.chainId)
  | .eip4844 t => .ok (some t.chainId)
  | .eip7702 t => .ok (some t.chainId)

/-- A y-parity must be 0 or 1. -/
def yParityId (y : Nat) : Except InvalidTx Nat :=
  if y ≤ 1 then .ok y else .error (.invalidSignature .badYParity)

/-- The secp256k1 recovery id encoded in the signature (`recover_sender`). -/
def recoveryId : Transaction → Except InvalidTx Nat
  | .legacy t =>
    if t.v = 27 ∨ t.v = 28 then .ok (t.v - 27)
    else if t.v ≥ 35 then .ok ((t.v - 35) % 2)
    else .error (.invalidSignature .badV)
  | .eip2930 t => yParityId t.yParity
  | .eip1559 t => yParityId t.yParity
  | .eip4844 t => yParityId t.yParity
  | .eip7702 t => yParityId t.yParity

/-- The address controlled by an uncompressed 64-byte public key: the low 20 bytes of its
Keccak. -/
def addressOfPublicKey (crypto : Crypto) (pub : ByteArray) : Address :=
  Word.toAddress (crypto.keccak256 pub)

/-- The transaction sender. Mirrors `recover_sender`: checks `r`, `s` (EIP-2 low-`s`) and
`v`/y-parity, then recovers the signer's key from the signing hash. When `hint` is given
(the conformance fixtures record each transaction's sender) the signature checks are still
performed but the address is taken from the hint instead of being recovered. -/
def resolveSender (crypto : Crypto) (tx : Transaction) (hint : Option Address) :
    Except InvalidTx Address := do
  let n := Secp256k1.n
  if tx.r = 0 ∨ tx.r ≥ n then throw (.invalidSignature .badR)
  if tx.s = 0 ∨ tx.s > n / 2 then throw (.invalidSignature .badS)
  let recId ← recoveryId tx
  match hint with
  | some a => return a
  | none =>
    let hash := Bytes.ofWord (crypto.keccak256 tx.signingMessage)
    match crypto.ecrecover hash recId tx.r tx.s with
    | some pub => return addressOfPublicKey crypto pub
    | none => throw (.invalidSignature .recoveryFailed)

/-- What `check_transaction` returns for an includable transaction. -/
structure Checked where
  /-- The sender. -/
  sender : Address
  /-- Price charged per unit of gas. -/
  effectiveGasPrice : Nat
  /-- Blob versioned hashes (empty unless a blob transaction). -/
  blobVersionedHashes : List Word
  /-- Blob gas consumed. -/
  blobGasUsed : Nat
  deriving DecidableEq, Inhabited

/-- Effective gas price and maximum execution-gas fee (`check_transaction`). Fee-market
transactions pay `min(maxPriorityFee, maxFee - baseFee) + baseFee`; others pay their gas
price. Either way the price must cover the base fee. -/
def gasPricing (baseFee : Nat) : Transaction → Except InvalidTx (Nat × Nat)
  | .legacy t => fixed t.gasPrice t.gas
  | .eip2930 t => fixed t.gasPrice t.gas
  | .eip1559 t => market t.maxFeePerGas t.maxPriorityFeePerGas t.gas
  | .eip4844 t => market t.maxFeePerGas t.maxPriorityFeePerGas t.gas
  | .eip7702 t => market t.maxFeePerGas t.maxPriorityFeePerGas t.gas
where
  /-- Pricing of a legacy or EIP-2930 transaction. -/
  fixed (price gas : Nat) : Except InvalidTx (Nat × Nat) :=
    if price < baseFee then .error (.gasPriceBelowBaseFee price baseFee)
    else .ok (price, gas * price)
  /-- Pricing of an EIP-1559 or EIP-4844 transaction. -/
  market (maxFee maxPrio gas : Nat) : Except InvalidTx (Nat × Nat) :=
    if maxFee < baseFee then .error (.insufficientMaxFeePerGas maxFee baseFee)
    else .ok (min maxPrio (maxFee - baseFee) + baseFee, gas * maxFee)

/-- The version byte of a blob versioned hash (its most significant byte). -/
def versionByte (h : Word) : Nat := h.toNat / 2 ^ 248

/-- EIP-4844 checks of `check_transaction` for a blob transaction; returns the maximum
blob-gas fee to add to the balance requirement (zero for other types). From Osaka a
transaction carries at most `BLOB_COUNT_LIMIT` blobs. -/
def blobChecks (fork : Fork) (env : BlockEnv) : Transaction → Except InvalidTx Nat
  | .legacy _ => .ok 0
  | .eip2930 _ => .ok 0
  | .eip1559 _ => .ok 0
  | .eip7702 _ => .ok 0
  | .eip4844 t => do
    if t.blobVersionedHashes.isEmpty then throw .noBlobData
    if fork ≥ .osaka && t.blobVersionedHashes.length > blobCountLimit then
      throw (.blobCountExceeded t.blobVersionedHashes.length)
    if t.blobVersionedHashes.any (versionByte · ≠ versionedHashVersionKzg) then
      throw .invalidBlobVersionedHash
    let price := Gas.blobGasPrice fork env.excessBlobGas
    if t.maxFeePerBlobGas < price then
      throw (.insufficientMaxFeePerBlobGas t.maxFeePerBlobGas price)
    return totalBlobGas (.eip4844 t) * t.maxFeePerBlobGas

/-- Whether `tx` can be included given the block environment, the gas and blob gas still
available in the block, and the current world. Mirrors `check_transaction`, in the same
order of checks. From Prague a set-code transaction needs a non-empty authorization list,
and a sender whose code is a delegation designator counts as an EOA (EIP-7702). -/
def check (crypto : Crypto) (fork : Fork) (env : BlockEnv) (gasAvailable blobGasAvailable : Nat)
    (world : World) (tx : Transaction) (senderHint : Option Address) :
    Except InvalidTx Checked := do
  if tx.gas > gasAvailable then throw (.gasAllowanceExceeded tx.gas gasAvailable)
  let blobGasUsed := totalBlobGas tx
  if blobGasUsed > blobGasAvailable then
    throw (.blobGasLimitExceeded blobGasUsed blobGasAvailable)
  match ← chainIdOf tx with
  | some c => if c ≠ env.chainId then throw (.wrongChainId env.chainId c)
  | none => pure ()
  let sender ← resolveSender crypto tx senderHint
  let account := world.account sender
  let (effectiveGasPrice, maxGasFee) ← gasPricing env.baseFee tx
  let maxBlobFee ← blobChecks fork env tx
  match tx with
  | .eip7702 t => if t.authorizations.isEmpty then throw .emptyAuthorizationList
  | .legacy _ | .eip2930 _ | .eip1559 _ | .eip4844 _ => pure ()
  if account.nonce > tx.nonce then throw (.nonceTooLow account.nonce tx.nonce)
  if account.nonce < tx.nonce then throw (.nonceTooHigh account.nonce tx.nonce)
  let required := maxGasFee + maxBlobFee + tx.value
  if account.balance.toNat < required then
    throw (.insufficientBalance account.balance.toNat required)
  if account.code.size ≠ 0 &&
      !(fork ≥ .prague && Interpreter.isValidDelegation account.code) then
    throw .senderNotEOA
  return { sender, effectiveGasPrice, blobVersionedHashes := tx.blobVersionedHashes,
           blobGasUsed }

/-! ## Execution -/

/-- Credit `amount` wei to `a` (`create_ether`); an account left empty is deleted
(`modify_state`, EIP-161). The sum is reduced modulo 2²⁵⁶, which
cannot happen for real ether amounts. -/
def creditBalance (w : World) (a : Address) (amount : Nat) : World :=
  Interpreter.modifyState w a fun acc => { acc with balance := BitVec.ofNat 256 (acc.balance.toNat + amount) }

/-- Delete every touched account that exists and is empty (EIP-161,
`destroy_touched_empty_accounts`). -/
def destroyTouchedEmpty (w : World) (touched : AddressSet) : World :=
  touched.foldl (fun w a => match w.account? a with
    | some acc => if acc.isEmpty then w.erase a else w
    | none => w) w

/-- Precompile addresses of `fork` (all lie in `0x01 … 0x100` up to Osaka), pre-warmed by
every transaction (EIP-2929). Uses `Precompile.isPrecompile` as the single source of truth. -/
def precompileAddresses (fork : Fork) : List Address :=
  (List.range 0x101).filterMap fun i =>
    let a : Address := BitVec.ofNat 160 i
    if Precompile.isPrecompile fork a then some a else none

/-- Add `key` to the warm storage keys of `a`. -/
def warmKey (s : StorageKeySet) (a : Address) (key : Word) : StorageKeySet :=
  s.insert a ((s.getD a ∅).insert key)

/-- Why a transaction could not be processed. -/
inductive TxError where
  /-- The transaction is invalid; the block containing it is invalid. -/
  | invalid (e : InvalidTx)
  /-- The interpreter ran out of fuel (not an EVM outcome; retry with more fuel). -/
  | outOfFuel
  deriving Inhabited

/-- Human-readable description of a transaction error. -/
def TxError.toString : TxError → String
  | .invalid e => e.toString
  | .outOfFuel => "interpreter out of fuel"

instance : ToString TxError := ⟨TxError.toString⟩

/-- The result of processing an includable transaction. -/
structure TxOutput where
  /-- World state after the transaction. -/
  world : World
  /-- The sender. -/
  sender : Address
  /-- Gas used after the refund; added to the block's gas used. -/
  gasUsed : Nat
  /-- Blob gas used. -/
  blobGasUsed : Nat
  /-- Logs emitted (empty unless successful). -/
  logs : Array Log
  /-- Whether execution succeeded (receipt status). -/
  succeeded : Bool
  deriving Inhabited

/-- The top-level message of `tx` sent by `sender` (`prepare_message`). `world` is the state
after the nonce increment and gas purchase; `senderNonce` the nonce before the increment,
which determines the address of a created contract. -/
def prepareMessage (crypto : Crypto) (fork : Fork) (env : BlockEnv) (world : World)
    (tx : Transaction) (sender : Address) (senderNonce gas : Nat) : Message :=
  let (currentTarget, data, code, codeAddress) := match tx.to with
    | none => (Interpreter.createAddress crypto.keccak256 sender senderNonce,
               ByteArray.empty, tx.data, none)
    | some to => (to, tx.data, world.code to, some to)
  let warmAddresses : AddressSet :=
    (precompileAddresses fork ++ [sender, currentTarget, env.coinbase] ++
      tx.accessList.map (·.address)).foldl (fun s a => s.insert a) ∅
  let warmKeys : StorageKeySet := tx.accessList.foldl
    (fun s i => i.storageKeys.foldl (fun s k => warmKey s i.address k) s) ∅
  { caller := sender, target := tx.to, currentTarget, gas,
    value := BitVec.ofNat 256 tx.value, data, codeAddress, code, depth := 0,
    shouldTransferValue := true, isStatic := false,
    accessedAddresses := warmAddresses, accessedStorageKeys := warmKeys }

/-- Execute `tx` in `world`. Mirrors `process_transaction`: validate and check, buy gas
(execution and blob gas), increment the nonce, run the top-level message (pre-warming the
origin, the target or new contract address, the precompiles, the coinbase (EIP-3651) and
the access list), refund unused gas plus the capped refund counter (EIP-3529: at most a
fifth of the gas used; from Prague at least the EIP-7623 calldata floor is charged), pay
the priority fee to the coinbase, delete self-destructed accounts and touched empty
accounts. A set-code transaction's authorizations travel in `TxEnv.authorizations` and are
applied by the interpreter (`Interpreter.applyTopLevelDelegation`). Transient storage starts empty and is discarded
afterwards (EIP-1153). `fuel` bounds interpreter steps. -/
def process (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv)
    (gasAvailable blobGasAvailable : Nat) (world : World) (tx : Transaction)
    (senderHint : Option Address) : Except TxError TxOutput := do
  let intrinsic ← (validate fork tx).mapError .invalid
  let c ← (check crypto fork env gasAvailable blobGasAvailable world tx senderHint).mapError
    .invalid
  let sender := c.sender
  let senderAccount := world.account sender
  let blobGasFee := c.blobGasUsed * Gas.blobGasPrice fork env.excessBlobGas
  let effectiveGasFee := tx.gas * c.effectiveGasPrice
  let w := Interpreter.incrementNonce world sender
  let w := Interpreter.setAccountBalance w sender
    (BitVec.ofNat 256 (senderAccount.balance.toNat - effectiveGasFee - blobGasFee))
  let msg := prepareMessage crypto fork env w tx sender senderAccount.nonce
    (tx.gas - intrinsic.regular)
  let ctx : Context := {
    crypto, fork, block := env,
    tx := { origin := sender, gasPrice := c.effectiveGasPrice,
            blobVersionedHashes := c.blobVersionedHashes.toArray,
            authorizations := tx.authorizations } }
  let res ← match Interpreter.processMessageCall fuel ctx w ∅ msg with
    | .ok r => pure r
    | .error _ => throw TxError.outOfFuel
  let gasUsedBeforeRefund := tx.gas - res.gasLeft
  let refund := min (gasUsedBeforeRefund / 5) res.refundCounter.toNat
  let gasUsed := gasUsedBeforeRefund - refund
  -- EIP-7623 (Prague): transactions pay at least the calldata floor.
  let gasUsed := if fork ≥ .prague then max gasUsed intrinsic.calldataFloor else gasUsed
  let gasLeft := tx.gas - gasUsed
  let priorityFeePerGas := c.effectiveGasPrice - env.baseFee
  let w := creditBalance res.world sender (gasLeft * c.effectiveGasPrice)
  let w := creditBalance w env.coinbase (gasUsed * priorityFeePerGas)
  let w := res.accountsToDelete.foldl (fun w a => w.erase a) w
  let w := destroyTouchedEmpty w res.touchedAccounts
  return { world := w, sender, gasUsed, blobGasUsed := c.blobGasUsed, logs := res.logs,
           succeeded := res.success }

end EvmLean.Tx
