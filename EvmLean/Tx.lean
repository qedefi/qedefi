import EvmLean.Interpreter
import EvmLean.Crypto.Secp256k1
import EvmLean.Tx.Types
import EvmLean.Tx.Codec

/-!
# Transactions

Validation, intrinsic gas and execution of a single transaction, following
`ethereum/execution-specs` (`src/ethereum/forks/cancun/`):

| Lean                 | execution-specs                                      |
|----------------------|------------------------------------------------------|
| `intrinsicGas`       | `calculate_intrinsic_cost` (`transactions.py`)       |
| `validate`           | `validate_transaction` (`transactions.py`)           |
| `chainIdOf`          | `chain_id` (`transactions.py`)                       |
| `resolveSender`      | `recover_sender` (`transactions.py`)                 |
| `check`              | `check_transaction` (`fork.py`)                      |
| `process`            | `process_transaction` + `prepare_message` (`fork.py`, `utils/message.py`) |
| `blobGasPrice`       | `calculate_blob_gas_price` (`vm/gas.py`)             |

Every rejection is a constructor of `InvalidTx`; fee arithmetic is in `Nat`, so a huge
`gas * maxFeePerGas` is simply a large number that fails the balance check, never a
wrapped-around one. EIP-161 clean-up follows the reference's `modify_state`: an account that
is empty after a balance change made here is deleted.
-/

namespace EvmLean.Tx

/-! ## Constants (`GasCosts` in `cancun/vm/gas.py`) -/

/-- `TX_BASE`: base cost of every transaction. -/
def txBase : Nat := 21000
/-- `TX_DATA_PER_ZERO`. -/
def txDataPerZero : Nat := 4
/-- `TX_DATA_PER_NON_ZERO`. -/
def txDataPerNonZero : Nat := 16
/-- `TX_CREATE`: extra cost of a contract-creation transaction. -/
def txCreate : Nat := 32000
/-- `TX_ACCESS_LIST_ADDRESS`. -/
def txAccessListAddress : Nat := 2400
/-- `TX_ACCESS_LIST_STORAGE_KEY`. -/
def txAccessListStorageKey : Nat := 1900
/-- `CODE_INIT_PER_WORD` (EIP-3860). -/
def codeInitPerWord : Nat := 2
/-- `MAX_INIT_CODE_SIZE = 2 * MAX_CODE_SIZE` (EIP-3860, `vm/interpreter.py`). -/
def maxInitCodeSize : Nat := 2 * 0x6000
/-- `GasCosts.PER_BLOB`: blob gas per blob (EIP-4844). -/
def gasPerBlob : Nat := 2 ^ 17
/-- `BLOB_MIN_GASPRICE`. -/
def minBlobGasPrice : Nat := 1
/-- `VERSIONED_HASH_VERSION_KZG`: required first byte of a blob versioned hash. -/
def versionedHashVersionKzg : Nat := 0x01
/-- The EIP-2681 nonce limit: transaction nonces must be below `2⁶⁴ - 1`. -/
def maxNonce : Nat := 2 ^ 64 - 1

/-- Per-fork blob parameters (EIP-4844; EIP-7691 raised them in Prague). -/
structure BlobParams where
  /-- `BLOB_TARGET_GAS_PER_BLOCK`. -/
  targetGasPerBlock : Nat
  /-- `MAX_BLOB_GAS_PER_BLOCK`. -/
  maxGasPerBlock : Nat
  /-- `BLOB_BASE_FEE_UPDATE_FRACTION`. -/
  baseFeeUpdateFraction : Nat

/-- Blob parameters of `fork`. Cancun: target 3 blobs, max 6 (`cancun/vm/gas.py`,
`cancun/fork.py`). Prague and Osaka: target 6, max 9 (EIP-7691). -/
def blobParams : Fork → BlobParams
  | .cancun => { targetGasPerBlock := 393216, maxGasPerBlock := 786432,
                 baseFeeUpdateFraction := 3338477 }
  | .prague => { targetGasPerBlock := 786432, maxGasPerBlock := 1179648,
                 baseFeeUpdateFraction := 5007716 }
  | .osaka => { targetGasPerBlock := 786432, maxGasPerBlock := 1179648,
                baseFeeUpdateFraction := 5007716 }

/-! ## Intrinsic gas and blob fees -/

/-- `init_code_cost`: EIP-3860 charge of 2 gas per 32-byte word of init code. -/
def initCodeCost (len : Nat) : Nat := codeInitPerWord * ((len + 31) / 32)

/-- Number of zero bytes in `b`. -/
def zeroBytes (b : ByteArray) : Nat := b.foldl (fun n x => if x = 0 then n + 1 else n) 0

/-- Gas charged before execution starts. Mirrors `calculate_intrinsic_cost`: base cost,
calldata (4 per zero byte, 16 per non-zero byte), creation (32000 plus the EIP-3860
init-code charge) and access list (2400 per address, 1900 per storage key). -/
def intrinsicGas (tx : Transaction) : Nat :=
  let zeros := zeroBytes tx.data
  let dataCost := zeros * txDataPerZero + (tx.data.size - zeros) * txDataPerNonZero
  let createCost := if tx.isCreate then txCreate + initCodeCost tx.data.size else 0
  let accessListCost := tx.accessList.foldl
    (fun c i => c + txAccessListAddress + i.storageKeys.length * txAccessListStorageKey) 0
  txBase + dataCost + createCost + accessListCost

/-- `taylor_exponential` with explicit fuel: approximates `factor * e ^ (num / denom)` by
summing Taylor terms until a term rounds to zero. -/
def taylorLoop (num denom : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, output, _ => output
  | fuel + 1, i, output, acc =>
    if acc = 0 then output
    else taylorLoop num denom fuel (i + 1) (output + acc) ((acc * num) / (denom * i))

/-- `taylor_exponential(factor, num, denom) = (Σᵢ termᵢ) / denom`. The terms halve once
`i > 2·num/denom` and never exceed `factor·denom·e^(num/denom)`, so the fuel below always
lets the sum reach a zero term. -/
def taylorExponential (factor num denom : Nat) : Nat :=
  let acc := factor * denom
  let fuel := 4 * (num / denom + 1) + acc.log2 + 8
  taylorLoop num denom fuel 1 0 acc / denom

/-- `calculate_blob_gas_price`: the blob base fee for a block with `excessBlobGas`. -/
def blobGasPrice (fork : Fork) (excessBlobGas : Nat) : Nat :=
  taylorExponential minBlobGasPrice excessBlobGas (blobParams fork).baseFeeUpdateFraction

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

/-- Stateless validity; returns the intrinsic gas. Mirrors `validate_transaction`. -/
def validate (tx : Transaction) : Except InvalidTx Nat := do
  let intrinsic := intrinsicGas tx
  if intrinsic > tx.gas then throw (.intrinsicGasTooLow intrinsic tx.gas)
  if tx.isCreate && tx.data.size > maxInitCodeSize then
    throw (.initCodeSizeExceeded tx.data.size)
  if tx.nonce ≥ maxNonce then throw (.nonceOverflow tx.nonce)
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
blob-gas fee to add to the balance requirement (zero for other types). -/
def blobChecks (fork : Fork) (env : BlockEnv) : Transaction → Except InvalidTx Nat
  | .legacy _ => .ok 0
  | .eip2930 _ => .ok 0
  | .eip1559 _ => .ok 0
  | .eip4844 t => do
    if t.blobVersionedHashes.isEmpty then throw .noBlobData
    if t.blobVersionedHashes.any (versionByte · ≠ versionedHashVersionKzg) then
      throw .invalidBlobVersionedHash
    let price := blobGasPrice fork env.excessBlobGas
    if t.maxFeePerBlobGas < price then
      throw (.insufficientMaxFeePerBlobGas t.maxFeePerBlobGas price)
    return totalBlobGas (.eip4844 t) * t.maxFeePerBlobGas

/-- Whether `tx` can be included given the block environment, the gas and blob gas still
available in the block, and the current world. Mirrors `check_transaction`, in the same
order of checks. -/
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
  if account.nonce > tx.nonce then throw (.nonceTooLow account.nonce tx.nonce)
  if account.nonce < tx.nonce then throw (.nonceTooHigh account.nonce tx.nonce)
  let required := maxGasFee + maxBlobFee + tx.value
  if account.balance.toNat < required then
    throw (.insufficientBalance account.balance.toNat required)
  if account.code.size ≠ 0 then throw .senderNotEOA
  return { sender, effectiveGasPrice, blobVersionedHashes := tx.blobVersionedHashes,
           blobGasUsed }

/-! ## Execution -/

/-- Apply `f` to the account at `a`, then delete it if it is empty. Mirrors `modify_state`
in `cancun/state_tracker.py` (EIP-161: an account left empty by a change is removed). -/
def modifyClean (w : World) (a : Address) (f : Account → Account) : World :=
  let w := w.modify a f
  if (w.account a).isEmpty then w.erase a else w

/-- Credit `amount` wei to `a` (`create_ether`). The sum is reduced modulo 2²⁵⁶, which
cannot happen for real ether amounts. -/
def creditBalance (w : World) (a : Address) (amount : Nat) : World :=
  modifyClean w a fun acc => { acc with balance := BitVec.ofNat 256 (acc.balance.toNat + amount) }

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
fifth of the gas used), pay the priority fee to the coinbase, delete self-destructed
accounts and touched empty accounts. Transient storage starts empty and is discarded
afterwards (EIP-1153). `fuel` bounds interpreter steps. -/
def process (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv)
    (gasAvailable blobGasAvailable : Nat) (world : World) (tx : Transaction)
    (senderHint : Option Address) : Except TxError TxOutput := do
  let intrinsic ← (validate tx).mapError .invalid
  let c ← (check crypto fork env gasAvailable blobGasAvailable world tx senderHint).mapError
    .invalid
  let sender := c.sender
  let senderAccount := world.account sender
  let blobGasFee := c.blobGasUsed * blobGasPrice fork env.excessBlobGas
  let effectiveGasFee := tx.gas * c.effectiveGasPrice
  let w := modifyClean world sender fun acc => { acc with nonce := acc.nonce + 1 }
  let w := modifyClean w sender fun acc => { acc with
    balance := BitVec.ofNat 256 (senderAccount.balance.toNat - effectiveGasFee - blobGasFee) }
  let msg := prepareMessage crypto fork env w tx sender senderAccount.nonce (tx.gas - intrinsic)
  let ctx : Context := {
    crypto, fork, block := env,
    tx := { origin := sender, gasPrice := c.effectiveGasPrice,
            blobVersionedHashes := c.blobVersionedHashes.toArray } }
  let res ← match Interpreter.processMessageCall fuel ctx w ∅ msg with
    | .ok r => pure r
    | .error _ => throw TxError.outOfFuel
  let gasUsedBeforeRefund := tx.gas - res.gasLeft
  let refund := min (gasUsedBeforeRefund / 5) res.refundCounter.toNat
  let gasUsed := gasUsedBeforeRefund - refund
  let gasLeft := tx.gas - gasUsed
  let priorityFeePerGas := c.effectiveGasPrice - env.baseFee
  let w := creditBalance res.world sender (gasLeft * c.effectiveGasPrice)
  let w := creditBalance w env.coinbase (gasUsed * priorityFeePerGas)
  let w := res.accountsToDelete.foldl (fun w a => w.erase a) w
  let w := destroyTouchedEmpty w res.touchedAccounts
  return { world := w, sender, gasUsed, blobGasUsed := c.blobGasUsed, logs := res.logs,
           succeeded := res.success }

end EvmLean.Tx
