import EvmLean.Tx
import EvmLean.Trie

/-!
# Blocks

Block processing for Cancun, Prague and Osaka, following `src/ethereum/forks/*/fork.py`,
`blocks.py`, `bloom.py` and `requests.py` in `ethereum/execution-specs`:

| Lean                      | execution-specs                                   |
|---------------------------|---------------------------------------------------|
| `Header`, `Block`, …      | `Header`, `Block`, `Withdrawal`, `Receipt`, `Log` |
| `Header.hash`             | `keccak256(rlp.encode(header))`                   |
| `logsBloom`               | `logs_bloom`                                      |
| `calcExcessBlobGas`       | `calculate_excess_blob_gas`                       |
| `calcBaseFeePerGas`       | `calculate_base_fee_per_gas`                      |
| `checkGasLimit`           | `check_gas_limit`                                 |
| `validateHeader`          | `validate_header`                                 |
| `systemCall`              | `process_unchecked_system_transaction`            |
| `checkedSystemCall`       | `process_checked_system_transaction` (Prague)     |
| `parseDepositRequests`    | `parse_deposit_requests` (EIP-6110)               |
| `computeRequestsHash`     | `compute_requests_hash` (EIP-7685)                |
| `applyBody`               | `apply_body` + `process_withdrawals` + `process_general_purpose_requests` |
| `stateTransition`         | `state_transition`                                |

Fork differences: Prague adds the header's `requestsHash`, the EIP-2935 block-hash history
system call, and the EIP-7002/EIP-7251 request system calls and EIP-6110 deposit requests
committed to by `requestsHash`; Osaka bounds the excess blob gas by the execution cost
(EIP-7918) and the RLP size of a block (EIP-7934).

All hashing goes through the `Crypto` passed in. Blocks are decoded from their RLP
(`Block.decode`), which is also how the conformance fixtures provide invalid blocks.
-/

namespace EvmLean

/-- A block header. Mirrors `Header` in `cancun/blocks.py`; `requestsHash` is Prague's
21st field (`none` for a Cancun header). -/
structure Header where
  /-- Keccak of the parent header's RLP. -/
  parentHash : Word
  /-- Keccak of the RLP of the ommers list (always `EMPTY_OMMER_HASH` after the merge). -/
  ommersHash : Word
  /-- Fee recipient. -/
  coinbase : Address
  /-- State root after the block. -/
  stateRoot : Word
  /-- Root of the transactions trie. -/
  transactionsRoot : Word
  /-- Root of the receipts trie. -/
  receiptRoot : Word
  /-- Logs bloom (256 bytes). -/
  bloom : ByteArray
  /-- Difficulty (zero after the merge). -/
  difficulty : Nat
  /-- Block number. -/
  number : Nat
  /-- Gas limit. -/
  gasLimit : Nat
  /-- Gas used by the block's transactions. -/
  gasUsed : Nat
  /-- Timestamp (`U256`). -/
  timestamp : Nat
  /-- Extra data (at most 32 bytes). -/
  extraData : ByteArray
  /-- RANDAO mix (`PREVRANDAO`). -/
  prevRandao : Word
  /-- PoW nonce (8 bytes, zero after the merge). -/
  nonce : ByteArray
  /-- EIP-1559 base fee per gas. -/
  baseFeePerGas : Nat
  /-- Root of the withdrawals trie (EIP-4895). -/
  withdrawalsRoot : Word
  /-- Blob gas used (EIP-4844, `U64`). -/
  blobGasUsed : Nat
  /-- Excess blob gas (EIP-4844, `U64`). -/
  excessBlobGas : Nat
  /-- Parent beacon block root (EIP-4788). -/
  parentBeaconBlockRoot : Word
  /-- EIP-7685 requests hash (Prague onward; `none` in a Cancun header). -/
  requestsHash : Option Word := none
  deriving DecidableEq, Inhabited

/-- A validator withdrawal (EIP-4895). Mirrors `Withdrawal`. -/
structure Withdrawal where
  /-- Withdrawal index (`U64`). -/
  index : Nat
  /-- Validator index (`U64`). -/
  validatorIndex : Nat
  /-- Recipient. -/
  address : Address
  /-- Amount in gwei (`U64`). -/
  amount : Nat
  deriving DecidableEq, Inhabited

/-- A block. Mirrors `Block`. Ommers are kept as raw RLP: post-merge blocks must have none,
so their contents are never inspected. -/
structure Block where
  /-- The header. -/
  header : Header
  /-- Transactions, in order. -/
  transactions : List Transaction
  /-- Ommer headers (must be empty). -/
  ommers : List Rlp
  /-- Withdrawals, in order. -/
  withdrawals : List Withdrawal
  deriving Inhabited

/-- A transaction receipt. Mirrors `Receipt`. -/
structure Receipt where
  /-- Whether execution succeeded. -/
  succeeded : Bool
  /-- Block gas used up to and including this transaction. -/
  cumulativeGasUsed : Nat
  /-- Bloom of this transaction's logs (256 bytes). -/
  bloom : ByteArray
  /-- Logs emitted. -/
  logs : Array Log
  deriving Inhabited

namespace Block

/-! ## Constants (`cancun/fork.py`, `cancun/vm/gas.py`) -/

/-- `BASE_FEE_MAX_CHANGE_DENOMINATOR`. -/
def baseFeeMaxChangeDenominator : Nat := 8
/-- `ELASTICITY_MULTIPLIER`. -/
def elasticityMultiplier : Nat := 2
/-- `LIMIT_ADJUSTMENT_FACTOR`. -/
def limitAdjustmentFactor : Nat := 1024
/-- `LIMIT_MINIMUM`. -/
def limitMinimum : Nat := 5000
/-- Maximum block gas limit `2⁶³ - 1` (EIP-1985; geth's `MaxGasLimit`). Not checked by
execution-specs' `validate_header`, but every client rejects larger limits and the
conformance suite expects it (`GasLimitHigherThan2p63m1`). -/
def maxGasLimit : Nat := 2 ^ 63 - 1
/-- `SYSTEM_ADDRESS` (`0xff…fe`): caller of system transactions. -/
def systemAddress : Address := 0xfffffffffffffffffffffffffffffffffffffffe
/-- `BEACON_ROOTS_ADDRESS` (EIP-4788). -/
def beaconRootsAddress : Address := 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
/-- `HISTORY_STORAGE_ADDRESS` (EIP-2935, Prague). -/
def historyStorageAddress : Address := 0x0000F90827F1C53a10cb7A02335B175320002935
/-- `WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS` (EIP-7002, Prague). -/
def withdrawalRequestAddress : Address := 0x00000961Ef480Eb55e80D19ad83579A64c007002
/-- `CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS` (EIP-7251, Prague). -/
def consolidationRequestAddress : Address := 0x0000BBdDc7CE488642fb579F8B00f3a590007251
/-- `DEPOSIT_CONTRACT_ADDRESS` (EIP-6110, Prague): the mainnet deposit contract. -/
def depositContractAddress : Address := 0x00000000219ab540356cbb839cbe05303d7705fa
/-- `DEPOSIT_EVENT_SIGNATURE_HASH`: first topic of the deposit contract's `DepositEvent`. -/
def depositEventSignatureHash : Word :=
  0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5
/-- `MAX_RLP_BLOCK_SIZE` (EIP-7934, Osaka): `MAX_BLOCK_SIZE − SAFETY_MARGIN`. -/
def maxRlpBlockSize : Nat := 10485760 - 2097152
/-- `SYSTEM_TRANSACTION_GAS`. -/
def systemTransactionGas : Nat := 30000000
/-- Wei per gwei (withdrawal amounts are in gwei). -/
def weiPerGwei : Nat := 10 ^ 9

/-! ## Encoding -/

open Transaction (addressRlp wordRlp) in
/-- The header's RLP list, fields in reference order. -/
def headerRlp (h : Header) : Rlp :=
  .list ([wordRlp h.parentHash, wordRlp h.ommersHash, addressRlp h.coinbase,
    wordRlp h.stateRoot, wordRlp h.transactionsRoot, wordRlp h.receiptRoot, .bytes h.bloom,
    .nat h.difficulty, .nat h.number, .nat h.gasLimit, .nat h.gasUsed, .nat h.timestamp,
    .bytes h.extraData, wordRlp h.prevRandao, .bytes h.nonce, .nat h.baseFeePerGas,
    wordRlp h.withdrawalsRoot, .nat h.blobGasUsed, .nat h.excessBlobGas,
    wordRlp h.parentBeaconBlockRoot] ++ h.requestsHash.toList.map wordRlp)

/-- The block hash: `keccak256(rlp.encode(header))`. -/
def headerHash (keccak256 : ByteArray → Word) (h : Header) : Word := keccak256 (headerRlp h).encode

/-- `rlp.encode(withdrawal)`: the withdrawals-trie value. -/
def withdrawalEncode (w : Withdrawal) : ByteArray :=
  (Rlp.list [.nat w.index, .nat w.validatorIndex, Transaction.addressRlp w.address,
    .nat w.amount]).encode

/-- A log as `[address, [topics], data]`. -/
def logRlp (l : Log) : Rlp :=
  .list [Transaction.addressRlp l.address, .list (l.topics.toList.map Transaction.wordRlp),
    .bytes l.data]

/-- The full block as RLP: `[header, transactions, ommers, withdrawals]`. -/
def toRlp (b : Block) : Rlp :=
  .list [headerRlp b.header, .list (b.transactions.map Transaction.bodyRlp), .list b.ommers,
    .list (b.withdrawals.map fun w => .list [.nat w.index, .nat w.validatorIndex,
      Transaction.addressRlp w.address, .nat w.amount])]

/-- `encode_receipt`: the receipts-trie value; typed receipts are prefixed by the
transaction type, like typed transactions. -/
def receiptEncode (txType : Nat) (r : Receipt) : ByteArray :=
  let body := (Rlp.list [.bytes (if r.succeeded then ⟨#[1]⟩ else .empty), .nat r.cumulativeGasUsed,
    .bytes r.bloom, .list (r.logs.toList.map logRlp)]).encode
  if txType = 0 then body else Transaction.typed txType.toUInt8 body

/-! ## Decoding -/

open Rlp in
/-- Decode a header with the reference field types: `Hash32`/`Root` are 32 bytes, `Bloom`
256, `Bytes8` 8; `U64`/`U256` are width-checked. A Cancun header has 20 fields, a Prague or
Osaka one 21 (`requestsHash`); which one the fork requires is checked by `stateTransition`. -/
def decodeHeader (r : Rlp) : Except DecodeError Header := do
  let fields ← asList "header" r
  let (cancunFields, requestsHash) ← match fields with
    | [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t] =>
      pure ([a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t], none)
    | [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u] =>
      pure ([a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t], some u)
    | _ => throw (.unexpected s!"header must have 20 or 21 fields, got {fields.length}")
  let requestsHash ← match requestsHash with
    | some u => pure (some (← asWord "requestsHash" u))
    | none => pure none
  match cancunFields with
  | [parentHash, ommersHash, coinbase, stateRoot, txRoot, receiptRoot, bloom, difficulty,
     number, gasLimit, gasUsed, timestamp, extraData, prevRandao, nonce, baseFee,
     withdrawalsRoot, blobGasUsed, excessBlobGas, beaconRoot] =>
    return {
      parentHash := ← asWord "parentHash" parentHash,
      ommersHash := ← asWord "ommersHash" ommersHash,
      coinbase := ← asAddress "coinbase" coinbase,
      stateRoot := ← asWord "stateRoot" stateRoot,
      transactionsRoot := ← asWord "transactionsRoot" txRoot,
      receiptRoot := ← asWord "receiptRoot" receiptRoot,
      bloom := ← asFixed "bloom" 256 bloom,
      difficulty := ← asUint "difficulty" difficulty,
      number := ← asUint "number" number,
      gasLimit := ← asUint "gasLimit" gasLimit,
      gasUsed := ← asUint "gasUsed" gasUsed,
      timestamp := ← asU256 "timestamp" timestamp,
      extraData := ← asBytes "extraData" extraData,
      prevRandao := ← asWord "prevRandao" prevRandao,
      nonce := ← asFixed "nonce" 8 nonce,
      baseFeePerGas := ← asUint "baseFeePerGas" baseFee,
      withdrawalsRoot := ← asWord "withdrawalsRoot" withdrawalsRoot,
      blobGasUsed := ← asU64 "blobGasUsed" blobGasUsed,
      excessBlobGas := ← asU64 "excessBlobGas" excessBlobGas,
      parentBeaconBlockRoot := ← asWord "parentBeaconBlockRoot" beaconRoot,
      requestsHash }
  | _ => throw (.unexpected "header must have 20 or 21 fields")

open Rlp in
/-- Decode a withdrawal `[index, validatorIndex, address, amount]`. -/
def decodeWithdrawal (r : Rlp) : Except DecodeError Withdrawal := do
  match ← asList "withdrawal" r with
  | [index, validatorIndex, address, amount] =>
    return { index := ← asU64 "withdrawal index" index,
             validatorIndex := ← asU64 "validator index" validatorIndex,
             address := ← asAddress "withdrawal address" address,
             amount := ← asU64 "withdrawal amount" amount }
  | _ => throw (.unexpected "withdrawal must have 4 fields")

open Rlp in
/-- Decode a block `[header, transactions, ommers, withdrawals]` from its RLP item. -/
def ofRlp (r : Rlp) : Except DecodeError Block := do
  match ← asList "block" r with
  | [header, txs, ommers, withdrawals] =>
    return { header := ← decodeHeader header,
             transactions := ← (← asList "transactions" txs).mapM Transaction.ofRlp,
             ommers := ← asList "ommers" ommers,
             withdrawals := ← (← asList "withdrawals" withdrawals).mapM decodeWithdrawal }
  | fields => throw (.unexpected s!"Cancun block must have 4 fields, got {fields.length}")

/-- Decode a block from its RLP encoding. -/
def decode (b : ByteArray) : Except Rlp.DecodeError Block := do ofRlp (← Rlp.decode b)

/-! ## Blooms -/

/-- The three bloom bits of an entry (`add_to_bloom`): the low 11 bits of each of the first
three 16-bit words of its Keccak. Bit `i` here is bit `i` of the bloom read as a big-endian
2048-bit number, i.e. the reference's `bit_index = 0x7FF - i`. -/
def bloomBits (keccak256 : ByteArray → Word) (entry : ByteArray) : Nat :=
  let h := (keccak256 entry).toNat
  [0, 2, 4].foldl (fun acc idx => acc ||| 1 <<< ((h >>> (240 - 8 * idx)) % 2048)) 0

/-- `logs_bloom`: the 256-byte bloom of the logs' addresses and topics. -/
def logsBloom (keccak256 : ByteArray → Word) (logs : Array Log) : ByteArray :=
  let bits := logs.foldl (fun acc l =>
    l.topics.foldl (fun acc t => acc ||| bloomBits keccak256 (Bytes.ofWord t))
      (acc ||| bloomBits keccak256 (Bytes.ofAddress l.address))) 0
  Bytes.ofNatBE 256 bits

/-! ## Header validation -/

/-- `GasCosts.BLOB_BASE_COST` (EIP-7918, Osaka): the execution-gas price floor of a blob. -/
def blobBaseCost : Nat := 2 ^ 13

/-- `calculate_excess_blob_gas`: excess blob gas of a child of `parent`, with the target of
the child's fork. From Osaka (EIP-7918), when the blob base fee is below the execution cost
`BLOB_BASE_COST · baseFee` of a blob, the excess only grows, by
`blobGasUsed · (max − target) / max` (with blob counts 9 and 6: `blobGasUsed · 3 / 9`). -/
def calcExcessBlobGas (fork : Fork) (parent : Header) : Nat :=
  let params := Tx.blobParams fork
  let parentBlobGas := parent.excessBlobGas + parent.blobGasUsed
  if parentBlobGas < params.targetGasPerBlock then 0
  else if fork ≥ .osaka &&
      blobBaseCost * parent.baseFeePerGas >
        Tx.gasPerBlob * Gas.blobGasPrice fork parent.excessBlobGas then
    -- `(max − target) / max` is the same ratio in blobs or in blob gas.
    parent.excessBlobGas + parent.blobGasUsed * (params.maxGasPerBlock - params.targetGasPerBlock)
      / params.maxGasPerBlock
  else parentBlobGas - params.targetGasPerBlock

/-- `check_gas_limit`: the gas limit moves by less than `parent / 1024` and stays at least
`LIMIT_MINIMUM`. -/
def checkGasLimit (gasLimit parentGasLimit : Nat) : Bool :=
  let delta := parentGasLimit / limitAdjustmentFactor
  gasLimit < parentGasLimit + delta && gasLimit + delta > parentGasLimit &&
    gasLimit ≥ limitMinimum

/-- `calculate_base_fee_per_gas` (EIP-1559), assuming `check_gas_limit` holds: the base fee
moves towards the parent's gas target by at most 1/8. -/
def calcBaseFeePerGas (parentGasLimit parentGasUsed parentBaseFee : Nat) : Nat :=
  let target := parentGasLimit / elasticityMultiplier
  if parentGasUsed = target then parentBaseFee
  else if parentGasUsed > target then
    let delta := parentBaseFee * (parentGasUsed - target) / target
    parentBaseFee + max (delta / baseFeeMaxChangeDenominator) 1
  else
    let delta := parentBaseFee * (target - parentGasUsed) / target
    parentBaseFee - delta / baseFeeMaxChangeDenominator

/-- Why a header is invalid (each a bare `InvalidBlock` in `validate_header`). -/
inductive HeaderError where
  /-- Block number zero. -/
  | numberZero
  /-- Excess blob gas differs from `calculate_excess_blob_gas(parent)`. -/
  | excessBlobGasMismatch (expected actual : Nat)
  /-- Gas used above the gas limit. -/
  | gasUsedAboveLimit
  /-- Gas limit outside the bounds of `check_gas_limit`. -/
  | invalidGasLimit (gasLimit parentGasLimit : Nat)
  /-- Gas limit above `maxGasLimit` (EIP-1985). -/
  | gasLimitTooBig (gasLimit : Nat)
  /-- Base fee differs from `calculate_base_fee_per_gas`. -/
  | baseFeeMismatch (expected actual : Nat)
  /-- Timestamp not after the parent's. -/
  | timestampNotIncreasing
  /-- Number is not the parent's plus one. -/
  | numberMismatch
  /-- Extra data longer than 32 bytes. -/
  | extraDataTooLong
  /-- Non-zero difficulty. -/
  | nonzeroDifficulty
  /-- Non-zero PoW nonce. -/
  | nonzeroNonce
  /-- Ommers hash is not `EMPTY_OMMER_HASH`. -/
  | invalidOmmersHash
  /-- Parent hash does not match the parent header. -/
  | parentHashMismatch
  deriving DecidableEq, Repr, Inhabited

/-- `EMPTY_OMMER_HASH = keccak256(rlp([]))`. -/
def emptyOmmerHash (keccak256 : ByteArray → Word) : Word := keccak256 (Rlp.list []).encode

/-- `validate_header`, given the parent header and its hash, in the reference's order, plus
the EIP-1985 gas-limit cap. -/
def validateHeader (keccak256 : ByteArray → Word) (fork : Fork) (parent : Header)
    (parentHash : Word) (h : Header) : Except HeaderError Unit := do
  if h.number < 1 then throw .numberZero
  let excess := calcExcessBlobGas fork parent
  if h.excessBlobGas ≠ excess then throw (.excessBlobGasMismatch excess h.excessBlobGas)
  if h.gasUsed > h.gasLimit then throw .gasUsedAboveLimit
  if h.gasLimit > maxGasLimit then throw (.gasLimitTooBig h.gasLimit)
  if !checkGasLimit h.gasLimit parent.gasLimit then
    throw (.invalidGasLimit h.gasLimit parent.gasLimit)
  let baseFee := calcBaseFeePerGas parent.gasLimit parent.gasUsed parent.baseFeePerGas
  if baseFee ≠ h.baseFeePerGas then throw (.baseFeeMismatch baseFee h.baseFeePerGas)
  if h.timestamp ≤ parent.timestamp then throw .timestampNotIncreasing
  if h.number ≠ parent.number + 1 then throw .numberMismatch
  if h.extraData.size > 32 then throw .extraDataTooLong
  if h.difficulty ≠ 0 then throw .nonzeroDifficulty
  if h.nonce ≠ Bytes.zeros 8 then throw .nonzeroNonce
  if h.ommersHash ≠ emptyOmmerHash keccak256 then throw .invalidOmmersHash
  if h.parentHash ≠ parentHash then throw .parentHashMismatch

/-! ## Block execution -/

/-- Why a block is invalid (or could not be processed). -/
inductive BlockError where
  /-- The header fails `validate_header`. -/
  | header (e : HeaderError)
  /-- The block has ommers. -/
  | ommersNotEmpty
  /-- Transaction `index` is invalid. -/
  | invalidTx (index : Nat) (e : Tx.InvalidTx)
  /-- The interpreter ran out of fuel (in transaction `index`, or the system call). -/
  | outOfFuel (index : Option Nat)
  /-- Computed gas used differs from the header. -/
  | gasUsedMismatch (computed header : Nat)
  /-- Transactions root differs from the header. -/
  | transactionsRootMismatch
  /-- State root differs from the header. -/
  | stateRootMismatch
  /-- Receipts root differs from the header. -/
  | receiptRootMismatch
  /-- Logs bloom differs from the header. -/
  | bloomMismatch
  /-- Withdrawals root differs from the header. -/
  | withdrawalsRootMismatch
  /-- Computed blob gas used differs from the header. -/
  | blobGasUsedMismatch (computed header : Nat)
  /-- The header lacks `requestsHash` (Prague onward) or has one (Cancun). -/
  | headerShape
  /-- Computed requests hash differs from the header (EIP-7685). -/
  | requestsHashMismatch
  /-- A checked system contract has no code (`process_checked_system_transaction`). -/
  | systemContractEmpty (address : Address)
  /-- A checked system call failed (`process_checked_system_transaction`). -/
  | systemContractFailed (address : Address)
  /-- A deposit-contract log has an invalid layout (`extract_deposit_data`, EIP-6110). -/
  | invalidDepositLog
  /-- The block's RLP is larger than `MAX_RLP_BLOCK_SIZE` (EIP-7934, Osaka). -/
  | blockTooLarge (size : Nat)
  deriving Inhabited

/-- Human-readable description of a block error. -/
def BlockError.toString : BlockError → String
  | .header e => s!"invalid header: {repr e}"
  | .ommersNotEmpty => "block has ommers"
  | .invalidTx i e => s!"invalid transaction {i}: {e}"
  | .outOfFuel none => "interpreter out of fuel in a system call"
  | .outOfFuel (some i) => s!"interpreter out of fuel in transaction {i}"
  | .gasUsedMismatch c h => s!"gas used {c} ≠ header {h}"
  | .transactionsRootMismatch => "transactions root mismatch"
  | .stateRootMismatch => "state root mismatch"
  | .receiptRootMismatch => "receipts root mismatch"
  | .bloomMismatch => "logs bloom mismatch"
  | .withdrawalsRootMismatch => "withdrawals root mismatch"
  | .blobGasUsedMismatch c h => s!"blob gas used {c} ≠ header {h}"
  | .headerShape => "header fields do not match the fork (requestsHash)"
  | .requestsHashMismatch => "requests hash mismatch"
  | .systemContractEmpty a => s!"system contract {a.toNat} has no code"
  | .systemContractFailed a => s!"system contract {a.toNat} call failed"
  | .invalidDepositLog => "invalid deposit contract log"
  | .blockTooLarge n => s!"block RLP size {n} exceeds MAX_RLP_BLOCK_SIZE"

instance : ToString BlockError := ⟨BlockError.toString⟩

/-- The block environment for executing `h` on chain `chainId`, with ancestor hashes
(most recent, i.e. the parent, first). -/
def blockEnv (chainId : Nat) (h : Header) (ancestorHashes : List Word) : BlockEnv :=
  { chainId, coinbase := h.coinbase, number := h.number, timestamp := h.timestamp,
    gasLimit := h.gasLimit, baseFee := h.baseFeePerGas, prevRandao := h.prevRandao,
    excessBlobGas := h.excessBlobGas, blockHashes := ancestorHashes.take 256,
    parentBeaconBlockRoot := h.parentBeaconBlockRoot }

/-- A system transaction (`process_unchecked_system_transaction`): `SYSTEM_ADDRESS` calls
`target` with `data` and 30M gas, without fees, nonce change or value transfer, and
regardless of the outcome. Touched empty accounts are then removed (EIP-161). Used for the
EIP-4788 beacon roots, the EIP-2935 block-hash history and the EIP-7002/EIP-7251 request
contracts. Returns the world and the call's result. -/
def systemCall (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv) (world : World)
    (target : Address) (data : ByteArray) : Except Interpreter.OutOfFuel (World × MessageResult) := do
  let msg : Message := {
    caller := systemAddress, target := some target, currentTarget := target,
    gas := systemTransactionGas, value := 0, data, codeAddress := some target,
    code := world.code target, depth := 0, shouldTransferValue := false,
    isStatic := false, accessedAddresses := ∅, accessedStorageKeys := ∅ }
  let txEnv : TxEnv := { origin := systemAddress, gasPrice := env.baseFee }
  let ctx : Context := { crypto, fork, block := env, tx := txEnv }
  let res ← Interpreter.processMessageCall fuel ctx world ∅ msg
  return (Tx.destroyTouchedEmpty res.world res.touchedAccounts, res)

/-- The EIP-4788 beacon-roots system call: the parent beacon block root to
`BEACON_ROOTS_ADDRESS`. -/
def beaconRootsCall (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv)
    (world : World) : Except Interpreter.OutOfFuel World := do
  return (← systemCall fuel crypto fork env world beaconRootsAddress
    (Bytes.ofWord env.parentBeaconBlockRoot)).1

/-- `process_checked_system_transaction` (Prague): like `systemCall`, but the block is
invalid if `target` has no code or the call fails (exceptional halt or revert). Returns the
world and the call's output. -/
def checkedSystemCall (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv)
    (world : World) (target : Address) (data : ByteArray) :
    Except BlockError (World × ByteArray) := do
  if (world.code target).size = 0 then throw (.systemContractEmpty target)
  let (world, res) ← (systemCall fuel crypto fork env world target data).mapError
    fun _ => .outOfFuel none
  if !res.success then throw (.systemContractFailed target)
  return (world, res.output)

/-! ## Requests (EIP-7685, Prague) -/

/-- `DEPOSIT_REQUEST_TYPE` (EIP-6110). -/
def depositRequestType : UInt8 := 0x00
/-- `WITHDRAWAL_REQUEST_TYPE` (EIP-7002). -/
def withdrawalRequestType : UInt8 := 0x01
/-- `CONSOLIDATION_REQUEST_TYPE` (EIP-7251). -/
def consolidationRequestType : UInt8 := 0x02

/-- `extract_deposit_data`: check the fixed ABI layout of a 576-byte `DepositEvent` payload
(five offsets `160, 256, 320, 384, 512` and sizes `48, 32, 8, 96, 8`) and return the
concatenated fields `pubkey ‖ withdrawal_credentials ‖ amount ‖ signature ‖ index`. -/
def extractDepositData (data : ByteArray) : Option ByteArray :=
  let word (off : Nat) : Nat := Bytes.toNat (data.extract off (off + 32))
  -- (offset position, expected offset, expected size) of each field.
  let fields : List (Nat × Nat × Nat) :=
    [(0, 160, 48), (32, 256, 32), (64, 320, 8), (96, 384, 96), (128, 512, 8)]
  if data.size ≠ 576 then none
  else if fields.any (fun (pos, off, _) => word pos ≠ off) then none
  else if fields.any (fun (_, off, size) => word off ≠ size) then none
  else some (fields.foldl (fun acc (_, off, size) => acc ++ data.extract (off + 32) (off + 32 + size)) .empty)

/-- `parse_deposit_requests`: the concatenated deposit data of every log emitted by the
deposit contract whose first topic is the `DepositEvent` signature, in block order. -/
def parseDepositRequests (logs : Array Log) : Except BlockError ByteArray :=
  logs.foldlM (init := ByteArray.empty) fun acc l =>
    if l.address = depositContractAddress && l.topics[0]? = some depositEventSignatureHash then
      match extractDepositData l.data with
      | some d => .ok (acc ++ d)
      | none => .error .invalidDepositLog
    else .ok acc

/-- `compute_requests_hash`: `sha256(sha256(r₁) ‖ sha256(r₂) ‖ …)` over the type-prefixed
requests. -/
def computeRequestsHash (sha256 : ByteArray → ByteArray) (requests : List ByteArray) : Word :=
  Bytes.toWord (sha256 (requests.foldl (fun acc r => acc ++ sha256 r) .empty))

/-- `process_general_purpose_requests`: deposit requests from the block's logs, then the
withdrawal and consolidation request system calls (each must succeed). Each non-empty
request list is prefixed by its type; empty ones are omitted. -/
def generalPurposeRequests (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv)
    (world : World) (logs : Array Log) : Except BlockError (World × List ByteArray) := do
  let deposits ← parseDepositRequests logs
  let (world, withdrawals) ←
    checkedSystemCall fuel crypto fork env world withdrawalRequestAddress .empty
  let (world, consolidations) ←
    checkedSystemCall fuel crypto fork env world consolidationRequestAddress .empty
  let typed (ty : UInt8) (d : ByteArray) : List ByteArray :=
    if d.size = 0 then [] else [⟨#[ty]⟩ ++ d]
  return (world, typed depositRequestType deposits ++ typed withdrawalRequestType withdrawals
    ++ typed consolidationRequestType consolidations)

/-- What executing a block body produces (`BlockOutput`). -/
structure BodyOutput where
  /-- World state after the body. -/
  world : World
  /-- Total gas used. -/
  gasUsed : Nat := 0
  /-- Total blob gas used. -/
  blobGasUsed : Nat := 0
  /-- Receipts, in transaction order. -/
  receipts : Array Receipt := #[]
  /-- Receipts-trie values, in transaction order. -/
  receiptValues : Array ByteArray := #[]
  /-- All logs of the block, in order. -/
  logs : Array Log := #[]
  /-- EIP-7685 requests (Prague onward), type-prefixed, in type order. -/
  requests : List ByteArray := []
  deriving Inhabited

/-- Process the transactions in order (`apply_body`'s loop), accumulating gas, blob gas,
receipts and logs. `hints` gives an optional known sender per transaction. -/
def applyTxs (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv) :
    Nat → List (Transaction × Option Address) → BodyOutput → Except BlockError BodyOutput
  | _, [], out => .ok out
  | i, (tx, hint) :: rest, out => do
    let gasAvailable := env.gasLimit - out.gasUsed
    let blobGasAvailable := (Tx.blobParams fork).maxGasPerBlock - out.blobGasUsed
    let r ← match Tx.process fuel crypto fork env gasAvailable blobGasAvailable out.world tx hint with
      | .ok r => pure r
      | .error (.invalid e) => throw (.invalidTx i e)
      | .error .outOfFuel => throw (.outOfFuel (some i))
    let gasUsed := out.gasUsed + r.gasUsed
    let receipt : Receipt := { succeeded := r.succeeded, cumulativeGasUsed := gasUsed,
                               bloom := logsBloom crypto.keccak256 r.logs, logs := r.logs }
    applyTxs fuel crypto fork env (i + 1) rest
      { world := r.world, gasUsed, blobGasUsed := out.blobGasUsed + r.blobGasUsed,
        receipts := out.receipts.push receipt,
        receiptValues := out.receiptValues.push (receiptEncode tx.typeByte receipt),
        logs := out.logs ++ r.logs }

/-- `process_withdrawals`: credit each withdrawal's amount (gwei) in wei; an account left
empty (a zero withdrawal to an empty account) is removed, as by `create_ether`. -/
def applyWithdrawals (world : World) (ws : List Withdrawal) : World :=
  ws.foldl (fun w wd => Tx.creditBalance w wd.address (wd.amount * weiPerGwei)) world

/-- `apply_body`: the beacon-roots system call, (Prague) the EIP-2935 history system call
with the parent hash, the transactions, the withdrawals, then (Prague) the requests. -/
def applyBody (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv) (world : World)
    (txs : List (Transaction × Option Address)) (withdrawals : List Withdrawal) :
    Except BlockError BodyOutput := do
  let world ← (beaconRootsCall fuel crypto fork env world).mapError fun _ => .outOfFuel none
  let world ←
    if fork ≥ .prague then
      let parentHash := env.blockHashes[0]?.getD 0
      pure (← (systemCall fuel crypto fork env world historyStorageAddress
        (Bytes.ofWord parentHash)).mapError fun _ => .outOfFuel none).1
    else pure world
  let out ← applyTxs fuel crypto fork env 0 txs { world }
  let out := { out with world := applyWithdrawals out.world withdrawals }
  if fork ≥ .prague then
    let (world, requests) ← generalPurposeRequests fuel crypto fork env out.world out.logs
    return { out with world, requests }
  else return out

/-- The tip of a chain: what is needed to apply its next block. -/
structure ChainHead where
  /-- Header of the head block. -/
  header : Header
  /-- Hash of the head block. -/
  hash : Word
  /-- World state after the head block. -/
  world : World
  /-- Hashes of the head block and its ancestors, most recent first (at most 256). -/
  ancestorHashes : List Word
  deriving Inhabited

/-- A chain whose head is the genesis block `genesis` with state `world`. -/
def genesisHead (keccak256 : ByteArray → Word) (genesis : Header) (world : World) : ChainHead :=
  let hash := headerHash keccak256 genesis
  { header := genesis, hash, world, ancestorHashes := [hash] }

/-- `state_transition`: (Osaka) check the RLP size limit, validate `block` against `head`,
execute it and check every header commitment (gas used, transactions root, state root,
receipts root, logs bloom, withdrawals root, blob gas used and, from Prague, the requests
hash). Returns the new head and the receipts. `senderHints[i]`, if present,
is a known sender of transaction `i`; `fuel` bounds each message call. -/
def stateTransition (fuel : Nat) (crypto : Crypto) (fork : Fork) (chainId : Nat)
    (head : ChainHead) (block : Block) (senderHints : List (Option Address)) :
    Except BlockError (ChainHead × Array Receipt) := do
  let keccak := crypto.keccak256
  let h := block.header
  if fork ≥ .osaka then
    let size := (toRlp block).encode.size
    if size > maxRlpBlockSize then throw (.blockTooLarge size)
  if h.requestsHash.isSome ≠ decide (fork ≥ .prague) then throw .headerShape
  (validateHeader keccak fork head.header head.hash h).mapError .header
  if !block.ommers.isEmpty then throw .ommersNotEmpty
  let env := blockEnv chainId h head.ancestorHashes
  let txs := block.transactions.zipIdx.map fun (tx, i) => (tx, (senderHints[i]?).join)
  let out ← applyBody fuel crypto fork env head.world txs block.withdrawals
  if out.gasUsed ≠ h.gasUsed then throw (.gasUsedMismatch out.gasUsed h.gasUsed)
  if Trie.indexedRoot keccak (block.transactions.map Transaction.encode) ≠ h.transactionsRoot then
    throw .transactionsRootMismatch
  if Trie.stateRoot keccak out.world ≠ h.stateRoot then throw .stateRootMismatch
  if Trie.indexedRoot keccak out.receiptValues.toList ≠ h.receiptRoot then
    throw .receiptRootMismatch
  if logsBloom keccak out.logs ≠ h.bloom then throw .bloomMismatch
  if Trie.indexedRoot keccak (block.withdrawals.map withdrawalEncode) ≠ h.withdrawalsRoot then
    throw .withdrawalsRootMismatch
  if out.blobGasUsed ≠ h.blobGasUsed then throw (.blobGasUsedMismatch out.blobGasUsed h.blobGasUsed)
  if fork ≥ .prague && some (computeRequestsHash crypto.sha256 out.requests) ≠ h.requestsHash then
    throw .requestsHashMismatch
  let hash := headerHash keccak h
  return ({ header := h, hash, world := out.world,
            ancestorHashes := (hash :: head.ancestorHashes).take 256 }, out.receipts)

end Block

end EvmLean
