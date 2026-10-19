import EvmLean.Tx
import EvmLean.Trie

/-!
# Blocks

Minimal block processing for Cancun, following `src/ethereum/forks/cancun/fork.py`,
`blocks.py` and `bloom.py` in `ethereum/execution-specs`:

| Lean                      | execution-specs                                   |
|---------------------------|---------------------------------------------------|
| `Header`, `Block`, …      | `Header`, `Block`, `Withdrawal`, `Receipt`, `Log` |
| `Header.hash`             | `keccak256(rlp.encode(header))`                   |
| `logsBloom`               | `logs_bloom`                                      |
| `calcExcessBlobGas`       | `calculate_excess_blob_gas`                       |
| `calcBaseFeePerGas`       | `calculate_base_fee_per_gas`                      |
| `checkGasLimit`           | `check_gas_limit`                                 |
| `validateHeader`          | `validate_header`                                 |
| `beaconRootsCall`         | `process_unchecked_system_transaction` (EIP-4788) |
| `applyBody`               | `apply_body` + `process_withdrawals`              |
| `stateTransition`         | `state_transition`                                |

All hashing goes through the `Crypto` passed in. Blocks are decoded from their RLP
(`Block.decode`), which is also how the conformance fixtures provide invalid blocks.
-/

namespace EvmLean

/-- A Cancun block header. Mirrors `Header` in `cancun/blocks.py`. -/
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
/-- `SYSTEM_ADDRESS` (`0xff…fe`): caller of system transactions. -/
def systemAddress : Address := 0xfffffffffffffffffffffffffffffffffffffffe
/-- `BEACON_ROOTS_ADDRESS` (EIP-4788). -/
def beaconRootsAddress : Address := 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
/-- `SYSTEM_TRANSACTION_GAS`. -/
def systemTransactionGas : Nat := 30000000
/-- Wei per gwei (withdrawal amounts are in gwei). -/
def weiPerGwei : Nat := 10 ^ 9

/-! ## Encoding -/

open Transaction (addressRlp wordRlp) in
/-- The header's RLP list, fields in reference order. -/
def headerRlp (h : Header) : Rlp :=
  .list [wordRlp h.parentHash, wordRlp h.ommersHash, addressRlp h.coinbase,
    wordRlp h.stateRoot, wordRlp h.transactionsRoot, wordRlp h.receiptRoot, .bytes h.bloom,
    .nat h.difficulty, .nat h.number, .nat h.gasLimit, .nat h.gasUsed, .nat h.timestamp,
    .bytes h.extraData, wordRlp h.prevRandao, .bytes h.nonce, .nat h.baseFeePerGas,
    wordRlp h.withdrawalsRoot, .nat h.blobGasUsed, .nat h.excessBlobGas,
    wordRlp h.parentBeaconBlockRoot]

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
/-- Decode a Cancun header (exactly 20 fields), with the reference field types: `Hash32`/
`Root` are 32 bytes, `Bloom` 256, `Bytes8` 8; `U64`/`U256` are width-checked. -/
def decodeHeader (r : Rlp) : Except DecodeError Header := do
  match ← asList "header" r with
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
      parentBeaconBlockRoot := ← asWord "parentBeaconBlockRoot" beaconRoot }
  | fields => throw (.unexpected s!"Cancun header must have 20 fields, got {fields.length}")

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

/-- `calculate_excess_blob_gas`: excess blob gas of a child of `parent`. -/
def calcExcessBlobGas (fork : Fork) (parent : Header) : Nat :=
  parent.excessBlobGas + parent.blobGasUsed - (Tx.blobParams fork).targetGasPerBlock

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

/-- `validate_header`, given the parent header and its hash, in the reference's order. -/
def validateHeader (keccak256 : ByteArray → Word) (fork : Fork) (parent : Header)
    (parentHash : Word) (h : Header) : Except HeaderError Unit := do
  if h.number < 1 then throw .numberZero
  let excess := calcExcessBlobGas fork parent
  if h.excessBlobGas ≠ excess then throw (.excessBlobGasMismatch excess h.excessBlobGas)
  if h.gasUsed > h.gasLimit then throw .gasUsedAboveLimit
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
  deriving Inhabited

/-- Human-readable description of a block error. -/
def BlockError.toString : BlockError → String
  | .header e => s!"invalid header: {repr e}"
  | .ommersNotEmpty => "block has ommers"
  | .invalidTx i e => s!"invalid transaction {i}: {e}"
  | .outOfFuel none => "interpreter out of fuel in system call"
  | .outOfFuel (some i) => s!"interpreter out of fuel in transaction {i}"
  | .gasUsedMismatch c h => s!"gas used {c} ≠ header {h}"
  | .transactionsRootMismatch => "transactions root mismatch"
  | .stateRootMismatch => "state root mismatch"
  | .receiptRootMismatch => "receipts root mismatch"
  | .bloomMismatch => "logs bloom mismatch"
  | .withdrawalsRootMismatch => "withdrawals root mismatch"
  | .blobGasUsedMismatch c h => s!"blob gas used {c} ≠ header {h}"

instance : ToString BlockError := ⟨BlockError.toString⟩

/-- The block environment for executing `h` on chain `chainId`, with ancestor hashes
(most recent, i.e. the parent, first). -/
def blockEnv (chainId : Nat) (h : Header) (ancestorHashes : List Word) : BlockEnv :=
  { chainId, coinbase := h.coinbase, number := h.number, timestamp := h.timestamp,
    gasLimit := h.gasLimit, baseFee := h.baseFeePerGas, prevRandao := h.prevRandao,
    excessBlobGas := h.excessBlobGas, blockHashes := ancestorHashes.take 256,
    parentBeaconBlockRoot := h.parentBeaconBlockRoot }

/-- The EIP-4788 beacon-roots system call (`process_unchecked_system_transaction`):
`SYSTEM_ADDRESS` calls `BEACON_ROOTS_ADDRESS` with the parent beacon block root as
calldata and 30M gas, without fees, nonce change or value transfer, and regardless of the
outcome. Touched empty accounts are then removed (EIP-161). -/
def beaconRootsCall (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv)
    (world : World) : Except Interpreter.OutOfFuel World := do
  let msg : Message := {
    caller := systemAddress, target := some beaconRootsAddress,
    currentTarget := beaconRootsAddress, gas := systemTransactionGas, value := 0,
    data := Bytes.ofWord env.parentBeaconBlockRoot, codeAddress := some beaconRootsAddress,
    code := world.code beaconRootsAddress, depth := 0, shouldTransferValue := false,
    isStatic := false, accessedAddresses := ∅, accessedStorageKeys := ∅ }
  let txEnv : TxEnv := { origin := systemAddress, gasPrice := env.baseFee }
  let ctx : Context := { crypto, fork, block := env, tx := txEnv }
  let res ← Interpreter.processMessageCall fuel ctx world ∅ msg
  return Tx.destroyTouchedEmpty res.world res.touchedAccounts

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

/-- `apply_body`: the beacon-roots system call, the transactions, then the withdrawals. -/
def applyBody (fuel : Nat) (crypto : Crypto) (fork : Fork) (env : BlockEnv) (world : World)
    (txs : List (Transaction × Option Address)) (withdrawals : List Withdrawal) :
    Except BlockError BodyOutput := do
  let world ← (beaconRootsCall fuel crypto fork env world).mapError fun _ => .outOfFuel none
  let out ← applyTxs fuel crypto fork env 0 txs { world }
  return { out with world := applyWithdrawals out.world withdrawals }

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

/-- `state_transition`: validate `block` against `head`, execute it and check every header
commitment (gas used, transactions root, state root, receipts root, logs bloom, withdrawals
root, blob gas used). Returns the new head and the receipts. `senderHints[i]`, if present,
is a known sender of transaction `i`; `fuel` bounds each message call. -/
def stateTransition (fuel : Nat) (crypto : Crypto) (fork : Fork) (chainId : Nat)
    (head : ChainHead) (block : Block) (senderHints : List (Option Address)) :
    Except BlockError (ChainHead × Array Receipt) := do
  let keccak := crypto.keccak256
  let h := block.header
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
  let hash := headerHash keccak h
  return ({ header := h, hash, world := out.world,
            ancestorHashes := (hash :: head.ancestorHashes).take 256 }, out.receipts)

end Block

end EvmLean
