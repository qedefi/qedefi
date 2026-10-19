import Lean.Data.Json
import Conformance.Hex

/-!
# BlockchainTests fixtures

Parsing of BlockchainTests JSON (`ethereum/tests`, and the `blockchain_tests` fixtures of
`ethereum/execution-spec-tests`) into Lean values:

* `pre` / `postState` become `World`s (zero storage values dropped, matching the canonical
  storage representation);
* every block is kept as its raw `rlp` (the authoritative encoding; invalid blocks are often
  given only in this form), together with `expectException`, the per-transaction `sender`
  hints, and — when present — the JSON `blockHeader` and `transactions`, which `--parse-only`
  cross-checks against the decoded RLP;
* the expected outcome is `postState` (exact world) or `postStateHash` (state root), plus
  `lastblockhash`.

All failures are `Except String` errors, reported by the runner as UNPARSEABLE.
-/

namespace Conformance

open EvmLean Lean

/-- Field `k` of a JSON object. -/
def field (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"missing field \"{k}\""

/-- Optional field `k` of a JSON object (`null` counts as absent). -/
def field? (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

/-- A string field. -/
def strField (j : Json) (k : String) : Except String String := do
  match (← field j k).getStr? with
  | .ok s => pure s
  | .error _ => throw s!"field \"{k}\" is not a string"

/-- A hex-number field. -/
def natField (j : Json) (k : String) : Except String Nat := do
  (parseHexNat (← strField j k)).mapError (s!"{k}: " ++ ·)

/-- A word field. -/
def wordField (j : Json) (k : String) : Except String Word := do
  (parseWord (← strField j k)).mapError (s!"{k}: " ++ ·)

/-- An address field. -/
def addressField (j : Json) (k : String) : Except String Address := do
  (parseAddress (← strField j k)).mapError (s!"{k}: " ++ ·)

/-- A hex-bytes field. -/
def bytesField (j : Json) (k : String) : Except String ByteArray := do
  (parseHexBytes (← strField j k)).mapError (s!"{k}: " ++ ·)

/-- The entries of a JSON object. -/
def objEntries (j : Json) : Except String (List (String × Json)) :=
  match j.getObj? with
  | .ok m => .ok m.toList
  | .error _ => .error "expected a JSON object"

/-- The elements of a JSON array. -/
def arrElems (j : Json) : Except String (Array Json) :=
  match j.getArr? with
  | .ok a => .ok a
  | .error _ => .error "expected a JSON array"

/-- Parse one account of a `pre`/`postState` map. -/
def parseAccount (j : Json) : Except String Account := do
  let storage ← (← objEntries (← field j "storage")).foldlM (init := (∅ : Storage))
    fun s (k, v) => do
      let key ← parseWord k
      let val ← match v.getStr? with
        | .ok str => parseWord str
        | .error _ => throw s!"storage value for {k} is not a string"
      pure (s.set key val)
  let balance ← natField j "balance"
  if balance ≥ 2 ^ 256 then throw "balance exceeds 256 bits"
  return { nonce := ← natField j "nonce", balance := BitVec.ofNat 256 balance,
           code := ← bytesField j "code", storage }

/-- Parse a world state (`pre`, `postState`). -/
def parseWorld (j : Json) : Except String World := do
  (← objEntries j).foldlM (init := (∅ : World)) fun w (addr, acc) => do
    let a ← parseAddress addr
    let acc ← (parseAccount acc).mapError (s!"account {addr}: " ++ ·)
    pure (w.insert a acc)

/-- Parse a JSON block header into a `Header` (used to cross-check decoded RLP).
`requestsHash` is present from Prague. -/
def parseHeader (j : Json) : Except String Header := do
  let requestsHash ← match field? j "requestsHash" with
    | some _ => pure (some (← wordField j "requestsHash"))
    | none => pure none
  return {
    requestsHash,
    parentHash := ← wordField j "parentHash", ommersHash := ← wordField j "uncleHash",
    coinbase := ← addressField j "coinbase", stateRoot := ← wordField j "stateRoot",
    transactionsRoot := ← wordField j "transactionsTrie",
    receiptRoot := ← wordField j "receiptTrie", bloom := ← bytesField j "bloom",
    difficulty := ← natField j "difficulty", number := ← natField j "number",
    gasLimit := ← natField j "gasLimit", gasUsed := ← natField j "gasUsed",
    timestamp := ← natField j "timestamp", extraData := ← bytesField j "extraData",
    prevRandao := ← wordField j "mixHash", nonce := ← bytesField j "nonce",
    baseFeePerGas := ← natField j "baseFeePerGas",
    withdrawalsRoot := ← wordField j "withdrawalsRoot",
    blobGasUsed := ← natField j "blobGasUsed", excessBlobGas := ← natField j "excessBlobGas",
    parentBeaconBlockRoot := ← wordField j "parentBeaconBlockRoot" }

/-- Parse a JSON access list. -/
def parseAccessList (j : Json) : Except String (List AccessListItem) := do
  (← arrElems j).toList.mapM fun e => do
    let keys ← (← arrElems (← field e "storageKeys")).toList.mapM fun k =>
      match k.getStr? with
      | .ok s => parseWord s
      | .error _ => .error "storage key is not a string"
    return { address := ← addressField e "address", storageKeys := keys }

/-- Parse a JSON EIP-7702 authorization list. The y-parity is `yParity` (or `v`). -/
def parseAuthorizations (j : Json) : Except String (List Authorization) := do
  (← arrElems j).toList.mapM fun e => do
    let yParity ← match field? e "yParity" with
      | some _ => natField e "yParity"
      | none => natField e "v"
    return { chainId := ← natField e "chainId", address := ← addressField e "address",
             nonce := ← natField e "nonce", yParity, r := ← natField e "r",
             s := ← natField e "s" }

/-- Parse the `to` field: empty for a contract creation. -/
def parseTo (j : Json) : Except String (Option Address) := do
  let s ← strField j "to"
  if stripHexPrefix s = "" then return none else return some (← parseAddress s)

/-- Parse a JSON transaction into a `Transaction` (used to cross-check decoded RLP). -/
def parseTransaction (j : Json) : Except String Transaction := do
  let ty ← match field? j "type" with
    | none => pure 0
    | some t => match t.getStr? with
      | .ok s => parseHexNat s
      | .error _ => throw "type is not a string"
  let accessList := fun (_ : Unit) => do
    match field? j "accessList" with
    | some al => parseAccessList al
    | none => pure []
  match ty with
  | 0 => return .legacy {
      nonce := ← natField j "nonce", gasPrice := ← natField j "gasPrice",
      gas := ← natField j "gasLimit", to := ← parseTo j, value := ← natField j "value",
      data := ← bytesField j "data", v := ← natField j "v", r := ← natField j "r",
      s := ← natField j "s" }
  | 1 => return .eip2930 {
      chainId := ← natField j "chainId", nonce := ← natField j "nonce",
      gasPrice := ← natField j "gasPrice", gas := ← natField j "gasLimit", to := ← parseTo j,
      value := ← natField j "value", data := ← bytesField j "data",
      accessList := ← accessList (), yParity := ← natField j "v", r := ← natField j "r",
      s := ← natField j "s" }
  | 2 => return .eip1559 {
      chainId := ← natField j "chainId", nonce := ← natField j "nonce",
      maxPriorityFeePerGas := ← natField j "maxPriorityFeePerGas",
      maxFeePerGas := ← natField j "maxFeePerGas", gas := ← natField j "gasLimit",
      to := ← parseTo j, value := ← natField j "value", data := ← bytesField j "data",
      accessList := ← accessList (), yParity := ← natField j "v", r := ← natField j "r",
      s := ← natField j "s" }
  | 3 =>
    let to ← match ← parseTo j with
      | some a => pure a
      | none => throw "blob transaction without recipient"
    let hashes ← (← arrElems (← field j "blobVersionedHashes")).toList.mapM fun h =>
      match h.getStr? with
      | .ok s => parseWord s
      | .error _ => .error "blob versioned hash is not a string"
    return .eip4844 {
      chainId := ← natField j "chainId", nonce := ← natField j "nonce",
      maxPriorityFeePerGas := ← natField j "maxPriorityFeePerGas",
      maxFeePerGas := ← natField j "maxFeePerGas", gas := ← natField j "gasLimit",
      to, value := ← natField j "value", data := ← bytesField j "data",
      accessList := ← accessList (), maxFeePerBlobGas := ← natField j "maxFeePerBlobGas",
      blobVersionedHashes := hashes, yParity := ← natField j "v", r := ← natField j "r",
      s := ← natField j "s" }
  | 4 =>
    let to ← match ← parseTo j with
      | some a => pure a
      | none => throw "set-code transaction without recipient"
    return .eip7702 {
      chainId := ← natField j "chainId", nonce := ← natField j "nonce",
      maxPriorityFeePerGas := ← natField j "maxPriorityFeePerGas",
      maxFeePerGas := ← natField j "maxFeePerGas", gas := ← natField j "gasLimit",
      to, value := ← natField j "value", data := ← bytesField j "data",
      accessList := ← accessList (),
      authorizations := ← parseAuthorizations (← field j "authorizationList"),
      yParity := ← natField j "v", r := ← natField j "r", s := ← natField j "s" }
  | n => throw s!"unknown transaction type {n}"

/-- One entry of a fixture's `blocks` array. -/
structure BlockFixture where
  /-- The block's RLP, if its hex parsed (the fixtures include deliberately malformed
  RLP, but always as valid hex). -/
  rlp : ByteArray
  /-- `expectException`: the block must be rejected. -/
  expectException : Option String
  /-- Per-transaction senders from the JSON `transactions` (if given). -/
  senders : List (Option Address)
  /-- The JSON `blockHeader`, if given. -/
  header : Option Header
  /-- The JSON `transactions`, if given. -/
  transactions : Option (List Transaction)

/-- The expected final state. -/
inductive PostCheck where
  /-- `postState`: the exact world. -/
  | state (w : World)
  /-- `postStateHash`: the state root. -/
  | hash (root : Word)

/-- A parsed BlockchainTests test case. -/
structure TestCase where
  /-- Test name (the JSON key). -/
  name : String
  /-- `network` (fork name). -/
  network : String
  /-- Pre-state. -/
  pre : World
  /-- Genesis block RLP. -/
  genesisRlp : ByteArray
  /-- Genesis header from JSON. -/
  genesisHeader : Header
  /-- Genesis block hash from JSON. -/
  genesisHash : Word
  /-- Blocks to import, in order. -/
  blocks : Array BlockFixture
  /-- Expected final state. -/
  post : PostCheck
  /-- Expected hash of the final head. -/
  lastBlockHash : Word
  /-- Chain id (`config.chainid`; `1` when absent, as in `ethereum/tests`). -/
  chainId : Nat

/-- Parse one block entry. -/
def parseBlock (j : Json) : Except String BlockFixture := do
  let expectException ← match field? j "expectException" with
    | none => pure none
    | some e => match e.getStr? with
      | .ok s => pure (some s)
      | .error _ => throw "expectException is not a string"
  let txsJson ← match field? j "transactions" with
    | some t => pure (some (← arrElems t))
    | none => pure none
  let senders ← match txsJson with
    | none => pure []
    | some txs => txs.toList.mapM fun tx => match field? tx "sender" with
      | some s => match s.getStr? with
        | .ok str => (parseAddress str).map some
        | .error _ => .error "sender is not a string"
      | none => .ok none
  -- The JSON forms of invalid blocks may be partial; only cross-check valid ones.
  let header ← match field? j "blockHeader", expectException with
    | some h, none => pure (some (← (parseHeader h).mapError ("blockHeader: " ++ ·)))
    | _, _ => pure none
  let transactions ← match txsJson, expectException with
    | some txs, none => pure (some (← txs.toList.mapM fun t =>
        (parseTransaction t).mapError ("transaction: " ++ ·)))
    | _, _ => pure none
  return { rlp := ← bytesField j "rlp", expectException, senders, header, transactions }

/-- Parse a test case. Returns the network first so that tests of other forks can be
skipped without parsing the rest. -/
def parseNetwork (j : Json) : Except String String := strField j "network"

/-- Parse a full test case. -/
def parseTestCase (name : String) (j : Json) : Except String TestCase := do
  let post ← match field? j "postState", field? j "postStateHash" with
    | some p, _ => pure (.state (← (parseWorld p).mapError ("postState: " ++ ·)))
    | none, some h => match h.getStr? with
      | .ok s => pure (.hash (← parseWord s))
      | .error _ => throw "postStateHash is not a string"
    | none, none => throw "neither postState nor postStateHash"
  let genesisJson ← field j "genesisBlockHeader"
  let chainId ← match field? j "config" with
    | some c => match field? c "chainid" with
      | some _ => natField c "chainid"
      | none => pure 1
    | none => pure 1
  return {
    chainId,
    name, network := ← parseNetwork j,
    pre := ← (parseWorld (← field j "pre")).mapError ("pre: " ++ ·),
    genesisRlp := ← bytesField j "genesisRLP",
    genesisHeader := ← (parseHeader genesisJson).mapError ("genesisBlockHeader: " ++ ·),
    genesisHash := ← wordField genesisJson "hash",
    blocks := ← (← arrElems (← field j "blocks")).mapIdxM fun i b =>
      (parseBlock b).mapError (s!"block {i}: " ++ ·),
    post, lastBlockHash := ← wordField j "lastblockhash" }

end Conformance
