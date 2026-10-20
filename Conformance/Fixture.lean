import Lean.Data.Json
import Conformance.Hex

/-!
# BlockchainTests fixtures

Parses BlockchainTests JSON (`ethereum/tests` and EEST) into Lean values. Blocks are kept as raw
`rlp` (authoritative; invalid blocks often exist only in this form); the JSON `blockHeader` and
`transactions` are parsed only to cross-check it. Failures are `Except String` errors, which the
runner reports as UNPARSEABLE.
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

def strField (j : Json) (k : String) : Except String String := do
  match (← field j k).getStr? with
  | .ok s => pure s
  | .error _ => throw s!"field \"{k}\" is not a string"

def natField (j : Json) (k : String) : Except String Nat := do
  (parseHexNat (← strField j k)).mapError (s!"{k}: " ++ ·)

def wordField (j : Json) (k : String) : Except String Word := do
  (parseWord (← strField j k)).mapError (s!"{k}: " ++ ·)

def addressField (j : Json) (k : String) : Except String Address := do
  (parseAddress (← strField j k)).mapError (s!"{k}: " ++ ·)

def bytesField (j : Json) (k : String) : Except String ByteArray := do
  (parseHexBytes (← strField j k)).mapError (s!"{k}: " ++ ·)

def objEntries (j : Json) : Except String (List (String × Json)) :=
  match j.getObj? with
  | .ok m => .ok m.toList
  | .error _ => .error "expected a JSON object"

def arrElems (j : Json) : Except String (Array Json) :=
  match j.getArr? with
  | .ok a => .ok a
  | .error _ => .error "expected a JSON array"

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

def parseWorld (j : Json) : Except String World := do
  (← objEntries j).foldlM (init := (∅ : World)) fun w (addr, acc) => do
    let a ← parseAddress addr
    let acc ← (parseAccount acc).mapError (s!"account {addr}: " ++ ·)
    pure (w.insert a acc)

/-- `requestsHash` is present from Prague. -/
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

def parseAccessList (j : Json) : Except String (List AccessListItem) := do
  (← arrElems j).toList.mapM fun e => do
    let keys ← (← arrElems (← field e "storageKeys")).toList.mapM fun k =>
      match k.getStr? with
      | .ok s => parseWord s
      | .error _ => .error "storage key is not a string"
    return { address := ← addressField e "address", storageKeys := keys }

/-- The y-parity is `yParity` (or `v`). -/
def parseAuthorizations (j : Json) : Except String (List Authorization) := do
  (← arrElems j).toList.mapM fun e => do
    let yParity ← match field? e "yParity" with
      | some _ => natField e "yParity"
      | none => natField e "v"
    return { chainId := ← natField e "chainId", address := ← addressField e "address",
             nonce := ← natField e "nonce", yParity, r := ← natField e "r",
             s := ← natField e "s" }

/-- `to` is empty for a contract creation. -/
def parseTo (j : Json) : Except String (Option Address) := do
  let s ← strField j "to"
  if stripHexPrefix s = "" then return none else return some (← parseAddress s)

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
  /-- Raw RLP (may be deliberately malformed, but is always valid hex). -/
  rlp : ByteArray
  /-- `expectException`: the block must be rejected. -/
  expectException : Option String
  /-- Per-transaction `sender` hints from the JSON `transactions`. -/
  senders : List (Option Address)
  header : Option Header
  transactions : Option (List Transaction)

inductive PostCheck where
  /-- `postState`: the exact world. -/
  | state (w : World)
  /-- `postStateHash`: the state root. -/
  | hash (root : Word)

structure TestCase where
  name : String
  /-- `network` (fork name). -/
  network : String
  pre : World
  genesisRlp : ByteArray
  genesisHeader : Header
  genesisHash : Word
  blocks : Array BlockFixture
  post : PostCheck
  lastBlockHash : Word
  /-- Chain id (`config.chainid`; `1` when absent, as in `ethereum/tests`). -/
  chainId : Nat

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

/-- Read first, so tests of other forks are skipped without parsing the rest. -/
def parseNetwork (j : Json) : Except String String := strField j "network"

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
