import Conformance.Hex
import Snapshot.Http

/-!
# Read-only JSON-RPC client

Only standard `eth_*` reads, all at an explicit block: no `debug_*` or `trace_*` methods, so
any archive endpoint works. Requests are sent in batches of at most `batchSize`.
-/

namespace Snapshot

open Lean EvmLean Conformance

/-- A JSON-RPC endpoint. The URL may contain an API key: it is never printed or saved. -/
structure Rpc where
  url : String

/-- Requests per HTTP batch. -/
def batchSize : Nat := 100

/-- The outcome of one request: its result, or the JSON-RPC error object. -/
abbrev RpcResult := Except Json Json

/-- Send one batch; results in request order. -/
def Rpc.batchOnce (r : Rpc) (part : Array (String × Json)) : IO (Array RpcResult) := do
  let reqs := part.mapIdx fun i (m, p) =>
    Json.mkObj [("jsonrpc", "2.0"), ("id", toJson i), ("method", m), ("params", p)]
  let text ← postJson r.url (Json.arr reqs).compress
  -- A throttled batch may be refused as a whole (an error object, or an empty body): every
  -- request of it is then marked rate-limited, to be retried.
  let refused := Array.replicate part.size (.error (Json.mkObj [("code", toJson (429 : Int))]))
  let some resp := (Json.parse text).toOption | return refused
  let arr ← match resp.getArr? with
    | .ok a => pure a
    | .error _ =>
      if (resp.getObjVal? "error" >>= (·.getObjValAs? Int "code")).toOption == some 429 then
        return refused
      else fail s!"JSON-RPC error: {text.take 500}"
  let mut res : Array RpcResult := Array.replicate part.size (.error (Json.str "no response"))
  for item in arr do
    let some i := (item.getObjValAs? Nat "id").toOption | continue
    if i < part.size then
      res := res.set! i <| match item.getObjVal? "error" with
        | .ok e => .error e
        | .error _ => .ok ((item.getObjVal? "result").toOption.getD .null)
  return res

/-- Whether a request was refused by rate limiting (HTTP/JSON-RPC 429), to be retried. -/
def rateLimited : RpcResult → Bool
  | .error e => (e.getObjValAs? Int "code").toOption == some 429
  | .ok _ => false

/-- Send `(method, params)` requests in batches; results in request order. Requests refused
by rate limiting (free tiers allow a few hundred compute units per second) are resent after
a growing pause. -/
def Rpc.batchRaw (r : Rpc) (calls : Array (String × Json)) : IO (Array RpcResult) := do
  let mut out : Array RpcResult := #[]
  for chunk in (List.range ((calls.size + batchSize - 1) / batchSize)) do
    let part := calls.extract (chunk * batchSize) ((chunk + 1) * batchSize)
    let mut res ← r.batchOnce part
    for attempt in [1:30] do
      let todo := (List.range part.size).filter fun i => rateLimited res[i]!
      if todo.isEmpty then break
      IO.sleep (min 10_000 (500 * attempt)).toUInt32
      let again ← r.batchOnce (todo.toArray.map (part[·]!))
      for (i, x) in todo.zip again.toList do res := res.set! i x
    out := out ++ res
  return out

/-- As `batchRaw`, failing on the first JSON-RPC error. -/
def Rpc.batch (r : Rpc) (calls : Array (String × Json)) : IO (Array Json) := do
  let res ← r.batchRaw calls
  res.mapIdxM fun i x => match x with
    | .ok j => pure j
    | .error e => fail s!"{calls[i]!.1} failed: {e.compress}"

def Rpc.call (r : Rpc) (method : String) (params : Json) : IO Json := do
  match (← r.batch #[(method, params)])[0]? with
  | some j => pure j
  | none => fail s!"{method}: no result"

def blockTag (n : Nat) : Json := Json.str (hexOfNat n)

def jsonStr (j : Json) : Except String String :=
  match j.getStr? with
  | .ok s => .ok s
  | .error _ => .error s!"expected a string, got {j.compress.take 80}"

def jsonNat (j : Json) : Except String Nat := jsonStr j >>= parseHexNat
def jsonWord (j : Json) : Except String Word := jsonStr j >>= parseWord
def jsonBytes (j : Json) : Except String ByteArray := jsonStr j >>= parseHexBytes

def Rpc.chainId (r : Rpc) : IO Nat := do
  ofExcept "eth_chainId" (jsonNat (← r.call "eth_chainId" (Json.arr #[])))

def Rpc.blockNumber (r : Rpc) : IO Nat := do
  ofExcept "eth_blockNumber" (jsonNat (← r.call "eth_blockNumber" (Json.arr #[])))

/-- The header of block `n` (transactions as hashes). -/
def Rpc.block (r : Rpc) (n : Nat) : IO Json :=
  r.call "eth_getBlockByNumber" (Json.arr #[blockTag n, Json.bool false])

/-- An account at block `n`: balance, nonce, code. -/
structure RemoteAccount where
  balance : Nat
  nonce : Nat
  code : ByteArray

/-- Fetch accounts at block `n` (three requests per account, batched). -/
def Rpc.accounts (r : Rpc) (n : Nat) (as : Array Address) : IO (Array RemoteAccount) := do
  let reqs := as.foldl (init := #[]) fun acc a =>
    let p := Json.arr #[Json.str (hexOfAddress a), blockTag n]
    acc.push ("eth_getBalance", p) |>.push ("eth_getTransactionCount", p) |>.push ("eth_getCode", p)
  let res ← r.batch reqs
  as.mapIdxM fun i a => ofExcept s!"account {hexOfAddress a}" do
    return { balance := ← jsonNat res[3 * i]!, nonce := ← jsonNat res[3 * i + 1]!,
             code := ← jsonBytes res[3 * i + 2]! }

/-- Fetch storage slots at block `n` (one request per slot, batched). -/
def Rpc.storage (r : Rpc) (n : Nat) (slots : Array (Address × Word)) : IO (Array Word) := do
  let reqs := slots.map fun (a, k) =>
    ("eth_getStorageAt", Json.arr #[Json.str (hexOfAddress a), Json.str (hexOfWord k), blockTag n])
  let res ← r.batch reqs
  res.mapIdxM fun i j => ofExcept s!"storage {hexOfAddress slots[i]!.1}" (jsonWord j)

/-- A call to simulate: sender, target, calldata, value, gas limit. -/
structure CallSpec where
  label : String := ""
  sender : Address
  target : Address
  data : ByteArray
  value : Nat := 0
  gas : Nat := 30_000_000

/-- The node's view of a call: success flag and return or revert data. -/
structure CallResult where
  success : Bool
  output : ByteArray
  deriving BEq

def CallSpec.toRpcJson (c : CallSpec) : Json :=
  Json.mkObj [("from", Json.str (hexOfAddress c.sender)), ("to", Json.str (hexOfAddress c.target)),
    ("data", Json.str (hexOfBytes c.data)), ("value", Json.str (hexOfNat c.value)),
    ("gas", Json.str (hexOfNat c.gas))]

/-- `eth_call` each spec at block `n`. A revert is a JSON-RPC error carrying the revert data
in `data`; an error without data (e.g. out of gas) counts as a failure with empty output. -/
def Rpc.ethCalls (r : Rpc) (n : Nat) (cs : Array CallSpec) : IO (Array CallResult) := do
  let res ← r.batchRaw (cs.map fun c => ("eth_call", Json.arr #[c.toRpcJson, blockTag n]))
  res.mapM fun
    | .ok j => do return { success := true, output := ← ofExcept "eth_call" (jsonBytes j) }
    | .error e =>
      let data := (e.getObjVal? "data").toOption.bind fun d => (jsonBytes d).toOption
      return { success := false, output := data.getD .empty }

end Snapshot
