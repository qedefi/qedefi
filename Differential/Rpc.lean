import Lean.Data.Json
import Conformance.Hex

/-!
# JSON-RPC client for anvil

The reference side of the differential tester is Foundry's `anvil` (revm), driven over
JSON-RPC. Requests go through `curl` (Lean core has no HTTP client); every request of a
step is sent as one JSON-RPC batch to keep the number of round trips small.

What is observed per transaction:

* the receipt: status, logs, `gasUsed`;
* `debug_traceTransaction` with `callTracer`: the top-level return or revert data;
* `debug_traceTransaction` with `prestateTracer` in diff mode: which storage slots of which
  accounts the transaction wrote. The storage comparison reads these slots (together with
  every slot evm-lean has non-zero before or after the call) with `eth_getStorageAt`, so a
  write on either side is never missed.
-/

namespace Differential

open Lean EvmLean Conformance

/-- A JSON-RPC endpoint. -/
structure Rpc where
  /-- HTTP URL, e.g. `http://127.0.0.1:8545`. -/
  url : String

/-- Raise a user error. -/
def fail {α : Type} (msg : String) : IO α := throw (IO.userError msg)

/-- Lift an `Except String` into `IO`. -/
def ofExcept {α : Type} (ctx : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => fail s!"{ctx}: {e}"

/-- POST a JSON body and return the response body. -/
def Rpc.post (r : Rpc) (body : String) : IO String := do
  let out ← IO.Process.output {
    cmd := "curl"
    args := #["-s", "-S", "-X", "POST", "-H", "Content-Type: application/json",
              "--data-binary", body, r.url] }
  if out.exitCode != 0 then fail s!"curl failed ({out.exitCode}): {out.stderr}"
  pure out.stdout

/-- Send a batch of `(method, params)` requests; returns the results in order, or fails on
the first JSON-RPC error. -/
def Rpc.batch (r : Rpc) (calls : Array (String × Json)) : IO (Array Json) := do
  if calls.isEmpty then return #[]
  let reqs := calls.mapIdx fun i (m, p) =>
    Json.mkObj [("jsonrpc", "2.0"), ("id", toJson i), ("method", m), ("params", p)]
  let text ← r.post (Json.arr reqs).compress
  let resp ← ofExcept "invalid JSON-RPC response" (Json.parse text)
  let arr ← match resp.getArr? with
    | .ok a => pure a
    | .error _ => fail s!"JSON-RPC error: {text.take 2000}"
  let mut out : Array Json := Array.replicate calls.size Json.null
  for item in arr do
    let id := (item.getObjValAs? Nat "id").toOption.getD calls.size
    match item.getObjVal? "error" with
    | .ok e =>
      let m := (calls[id]?.map (·.1)).getD "?"
      fail s!"JSON-RPC error in {m}: {e.compress}"
    | .error _ => pure ()
    if h : id < out.size then
      out := out.set id ((item.getObjVal? "result").toOption.getD Json.null)
  return out

/-- Send one request. -/
def Rpc.call (r : Rpc) (method : String) (params : Json) : IO Json := do
  let rs ← r.batch #[(method, params)]
  pure (rs[0]?.getD Json.null)

/-! ## JSON field access -/

/-- A string field (`""` if absent). -/
def strField (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

/-- A hex-number field (`0` if absent or malformed). -/
def natField (j : Json) (k : String) : Nat :=
  (parseHexNat (strField j k)).toOption.getD 0

/-- A hex-bytes field (empty if absent or malformed). -/
def bytesField (j : Json) (k : String) : ByteArray :=
  (parseHexBytes (strField j k)).toOption.getD .empty

/-- Parse a hex word. -/
def wordOfHex (s : String) : Word := BitVec.ofNat 256 ((parseHexNat s).toOption.getD 0)

/-- Parse a hex address. -/
def addressOfHex (s : String) : Address := BitVec.ofNat 160 ((parseHexNat s).toOption.getD 0)

/-- The members of a JSON object (empty if not an object). -/
def objEntries (j : Json) : List (String × Json) :=
  match j.getObj? with
  | .ok kvs => kvs.toList.map fun ⟨k, v⟩ => (k, v)
  | .error _ => []

/-! ## Anvil -/

/-- What anvil reports about an executed transaction. -/
structure Observed where
  /-- Receipt status. -/
  success : Bool
  /-- Return data, or revert data (top-level call frame). -/
  output : ByteArray
  /-- Receipt logs. -/
  logs : Array Log
  /-- Receipt `gasUsed` (after the refund). -/
  gasUsed : Nat
  /-- Created contract (creations only). -/
  created : Option Address
  /-- Storage slots written, per account (`prestateTracer` diff, pre and post). -/
  touchedSlots : List (Address × Word)
  /-- The environment of the block the transaction was mined in. -/
  env : BlockEnv

/-- A transaction as sent to anvil. -/
def txJson (sender : Address) (to : Option Address) (data : ByteArray) (gas : Nat) : Json :=
  let base := [("from", Json.str (hexOfAddress sender)), ("data", Json.str (hexOfBytes data)),
               ("gas", Json.str (hexOfNat gas)), ("gasPrice", Json.str "0x0"),
               ("value", Json.str "0x0")]
  Json.mkObj (match to with
    | some a => ("to", Json.str (hexOfAddress a)) :: base
    | none => base)

/-- Parse a receipt log. -/
def logOfJson (j : Json) : Log :=
  let topics := match j.getObjValAs? (Array String) "topics" with
    | .ok ts => ts.map wordOfHex
    | .error _ => #[]
  { address := addressOfHex (strField j "address"), topics, data := bytesField j "data" }

/-- Storage slots mentioned in a `prestateTracer` diff (`pre` and `post`). -/
def diffSlots (j : Json) : List (Address × Word) :=
  ["pre", "post"].flatMap fun side =>
    let accounts := objEntries ((j.getObjVal? side).toOption.getD Json.null)
    accounts.flatMap fun (a, acct) =>
      let storage := objEntries ((acct.getObjVal? "storage").toOption.getD Json.null)
      storage.map fun (k, _) => (addressOfHex a, wordOfHex k)

/-- Send a transaction (automine) and collect its receipt, its block's environment (for chain
`chainId`) and its traces. -/
def Rpc.execute (r : Rpc) (chainId : Nat) (sender : Address) (to : Option Address) (data : ByteArray)
    (gas : Nat) : IO Observed := do
  let hashJ ← r.call "eth_sendTransaction" (Json.arr #[txJson sender to data gas])
  let hash ← match hashJ.getStr? with
    | .ok h => pure h
    | .error _ => fail s!"eth_sendTransaction returned {hashJ.compress}"
  let rs ← r.batch #[
    ("eth_getTransactionReceipt", Json.arr #[hash]),
    ("eth_getBlockByNumber", Json.arr #["latest", false]),
    ("debug_traceTransaction", Json.arr #[hash, Json.mkObj [("tracer", "callTracer")]]),
    ("debug_traceTransaction", Json.arr #[hash, Json.mkObj [("tracer", "prestateTracer"),
      ("tracerConfig", Json.mkObj [("diffMode", true)])]])]
  let receipt := rs[0]?.getD Json.null
  let block := rs[1]?.getD Json.null
  let call := rs[2]?.getD Json.null
  let diff := rs[3]?.getD Json.null
  if natField block "number" != natField receipt "blockNumber" then
    fail s!"transaction {hash} was not mined in the latest block"
  let env : BlockEnv :=
    { chainId, number := natField block "number", timestamp := natField block "timestamp",
      coinbase := addressOfHex (strField block "miner"), gasLimit := natField block "gasLimit",
      baseFee := natField block "baseFeePerGas", prevRandao := wordOfHex (strField block "mixHash") }
  let logs := match receipt.getObjValAs? (Array Json) "logs" with
    | .ok ls => ls.map logOfJson
    | .error _ => #[]
  let created := match receipt.getObjValAs? String "contractAddress" with
    | .ok a => some (addressOfHex a)
    | .error _ => none
  return { success := natField receipt "status" == 1, output := bytesField call "output", logs,
           gasUsed := natField receipt "gasUsed", created, touchedSlots := diffSlots diff, env }

/-- Read storage slots at the latest block (one batch). -/
def Rpc.storageAt (r : Rpc) (slots : Array (Address × Word)) : IO (Array Word) := do
  let rs ← r.batch (slots.map fun (a, k) =>
    ("eth_getStorageAt", Json.arr #[hexOfAddress a, hexOfWord k, "latest"]))
  return rs.map fun j => wordOfHex (j.getStr?.toOption.getD "0x0")

/-- Deployed code of an account. -/
def Rpc.code (r : Rpc) (a : Address) : IO ByteArray := do
  let j ← r.call "eth_getCode" (Json.arr #[hexOfAddress a, "latest"])
  ofExcept "eth_getCode" (parseHexBytes (j.getStr?.toOption.getD "0x"))

/-- Take a snapshot (`evm_snapshot`). -/
def Rpc.snapshot (r : Rpc) : IO Json := r.call "evm_snapshot" (Json.arr #[])

/-- Revert to a snapshot (`evm_revert`); the snapshot is consumed. -/
def Rpc.revertTo (r : Rpc) (id : Json) : IO Unit := do
  let ok ← r.call "evm_revert" (Json.arr #[id])
  if ok != Json.bool true then fail s!"evm_revert {id.compress} failed"

/-- Reset the chain to genesis (`anvil_reset`). -/
def Rpc.reset (r : Rpc) : IO Unit := discard <| r.call "anvil_reset" (Json.arr #[])

/-- Start anvil (Cancun, chain id 1, zero base fee, any sender impersonated) on `port`, and
wait until it answers. -/
def spawnAnvil (port : Nat) (chainId : Nat) :
    IO (IO.Process.Child { stdin := .null, stdout := .null, stderr := .null }) := do
  let child ← IO.Process.spawn {
    cmd := "anvil"
    args := #["--port", toString port, "--chain-id", toString chainId, "--hardfork", "cancun",
              "--silent", "--auto-impersonate", "--base-fee", "0", "--gas-price", "0",
              "--gas-limit", "1000000000"]
    stdin := .null, stdout := .null, stderr := .null }
  let r : Rpc := { url := s!"http://127.0.0.1:{port}" }
  for _ in [0:100] do
    try
      discard <| r.call "eth_chainId" (Json.arr #[])
      return child
    catch _ => IO.sleep 100
  child.kill
  fail "anvil did not start (is Foundry in PATH?)"

end Differential
