import Snapshot.Rpc
import Snapshot.State

/-!
# Simulating calls on a snapshot

A call runs like `eth_call`: a legacy transaction with gas price zero (no fee is charged, the
sender's nonce is bumped), its top-level message executed by the interpreter with
`runObserved`, so the result comes with the reads it made.

`calls.json` records each call with the node's `eth_call` result at the snapshot block:
```
[{"label", "from", "to", "data", "value", "gas", "rpc": {"success", "output"}}, …]
```
-/

namespace Snapshot

open Lean EvmLean Conformance

/-- Interpreter steps allowed per call. -/
def fuel : Nat := 100_000_000

/-- Run `c` on `world` in the snapshot's environment. -/
def simulate (s : State) (world : World) (c : CallSpec) :
    Except String (MessageResult × Accesses) := do
  let tx : Transaction := .legacy
    { nonce := (world.account c.sender).nonce, gasPrice := 0, gas := c.gas, to := some c.target,
      value := c.value, data := c.data, v := 27, r := 0, s := 0 }
  let intrinsic := (Tx.intrinsicGas tx).regular
  if c.gas < intrinsic then throw s!"gas {c.gas} below the intrinsic cost {intrinsic}"
  if (world.balance c.sender).toNat < c.value then throw "the sender cannot pay the value"
  let nonce := (world.account c.sender).nonce
  let w := Interpreter.incrementNonce world c.sender
  let msg := Tx.prepareMessage Crypto.real s.fork s.blockEnv w tx c.sender nonce (c.gas - intrinsic)
  match runObserved fuel (s.context c.sender) w msg with
  | (.ok r, acc) => pure (r, acc)
  | (.error _, _) => throw "interpreter out of fuel"

/-- A call and the node's result for it. -/
structure RecordedCall where
  spec : CallSpec
  rpc : CallResult

def CallSpec.encode (c : CallSpec) : List (String × Json) :=
  [("label", Json.str c.label), ("from", Json.str (hexOfAddress c.sender)),
   ("to", Json.str (hexOfAddress c.target)), ("data", Json.str (hexOfBytes c.data)),
   ("value", Json.str (hexOfNat c.value)), ("gas", toJson c.gas)]

/-- Parse a call (`from`, `value`, `gas`, `label` optional). -/
def CallSpec.decode (j : Json) (defaultSender : Address) : Except String CallSpec := do
  let sender ← match j.getObjValAs? String "from" with
    | .ok s => parseAddress s
    | .error _ => pure defaultSender
  return {
    label := (j.getObjValAs? String "label").toOption.getD "",
    sender, target := ← parseAddress (← getStrField j "to"),
    data := ← parseHexBytes ((j.getObjValAs? String "data").toOption.getD "0x"),
    value := ← parseHexNat ((j.getObjValAs? String "value").toOption.getD "0x0"),
    gas := (j.getObjValAs? Nat "gas").toOption.getD 30_000_000 }

def RecordedCall.encode (r : RecordedCall) : Json :=
  Json.mkObj (r.spec.encode ++ [("rpc", Json.mkObj [("success", Json.bool r.rpc.success),
    ("output", Json.str (hexOfBytes r.rpc.output))])])

def RecordedCall.decode (j : Json) : Except String RecordedCall := do
  let rpc ← getField j "rpc"
  return { spec := ← CallSpec.decode j 0,
           rpc := { success := ← (match rpc.getObjValAs? Bool "success" with
                                    | .ok b => pure b
                                    | .error e => throw e),
                    output := ← parseHexBytes (← getStrField rpc "output") } }

def saveCalls (dir : System.FilePath) (cs : Array RecordedCall) : IO Unit :=
  IO.FS.writeFile (dir / "calls.json") ((Json.arr (cs.map (·.encode))).pretty ++ "\n")

def loadCalls (dir : System.FilePath) : IO (Array RecordedCall) := do
  let j ← ofExcept "calls.json" (Json.parse (← IO.FS.readFile (dir / "calls.json")))
  let arr ← ofExcept "calls.json" (match j.getArr? with
    | .ok a => .ok a
    | .error _ => .error "expected an array")
  arr.mapM fun c => ofExcept "calls.json" (RecordedCall.decode c)

/-- The verdict on one recorded call replayed on the snapshot. -/
inductive Verdict where
  /-- Same success flag and output as the node, and every read determined by the snapshot. -/
  | ok
  /-- Different result from the node's. -/
  | mismatch (got : CallResult)
  /-- Reads outside the snapshot: the result is not determined by it. -/
  | incomplete (missing : Accesses)
  | error (msg : String)

/-- Replay a recorded call on the snapshot. -/
def replay (s : State) (world : World) (r : RecordedCall) : Verdict :=
  match simulate s world r.spec with
  | .error e => .error e
  | .ok (res, acc) =>
    let miss := s.missing acc
    if !miss.isEmpty then .incomplete miss
    else
      let got : CallResult := { success := res.success, output := res.output }
      if got == r.rpc then .ok else .mismatch got

end Snapshot
