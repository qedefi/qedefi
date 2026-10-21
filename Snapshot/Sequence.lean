import Snapshot.Fetch

/-!
# Transaction sequences on a snapshot

`targets.json` may list a `sequence`: transactions that change state, run one after the
other from the snapshot block, and node-side cheats between them (as anvil offers them):
```
"sequence": [
  {"label": "…", "setBalance": ["0x…", …], "value": "0x…"},       -- ether balances
  {"label": "…", "setCode": "0x…", "code": "0x…"},                 -- replace code (mock a feed)
  {"label": "…", "setStorage": "0x…", "slot": "0x…", "value": "0x…"},
  {"label": "…", "increaseTime": 2592000},                          -- advance time, mine a block
  {"label": "…", "from": "0x…", "to": "0x…", "data": "0x…", "value": "0x…", "gas": 3000000}, …]
```
Transactions are processed as `Tx.process` does with gas price zero (refund, EIP-7623 floor,
self-destructs, EIP-161 cleanup), each in the block environment the node mined it in. The
node's side (`Snapshot.Fork`) is recorded in `sequence.json`: per transaction the block
environment, status, return data, logs, `gasUsed`, and the balance, nonce and storage after it
of every account and slot either side touched. `snapshot check` replays the sequence offline
against that record (`checkSequence`).
-/

namespace Snapshot

open Lean EvmLean Conformance

/-! ## Steps -/

/-- What a step does. -/
inductive Action where
  | tx (c : CallSpec)
  | setBalance (accounts : List Address) (value : Nat)
  | setCode (account : Address) (code : ByteArray)
  | setStorage (account : Address) (slot value : Word)
  /-- Advance the clock by `seconds` and mine an empty block. -/
  | increaseTime (seconds : Nat)

structure Step where
  label : String
  action : Action

def Step.decode (j : Json) (sender : Address) : Except String Step := do
  let label := (j.getObjValAs? String "label").toOption.getD ""
  let value : Except String Nat := parseHexNat ((j.getObjValAs? String "value").toOption.getD "0x0")
  if let .ok v := j.getObjVal? "setBalance" then
    let as ← match v with
      | .str a => pure [← parseAddress a]
      | _ => (jsonArr v).toList.mapM fun a => jsonStr a >>= parseAddress
    return { label, action := .setBalance as (← value) }
  if let .ok a := j.getObjValAs? String "setCode" then
    return { label, action := .setCode (← parseAddress a) (← parseHexBytes (← getStrField j "code")) }
  if let .ok a := j.getObjValAs? String "setStorage" then
    return { label, action := .setStorage (← parseAddress a) (← parseWord (← getStrField j "slot"))
                                          (← parseWord (← getStrField j "value")) }
  if let .ok n := j.getObjValAs? Nat "increaseTime" then
    return { label, action := .increaseTime n }
  return { label, action := .tx (← CallSpec.decode j sender) }

/-- The `sequence` of `<dir>/targets.json` (empty if none). -/
def loadSequence (dir : System.FilePath) : IO (Array Step) := do
  let j ← ofExcept "targets.json" (Json.parse (← IO.FS.readFile (dir / "targets.json")))
  let sender ← match j.getObjValAs? String "sender" with
    | .ok s => ofExcept "sender" (parseAddress s)
    | .error _ => pure defaultSender
  ofExcept "targets.json sequence"
    ((jsonArr ((j.getObjVal? "sequence").toOption.getD .null)).mapM (Step.decode · sender))

/-! ## Running a sequence in the interpreter -/

/-- A transaction's outcome as its receipt and call trace show it. -/
structure TxOutcome where
  success : Bool
  output : ByteArray
  logs : Array Log
  /-- After the refund and the EIP-7623 floor. -/
  gasUsed : Nat
  deriving Inhabited

/-- Process the transaction of `c` (gas price zero) in `env`: the outcome, the world after,
and the reads. -/
def execTx (fork : Fork) (env : BlockEnv) (world : World) (c : CallSpec) :
    Except String (TxOutcome × World × Accesses) := do
  let (r, acc) ← simulateIn fork env world c
  let used := c.gas - r.gasLeft
  let gasUsed := used - min (used / 5) r.refundCounter.toNat
  let gasUsed := if fork ≥ .prague then max gasUsed (Tx.intrinsicGas (c.tx 0)).calldataFloor
    else gasUsed
  let w := r.accountsToDelete.foldl (fun w a => w.erase a) r.world
  let w := Tx.destroyTouchedEmpty w r.touchedAccounts
  return ({ success := r.success, output := r.output, logs := r.logs, gasUsed }, w, acc)

def applyCheat (w : World) : Action → World
  | .setBalance as v => as.foldl (fun w a => w.setBalance a (BitVec.ofNat 256 v)) w
  | .setCode a code => w.modify a fun acc => { acc with code }
  | .setStorage a k v => w.sstore a k v
  | _ => w

/-- What a cheat needs from the snapshot: the rest of the accounts (and slots) it changes. -/
def cheatReads : Action → Accesses
  | .setBalance as _ => as.foldl (·.addAccount ·) {}
  | .setCode a _ => ({} : Accesses).addAccount a
  | .setStorage a k _ => ({} : Accesses).addSlot a k
  | _ => {}

/-- One step as the interpreter ran it. -/
structure StepRun where
  outcome : Option TxOutcome
  before : World
  after : World
  reads : Accesses

/-- Run the steps from the snapshot state; transaction `i` runs in `envs[i]`. -/
def runSequence (s : State) (steps : Array Step) (envs : Array BlockEnv) :
    Except String (Array StepRun) := do
  let mut w := s.world
  let mut out := #[]
  for h : i in [0:steps.size] do
    let st := steps[i]
    match st.action with
    | .tx c =>
      let env := envs[i]?.getD s.blockEnv
      let (o, w', acc) ← (execTx s.fork env w c).mapError (s!"{st.label}: " ++ ·)
      out := out.push { outcome := some o, before := w, after := w', reads := acc }
      w := w'
    | a =>
      let w' := applyCheat w a
      out := out.push { outcome := none, before := w, after := w', reads := cheatReads a }
      w := w'
  return out

/-- Fetch what the sequence reads and the snapshot does not determine, until nothing is
missing (as `discover` does for calls). Every read is of the snapshot block: a slot a step
writes before a later step reads it is fetched too, as its original value (gas depends on
it). Returns the state and the rounds taken. -/
def discoverSequence (r : Rpc) (s : State) (steps : Array Step) (envs : Array BlockEnv)
    (maxRounds : Nat := 256) : IO (State × Nat) := do
  let mut s := s
  for round in [1:maxRounds + 1] do
    let runs ← ofExcept "sequence" (runSequence s steps envs)
    let miss := s.missing (runs.foldl (fun a x => a.union x.reads) {})
    if miss.isEmpty then return (s, round)
    IO.println s!"sequence round {round}: fetching {miss.accounts.size} accounts, \
      {miss.slotList.length} slots"
    s ← fetchInto r s miss.accounts.toList miss.slotList []
  fail s!"sequence state still incomplete after {maxRounds} rounds"

/-! ## The node's record: `sequence.json` -/

/-- What the node reported for a step (transactions; for cheats only the label). -/
structure Observed where
  label : String
  /-- The block the transaction was mined in. -/
  block : Nat := 0
  env : BlockEnv := {}
  outcome : Option TxOutcome := none
  /-- Balance and nonce after the step, of every account either side touched. -/
  accounts : Array (Address × Nat × Nat) := #[]
  /-- Storage after the step, of every slot either side touched. -/
  slots : Array (Address × Word × Word) := #[]
  deriving Inhabited

def encodeEnv (e : BlockEnv) : Json := Json.mkObj [
  ("coinbase", jStr (hexOfAddress e.coinbase)), ("number", toJson e.number),
  ("timestamp", toJson e.timestamp), ("gasLimit", toJson e.gasLimit),
  ("baseFee", toJson e.baseFee), ("prevRandao", jStr (hexOfWord e.prevRandao)),
  ("excessBlobGas", toJson e.excessBlobGas),
  ("parentBeaconBlockRoot", jStr (hexOfWord e.parentBeaconBlockRoot)),
  ("blockHashes", Json.arr (e.blockHashes.toArray.map (jStr ∘ hexOfWord)))]

def decodeEnv (chainId : Nat) (env : Json) : Except String BlockEnv := do
  return { chainId, coinbase := ← parseAddress (← getStrField env "coinbase"),
           number := ← getNatField env "number", timestamp := ← getNatField env "timestamp",
           gasLimit := ← getNatField env "gasLimit", baseFee := ← getNatField env "baseFee",
           prevRandao := ← parseWord (← getStrField env "prevRandao"),
           excessBlobGas := ← getNatField env "excessBlobGas",
           parentBeaconBlockRoot := ← parseWord (← getStrField env "parentBeaconBlockRoot"),
           blockHashes := ← (jsonArr ((env.getObjVal? "blockHashes").toOption.getD .null)).toList.mapM
             (jsonStr · >>= parseWord) }

def encodeLog (l : Log) : Json := Json.mkObj [("address", jStr (hexOfAddress l.address)),
  ("topics", Json.arr (l.topics.map (jStr ∘ hexOfWord))), ("data", jStr (hexOfBytes l.data))]

def decodeLog (j : Json) : Except String Log := do
  return { address := ← parseAddress (← getStrField j "address"),
           topics := ← (jsonArr ((j.getObjVal? "topics").toOption.getD .null)).mapM (jsonStr · >>= parseWord),
           data := ← parseHexBytes (← getStrField j "data") }

def Observed.encode (o : Observed) : Json :=
  let tx := match o.outcome with
    | none => []
    | some x => [("block", toJson o.block), ("env", encodeEnv o.env), ("success", Json.bool x.success),
        ("output", jStr (hexOfBytes x.output)), ("gasUsed", toJson x.gasUsed),
        ("logs", Json.arr (x.logs.map encodeLog))]
  Json.mkObj ([("label", jStr o.label)] ++ tx ++ [
    ("accounts", Json.mkObj (o.accounts.toList.map fun (a, b, n) =>
      (hexOfAddress a, Json.mkObj [("balance", jStr (hexOfNat b)), ("nonce", toJson n)]))),
    ("storage", Json.arr (o.slots.map fun (a, k, v) =>
      Json.arr #[jStr (hexOfAddress a), jStr (hexOfWord k), jStr (hexOfWord v)]))])

def Observed.decode (chainId : Nat) (j : Json) : Except String Observed := do
  let label := (j.getObjValAs? String "label").toOption.getD ""
  let accounts ← (objList (← getField j "accounts")).toArray.mapM fun (a, x) => do
    pure (← parseAddress a, ← parseHexNat (← getStrField x "balance"), ← getNatField x "nonce")
  let slots ← (jsonArr (← getField j "storage")).mapM fun x => do
    match (jsonArr x).toList with
    | [a, k, v] => pure (← jsonStr a >>= parseAddress, ← jsonStr k >>= parseWord, ← jsonStr v >>= parseWord)
    | _ => throw "storage entry"
  match j.getObjValAs? Bool "success" with
  | .error _ => return { label, accounts, slots }
  | .ok success =>
    return { label, accounts, slots, block := ← getNatField j "block",
             env := ← decodeEnv chainId (← getField j "env"),
             outcome := some { success, output := ← parseHexBytes (← getStrField j "output"),
                               gasUsed := ← getNatField j "gasUsed",
                               logs := ← (jsonArr (← getField j "logs")).mapM decodeLog } }

def saveObserved (dir : System.FilePath) (os : Array Observed) : IO Unit :=
  IO.FS.writeFile (dir / "sequence.json") ((Json.arr (os.map (·.encode))).pretty ++ "\n")

def loadObserved (dir : System.FilePath) (chainId : Nat) : IO (Array Observed) := do
  let j ← ofExcept "sequence.json" (Json.parse (← IO.FS.readFile (dir / "sequence.json")))
  ofExcept "sequence.json" ((jsonArr j).mapM (Observed.decode chainId))

/-! ## Comparing -/

def showLog (l : Log) : String :=
  s!"\{{hexOfAddress l.address} {l.topics.toList.map hexOfWord} {hexOfBytes l.data}}"

/-- The differences between a step run in the interpreter and the node's record, gas apart
(`gasNote`). Every recorded account and slot is compared; a slot or account the interpreter
changed and the record lacks is a difference too. -/
def compareStep (r : StepRun) (o : Observed) : List String := Id.run do
  let mut out := []
  match r.outcome, o.outcome with
  | some x, some y =>
    if x.success != y.success then out := out ++ [s!"status: lean {x.success}, node {y.success}"]
    if x.output != y.output then
      out := out ++ [s!"output: lean {hexOfBytes x.output}, node {hexOfBytes y.output}"]
    if x.logs.size != y.logs.size then
      out := out ++ [s!"logs: lean {x.logs.size}, node {y.logs.size}"]
    for (a, b) in x.logs.toList.zip y.logs.toList do
      if a != b then out := out ++ [s!"log: lean {showLog a}, node {showLog b}"]
  | _, _ => pure ()
  for (a, bal, n) in o.accounts do
    let acc := r.after.account a
    if acc.balance.toNat != bal then out := out ++ [s!"balance {hexOfAddress a}: lean {acc.balance.toNat}, node {bal}"]
    if acc.nonce != n then out := out ++ [s!"nonce {hexOfAddress a}: lean {acc.nonce}, node {n}"]
  for (a, k, v) in o.slots do
    let mine := r.after.sload a k
    if mine != v then
      out := out ++ [s!"storage {hexOfAddress a}[{hexOfWord k}]: lean {hexOfWord mine}, node {hexOfWord v}"]
  -- Cheats are compared through the transactions after them.
  if r.outcome.isNone then return out
  for (a, k) in r.reads.slotList do
    if r.before.sload a k != r.after.sload a k && !o.slots.any (fun (b, l, _) => a == b && k == l) then
      out := out ++ [s!"storage {hexOfAddress a}[{hexOfWord k}] written by lean only (not recorded)"]
  for a in r.reads.accounts.toList do
    let (x, y) := (r.before.account a, r.after.account a)
    if (x.balance != y.balance || x.nonce != y.nonce) && !o.accounts.any (·.1 == a) then
      out := out ++ [s!"account {hexOfAddress a} changed by lean only (not recorded)"]
  return out

/-- The gas difference of a transaction step, if any. -/
def gasNote (r : StepRun) (o : Observed) : Option String :=
  match r.outcome, o.outcome with
  | some x, some y => if x.gasUsed == y.gasUsed then none
    else some s!"gasUsed: lean {x.gasUsed}, node {y.gasUsed} ({(x.gasUsed : Int) - y.gasUsed})"
  | _, _ => none

/-- Replay the sequence offline against `sequence.json`; prints a line per step and returns
the number of steps that differ (gas included). -/
def checkSequence (dir : System.FilePath) (s : State) (verbose : Bool := false) : IO Nat := do
  let steps ← loadSequence dir
  let obs ← loadObserved dir s.chainId
  if obs.size != steps.size then fail "sequence.json does not match the sequence of targets.json"
  let runs ← ofExcept "sequence" (runSequence s steps (obs.map (·.env)))
  let miss := s.missing (runs.foldl (fun a x => a.union x.reads) {})
  let mut failures := 0
  for (st, r, o) in steps.toList.zip (runs.toList.zip obs.toList) do
    let diffs := compareStep r o
    let gas := gasNote r o
    if !diffs.isEmpty || gas.isSome then failures := failures + 1
    let tag := if !diffs.isEmpty then "MISMATCH  " else if gas.isSome then "GAS       " else "ok        "
    let summary := match r.outcome with
      | some x => s!" ({if x.success then "success" else "revert"}, {x.logs.size} logs, \
          gas {x.gasUsed}, {o.slots.size} slots, {o.accounts.size} accounts compared)"
      | none => ""
    if verbose || !diffs.isEmpty || gas.isSome then IO.println s!"{tag}{st.label}{summary}"
    for d in diffs ++ gas.toList do IO.println s!"            {d}"
  IO.println s!"{dir}: sequence of {steps.size} steps, {steps.size - failures} reproduce the \
    node's record exactly"
  if !miss.isEmpty then
    IO.println s!"INCOMPLETE  the sequence reads {miss.accounts.size} accounts, \
      {miss.slotList.length} slots outside the snapshot"
    return failures + 1
  return failures

end Snapshot
