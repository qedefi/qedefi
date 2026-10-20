import Examples.Differential.Rpc
import Examples.Differential.Local
import Examples.Differential.Gen

/-!
# Comparing evm-lean with anvil, call by call

A `Session` is a deployed system (a vault family or a token) on both sides, with a call
generator. Every call runs on anvil first, then in evm-lean in the environment of the block
anvil mined; status, output, logs, `gasUsed`, the storage of the watched accounts (and of
every account anvil wrote) and, optionally, ether balances are compared. Random sequences
are generated, run and shrunk to a minimal mismatch.
-/

namespace Examples.Differential

open Lean EvmLean Conformance

/-- Gas limit of every transaction. -/
def gasLimit : Nat := 10_000_000

/-- Run statistics. -/
structure Stats where
  /-- Calls executed (including deployments and replays while shrinking). -/
  calls : Nat := 0
  /-- Calls that succeeded on both sides. -/
  successes : Nat := 0
  /-- Per operation: calls and successes. -/
  byKind : Std.HashMap String (Nat × Nat) := {}
  /-- Mismatching sequences. -/
  mismatches : Nat := 0

/-- What is compared after each call besides the outcome. -/
structure Watch where
  /-- Accounts whose storage is compared (with every account anvil wrote). -/
  accounts : List Address
  /-- Accounts whose ether balance is compared. -/
  eth : List Address := []
  /-- Corrupt evm-lean's state after a call of the given kind (tester self-test). -/
  corrupt : String → World → World := fun _ w => w

def showLog (l : Log) : String :=
  s!"\{address {hexOfAddress l.address}, topics {l.topics.toList.map hexOfWord}, " ++
    s!"data {hexOfBytes l.data}}"

/-- Differences between the evm-lean outcome and anvil's observation. -/
def compareOutcome (o : Outcome) (obs : Observed) : List String := Id.run do
  let mut out := []
  if o.success != obs.success then
    out := out ++ [s!"status: evm-lean {o.success}, anvil {obs.success}"]
  if o.output != obs.output then
    out := out ++ [s!"output: evm-lean {hexOfBytes o.output}, anvil {hexOfBytes obs.output}"]
  if o.gasUsed != obs.gasUsed then
    out := out ++ [s!"gasUsed: evm-lean {o.gasUsed}, anvil {obs.gasUsed}"]
  if o.logs.size != obs.logs.size then
    out := out ++ [s!"logs: evm-lean {o.logs.size}, anvil {obs.logs.size}"]
  for i in [0:min o.logs.size obs.logs.size] do
    match o.logs[i]?, obs.logs[i]? with
    | some a, some b =>
      if a != b then out := out ++ [s!"log {i}: evm-lean {showLog a}, anvil {showLog b}"]
    | _, _ => pure ()
  return out

/-- Compare the storage of the relevant accounts: every slot evm-lean holds before or after
the call in a watched account or any account anvil wrote, and every slot anvil wrote. -/
def compareStorage (rpc : Rpc) (watched : List Address) (before after : World)
    (touched : List (Address × Word)) : IO (List String) := do
  let accounts := touched.map (·.1) ++ watched
  let lean := accounts.flatMap fun a =>
    (storageSlots before a ++ storageSlots after a).map fun k => (a, k)
  let mut seen : Std.HashMap String (Address × Word) := {}
  for (a, k) in touched ++ lean do
    seen := seen.insert (hexOfAddress a ++ hexOfWord k) (a, k)
  let slots := seen.toArray.map (·.2)
  let vals ← rpc.storageAt slots
  let mut out := []
  for h : i in [0:slots.size] do
    let (a, k) := slots[i]
    let v := vals[i]?.getD 0
    let mine := after.sload a k
    if mine != v then
      out := out ++ [s!"storage {hexOfAddress a}[{hexOfWord k}]: evm-lean {hexOfWord mine}, " ++
        s!"anvil {hexOfWord v}"]
  return out

/-- Compare ether balances. -/
def compareEth (rpc : Rpc) (accounts : List Address) (after : World) : IO (List String) := do
  if accounts.isEmpty then return []
  let theirs ← rpc.balances accounts.toArray
  let mut out := []
  for h : i in [0:accounts.length] do
    let a := accounts[i]
    let mine := (after.balance a).toNat
    let v := theirs[i]?.getD 0
    if mine != v then
      out := out ++ [s!"balance {hexOfAddress a}: evm-lean {mine}, anvil {v}"]
  return out

/-- Execute one transaction on both sides and compare. Anvil goes first, so that evm-lean
runs in the environment of the block anvil mined (timestamp, number, coinbase, …). -/
def step (rpc : Rpc) (watch : Watch) (w : World) (sender : Address) (to : Option Address)
    (data : ByteArray) (value : Nat) (kind : String) :
    IO (World × Outcome × Observed × List String) := do
  let obs ← rpc.execute Examples.Deployment.chainId sender to data gasLimit value
  let (o, w') ← ofExcept "evm-lean" (execTx Crypto.real obs.env w sender to data gasLimit value)
  let w' := if o.success then watch.corrupt kind w' else w'
  -- The return data of a creation is the deployed code, compared separately.
  let obs := if to.isNone then { obs with output := o.output } else obs
  let diffs := compareOutcome o obs
  let sdiffs ← compareStorage rpc watch.accounts w w' obs.touchedSlots
  let ediffs ← if watch.eth.isEmpty then pure []
    else compareEth rpc (watch.eth ++ [sender]).eraseDups w'
  return (w', o, obs, diffs ++ sdiffs ++ ediffs)

/-- A system deployed on both sides, with its call generator. -/
structure Session where
  /-- Anvil. -/
  rpc : Rpc
  /-- Name in reports. -/
  name : String
  /-- What is compared. -/
  watch : Watch
  /-- The evm-lean world after deployment. -/
  world0 : World
  /-- The anvil snapshot of the same state. -/
  snap : IO.Ref Json
  /-- Statistics. -/
  stats : IO.Ref Stats
  /-- The next call, given the current evm-lean world and recently returned words. -/
  gen : World → Array Word → Gen Call
  /-- Calls per random sequence. -/
  length : Nat
  /-- Print every call. -/
  verbose : Bool := false

/-- Restore the deployed state in anvil (and re-arm the snapshot). -/
def Session.restart (s : Session) : IO Unit := do
  s.rpc.revertTo (← s.snap.get)
  s.snap.set (← s.rpc.snapshot)

def Session.record (s : Session) (c : Call) (ok : Bool) : IO Unit :=
  s.stats.modify fun st =>
    let (n, k) := st.byKind.getD c.kind (0, 0)
    let inc := if ok then 1 else 0
    { st with calls := st.calls + 1, successes := st.successes + inc
              byKind := st.byKind.insert c.kind (n + 1, k + inc) }

def Session.exec (s : Session) (w : World) (c : Call) : IO (World × Outcome × List String) := do
  let (w', o, obs, diffs) ← step s.rpc s.watch w c.sender (some c.to) c.data c.value c.kind
  s.record c (o.success && obs.success)
  if s.verbose then
    IO.println s!"    {c.desc}: {if o.success then "ok" else "revert"} {hexOfBytes o.output}"
  return (w', o, diffs)

/-- Replay fixed calls from the deployed state; the index and differences of the first
mismatch, if any. -/
def Session.replay (s : Session) (calls : Array Call) : IO (Option (Nat × List String)) := do
  s.restart
  let mut w := s.world0
  for h : i in [0:calls.size] do
    let (w', _, diffs) ← s.exec w calls[i]
    unless diffs.isEmpty do return some (i, diffs)
    w := w'
  return none

/-- Words of a return value, for reuse as amounts. -/
def outputWords (b : ByteArray) : Array Word :=
  (Array.range (b.size / 32)).map fun i => Bytes.toWord (b.extract (32 * i) (32 * i + 32))

/-- Generate and run one random sequence. Returns the calls up to the first mismatch and its
differences, if any. -/
def Session.fuzz (s : Session) (seed : UInt64) : IO (Option (Array Call × List String)) := do
  s.restart
  let mut w := s.world0
  let mut g := seed
  let mut recent : Array Word := #[]
  let mut calls : Array Call := #[]
  for _ in [0:s.length] do
    let (c, g') := (s.gen w recent).run g
    g := g'
    calls := calls.push c
    let (w', o, diffs) ← s.exec w c
    unless diffs.isEmpty do return some (calls, diffs)
    w := w'
    let r := recent ++ outputWords o.output
    recent := r.extract (r.size - min r.size 16) r.size
  return none

/-- Greedily remove calls while a mismatch persists. -/
def Session.shrink (s : Session) (calls : Array Call) (diffs : List String) :
    IO (Array Call × List String) := do
  let mut cur := calls
  let mut msgs := diffs
  let mut i := 0
  for _ in [0:calls.size * calls.size + 1] do
    if i ≥ cur.size then break
    let cand := cur.eraseIdxIfInBounds i
    match ← s.replay cand with
    | some (k, d) => cur := cand.extract 0 (k + 1); msgs := d
    | none => i := i + 1
  return (cur, msgs)

/-- Print a mismatch with its minimal reproduction. -/
def Session.report (s : Session) (seq : Nat) (seed : UInt64) (calls : Array Call)
    (diffs : List String) : IO Unit := do
  IO.println (s!"  MISMATCH in {s.name} sequence {seq} (generator state {seed}); " ++
    s!"minimal reproduction from the deployed state ({calls.size} calls):")
  for h : i in [0:calls.size] do
    let c := calls[i]
    IO.println s!"    {i + 1}. {c.desc}"
    IO.println (s!"       from {hexOfAddress c.sender} to {hexOfAddress c.to} value {c.value} " ++
      s!"data {hexOfBytes c.data}")
  IO.println "  differences after the last call:"
  for d in diffs do IO.println s!"    - {d}"

/-- Run fixed calls from the deployed state, comparing after each; the final evm-lean world
and the first mismatch, if any. -/
def Session.runFixed (s : Session) (calls : Array Call) :
    IO (World × Option (Nat × List String)) := do
  s.restart
  let mut w := s.world0
  for h : i in [0:calls.size] do
    let (w', _, diffs) ← s.exec w calls[i]
    unless diffs.isEmpty do return (w', some (i, diffs))
    w := w'
  return (w, none)

/-- Run `n` random sequences (seeds derived from `seed` and `famIdx`), shrinking and
reporting each mismatch; the number of mismatching sequences. -/
def Session.fuzzMany (s : Session) (seed famIdx n : Nat) : IO Nat := do
  let mut found := 0
  for seq in [0:n] do
    (← IO.getStdout).flush
    let g : UInt64 := (seed * 1_000_003 + famIdx * 7_919 + seq).toUInt64
    match ← s.fuzz g with
    | none => pure ()
    | some (calls, diffs) =>
      found := found + 1
      let (calls, diffs) ← s.shrink calls diffs
      s.report seq g calls diffs
  return found

end Examples.Differential
