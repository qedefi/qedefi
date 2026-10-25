import Difftest.Rpc
import Difftest.Local
import Difftest.Gen

/-!
# Comparing evm-lean with anvil, call by call

A `Session` is a deployed system (a vault family or a token) on both sides, with a call
generator. Every call runs on anvil first, then in evm-lean in the environment of the block
anvil mined; status, output, logs, `gasUsed`, the storage of the watched accounts (and of
every account anvil wrote) and, optionally, ether balances are compared. Random sequences
are generated, run and shrunk to a minimal mismatch.
-/

namespace Difftest

open Lean EvmLean Conformance

/-- Gas limit of every transaction unless lowered (`Call.gas`). -/
def gasLimit : Nat := defaultGas

/-- Statistics of one operation. -/
structure KindStats where
  /-- Calls. -/
  calls : Nat := 0
  /-- Calls that succeeded on both sides. -/
  ok : Nat := 0
  /-- Failures that consumed the whole gas limit (out of gas, `INVALID`, other exceptional
  halts), in evm-lean. -/
  halts : Nat := 0
  /-- Successful calls returning exactly one zero word (`false`, or a zero view). -/
  zeroReturns : Nat := 0
  deriving Inhabited

/-- Run statistics. -/
structure Stats where
  /-- Calls executed (including deployments and replays while shrinking). -/
  calls : Nat := 0
  /-- Calls that succeeded on both sides. -/
  successes : Nat := 0
  /-- Failures that consumed the whole gas limit. -/
  halts : Nat := 0
  /-- Per operation. -/
  byKind : Std.HashMap String KindStats := {}
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

/-- A log, for reports. -/
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
    (data : ByteArray) (value : Nat) (kind : String) (gas : Nat := gasLimit) :
    IO (World × Outcome × Observed × List String) := do
  let obs ← rpc.execute Examples.Deployment.chainId sender to data gas value
  let (o, w') ← ofExcept "evm-lean" (execTx Crypto.real obs.env w sender to data gas value)
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
  /-- Percentage of random calls whose gas limit is lowered (`lowerGas`). -/
  lowGasPct : Nat := 0

/-- Restore the deployed state in anvil (and re-arm the snapshot). -/
def Session.restart (s : Session) : IO Unit := do
  s.rpc.revertTo (← s.snap.get)
  s.snap.set (← s.rpc.snapshot)

/-- Count a call in the statistics. -/
def Session.record (s : Session) (c : Call) (ok : Bool) (o : Outcome) : IO Unit :=
  s.stats.modify fun st =>
    let ks := st.byKind.getD c.kind {}
    let inc := if ok then 1 else 0
    let halt := if !o.success && o.gasUsed = c.gas then 1 else 0
    let zeroRet := if o.success && o.output = Bytes.ofWord 0 then 1 else 0
    { st with calls := st.calls + 1, successes := st.successes + inc, halts := st.halts + halt
              byKind := st.byKind.insert c.kind
                { calls := ks.calls + 1, ok := ks.ok + inc, halts := ks.halts + halt
                  zeroReturns := ks.zeroReturns + zeroRet } }

/-- Execute a call on both sides and compare. -/
def Session.exec (s : Session) (w : World) (c : Call) : IO (World × Outcome × List String) := do
  let (w', o, obs, diffs) ← step s.rpc s.watch w c.sender (some c.to) c.data c.value c.kind c.gas
  s.record c (o.success && obs.success) o
  if s.verbose then
    IO.println s!"    {c.desc} (gas {c.gas}): {if o.success then "ok" else "revert"} {hexOfBytes o.output}"
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

/-- With probability `pct` %, lower the gas limit of the next call to provoke out-of-gas
failures at every depth: either repeat the previous call with a limit around the gas it used
(`gasUsed + δ`, δ from −2 to a few thousand: refunds, the 63/64 rule and stipends make the
needed limit differ from `gasUsed`), or send the new call with its intrinsic gas plus a small
random amount. Never below the intrinsic gas (anvil rejects such transactions); the previous
call is repeated only if its sender can still pay its value in `w`. Lowered calls
get the kind suffix `@lowgas` (reports show each call's gas limit). -/
def lowerGas (pct : Nat) (w : World) (prev : Option (Call × Nat)) (c : Call) : Gen Call := do
  if (← below 100) ≥ pct then return c
  let (base, target) ← match prev with
    | some (p, used) =>
      if (← below 2) = 0 && p.value ≤ (w.balance p.sender).toNat then
        let δ : Int ← match ← below 4 with
          | 0 => pure ((← pick #[-2, -1, 0, 1, 2]) : Int)
          | 1 => pure ((← pick #[100, 2300, 2301, 4800, 5000, 9000, 20000]) : Int)
          | 2 => pure ((← below 5000 : Nat) : Int)
          | _ => pure (((← below 40000 : Nat) : Int) - 2000)
        pure (p, ((used : Int) + δ).toNat)
      else pure (c, intrinsicGasOf (some c.to) c.data + (← below 60000))
    | none => pure (c, intrinsicGasOf (some c.to) c.data + (← below 60000))
  let gas := max target (intrinsicGasOf (some base.to) base.data)
  let kind := if base.kind.endsWith "@lowgas" then base.kind else base.kind ++ "@lowgas"
  return { base with gas, kind }

/-- Generate and run one random sequence. Returns the calls up to the first mismatch and its
differences, if any. -/
def Session.fuzz (s : Session) (seed : UInt64) : IO (Option (Array Call × List String)) := do
  s.restart
  let mut w := s.world0
  let mut g := seed
  let mut recent : Array Word := #[]
  let mut calls : Array Call := #[]
  let mut prev : Option (Call × Nat) := none
  for _ in [0:s.length] do
    let (c, g') := (s.gen w recent).run g
    let (c, g') := (lowerGas s.lowGasPct w prev c).run g'
    g := g'
    calls := calls.push c
    let (w', o, diffs) ← s.exec w c
    unless diffs.isEmpty do return some (calls, diffs)
    prev := some (c, o.gasUsed)
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
      s!"gas {c.gas} data {hexOfBytes c.data}")
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

end Difftest
