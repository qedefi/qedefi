import Examples.Differential.Rpc
import Examples.Differential.Local
import Examples.Differential.Gen
import Examples.Deployment

/-!
# `lake exe difftest`: evm-lean vs. anvil on the ERC-4626 targets

```
lake exe difftest [--seed N] [--sequences N] [--length N] [--family solmate|oz|all]
                  [--rpc URL | --port N] [--inject-bug] [--verbose]
```

For each family (Solmate `MockERC20`/`MockERC4626`, OpenZeppelin `ERC20Mock`/`OzVault`):

1. **Deployment.** Both contracts are deployed by running their creation code, in evm-lean
   as a creation message through `Interpreter.processMessageCall` and in anvil as a creation
   transaction, first from a non-canonical deployer (the runtime code must equal
   `runtimeCodeFor` of the new addresses: immutables patched by position) and then from the
   canonical deployer (the code must equal the committed `runtimeCode`). Outcomes and
   storage are compared as below.
2. **Random sequences.** `--sequences` sequences of `--length` calls (`Examples.Differential.Gen`) from
   four actors, each starting from the deployed state (anvil `evm_snapshot`/`evm_revert`).
   After every call the tester compares success, return/revert data, logs, receipt
   `gasUsed`, and storage: every slot either side wrote or holds (see `Examples.Differential.Rpc`).
   Before them, a fixed first-depositor inflation-attack scenario is run and compared.
3. **Shrinking.** On a mismatch the sequence is cut after the failing call and calls are
   removed greedily while the mismatch persists; the minimal sequence is printed with
   calldata.

`--inject-bug` corrupts evm-lean's result of every successful `deposit` (the vault's total
supply is incremented) to check that mismatches are detected and shrunk. The exit code is 0
iff no mismatch was found.

Anvil (Foundry) must be in `PATH` unless `--rpc` points at a running Cancun anvil with chain
id 1, `--auto-impersonate` and a zero base fee.
-/

namespace Examples.Differential

open EvmLean Examples.OpenZeppelin Examples.Solmate EvmLogic EvmLogic.Solidity Examples.Deployment Examples.OpenZeppelin.Contracts Examples.Solmate.Contracts Lean Conformance

/-- Gas limit of every transaction. -/
def gasLimit : Nat := 10_000_000

/-- A deployer different from the canonical one, to exercise immutables patching. -/
def otherDeployer : Address := 0x2000000000000000000000000000000000000002

/-- Command-line configuration. -/
structure Config where
  /-- Base seed. -/
  seed : Nat := 1
  /-- Sequences per family. -/
  sequences : Nat := 25
  /-- Calls per sequence. -/
  length : Nat := 40
  /-- Families to test. -/
  families : List Family := [solmate, openzeppelin]
  /-- Use a running anvil instead of starting one. -/
  rpc : Option String := none
  /-- Port for the anvil started by the tester (`0`: pick one). -/
  port : Nat := 0
  /-- Corrupt evm-lean's `deposit` results (self-test of the tester). -/
  injectBug : Bool := false
  /-- Print every call. -/
  verbose : Bool := false

/-- A decimal command-line argument. -/
def natArg (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .error s!"expected a number, got {s}"

/-- Parse the command line. -/
def parseArgs : Config → List String → Except String Config
  | c, [] => .ok c
  | c, "--seed" :: n :: rest => do parseArgs { c with seed := ← natArg n } rest
  | c, "--sequences" :: n :: rest => do parseArgs { c with sequences := ← natArg n } rest
  | c, "--length" :: n :: rest => do parseArgs { c with length := ← natArg n } rest
  | c, "--port" :: n :: rest => do parseArgs { c with port := ← natArg n } rest
  | c, "--rpc" :: u :: rest => parseArgs { c with rpc := some u } rest
  | c, "--family" :: f :: rest => do
    let fams ← match f with
      | "solmate" => pure [solmate]
      | "oz" => pure [openzeppelin]
      | "all" => pure [solmate, openzeppelin]
      | _ => throw s!"unknown family {f} (solmate, oz, all)"
    parseArgs { c with families := fams } rest
  | c, "--inject-bug" :: rest => parseArgs { c with injectBug := true } rest
  | c, "--verbose" :: rest => parseArgs { c with verbose := true } rest
  | _, a :: _ => throw s!"unknown argument {a}"

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

/-- A family under test, deployed on both sides. -/
structure Session where
  /-- Configuration. -/
  cfg : Config
  /-- Anvil. -/
  rpc : Rpc
  /-- The family. -/
  fam : Family
  /-- The evm-lean world after the canonical deployment. -/
  world0 : World
  /-- The anvil snapshot of the same state. -/
  snap : IO.Ref Json
  /-- Statistics. -/
  stats : IO.Ref Stats

/-! ## Comparison -/

/-- Render a log. -/
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
the call in the asset, the vault or any account anvil wrote, and every slot anvil wrote. -/
def compareStorage (rpc : Rpc) (fam : Family) (before after : World)
    (touched : List (Address × Word)) : IO (List String) := do
  let accounts := touched.map (·.1) ++ [fam.asset, fam.vault]
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

/-- Execute one transaction on both sides and compare. Anvil goes first, so that evm-lean
runs in the environment of the block anvil mined (timestamp, number, coinbase, …). -/
def step (cfg : Config) (rpc : Rpc) (fam : Family) (w : World) (sender : Address)
    (to : Option Address) (data : ByteArray) (kind : String) :
    IO (World × Outcome × Observed × List String) := do
  let obs ← rpc.execute chainId sender to data gasLimit
  let (o, w') ← ofExcept "evm-lean" (execTx Crypto.real obs.env w sender to data gasLimit)
  let w' := if cfg.injectBug && kind == "vault.deposit" && o.success then
      let k : Word := BitVec.ofNat 256 fam.vaultTotalSupply
      w'.sstore fam.vault k (w'.sload fam.vault k + 1)
    else w'
  -- The return data of a creation is the deployed code, compared separately.
  let obs := if to.isNone then { obs with output := o.output } else obs
  let diffs := compareOutcome o obs
  let sdiffs ← compareStorage rpc fam w w' obs.touchedSlots
  return (w', o, obs, diffs ++ sdiffs)

/-! ## Deployment -/

/-- Deploy the family from `deployer` on a fresh chain on both sides and check the deployed
code against `expected` (asset and vault code, given their addresses). Returns the
evm-lean world. -/
def deploy (cfg : Config) (rpc : Rpc) (stats : IO.Ref Stats) (fam : Family) (deployer : Address)
    (expected : Address → Address → ByteArray × ByteArray) : IO World := do
  rpc.reset
  let assetAddr := Interpreter.createAddress Crypto.real.keccak256 deployer 0
  let vaultAddr := Interpreter.createAddress Crypto.real.keccak256 deployer 1
  let fam' := { fam with asset := assetAddr, vault := vaultAddr }
  let (wA, oA, obsA, dA) ← step cfg rpc fam' ∅ deployer none fam.assetInit "deploy"
  let (wV, oV, obsV, dV) ←
    step cfg rpc fam' wA deployer none (fam.vaultInitFor assetAddr) "deploy"
  stats.modify fun st => { st with calls := st.calls + 2 }
  let (expA, expV) := expected assetAddr vaultAddr
  let anvilA ← rpc.code assetAddr
  let anvilV ← rpc.code vaultAddr
  let mut errs := (dA ++ dV).map (s!"deployment from {hexOfAddress deployer}: " ++ ·)
  if !(oA.success && oV.success) then errs := errs ++ ["evm-lean deployment failed"]
  if obsA.created != some assetAddr || obsV.created != some vaultAddr then
    errs := errs ++ ["anvil deployed at unexpected addresses"]
  if wV.code assetAddr != anvilA || wV.code vaultAddr != anvilV then
    errs := errs ++ ["deployed code differs between evm-lean and anvil"]
  if anvilA != expA || anvilV != expV then
    errs := errs ++ ["deployed code differs from the Lean constants (runtimeCode/runtimeCodeFor)"]
  unless errs.isEmpty do fail ("\n".intercalate errs)
  IO.println (s!"  deployed by {hexOfAddress deployer}: asset {hexOfAddress assetAddr} " ++
    s!"({anvilA.size} B), vault {hexOfAddress vaultAddr} ({anvilV.size} B); code, " ++
    s!"storage and gas ({obsA.gasUsed} + {obsV.gasUsed}) agree")
  return wV

/-! ## Sequences -/

/-- Restore the deployed state in anvil (and re-arm the snapshot). -/
def Session.restart (s : Session) : IO Unit := do
  s.rpc.revertTo (← s.snap.get)
  s.snap.set (← s.rpc.snapshot)

/-- Record a call in the statistics. -/
def Session.record (s : Session) (c : Call) (ok : Bool) : IO Unit :=
  s.stats.modify fun st =>
    let (n, k) := st.byKind.getD c.kind (0, 0)
    let inc := if ok then 1 else 0
    { st with calls := st.calls + 1, successes := st.successes + inc
              byKind := st.byKind.insert c.kind (n + 1, k + inc) }

/-- Run a call on both sides and compare. -/
def Session.exec (s : Session) (w : World) (c : Call) : IO (World × Outcome × List String) := do
  let (w', o, obs, diffs) ← step s.cfg s.rpc s.fam w c.sender (some c.to) c.data c.kind
  s.record c (o.success && obs.success)
  if s.cfg.verbose then
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
  for _ in [0:s.cfg.length] do
    let (c, g') := (genCall s.fam w recent).run g
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
  IO.println (s!"  MISMATCH in {s.fam.name} sequence {seq} (generator state {seed}); " ++
    s!"minimal reproduction from the deployed state ({calls.size} calls):")
  for h : i in [0:calls.size] do
    let c := calls[i]
    IO.println s!"    {i + 1}. {c.desc}"
    IO.println s!"       from {hexOfAddress c.sender} to {hexOfAddress c.to} data {hexOfBytes c.data}"
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

/-- The first-depositor inflation (donation) attack: alice deposits 1 wei, donates `10¹⁸`
directly to the vault, bob deposits `2·10¹⁸ - 1`, alice redeems her share. -/
def inflationScenario (f : Family) : Array Call :=
  let alice := actors[0]?.getD 0
  let bob := actors[1]?.getD 0
  let a := f.assetSelectors
  let v := f.vaultSelectors
  let addr (x : Address) : Word × String := (Word.ofAddress x, addrName f x)
  let num (n : Nat) : Word × String := (BitVec.ofNat 256 n, toString n)
  let e18 := 10 ^ 18
  #[mkCall f a alice f.asset "mint(address,uint256)" [addr alice, num (e18 + 1)],
    mkCall f a alice f.asset "approve(address,uint256)" [addr f.vault, num (2 ^ 256 - 1)],
    mkCall f v alice f.vault "deposit(uint256,address)" [num 1, addr alice],
    mkCall f a alice f.asset "transfer(address,uint256)" [addr f.vault, num e18],
    mkCall f a bob f.asset "mint(address,uint256)" [addr bob, num (2 * e18 - 1)],
    mkCall f a bob f.asset "approve(address,uint256)" [addr f.vault, num (2 ^ 256 - 1)],
    mkCall f v bob f.vault "previewDeposit(uint256)" [num (2 * e18 - 1)],
    mkCall f v bob f.vault "deposit(uint256,address)" [num (2 * e18 - 1), addr bob],
    mkCall f v alice f.vault "maxRedeem(address)" [addr alice],
    mkCall f v alice f.vault "redeem(uint256,address,address)" [num 1, addr alice, addr alice],
    mkCall f v bob f.vault "maxWithdraw(address)" [addr bob]]

/-- Test one family. -/
def testFamily (cfg : Config) (rpc : Rpc) (stats : IO.Ref Stats) (famIdx : Nat) (fam : Family) :
    IO Unit := do
  IO.println s!"[{fam.name}]"
  discard <| deploy cfg rpc stats fam otherDeployer fam.codeFor
  let world0 ← deploy cfg rpc stats fam deployer fun _ _ => (fam.assetCode, fam.vaultCode)
  let snap ← IO.mkRef (← rpc.snapshot)
  let s : Session := { cfg, rpc, fam, world0, snap, stats }
  let mut found := 0
  let scenario := inflationScenario fam
  let (w, res) ← s.runFixed scenario
  match res with
  | some (k, diffs) =>
    found := found + 1
    s.report 0 0 (scenario.extract 0 (k + 1)) diffs
  | none =>
    let bal (x : Address) := (balanceIn w fam.asset fam.assetBalances x).toNat
    IO.println (s!"  inflation-attack scenario agrees: alice paid {10 ^ 18 + 1} and ends " ++
      s!"with {bal (actors[0]?.getD 0)}, bob paid {2 * 10 ^ 18 - 1} and holds " ++
      s!"{(balanceIn w fam.vault fam.vaultBalances (actors[1]?.getD 0)).toNat} shares")
  for seq in [0:cfg.sequences] do
    (← IO.getStdout).flush
    let seed : UInt64 := (cfg.seed * 1_000_003 + famIdx * 7_919 + seq).toUInt64
    match ← s.fuzz seed with
    | none => pure ()
    | some (calls, diffs) =>
      found := found + 1
      let (calls, diffs) ← s.shrink calls diffs
      s.report seq seed calls diffs
  stats.modify fun st => { st with mismatches := st.mismatches + found }
  IO.println s!"  {cfg.sequences} sequences × {cfg.length} calls: {found} mismatching sequences"

/-- Run every family against anvil at `rpc`. -/
def runAll (cfg : Config) (rpc : Rpc) (stats : IO.Ref Stats) : IO Unit := do
  let mut i := 0
  for fam in cfg.families do
    testFamily cfg rpc stats i fam
    i := i + 1

end Examples.Differential

open Examples.Differential in
/-- Entry point of `lake exe difftest`. -/
def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs {} args with
    | .ok c => pure c
    | .error e => IO.eprintln e; return 2
  let stats ← IO.mkRef ({} : Stats)
  let start ← IO.monoMsNow
  match cfg.rpc with
  | some url =>
    try runAll cfg { url } stats
    catch e => IO.eprintln s!"error: {e}"; return 2
  | none =>
    let now ← IO.monoMsNow
    let port := if cfg.port = 0 then 30000 + now % 20000 else cfg.port
    let child ← spawnAnvil port Examples.Deployment.chainId
    try runAll cfg { url := s!"http://127.0.0.1:{port}" } stats
    catch e => child.kill; IO.eprintln s!"error: {e}"; return 2
    child.kill
  let st ← stats.get
  let secs := ((← IO.monoMsNow) - start) / 1000
  IO.println (s!"summary: {st.calls} transactions ({st.successes} successful on both sides), " ++
    s!"{st.mismatches} mismatching sequences, {secs} s")
  for (k, (n, ok)) in st.byKind.toList.mergeSort (fun a b => a.1 ≤ b.1) do
    IO.println s!"  {k}: {n} calls, {ok} successful"
  return if st.mismatches = 0 then 0 else 1
