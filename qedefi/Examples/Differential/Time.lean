import Examples.Differential.Session
import Examples.Time.Contracts.VestingWalletData

/-!
# Differential testing across blocks: OpenZeppelin `VestingWallet`

The wallet is deployed on both sides with a schedule starting shortly after genesis. Random
sequences mix deposits (plain ether transfers to `receive()`), `release()` by anyone, the views
(`releasable()`, `released()`, `vestedAmount(uint64)` at times around the schedule and beyond
`2⁶⁴`), a non-payable call with value, and **time jumps** (`evm_increaseTime`): every
transaction is mined in its own block, and evm-lean runs it in the environment of that block,
so the comparison covers `TIMESTAMP` advancing across blocks. Status, output, logs, `gasUsed`,
the wallet's storage and the ether balances of the wallet and the actors are compared after
every call. A fixed scenario releases before the start, in the middle, after more deposits
and after the end, and checks that everything was released.
-/

namespace Examples.Differential.Time

open Lean EvmLean EvmLogic Conformance Examples.Deployment Examples.Differential
open Examples.Time.Contracts

/-- Seconds between genesis and the start of the schedule. -/
def startDelay : Nat := 600

/-- The schedule's duration. -/
def duration : Nat := 3600

/-- The wallet's address (deployer nonce 0 on a fresh chain). -/
def walletAddr : Address := Interpreter.createAddress Crypto.real.keccak256 deployer 0

/-- Ether given to each actor. -/
def funding : Nat := 10 ^ 21

/-- The latest block's timestamp on anvil. -/
def latestTimestamp (rpc : Rpc) : IO Nat := do
  let b ← rpc.call "eth_getBlockByNumber" (Json.arr #["latest", false])
  return natField b "timestamp"

/-- An actor's name. -/
def actorName (a : Address) : String :=
  match actors.toList.idxOf? a with
  | some 0 => "alice"
  | some 1 => "bob"
  | some 2 => "carol"
  | some 3 => "dave"
  | _ => hexOfAddress a

/-- A call to the wallet. -/
def walletCall (sender : Address) (sel : UInt32) (args : List Word) (desc kind : String)
    (value : Nat := 0) : Call :=
  { sender, to := walletAddr, data := calldata sel args, desc := s!"{actorName sender} → {desc}",
    kind, value }

/-- A deposit: a plain ether transfer (empty calldata, `receive()`). -/
def depositCall (sender : Address) (v : Nat) : Call :=
  { sender, to := walletAddr, data := .empty, desc := s!"{actorName sender} → wallet ⟵ {v} wei",
    kind := "wallet.deposit", value := v }

/-- One step of a sequence: a transaction, or a jump in time (anvil only; the next block's
timestamp moves). -/
inductive Op where
  /-- A transaction. -/
  | tx (c : Call)
  /-- `evm_increaseTime` by this many seconds. -/
  | warp (secs : Nat)
  deriving Inhabited

/-- A random step, with the schedule starting at `start`. -/
def genOp (start : Nat) : Gen Op := do
  let sender ← pick actors
  match ← below 10 with
  | 0 | 1 =>
    let v ← match ← below 3 with
      | 0 => pure ((← below 1000) + 1)
      | 1 => pure ((← below (10 ^ 18)) + 1)
      | _ => pure 0
    return .tx (depositCall sender v)
  | 2 | 3 => return .tx (walletCall sender 0x86d1a69f [] "wallet.release()" "wallet.release")
  | 4 => return .tx (walletCall sender 0xfbccedae [] "wallet.releasable()" "wallet.releasable")
  | 5 => return .tx (walletCall sender 0x96132521 [] "wallet.released()" "wallet.released")
  | 6 =>
    let t ← match ← below 4 with
      | 0 => pure (start + (← below (duration + 1)))
      | 1 => pure (start - (← below 100))
      | 2 => pure (start + duration + (← below 1000))
      | _ => pure (2 ^ 64 + (← below 10))
    return .tx (walletCall sender 0x0a17b06b [BitVec.ofNat 256 t] s!"wallet.vestedAmount({t})"
      "wallet.vestedAmount")
  | 7 => return .tx (walletCall sender 0x86d1a69f [] "wallet.release() with value"
      "wallet.release+value" (value := 1))
  | _ => return .warp ((← below 600) + 1)

/-- Run one step on both sides; differences, if any. -/
def runOp (rpc : Rpc) (stats : IO.Ref Stats) (verbose : Bool) (w : World) (op : Op) :
    IO (World × List String) := do
  match op with
  | .warp s =>
    discard <| rpc.call "evm_increaseTime" (Json.arr #[toJson s])
    if verbose then IO.println s!"    +{s} s"
    return (w, [])
  | .tx c =>
    let watch : Watch := { accounts := [walletAddr], eth := walletAddr :: actors.toList }
    let (w', o, obs, diffs) ← step rpc watch w c.sender (some c.to) c.data c.value c.kind c.gas
    stats.modify fun st =>
      let ks := st.byKind.getD c.kind {}
      let ok := if o.success && obs.success then 1 else 0
      { st with calls := st.calls + 1, successes := st.successes + ok
                byKind := st.byKind.insert c.kind { ks with calls := ks.calls + 1, ok := ks.ok + ok } }
    if verbose then
      IO.println (s!"    [t={obs.env.timestamp}] {c.desc}: " ++
        s!"{if o.success then "ok" else "revert"} {hexOfBytes o.output}")
    return (w', diffs)

/-- The descriptions of steps, for reports. -/
def opDesc : Op → String
  | .warp s => s!"+{s} s"
  | .tx c => c.desc

/-- Deploy the wallet on a fresh chain on both sides (beneficiary alice, start
`now + startDelay`, `duration`) and fund the actors. The evm-lean world and the start. -/
def setup (rpc : Rpc) (stats : IO.Ref Stats) : IO (World × Nat) := do
  rpc.reset
  let mut w : World := ∅
  for a in actors do
    rpc.setBalance a funding
    w := w.setBalance a (BitVec.ofNat 256 funding)
  let start := (← latestTimestamp rpc) + startDelay
  let args := Bytes.ofWord (Word.ofAddress (actors[0]?.getD 0)) ++
    Bytes.ofWord (BitVec.ofNat 256 start) ++ Bytes.ofWord (BitVec.ofNat 256 duration)
  let (w', o, obs, d) ← step rpc { accounts := [walletAddr] } w deployer none
    (VestingWallet.creationCode ++ args) 0 "deploy"
  stats.modify fun st => { st with calls := st.calls + 1 }
  let mut errs := d.map ("deployment: " ++ ·)
  if !o.success then errs := errs ++ ["evm-lean deployment failed"]
  if obs.created != some walletAddr then errs := errs ++ ["anvil deployed at an unexpected address"]
  let theirs ← rpc.code walletAddr
  if w'.code walletAddr != theirs then errs := errs ++ ["code differs between evm-lean and anvil"]
  unless errs.isEmpty do fail ("\n".intercalate errs)
  IO.println (s!"  deployed at {hexOfAddress walletAddr} ({theirs.size} B), beneficiary alice, " ++
    s!"start {start}, duration {duration} s; code and storage agree")
  return (w', start)

/-- Run steps from the deployed state; the final world and the first mismatch. -/
def runSeq (rpc : Rpc) (stats : IO.Ref Stats) (verbose : Bool) (w0 : World) (ops : Array Op) :
    IO (World × Option (Nat × List String)) := do
  let mut w := w0
  for h : i in [0:ops.size] do
    let (w', diffs) ← runOp rpc stats verbose w ops[i]
    unless diffs.isEmpty do return (w', some (i, diffs))
    w := w'
  return (w, none)

/-- The fixed scenario: deposit, release before the start (nothing), half-way, deposit more,
release after the end (everything). -/
def scenario : Array Op :=
  let alice := actors[0]?.getD 0
  let bob := actors[1]?.getD 0
  let rel (s : Address) := Op.tx (walletCall s 0x86d1a69f [] "wallet.release()" "wallet.release")
  #[.tx (depositCall bob (10 ^ 18)), rel bob, .warp (startDelay + duration / 2), rel alice,
    .tx (walletCall bob 0xfbccedae [] "wallet.releasable()" "wallet.releasable"),
    .tx (depositCall bob (3 * 10 ^ 17)), .warp duration, rel bob,
    .tx (walletCall alice 0x96132521 [] "wallet.released()" "wallet.released")]

/-- Test the wallet: the fixed scenario and `sequences` random sequences of `length` steps.
The number of mismatching sequences. -/
def testVesting (rpc : Rpc) (stats : IO.Ref Stats) (seed sequences length : Nat)
    (verbose : Bool) : IO Nat := do
  IO.println "[vesting]"
  let (w0, start) ← setup rpc stats
  let mut snap ← rpc.snapshot
  let mut found := 0
  let (w, res) ← runSeq rpc stats verbose w0 scenario
  rpc.revertTo snap
  snap ← rpc.snapshot
  match res with
  | some (k, diffs) =>
    found := found + 1
    IO.println s!"  MISMATCH in the fixed scenario at step {k + 1} ({opDesc (scenario[k]?.getD default)}):"
    for d in diffs do IO.println s!"    - {d}"
  | none =>
    let released := (w.sload walletAddr 1#256).toNat
    let left := (w.balance walletAddr).toNat
    IO.println (s!"  fixed scenario agrees ({scenario.size} steps): released {released} wei, " ++
      s!"{left} wei left after the end")
    if left != 0 || released != 13 * 10 ^ 17 then
      found := found + 1
      IO.println "  UNEXPECTED: everything should have been released after the end"
  for seq in [0:sequences] do
    (← IO.getStdout).flush
    rpc.revertTo snap
    snap ← rpc.snapshot
    let g : UInt64 := (seed * 1_000_003 + 77_777 + seq).toUInt64
    let ops := (List.range length |>.mapM fun _ => genOp start).run' g |>.toArray
    let (_, res) ← runSeq rpc stats verbose w0 ops
    if let some (k, diffs) := res then
      found := found + 1
      IO.println s!"  MISMATCH in sequence {seq} at step {k + 1}; steps:"
      for h : i in [0:k + 1] do
        if h' : i < ops.size then IO.println s!"    {i + 1}. {opDesc ops[i]}"
      for d in diffs do IO.println s!"    - {d}"
  stats.modify fun st => { st with mismatches := st.mismatches + found }
  IO.println s!"  {sequences} sequences × {length} steps: {found} mismatching sequences"
  return found

/-- Take the `vesting` family out of the command line (the other families are parsed as
before): the remaining arguments, whether to test the wallet (`vesting` or `all`), and whether
it was the only family requested. -/
def stripVesting : List String → List String × Bool × Bool
  | "--family" :: f :: rest =>
    let names := f.splitOn ","
    let others := names.filter (· != "vesting")
    let vest := names.contains "vesting" || names.contains "all"
    let (rest', v, o) := stripVesting rest
    if others.isEmpty then (rest', vest || v, true || o)
    else ("--family" :: ",".intercalate others :: rest', vest || v, o)
  | a :: rest =>
    let (rest', v, o) := stripVesting rest
    (a :: rest', v, o)
  | [] => ([], false, false)

end Examples.Differential.Time
