import Snapshot.Sequence

/-!
# The sequence on an anvil fork: recording the node's side

`snapshot fork <dir>` runs the `sequence` of `targets.json` on anvil forked from the RPC at
the snapshot block (cheats with `anvil_setBalance`/`anvil_setCode`/`anvil_setStorageAt`,
time with `evm_setNextBlockTimestamp` + `evm_mine`, blocks 12 s apart otherwise, transactions from impersonated senders at gas price
zero, one block each), then in the interpreter in the environment of each mined block,
fetching from the RPC whatever the interpreter reads and the snapshot lacks (the snapshot is
saved with these reads). The node's state after each transaction is read back from anvil at
that block for every account and slot either side touched (the interpreter's reads, anvil's
`prestateTracer` diff), recorded in `sequence.json`, and compared (`checkSequence`).
-/

namespace Snapshot

open Lean EvmLean Conformance

/-- Start anvil forked from `rpc` at the snapshot block on `port`. The URL reaches anvil
through the environment (an RPC alias in `<dir>/anvil/foundry.toml` expanding
`SNAPSHOT_FORK_URL`): it is never an argument, printed or saved. -/
def spawnAnvil (dir : System.FilePath) (rpc : Rpc) (s : State) (port : Nat) :
    IO (IO.Process.Child { stdin := .null, stdout := .null, stderr := .null }) := do
  let wd := dir / "anvil"
  IO.FS.createDirAll wd
  IO.FS.writeFile (wd / "foundry.toml") "[rpc_endpoints]\nsnapshot = \"${SNAPSHOT_FORK_URL}\"\n"
  let child ← IO.Process.spawn {
    cmd := "anvil", cwd := wd, env := #[("SNAPSHOT_FORK_URL", some rpc.url)]
    args := #["--port", toString port, "--fork-url", "snapshot", "--fork-block-number",
              toString s.block, "--hardfork", s.fork.name.toLower, "--auto-impersonate",
              "--base-fee", "0", "--gas-price", "0", "--silent"]
    stdin := .null, stdout := .null, stderr := .null }
  let a : Rpc := { url := s!"http://127.0.0.1:{port}" }
  for _ in [0:600] do
    try
      if (← a.blockNumber) == s.block then return child
    catch _ => pure ()
    IO.sleep 100
  child.kill
  fail "anvil did not start (is Foundry in PATH, the port free?)"

def hexField (j : Json) (k : String) : Nat := ((getStrField j k >>= parseHexNat).toOption).getD 0

/-- Accounts and slots in a `prestateTracer` diff (`pre` and `post`). -/
def diffTouched (j : Json) : List Address × List (Address × Word) :=
  let accts := ["pre", "post"].flatMap fun side => objList ((j.getObjVal? side).toOption.getD .null)
  let addr (a : String) : Address := ((parseAddress a).toOption).getD 0
  (accts.map (addr ·.1), accts.flatMap fun (a, x) =>
    (objList ((x.getObjVal? "storage").toOption.getD .null)).map fun (k, _) =>
      (addr a, ((parseWord k).toOption).getD 0))

/-- Send `c` to anvil (automine) and collect its block, block environment, outcome, and the
accounts and slots it touched. -/
def anvilTx (a : Rpc) (chainId : Nat) (c : CallSpec) :
    IO (Nat × BlockEnv × TxOutcome × (List Address × List (Address × Word))) := do
  let tx := Json.mkObj [("from", Json.str (hexOfAddress c.sender)),
    ("to", Json.str (hexOfAddress c.target)), ("data", Json.str (hexOfBytes c.data)),
    ("value", Json.str (hexOfNat c.value)), ("gas", Json.str (hexOfNat c.gas)), ("gasPrice", "0x0")]
  let h ← ofExcept "eth_sendTransaction" (jsonStr (← a.call "eth_sendTransaction" (Json.arr #[tx])))
  let mut receipt := Json.null
  for _ in [0:2000] do
    receipt ← a.call "eth_getTransactionReceipt" (Json.arr #[Json.str h])
    if receipt != Json.null then break
    IO.sleep 5
  let n := hexField receipt "blockNumber"
  let rs ← a.batch #[("eth_getBlockByNumber", Json.arr #[blockTag n, Json.bool false]),
    ("debug_traceTransaction", Json.arr #[Json.str h, Json.mkObj [("tracer", "callTracer")]]),
    ("debug_traceTransaction", Json.arr #[Json.str h, Json.mkObj [("tracer", "prestateTracer"),
      ("tracerConfig", Json.mkObj [("diffMode", true)])]])]
  let (block, call, diff) := (rs[0]!, rs[1]!, rs[2]!)
  let word (j : Json) (k : String) : Word := ((getStrField j k >>= parseWord).toOption).getD 0
  let env : BlockEnv := {
    chainId, coinbase := ((getStrField block "miner" >>= parseAddress).toOption).getD 0,
    number := n, timestamp := hexField block "timestamp", gasLimit := hexField block "gasLimit",
    baseFee := hexField block "baseFeePerGas", prevRandao := word block "mixHash",
    excessBlobGas := hexField block "excessBlobGas",
    parentBeaconBlockRoot := word block "parentBeaconBlockRoot",
    -- `BLOCKHASH(number - 1)`; older hashes are not provided.
    blockHashes := [word block "parentHash"] }
  let logs ← ofExcept "receipt logs" ((jsonArr ((receipt.getObjVal? "logs").toOption.getD .null)).mapM decodeLog)
  let output := ((getStrField call "output" >>= parseHexBytes).toOption).getD .empty
  return (n, env, { success := hexField receipt "status" == 1, output, logs,
                    gasUsed := hexField receipt "gasUsed" }, diffTouched diff)

/-- Run the sequence on anvil and in the interpreter, record the node's side in
`sequence.json`, save the snapshot extended with the sequence's reads, and compare. Uses the
anvil at `anvilUrl` if given (it must be forked at the snapshot block and fresh), else spawns
one on `port`. Returns the number of differing steps. -/
def forkSequence (dir : System.FilePath) (rpc : Rpc) (anvilUrl : Option String) (port : Nat) :
    IO Nat := do
  let s ← State.load dir
  let steps ← loadSequence dir
  if steps.isEmpty then fail "targets.json has no sequence"
  let child ← match anvilUrl with
    | some _ => pure none
    | none => some <$> spawnAnvil dir rpc s port
  let a : Rpc := { url := anvilUrl.getD s!"http://127.0.0.1:{port}" }
  try
    -- Blocks 12 s apart (anvil otherwise follows the wall clock: runs would differ).
    discard <| a.call "anvil_setBlockTimestampInterval" (Json.arr #[toJson 12])
    -- The node.
    let mut obs : Array Observed := #[]
    let mut touched : Array (List Address × List (Address × Word)) := #[]
    for st in steps do
      let call (m : String) (ps : Array Json) : IO Unit := discard <| a.call m (Json.arr ps)
      match st.action with
      | .tx c =>
        let (n, env, o, t) ← anvilTx a s.chainId c
        IO.println s!"anvil: {st.label}: {if o.success then "success" else "revert"}, gas {o.gasUsed}"
        obs := obs.push { label := st.label, block := n, env, outcome := some o }
        touched := touched.push t
      | act =>
        match act with
        | .setBalance as v => for x in as do call "anvil_setBalance" #[Json.str (hexOfAddress x), Json.str (hexOfNat v)]
        | .setCode x code => call "anvil_setCode" #[Json.str (hexOfAddress x), Json.str (hexOfBytes code)]
        | .setStorage x k v =>
          call "anvil_setStorageAt" #[Json.str (hexOfAddress x), Json.str (hexOfWord k), Json.str (hexOfWord v)]
        | .increaseTime t =>
          -- `evm_increaseTime` is overridden by the block timestamp interval: set the time.
          let now := hexField (← a.call "eth_getBlockByNumber" (Json.arr #["latest", Json.bool false])) "timestamp"
          call "evm_setNextBlockTimestamp" #[toJson (now + t)]; call "evm_mine" #[]
        | .tx _ => pure ()
        obs := obs.push { label := st.label }
        touched := touched.push ([], [])
    -- The interpreter, fetching what it reads.
    let envs := obs.map (·.env)
    let (s, rounds) ← discoverSequence rpc s steps envs
    s.save dir
    let runs ← ofExcept "sequence" (runSequence s steps envs)
    -- The node's state after each transaction where either side touched it.
    for i in [0:obs.size] do
      let o := obs[i]!
      if o.outcome.isNone then continue
      let some r := runs[i]? | continue
      let (ta, ts) := touched[i]!
      let accts := (r.reads.accounts.toList ++ ta).eraseDups.toArray
      let slots := (r.reads.slotList ++ ts).eraseDups.toArray
      let ra ← a.accounts o.block accts
      let vs ← a.storage o.block slots
      obs := obs.set! i { o with
        accounts := (accts.zip ra).map fun (x, y) => (x, y.balance, y.nonce)
        slots := (slots.zip vs).map fun ((x, k), v) => (x, k, v) }
    saveObserved dir obs
    IO.println s!"sequence: {steps.size} steps, {rounds} discovery rounds; snapshot now \
      {s.accounts.size} accounts, {s.slotCount} slots"
    let summary ← ofExcept "meta.json" (Json.parse (← IO.FS.readFile (dir / "meta.json")))
    let summary := summary.setObjVal! "accounts" (toJson s.accounts.size)
      |>.setObjVal! "slots" (toJson s.slotCount)
      |>.setObjVal! "sequence" (Json.mkObj [("steps", toJson steps.size),
        ("discoveryRounds", toJson rounds)])
    IO.FS.writeFile (dir / "meta.json") (summary.pretty ++ "\n")
    checkSequence dir s true
  finally
    if let some c := child then c.kill

end Snapshot
