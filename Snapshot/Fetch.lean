import Snapshot.Run
import Snapshot.Sources

/-!
# Fetching a snapshot

Input: `<dir>/targets.json`, written by hand:
```
{ "name": "StrataUSDe", "chainId": 1,
  "block": 24000000,                      -- optional: default the latest block minus 3
  "fork": "Osaka",                        -- optional on Ethereum mainnet (from the timestamp)
  "sender": "0x…",                        -- optional: caller of the seed calls
  "autoViews": true,                      -- optional: seed every argument-free view
  "sourceClosure": true,                  -- optional: sources of every contract read, not
                                          --   only of the targets and their implementations
  "contracts": [{"label": "srUSDe", "address": "0x…"}, …],
  "calls": [{"label": "…", "to": "0x…", "data": "0x…", "from": "0x…", "value": "0x0",
             "gas": 30000000}, …] }
```

The block is pinned once; every read is made at it. The state is found without `debug_*`
tracing: the seed calls (the given `calls`, plus each argument-free view of each target)
run in the Lean interpreter on the state fetched so far, `runObserved` records what they
read, the reads the snapshot does not determine are fetched with plain `eth_get*` requests,
and this repeats until the runs read nothing new. The snapshot is then complete for the
seeds by construction: replaying them reads only fetched state (`snapshot check` verifies
this, and compares each result with the node's `eth_call`).

Output: `state.json` and `code/` (`Snapshot.State`), `calls.json` (`Snapshot.Run`),
`contracts/<address>/` (`Snapshot.Sources`), and `meta.json` (summary; never the RPC URL).
-/

namespace Snapshot

open Lean EvmLean Conformance

structure Target where
  label : String
  address : Address

structure Targets where
  name : String
  chainId : Nat
  block : Option Nat := none
  fork : Option Fork := none
  sender : Address
  autoViews : Bool := true
  sourceClosure : Bool := true
  contracts : Array Target
  calls : Array CallSpec

/-- Default caller of seed calls: an address without code or funds. -/
def defaultSender : Address := 0x5ee05ee05ee05ee05ee05ee05ee05ee05ee05ee0

def jsonArr (j : Json) : Array Json :=
  match j.getArr? with
  | .ok a => a
  | .error _ => #[]

def Targets.decode (j : Json) : Except String Targets := do
  let sender ← match j.getObjValAs? String "sender" with
    | .ok s => parseAddress s
    | .error _ => pure defaultSender
  let fork ← match j.getObjValAs? String "fork" with
    | .ok f => match Fork.ofName? f with
      | some f => pure (some f)
      | none => throw s!"unknown fork {f} (Cancun, Prague, Osaka)"
    | .error _ => pure none
  let contracts ← (jsonArr ((j.getObjVal? "contracts").toOption.getD .null)).mapM fun c => do
    let address ← parseAddress (← getStrField c "address")
    pure { label := (c.getObjValAs? String "label").toOption.getD (hexOfAddress address), address }
  let calls ← (jsonArr ((j.getObjVal? "calls").toOption.getD .null)).mapM (CallSpec.decode · sender)
  return { name := ← getStrField j "name", chainId := ← getNatField j "chainId",
           block := (j.getObjValAs? Nat "block").toOption, fork, sender,
           autoViews := (j.getObjValAs? Bool "autoViews").toOption.getD true,
           sourceClosure := (j.getObjValAs? Bool "sourceClosure").toOption.getD true,
           contracts, calls }

/-! ## Proxies -/

/-- EIP-1967 implementation and beacon slots, and the older ZeppelinOS implementation slot. -/
def eip1967Impl : Word := 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc
def eip1967Beacon : Word := 0xa3f0ad74e5423aebfd80d3ef4346578335a9a72aeaee59ff6cb3582b35133d50
def eip1967Admin : Word := 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103
def zosImpl : Word := 0x7050c9e0f4ca769c69bd3a8ef740bc37934f8e2c036e5a723fd8ee048ed3f8c3
def proxySlots : List Word := [eip1967Impl, eip1967Beacon, eip1967Admin, zosImpl]

/-- The EIP-7702 delegate of an account whose code is a delegation designator. -/
def delegateOf? (code : ByteArray) : Option Address :=
  if code.size = 23 && code[0]! = 0xef && code[1]! = 0x01 && code[2]! = 0x00 then
    some (BitVec.ofNat 160 (Bytes.toNat (code.extract 3 23)))
  else none

/-! ## Fetching into a state -/

/-- Fetch the given accounts (and the delegates of delegated ones), slots and block hashes at
the snapshot block. Accounts and slots already present are not fetched again. -/
def fetchInto (r : Rpc) (s : State) (accounts : List Address) (slots : List (Address × Word))
    (blocks : List Nat) : IO State := do
  let mut s := s
  let mut todo := (accounts ++ slots.map (·.1)).eraseDups.filter (!s.accounts.contains ·)
  while !todo.isEmpty do
    let fetched ← r.accounts s.block todo.toArray
    for (a, ra) in todo.zip fetched.toList do
      let st : AccountState := { nonce := ra.nonce, balance := ra.balance, code := ra.code }
      s := { s with accounts := s.accounts.insert a st }
    todo := (fetched.toList.filterMap (delegateOf? ·.code)).eraseDups.filter (!s.accounts.contains ·)
  let slots := slots.eraseDups.filter fun (a, k) =>
    !((s.accounts[a]?.map (·.storage.contains k)).getD false)
  let values ← r.storage s.block slots.toArray
  for ((a, k), v) in slots.zip values.toList do
    let upd (st : AccountState) : AccountState := { st with storage := st.storage.insert k v }
    s := { s with accounts := s.accounts.modify a upd }
  let blocks := blocks.eraseDups.filter (!s.blockHashes.contains ·)
  let hashes ← r.batch (blocks.toArray.map fun n =>
    ("eth_getBlockByNumber", Json.arr #[blockTag n, Json.bool false]))
  for (n, h) in blocks.zip hashes.toList do
    let w ← ofExcept s!"block {n}" (getStrField h "hash" >>= parseWord)
    s := { s with blockHashes := s.blockHashes.insert n w }
  return s

/-- The slots of the snapshot, over all accounts. -/
def State.slotCount (s : State) : Nat := s.accounts.foldl (fun n _ st => n + st.storage.size) 0

/-- Run every seed on the current state, fetch what they read and the state does not
determine, and repeat until nothing is missing. Returns the state and the rounds taken. -/
def discover (r : Rpc) (s : State) (seeds : Array CallSpec) (maxRounds : Nat := 64) :
    IO (State × Nat) := do
  let mut s := s
  for round in [1:maxRounds + 1] do
    let world := s.world
    let mut acc : Accesses := {}
    for c in seeds do
      match simulate s world c with
      | .ok (_, a) => acc := acc.union a
      | .error e => IO.eprintln s!"  {c.label}: {e}"
    let miss := s.missing acc
    if miss.isEmpty then return (s, round)
    IO.println s!"round {round}: fetching {miss.accounts.size} accounts, \
      {miss.slotList.length} slots, {miss.blockNumbers.size} block hashes"
    s ← fetchInto r s miss.accounts.toList miss.slotList miss.blockNumbers.toList
  fail s!"state still incomplete after {maxRounds} rounds"

/-! ## The whole fetch -/

/-- The host of an RPC URL (what `meta.json` records instead of the URL). -/
def urlHost (url : String) : String :=
  let rest := match url.splitOn "://" with
    | [_, r] => r
    | _ => url
  (rest.splitOn "/").headD ""

def word0 (b : ByteArray) : Word := Bytes.toWord (b.extract 0 32)

/-- The implementation behind a proxy target, from its EIP-1967 or ZeppelinOS slot, or from
its beacon (`implementation()` called at the snapshot block). -/
def implementationOf? (r : Rpc) (s : State) (a : Address) : IO (Option Address) := do
  let some st := s.accounts[a]? | return none
  let slot (k : Word) : Word := st.storage.getD k 0
  if slot eip1967Impl != 0 then return some (Word.toAddress (slot eip1967Impl))
  if slot zosImpl != 0 then return some (Word.toAddress (slot zosImpl))
  if slot eip1967Beacon != 0 then
    let beacon := Word.toAddress (slot eip1967Beacon)
    let res ← r.ethCalls s.block #[{ sender := defaultSender, target := beacon,
                                      data := selector "implementation()" }]
    if let some res := res[0]? then
      if res.success && res.output.size ≥ 32 then return some (Word.toAddress (word0 res.output))
  return none

/-- Fetch and save the verified sources of `a`, if it has code and they exist. -/
def saveSources (dir : System.FilePath) (s : State) (labels : Std.HashMap Address String)
    (a : Address) : IO (Option Verified) := do
  let some st := s.accounts[a]? | return none
  if st.code.size = 0 then return none
  let some v ← verifiedSources? s.chainId a | return none
  v.save dir a (codeName st.code) (labels.getD a "")
  return some v

def fetchSnapshot (dir : System.FilePath) (rpc : Rpc) : IO Unit := do
  let t ← ofExcept "targets.json" (Targets.decode
    (← ofExcept "targets.json" (Json.parse (← IO.FS.readFile (dir / "targets.json")))))
  let chainId ← rpc.chainId
  if chainId != t.chainId then fail s!"the RPC serves chain {chainId}, targets.json says {t.chainId}"
  let block ← match t.block with
    | some b => pure b
    | none => do pure ((← rpc.blockNumber) - 3)  -- load-balanced nodes lag behind the head
  let header ← rpc.block block
  let hnat (k : String) : IO Nat := ofExcept s!"block {block}" (getStrField header k >>= parseHexNat)
  let hnatD (k : String) : Nat := ((getStrField header k >>= parseHexNat).toOption).getD 0
  let hword (k : String) : IO Word := do
    match header.getObjValAs? String k with
    | .ok v => ofExcept s!"block {block}" (parseWord v)
    | .error _ => pure 0
  let timestamp ← hnat "timestamp"
  let fork ← match t.fork, forkAt? chainId timestamp with
    | some f, _ => pure f
    | none, some f => pure f
    | none, none => fail s!"no fork schedule for chain {chainId}: set \"fork\" in targets.json"
  let env : BlockEnv := {
    chainId, coinbase := ← ofExcept "miner" (getStrField header "miner" >>= parseAddress),
    number := block, timestamp, gasLimit := ← hnat "gasLimit",
    baseFee := hnatD "baseFeePerGas",
    prevRandao := ← hword "mixHash",
    excessBlobGas := hnatD "excessBlobGas",
    parentBeaconBlockRoot := ← hword "parentBeaconBlockRoot" }
  IO.println s!"{t.name}: chain {chainId}, block {block}, {fork.name}"
  let mut s : State := { chainId, block, blockHash := ← hword "hash", fork, env }
  -- Targets, their proxy slots, their implementations.
  let targets := t.contracts.toList.map (·.address)
  s ← fetchInto rpc s (t.sender :: targets) (targets.flatMap fun a => proxySlots.map (a, ·)) []
  let mut labels : Std.HashMap Address String := {}
  let mut impls : Array (Target × Address) := #[]
  for c in t.contracts do
    labels := labels.insert c.address c.label
    if let some i ← implementationOf? rpc s c.address then
      impls := impls.push (c, i)
      labels := labels.insert i s!"{c.label} (implementation)"
  s ← fetchInto rpc s (impls.toList.map (·.2)) [] []
  -- Sources and ABIs of the targets and implementations.
  let mut abis : Std.HashMap Address Json := {}
  let mut verified : Array (Address × String × Verified) := #[]
  for a in (targets ++ impls.toList.map (·.2)).eraseDups do
    match ← saveSources dir s labels a with
    | some v => abis := abis.insert a v.abi; verified := verified.push (a, labels.getD a "", v)
    | none => IO.println s!"  {labels.getD a (hexOfAddress a)}: no verified source"
  -- Seeds.
  let mut seeds := t.calls
  if t.autoViews then
    for c in t.contracts do
      let implAbi := (impls.find? (·.1.address == c.address)).bind fun (_, i) => abis[i]?
      let sigs := ((abis[c.address]?.map argFreeViews).getD #[] ++
        (implAbi.map argFreeViews).getD #[]).toList.eraseDups
      for sig in sigs do
        seeds := seeds.push { label := s!"{c.label}.{sig}", sender := t.sender,
                              target := c.address, data := selector sig }
  IO.println s!"{seeds.size} seed calls"
  let (s', rounds) ← discover rpc s seeds
  s := s'
  -- Sources of every other contract the seeds reached.
  if t.sourceClosure then
    let done := verified.map (·.1)
    for (a, st) in s.accounts.toList do
      if st.code.size > 0 && !done.contains a && !targets.contains a then
        if let some v ← saveSources dir s labels a then verified := verified.push (a, labels.getD a "", v)
  -- The node's results, the snapshot, the summary.
  let results ← rpc.ethCalls block seeds
  let calls := (seeds.zip results).map fun (spec, rpc) => { spec, rpc : RecordedCall }
  s.save dir
  saveCalls dir calls
  let codes := (s.accounts.toList.filterMap fun (_, st) =>
    if st.code.size > 0 then some (codeName st.code) else none).eraseDups
  IO.FS.writeFile (dir / "meta.json") ((Json.mkObj [
    ("name", Json.str t.name), ("chainId", toJson chainId), ("block", toJson block),
    ("blockHash", Json.str (hexOfWord s.blockHash)), ("timestamp", toJson timestamp),
    ("fork", Json.str fork.name), ("rpcHost", Json.str (urlHost rpc.url)),
    ("discoveryRounds", toJson rounds), ("accounts", toJson s.accounts.size),
    ("slots", toJson s.slotCount), ("codes", toJson codes.length), ("calls", toJson calls.size),
    ("verified", Json.arr (verified.map fun (a, l, v) => Json.mkObj [
      ("address", Json.str (hexOfAddress a)), ("label", Json.str l), ("name", Json.str v.name),
      ("provider", Json.str v.provider), ("compiler", Json.str v.compiler)]))]).pretty ++ "\n")
  IO.println s!"saved: {s.accounts.size} accounts, {s.slotCount} slots, {codes.length} codes, \
    {verified.size} verified contracts, {calls.size} calls ({rounds} discovery rounds)"

end Snapshot
