import Conformance.Fixture

/-!
# Running BlockchainTests

`runTest` imports a test's blocks into a chain starting at its genesis, exactly as a client
would: each block's RLP is decoded, attached to the block whose hash is its `parentHash`,
and run through `Block.stateTransition` (header validation, execution, and every header
commitment). A block with `expectException` must be rejected; any other block must be
accepted. Finally the head must have hash `lastblockhash` and the expected post-state
(compared exactly, or by state root for `postStateHash`).

The fork of each block follows the test's `network`: a single fork, or a transition network
such as `CancunToPragueAtTime15k` (the second fork from timestamp 15000 on).

`parseTest` is the `--parse-only` mode: it decodes every RLP in the test and cross-checks
the decoded headers and transactions against their JSON forms, without executing anything
(and without any hashing, so it works before the crypto is implemented).
-/

namespace Conformance

open EvmLean Lean

/-- Outcome category of a test. -/
inductive Status where
  /-- The test passed (or, in `--parse-only` mode, parsed). -/
  | passed
  /-- The test failed. -/
  | failed
  /-- The test targets another fork. -/
  | skipped
  /-- The fixture could not be parsed. -/
  | unparseable
  deriving DecidableEq, Repr, Inhabited

/-- Label used in reports. -/
def Status.label : Status → String
  | .passed => "PASSED"
  | .failed => "FAILED"
  | .skipped => "SKIPPED"
  | .unparseable => "UNPARSEABLE"

/-- The result of one test. -/
structure TestResult where
  /-- Fixture file. -/
  file : String
  /-- Test name. -/
  name : String
  /-- The test's `network` (empty if unknown). -/
  network : String := ""
  /-- Outcome. -/
  status : Status
  /-- Explanation (empty for plain passes). -/
  reason : String := ""
  deriving Inhabited

/-- Runner options. -/
structure Options where
  /-- Only decode and cross-check, do not execute. -/
  parseOnly : Bool := false
  /-- The fork to run (`none`: every supported network); tests whose network ends in
  another fork are skipped. -/
  fork : Option Fork := some .cancun
  /-- Interpreter fuel per message call. -/
  fuel : Nat := 2 ^ 40

/-- The forks of a test network: `first` until the block timestamp reaches `switchAt`, then
`next`. -/
structure Schedule where
  /-- The fork at genesis. -/
  first : Fork
  /-- The fork transition, if any: the new fork and its activation timestamp. -/
  next : Option (Fork × Nat) := none

/-- The fork active at `timestamp`. -/
def Schedule.forkAt (s : Schedule) (timestamp : Nat) : Fork :=
  match s.next with
  | some (f, t) => if timestamp ≥ t then f else s.first
  | none => s.first

/-- The fork a test network ends in (used for `--fork` selection and reporting). -/
def Schedule.final (s : Schedule) : Fork :=
  match s.next with
  | some (f, _) => f
  | none => s.first

/-- The schedule of a fixture `network`: a fork name, or a transition network
`<A>To<B>AtTime15k` between two supported forks. -/
def parseSchedule (network : String) : Option Schedule :=
  match Fork.ofName? network with
  | some f => some { first := f }
  | none =>
    match network.splitOn "To" with
    | [a, rest] =>
      match rest.splitOn "AtTime15k", Fork.ofName? a with
      | [b, ""], some fa => (Fork.ofName? b).map fun fb => { first := fa, next := some (fb, 15000) }
      | _, _ => none
    | _ => none

/-! ## World comparison -/

/-- First difference between two accounts, if any. -/
def accountDiff (a : Address) (got expected : Account) : Option String :=
  let addr := hexOfAddress a
  if got.nonce ≠ expected.nonce then
    some s!"{addr}: nonce {got.nonce}, expected {expected.nonce}"
  else if got.balance ≠ expected.balance then
    some s!"{addr}: balance {got.balance.toNat}, expected {expected.balance.toNat}"
  else if got.code ≠ expected.code then
    some s!"{addr}: code differs (size {got.code.size}, expected {expected.code.size})"
  else
    let keys := (got.storage.keys ++ expected.storage.keys)
    keys.findSome? fun k =>
      let g := got.storage.get k
      let e := expected.storage.get k
      if g ≠ e then
        some s!"{addr}: storage[{hexOfWord k}] = {hexOfWord g}, expected {hexOfWord e}"
      else none

/-- First difference between two worlds, if any. -/
def worldDiff (got expected : World) : Option String :=
  let addrs := got.keys ++ expected.keys
  addrs.findSome? fun a =>
    match got.account? a, expected.account? a with
    | some g, some e => accountDiff a g e
    | some _, none => some s!"{hexOfAddress a}: exists, expected absent"
    | none, some _ => some s!"{hexOfAddress a}: absent, expected to exist"
    | none, none => none

/-! ## Parse-only mode -/

/-- Cross-check a decoded block against its JSON form. -/
def crossCheckBlock (i : Nat) (fx : BlockFixture) (b : Block) : Option String :=
  let headerCheck := match fx.header with
    | some h => if h = b.header then none else some s!"block {i}: decoded header ≠ JSON header"
    | none => none
  let txCheck := match fx.transactions with
    | some txs =>
      if txs.length ≠ b.transactions.length then
        some s!"block {i}: {b.transactions.length} decoded transactions, JSON has {txs.length}"
      else (txs.zip b.transactions).zipIdx.findSome? fun ((j, d), k) =>
        if j = d then none else some s!"block {i}: transaction {k} decoded ≠ JSON"
    | none => none
  headerCheck <|> txCheck

/-- `--parse-only`: decode all RLP and cross-check against the JSON. -/
def parseTest (t : TestCase) : Status × String :=
  match Block.decode t.genesisRlp with
  | .error e => (.unparseable, s!"genesis RLP: {e}")
  | .ok g =>
    if g.header ≠ t.genesisHeader then (.unparseable, "decoded genesis header ≠ JSON header")
    else
      let problems := t.blocks.toList.zipIdx.filterMap fun (fx, i) =>
        match Block.decode fx.rlp, fx.expectException with
        | .error e, none => some s!"block {i}: RLP: {e}"
        | .error _, some _ => none
        | .ok b, _ => crossCheckBlock i fx b
      match problems with
      | [] => (.passed, "parsed")
      | p :: _ => (.unparseable, p)

/-! ## Execution -/

/-- Import the blocks of `t` in order. Returns the final head, or the failure reason. -/
def importBlocks (opts : Options) (crypto : Crypto) (schedule : Schedule) (t : TestCase)
    (genesis : Block.ChainHead) : Except String Block.ChainHead := do
  let mut store : Std.TreeMap Word Block.ChainHead compare := Std.TreeMap.empty.insert genesis.hash genesis
  let mut head := genesis
  for h : i in [0:t.blocks.size] do
    let fx := t.blocks[i]
    let expected := fx.expectException
    match Block.decode fx.rlp with
    | .error e =>
      if expected.isNone then throw s!"block {i}: undecodable RLP ({e})"
    | .ok b =>
      match store.get? b.header.parentHash with
      | none => if expected.isNone then throw s!"block {i}: unknown parent"
      | some parent =>
        let fork := schedule.forkAt b.header.timestamp
        match Block.stateTransition opts.fuel crypto fork t.chainId parent b fx.senders with
        | .error (.outOfFuel idx) => throw s!"block {i}: interpreter out of fuel ({idx})"
        | .error e =>
          if expected.isNone then throw s!"block {i} rejected: {e}"
        | .ok (newHead, _) =>
          match expected with
          | some exc => throw s!"block {i}: expected exception {exc}, but block was accepted"
          | none =>
            store := store.insert newHead.hash newHead
            head := newHead
  return head

/-- Run one test: import its blocks and compare the outcome with the expectation. -/
def execTest (opts : Options) (crypto : Crypto) (schedule : Schedule) (t : TestCase) :
    Status × String :=
  match Block.decode t.genesisRlp with
  | .error e => (.unparseable, s!"genesis RLP: {e}")
  | .ok g =>
    let keccak := crypto.keccak256
    let genesis := Block.genesisHead keccak g.header t.pre
    if genesis.hash ≠ t.genesisHash then
      (.failed, s!"genesis hash {hexOfWord genesis.hash}, expected {hexOfWord t.genesisHash}")
    else if Trie.stateRoot keccak t.pre ≠ g.header.stateRoot then
      (.failed, "genesis state root mismatch")
    else match importBlocks opts crypto schedule t genesis with
      | .error e => (.failed, e)
      | .ok head =>
        if head.hash ≠ t.lastBlockHash then
          (.failed, s!"head {hexOfWord head.hash}, expected lastblockhash {hexOfWord t.lastBlockHash}")
        else match t.post with
          | .state w => match worldDiff head.world w with
            | some d => (.failed, s!"post-state: {d}")
            | none => (.passed, "")
          | .hash root =>
            if Trie.stateRoot keccak head.world = root then (.passed, "")
            else (.failed, "post-state root mismatch")

/-- Run (or, with `parseOnly`, parse) every test of a fixture file's JSON. `select` says
which test names to run. -/
def runFileJson (opts : Options) (crypto : Crypto) (file : String) (select : String → Bool)
    (j : Json) : Array TestResult :=
  match objEntries j with
  | .error e => #[{ file, name := "<file>", status := .unparseable, reason := e }]
  | .ok tests => tests.toArray.filterMap fun (name, tj) =>
    if !select name then none else
    some <| match parseNetwork tj with
    | .error e => { file, name, status := .unparseable, reason := e }
    | .ok network =>
      match parseSchedule network with
      | none => { file, name, network, status := .skipped, reason := s!"network {network}" }
      | some schedule =>
        if opts.fork.any (· ≠ schedule.final) then
          { file, name, network, status := .skipped, reason := s!"network {network}" }
        else match parseTestCase name tj with
          | .error e => { file, name, network, status := .unparseable, reason := e }
          | .ok t =>
            let (status, reason) :=
              if opts.parseOnly then parseTest t else execTest opts crypto schedule t
            { file, name, network, status, reason }

end Conformance
