import Conformance.Hex
import Snapshot.Access
import Snapshot.Http

/-!
# Snapshot state: on-disk format and the Lean world it denotes

A snapshot is the part of a chain's state at one block that a set of runs reads, with the
block environment:

```
<dir>/state.json     chain id, block number and hash, fork, block environment, block hashes,
                     accounts: nonce, balance, code hash, storage (every fetched slot, zeros too)
<dir>/code/<h>.hex   runtime code with keccak-256 hash h (shared by accounts with equal code)
```

Fetched slots that hold zero are kept: they record that the slot was read and is zero, as
opposed to never fetched. `State.known` answers "does the snapshot determine this read?";
`State.world` drops the zeros (storage never holds zeros) and the empty accounts (they do not
exist after EIP-161, and `EXTCODEHASH` tells the two apart).
-/

namespace Snapshot

open Lean EvmLean Conformance

/-- An account as fetched; `storage` maps every fetched slot to its value, including zeros. -/
structure AccountState where
  nonce : Nat := 0
  balance : Nat := 0
  code : ByteArray := .empty
  storage : Std.ExtTreeMap Word Word compare := ∅

/-- The fetched state and its block environment. -/
structure State where
  chainId : Nat
  block : Nat
  blockHash : Word
  fork : Fork
  /-- Environment of the call simulation (`number = block`; `blockHashes` unused, see below). -/
  env : BlockEnv
  /-- Hashes of ancestor blocks that some run read with `BLOCKHASH`. -/
  blockHashes : Std.ExtTreeMap Nat Word compare := ∅
  accounts : Std.ExtTreeMap Address AccountState compare := ∅

namespace State

/-- The reads in `acc` the snapshot does not determine (empty iff it determines them all). -/
def missing (s : State) (acc : Accesses) : Accesses :=
  { accounts := acc.accounts.foldl (init := ∅) fun r a =>
      if s.accounts.contains a then r else r.insert a
    slots := acc.slotList.foldl (init := ∅) fun r (a, k) =>
      match s.accounts[a]? with
      | some st => if st.storage.contains k then r else Tx.warmKey r a k
      | none => Tx.warmKey r a k
    blockNumbers := acc.blockNumbers.foldl (init := ∅) fun r n =>
      if n + 256 < s.block || n ≥ s.block || s.blockHashes.contains n then r else r.insert n }

/-- The block environment with the known ancestor hashes (`BLOCKHASH` of an unknown one is 0;
`missing` reports such reads). -/
def blockEnv (s : State) : BlockEnv :=
  { s.env with blockHashes := (List.range 256).map fun i =>
      if i < s.block then s.blockHashes.getD (s.block - 1 - i) 0 else 0 }

/-- The world: fetched accounts that exist, without zero slots. -/
def world (s : State) : World :=
  s.accounts.foldl (init := ∅) fun w a st =>
    if st.nonce = 0 && st.balance = 0 && st.code.size = 0 && st.storage.all (fun _ v => v = 0) then w
    else w.insert a { nonce := st.nonce, balance := BitVec.ofNat 256 st.balance, code := st.code,
                      storage := st.storage.foldl (fun m k v => m.set k v) ∅ }

/-- The execution context for a call from `sender` (gas price zero, no authorizations). -/
def context (s : State) (sender : Address) : Context :=
  { crypto := Crypto.real, fork := s.fork, block := s.blockEnv,
    tx := { origin := sender, gasPrice := 0 } }

end State

/-- Keccak-256 of code as a file name (64 hex digits, no prefix). -/
def codeName (code : ByteArray) : String :=
  (hexOfWord (Crypto.real.keccak256 code)).drop 2 |>.toString

/-! ## JSON -/

def jStr (s : String) : Json := Json.str s

def State.encode (s : State) : Json :=
  let accounts := s.accounts.toList.map fun (a, st) =>
    (hexOfAddress a, Json.mkObj [
      ("nonce", jStr (hexOfNat st.nonce)), ("balance", jStr (hexOfNat st.balance)),
      ("code", if st.code.size = 0 then Json.null else jStr (codeName st.code)),
      ("storage", Json.mkObj (st.storage.toList.map fun (k, v) => (hexOfWord k, jStr (hexOfNat v.toNat))))])
  Json.mkObj [
    ("chainId", toJson s.chainId), ("block", toJson s.block),
    ("blockHash", jStr (hexOfWord s.blockHash)), ("fork", jStr s.fork.name),
    ("env", Json.mkObj [
      ("coinbase", jStr (hexOfAddress s.env.coinbase)), ("number", toJson s.env.number),
      ("timestamp", toJson s.env.timestamp), ("gasLimit", toJson s.env.gasLimit),
      ("baseFee", toJson s.env.baseFee), ("prevRandao", jStr (hexOfWord s.env.prevRandao)),
      ("excessBlobGas", toJson s.env.excessBlobGas),
      ("parentBeaconBlockRoot", jStr (hexOfWord s.env.parentBeaconBlockRoot))]),
    ("blockHashes", Json.mkObj (s.blockHashes.toList.map fun (n, h) => (toString n, jStr (hexOfWord h)))),
    ("accounts", Json.mkObj accounts)]

def getField (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"missing field \"{k}\""

def getStrField (j : Json) (k : String) : Except String String := do
  match (← getField j k).getStr? with
  | .ok s => .ok s
  | .error _ => .error s!"field \"{k}\" is not a string"

def getNatField (j : Json) (k : String) : Except String Nat := do
  match (← getField j k).getNat? with
  | .ok n => .ok n
  | .error _ => .error s!"field \"{k}\" is not a natural number"

def objList (j : Json) : List (String × Json) :=
  match j.getObj? with
  | .ok m => m.toList
  | .error _ => []

/-- Parse `state.json`; `code h` reads the code with hash `h`. -/
def State.decode (j : Json) (code : String → Except String ByteArray) : Except String State := do
  let env ← getField j "env"
  let fork ← match Fork.ofName? (← getStrField j "fork") with
    | some f => pure f
    | none => throw "unknown fork"
  let accounts ← (objList (← getField j "accounts")).foldlM (init := ∅) fun m (a, aj) => do
    let addr ← parseAddress a
    let c ← match aj.getObjVal? "code" with
      | .ok (.str h) => code h
      | _ => pure .empty
    let storage ← (objList (← getField aj "storage")).foldlM (init := ∅) fun s (k, v) => do
      let v ← match v.getStr? with
        | .ok x => parseWord x
        | .error _ => throw s!"storage value of {a} is not a string"
      pure (s.insert (← parseWord k) v)
    pure (m.insert addr { nonce := ← parseHexNat (← getStrField aj "nonce"),
                          balance := ← parseHexNat (← getStrField aj "balance"),
                          code := c, storage })
  let blockHashes ← (objList (← getField j "blockHashes")).foldlM (init := ∅) fun m (n, h) => do
    let some n := n.toNat? | throw s!"block number {n}"
    let h ← match h.getStr? with
      | .ok x => parseWord x
      | .error _ => throw "block hash is not a string"
    pure (m.insert n h)
  return {
    chainId := ← getNatField j "chainId", block := ← getNatField j "block",
    blockHash := ← parseWord (← getStrField j "blockHash"), fork,
    env := { chainId := ← getNatField j "chainId",
             coinbase := ← parseAddress (← getStrField env "coinbase"),
             number := ← getNatField env "number", timestamp := ← getNatField env "timestamp",
             gasLimit := ← getNatField env "gasLimit", baseFee := ← getNatField env "baseFee",
             prevRandao := ← parseWord (← getStrField env "prevRandao"),
             excessBlobGas := ← getNatField env "excessBlobGas",
             parentBeaconBlockRoot := ← parseWord (← getStrField env "parentBeaconBlockRoot") },
    blockHashes, accounts }

/-! ## Files -/

/-- Write `state.json` and the code files under `dir`. -/
def State.save (s : State) (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (dir / "code")
  for (_, st) in s.accounts.toList do
    if st.code.size > 0 then
      let f := dir / "code" / (codeName st.code ++ ".hex")
      unless ← f.pathExists do
        IO.FS.writeFile f ((hexOfBytes st.code).drop 2 |>.toString)
  IO.FS.writeFile (dir / "state.json") (s.encode.pretty ++ "\n")

/-- Read a snapshot written by `State.save`, checking every code file against its hash. -/
def State.load (dir : System.FilePath) : IO State := do
  let j ← ofExcept "state.json" (Json.parse (← IO.FS.readFile (dir / "state.json")))
  let names := (objList ((j.getObjVal? "accounts").toOption.getD .null)).filterMap fun (_, a) =>
    match a.getObjVal? "code" with
    | .ok (.str h) => some h
    | _ => none
  let mut codes : Std.HashMap String ByteArray := {}
  for h in names do
    unless codes.contains h do
      let text ← IO.FS.readFile (dir / "code" / (h ++ ".hex"))
      let code ← ofExcept s!"code {h}" (parseHexBytes (String.ofList (text.toList.filter (!·.isWhitespace))))
      if codeName code != h then fail s!"code/{h}.hex does not hash to its name"
      codes := codes.insert h code
  ofExcept "state.json" (State.decode j fun h =>
    match codes[h]? with
    | some c => .ok c
    | none => .error s!"missing code {h}")

end Snapshot
