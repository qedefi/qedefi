import Examples.Differential.Session
import Examples.Differential.Token
import Examples.Deployment

/-!
# `lake exe difftest`: evm-lean vs. anvil on the compiled and mainnet targets

```
lake exe difftest [--seed N] [--sequences N] [--length N] [--family NAME[,NAME…]]
                  [--rpc URL | --port N] [--inject-bug] [--verbose]
```

Families: vaults `solmate`, `oz`, `oz3` (OpenZeppelin, decimals offset 3); tokens `oz20`,
`solady`, `weth9`; groups `vaults`, `tokens`, `all`. Default: `solmate,oz`.

Per vault family: deploy from a non-canonical and the canonical deployer (checking
`runtimeCodeFor` and `runtimeCode`), run an inflation-attack scenario and random call
sequences, comparing status, output, logs, `gasUsed` and storage after every call, and
shrink any mismatch. Per token family (`Token.lean`): deploy or install the token, run its
fixed scenario and random sequences the same way (ether balances too, for ether-holding
tokens). `--inject-bug` self-tests the tester. Needs `anvil` in `PATH` unless `--rpc` is
given; exit code 0 iff no mismatch.
-/

namespace Examples.Differential

open Lean EvmLean EvmLogic EvmLogic.Solidity Conformance Examples.Deployment
open Examples.OpenZeppelin Examples.OpenZeppelin.Contracts
open Examples.Solmate Examples.Solmate.Contracts

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
  /-- Vault families to test. -/
  families : List Family := [solmate, openzeppelin]
  /-- Token families to test. -/
  tokens : List TokenFamily := []
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

def parseArgs : Config → List String → Except String Config
  | c, [] => .ok c
  | c, "--seed" :: n :: rest => do parseArgs { c with seed := ← natArg n } rest
  | c, "--sequences" :: n :: rest => do parseArgs { c with sequences := ← natArg n } rest
  | c, "--length" :: n :: rest => do parseArgs { c with length := ← natArg n } rest
  | c, "--port" :: n :: rest => do parseArgs { c with port := ← natArg n } rest
  | c, "--rpc" :: u :: rest => parseArgs { c with rpc := some u } rest
  | c, "--family" :: f :: rest => do
    let vaults := [solmate, openzeppelin, openzeppelinOffset]
    let mut fams := []
    let mut toks := []
    for n in f.splitOn "," do
      match vaults.find? (·.name == n), tokenFamilies.find? (·.name == n) with
      | some v, _ => fams := fams ++ [v]
      | _, some t => toks := toks ++ [t]
      | none, none =>
        match n with
        | "vaults" => fams := fams ++ vaults
        | "tokens" => toks := toks ++ tokenFamilies
        | "all" => fams := fams ++ vaults; toks := toks ++ tokenFamilies
        | _ => throw (s!"unknown family {n} (" ++ ", ".intercalate
            ((vaults.map (·.name)) ++ (tokenFamilies.map (·.name)) ++ ["vaults", "tokens", "all"]) ++ ")")
    parseArgs { c with families := fams, tokens := toks } rest
  | c, "--inject-bug" :: rest => parseArgs { c with injectBug := true } rest
  | c, "--verbose" :: rest => parseArgs { c with verbose := true } rest
  | _, a :: _ => throw s!"unknown argument {a}"

/-! ## Deployment -/

/-- Deploy the family from `deployer` on a fresh chain on both sides and check the deployed
code against `expected` (asset and vault code, given their addresses). Returns the
evm-lean world. -/
def deploy (rpc : Rpc) (stats : IO.Ref Stats) (fam : Family) (deployer : Address)
    (expected : Address → Address → ByteArray × ByteArray) : IO World := do
  rpc.reset
  let assetAddr := Interpreter.createAddress Crypto.real.keccak256 deployer 0
  let vaultAddr := Interpreter.createAddress Crypto.real.keccak256 deployer 1
  let watch : Watch := { accounts := [assetAddr, vaultAddr] }
  let (wA, oA, obsA, dA) ← step rpc watch ∅ deployer none fam.assetInit 0 "deploy"
  let (wV, oV, obsV, dV) ←
    step rpc watch wA deployer none (fam.vaultInitFor assetAddr) 0 "deploy"
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

def testFamily (cfg : Config) (rpc : Rpc) (stats : IO.Ref Stats) (famIdx : Nat) (fam : Family) :
    IO Unit := do
  IO.println s!"[{fam.name}]"
  discard <| deploy rpc stats fam otherDeployer fam.codeFor
  let world0 ← deploy rpc stats fam deployer fun _ _ => (fam.assetCode, fam.vaultCode)
  let snap ← IO.mkRef (← rpc.snapshot)
  let corrupt (kind : String) (w : World) : World :=
    if cfg.injectBug && kind == "vault.deposit" then
      let k : Word := BitVec.ofNat 256 fam.vaultTotalSupply
      w.sstore fam.vault k (w.sload fam.vault k + 1)
    else w
  let s : Session := { rpc, name := fam.name, watch := { accounts := [fam.asset, fam.vault], corrupt },
                       world0, snap, stats, gen := genCall fam, length := cfg.length,
                       verbose := cfg.verbose }
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
  found := found + (← s.fuzzMany cfg.seed famIdx cfg.sequences)
  stats.modify fun st => { st with mismatches := st.mismatches + found }
  IO.println s!"  {cfg.sequences} sequences × {cfg.length} calls: {found} mismatching sequences"

/-- Run every family against anvil at `rpc`. -/
def runAll (cfg : Config) (rpc : Rpc) (stats : IO.Ref Stats) : IO Unit := do
  let mut i := 0
  for fam in cfg.families do
    testFamily cfg rpc stats i fam
    i := i + 1
  for tok in cfg.tokens do
    discard <| testToken rpc stats cfg.seed i cfg.sequences cfg.length cfg.verbose tok
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
