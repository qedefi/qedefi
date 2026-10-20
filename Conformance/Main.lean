import Conformance.Runner

/-!
# `lake exe conform`

```
lake exe conform [<dir-or-file> …] [--threads N] [--filter SUBSTRING]
                 [--fork Cancun|Prague|Osaka|all] [--parse-only] [--results FILE] [--fuel N]
```

Runs BlockchainTests fixtures (`ethereum/tests` or EEST `blockchain_tests`; default dir
`tests/fixtures/BlockchainTests`) with `Crypto.real`, prints a summary and writes per-test
results. Exit code is non-zero iff some test FAILED or was UNPARSEABLE. `--fork F` (default
`Cancun`) also selects transition networks ending in `F`. `--parse-only` decodes without executing.
-/

namespace Conformance

open EvmLean Lean

/-- Command-line configuration. -/
structure Config where
  /-- Fixture directories or files (default `tests/fixtures/BlockchainTests`). -/
  roots : Array System.FilePath := #[]
  threads : Nat := 8
  /-- Substring filter on `file::name`. -/
  filter : Option String := none
  results : System.FilePath := "conformance-results.txt"
  opts : Options := {}

def usage : String :=
  "usage: conform [<dir-or-file> …] [--threads N] [--filter SUBSTRING] [--fork NAME|all] " ++
  "[--parse-only] [--results FILE] [--fuel N]"

def parseArgs : List String → Config → Except String Config
  | [], c => .ok c
  | "--threads" :: n :: rest, c => match n.toNat? with
    | some k => if k = 0 then .error "--threads must be positive" else parseArgs rest { c with threads := k }
    | none => .error s!"--threads: not a number: {n}"
  | "--filter" :: s :: rest, c => parseArgs rest { c with filter := some s }
  | "--fork" :: "all" :: rest, c => parseArgs rest { c with opts.fork := none }
  | "--fork" :: f :: rest, c => match Fork.ofName? f with
    | some fork => parseArgs rest { c with opts.fork := some fork }
    | none => .error s!"--fork: unknown fork {f}"
  | "--parse-only" :: rest, c => parseArgs rest { c with opts.parseOnly := true }
  | "--results" :: f :: rest, c => parseArgs rest { c with results := f }
  | "--fuel" :: n :: rest, c => match n.toNat? with
    | some k => parseArgs rest { c with opts.fuel := k }
    | none => .error s!"--fuel: not a number: {n}"
  | arg :: rest, c =>
    if arg.startsWith "--" then .error s!"unknown option {arg}"
    else parseArgs rest { c with roots := c.roots.push arg }

def containsSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- All `*.json` files under `root` (or `root` itself if it is a file), sorted. -/
def jsonFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  if ← root.isDir then
    let all ← root.walkDir
    let files := all.filter fun p => p.extension == some "json"
    return files.qsort (·.toString < ·.toString)
  else return #[root]

/-- Run all tests of one file, turning I/O and JSON errors into UNPARSEABLE results. -/
def runFile (cfg : Config) (path : System.FilePath) : IO (Array TestResult) := do
  let file := path.toString
  let select (name : String) : Bool := match cfg.filter with
    | none => true
    | some f => containsSubstr (file ++ "::" ++ name) f
  try
    let text ← IO.FS.readFile path
    match Json.parse text with
    | .error e => return #[{ file, name := "<file>", status := .unparseable, reason := s!"JSON: {e}" }]
    | .ok j => return runFileJson cfg.opts Crypto.real file select j
  catch e =>
    return #[{ file, name := "<file>", status := .unparseable, reason := s!"I/O: {e}" }]

/-- Run `work` over `files` on `threads` dedicated threads pulling from a shared counter. -/
def runPool (files : Array System.FilePath) (threads : Nat)
    (work : System.FilePath → IO (Array TestResult)) : IO (Array TestResult) := do
  let next ← IO.mkRef 0
  let done ← IO.mkRef 0
  let worker : IO (Array TestResult) := do
    let mut acc := #[]
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      match files[i]? with
      | none => break
      | some f =>
        acc := acc ++ (← work f)
        let d ← done.modifyGet fun d => (d + 1, d + 1)
        if d % 200 = 0 then
          IO.eprintln s!"  … {d}/{files.size} files"
    return acc
  let tasks ← (List.range threads).mapM fun _ => IO.asTask worker .dedicated
  let mut results := #[]
  for t in tasks do
    match ← IO.wait t with
    | .ok r => results := results ++ r
    | .error e =>
      let r : TestResult := { file := "<worker>", name := "<worker>", status := .unparseable,
                              reason := s!"worker crashed: {e}" }
      results := results.push r
  return results

def runMain (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {} with
    | .ok c => pure c
    | .error e => IO.eprintln e; IO.eprintln usage; return 2
  let roots := if cfg.roots.isEmpty then #[⟨"tests/fixtures/BlockchainTests"⟩] else cfg.roots
  let files ← roots.foldlM (fun acc r => return acc ++ (← jsonFiles r)) #[]
  if files.isEmpty then
    IO.eprintln s!"no JSON fixtures found under {roots}"
    return 2
  let mode := if cfg.opts.parseOnly then "parse-only" else "execute"
  let forkName := match cfg.opts.fork with
    | some f => f.name
    | none => "all"
  IO.println s!"conform: {files.size} files under {roots}, {cfg.threads} threads, fork {forkName}, mode {mode}"
  let start ← IO.monoMsNow
  let results ← runPool files cfg.threads (runFile cfg)
  let results := results.qsort fun a b => a.file < b.file || (a.file == b.file && a.name < b.name)
  let elapsed := (← IO.monoMsNow) - start
  let count (s : Status) := (results.filter (·.status == s)).size
  let lines := results.map fun r => s!"{r.status.label}\t{r.file}::{r.name}\t{r.reason}"
  IO.FS.writeFile cfg.results (String.intercalate "\n" lines.toList ++ "\n")
  let unparseable := results.filter (·.status == .unparseable)
  let failed := results.filter (·.status == .failed)
  if !unparseable.isEmpty then
    IO.println s!"UNPARSEABLE tests ({unparseable.size}):"
    for r in unparseable do IO.println s!"  {r.file}::{r.name}: {r.reason}"
  if !failed.isEmpty then
    IO.println s!"first failures (of {failed.size}):"
    for r in failed.toList.take 25 do IO.println s!"  {r.file}::{r.name}: {r.reason}"
  let passLabel := if cfg.opts.parseOnly then "PARSED" else "PASSED"
  let networks := (results.filter (·.status != .skipped)).foldl
    (fun (acc : Array String) r => if acc.contains r.network then acc else acc.push r.network) #[]
  for n in networks.qsort (· < ·) do
    let rs := results.filter (·.network == n)
    let c (s : Status) := (rs.filter (·.status == s)).size
    IO.println s!"  {n}: {passLabel} {c .passed}  FAILED {c .failed}  UNPARSEABLE {c .unparseable}"
  IO.println s!"{passLabel}: {count .passed}  FAILED: {count .failed}  SKIPPED: {count .skipped}  UNPARSEABLE: {count .unparseable}  (total {results.size}, {elapsed / 1000}s)"
  IO.println s!"results written to {cfg.results}"
  return if failed.isEmpty && unparseable.isEmpty then 0 else 1

end Conformance

/-- `lake exe conform`: see `Conformance.runMain`. -/
def main (args : List String) : IO UInt32 := Conformance.runMain args
