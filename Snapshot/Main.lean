import Snapshot.Check
import Snapshot.Fetch

/-!
# `lake exe snapshot`

```
lake exe snapshot fetch <dir> [--rpc URL]   read <dir>/targets.json, fetch once, save
lake exe snapshot check <dir> [--verbose]   replay the recorded calls offline
```

`fetch` needs network access. Without `--rpc` it uses Alchemy with the key `ALCHEMY_KEY`
from the environment, else from `.env` in the working directory (`KEY=value` lines, `#`
comments; gitignored), and the network of the targets' chain id. The URL is never printed
or saved. `check` is offline; its exit code is non-zero iff some call fails.
-/

open Snapshot

def usage : String :=
  "usage: snapshot fetch <dir> [--rpc URL]\n       snapshot check <dir> [--verbose]"

/-- The value of `name` in a `.env` file: `KEY=value` lines (optional `export `, quotes
around the value), `#` comments. -/
def dotEnv? (file : System.FilePath) (name : String) : IO (Option String) := do
  unless ← file.pathExists do return none
  let mut found := none
  for line in (← IO.FS.readFile file).splitOn "\n" do
    let line := (line.dropWhile Char.isWhitespace).toString
    let line := if line.startsWith "export " then (line.drop 7).toString else line
    if line.startsWith "#" then continue
    match line.splitOn "=" with
    | k :: v :: rest =>
      if String.ofList (k.toList.filter (!·.isWhitespace)) == name then
        let v := "=".intercalate (v :: rest)
        let v := String.ofList (v.toList.filter fun c => !c.isWhitespace && c != '"' && c != '\'')
        if v != "" then found := some v
    | _ => pure ()
  return found

/-- The RPC for `chainId`: `--rpc`, else Alchemy with `ALCHEMY_KEY` (environment, then `.env`). -/
def rpcFor (explicit : Option String) (chainId : Nat) : IO Rpc := do
  if let some url := explicit then return { url }
  let key ← match ← IO.getEnv "ALCHEMY_KEY" with
    | some k => pure (some k)
    | none => dotEnv? ".env" "ALCHEMY_KEY"
  let some key := key
    | fail "no RPC: pass --rpc URL, set ALCHEMY_KEY, or put ALCHEMY_KEY=… in .env"
  let some net := alchemyNetwork? chainId
    | fail s!"no Alchemy network known for chain {chainId}: pass --rpc URL"
  return { url := s!"https://{net}.g.alchemy.com/v2/{key}" }

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["fetch", dir] | ["fetch", dir, "--rpc", _] =>
      let explicit := match args with
        | [_, _, _, url] => some url
        | _ => none
      let t ← ofExcept "targets.json" (Lean.Json.parse (← IO.FS.readFile (dir / "targets.json")))
      let chainId ← ofExcept "targets.json" (getNatField t "chainId")
      fetchSnapshot dir (← rpcFor explicit chainId)
      let failures ← checkSnapshot dir
      return if failures = 0 then 0 else 1
    | ["check", dir] => return if (← checkSnapshot dir) = 0 then 0 else 1
    | ["check", dir, "--verbose"] => return if (← checkSnapshot dir true) = 0 then 0 else 1
    | _ =>
      IO.eprintln usage
      return 2
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1
