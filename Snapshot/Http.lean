import Lean.Data.Json

/-!
# HTTP through `curl`

Lean core has no HTTP client, so requests go through `curl` (as in the differential tester).
Request bodies are piped through stdin, never passed as arguments: JSON-RPC batches can exceed
the argument-size limit. Error messages never echo the URL, which may carry an API key.
-/

namespace Snapshot

open Lean

def fail {α : Type} (msg : String) : IO α := throw (IO.userError msg)

/-- Lift an `Except String` into `IO`, prefixing the error with `ctx`. -/
def ofExcept {α : Type} (ctx : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => fail s!"{ctx}: {e}"

/-- Run `curl` with `args`, feeding `stdin`; returns stdout, or fails with curl's message. -/
def curl (args : Array String) (stdin : String := "") : IO String := do
  let child ← IO.Process.spawn {
    cmd := "curl", args := #["-sS", "-m", "120", "--retry", "3", "--retry-all-errors"] ++ args,
    stdin := .piped, stdout := .piped, stderr := .piped }
  let (input, child) ← child.takeStdin
  input.putStr stdin
  input.flush
  let out ← IO.asTask child.stdout.readToEnd .dedicated
  let err ← child.stderr.readToEnd
  let code ← child.wait
  let out ← IO.ofExcept out.get
  if code != 0 then fail s!"curl failed ({code}): {err}"
  pure out

/-- POST a JSON body; returns the response body. -/
def postJson (url : String) (body : String) : IO String :=
  curl #["-X", "POST", "-H", "Content-Type: application/json", "--data-binary", "@-", url] body

/-- GET `url`; `none` on HTTP 404, the body otherwise (other HTTP errors fail). -/
def getJson? (url : String) : IO (Option Json) := do
  let out ← curl #["-w", "\n%{http_code}", url]
  let lines := out.splitOn "\n"
  let status := lines.getLast?.getD ""
  let body := "\n".intercalate (lines.dropLast)
  if status == "404" then return none
  if !status.startsWith "2" then fail s!"GET {url}: HTTP {status}"
  match Json.parse body with
  | .ok j => pure (some j)
  | .error e => fail s!"GET {url}: invalid JSON ({e})"

end Snapshot
