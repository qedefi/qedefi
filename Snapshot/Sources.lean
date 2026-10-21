import Conformance.Hex
import Snapshot.Chain
import Snapshot.Http

/-!
# Verified sources: Sourcify, then Blockscout

Sourcify (`sourcify.dev`, the open verification repository) is asked first; contracts it does
not have are looked up on the chain's public Blockscout instance, which also holds sources
verified on other explorers. Both are free, keyless APIs. For each verified contract the
fetcher writes, under `<dir>/contracts/<address>/`:

```
source/<path>        every source file, at its compiler path
abi.json             the ABI
verification.json    provider, contract name, compiler version and settings
```

Source paths come from the network and are sanitized: no absolute paths, no `..`.
-/

namespace Snapshot

open Lean EvmLean Conformance

/-- A verified contract. -/
structure Verified where
  provider : String
  name : String
  compiler : String
  abi : Json
  /-- Compiler settings, and anything else worth keeping, as returned by the provider. -/
  info : Json
  sources : Array (String × String)

/-- A relative path inside `source/`: separators normalized, empty, `.` and `..` components
dropped, so the result never leaves the directory. -/
def safeRelPath (p : String) : Option System.FilePath :=
  let parts := (p.replace "\\" "/").splitOn "/" |>.filter fun c => c != "" && c != "." && c != ".."
  match parts with
  | [] => none
  | c :: cs => some (cs.foldl (fun (p : System.FilePath) (x : String) => p / x) (System.FilePath.mk c))

def strOr (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

/-- Sourcify API v2: `none` unless verified. -/
def sourcify? (chainId : Nat) (a : Address) : IO (Option Verified) := do
  let some j ← getJson? s!"https://sourcify.dev/server/v2/contract/{chainId}/{hexOfAddress a}?fields=all"
    | return none
  match j.getObjVal? "match" with
  | .ok (.str _) => pure ()
  | _ => return none
  let comp := (j.getObjVal? "compilation").toOption.getD .null
  let sources := (match (j.getObjVal? "sources").toOption.getD .null |>.getObj? with
    | .ok m => m.toArray
    | .error _ => #[]).map fun (p, v) => (p, strOr v "content")
  return some {
    provider := "sourcify", name := strOr comp "name", compiler := strOr comp "compilerVersion",
    abi := (j.getObjVal? "abi").toOption.getD (Json.arr #[]),
    info := Json.mkObj [("match", (j.getObjVal? "match").toOption.getD .null),
      ("compilerSettings", (comp.getObjVal? "compilerSettings").toOption.getD .null),
      ("language", (comp.getObjVal? "language").toOption.getD .null),
      ("fullyQualifiedName", (comp.getObjVal? "fullyQualifiedName").toOption.getD .null),
      ("deployment", (j.getObjVal? "deployment").toOption.getD .null)],
    sources }

/-- Blockscout API v2: `none` unless verified (or no instance for the chain). -/
def blockscout? (chainId : Nat) (a : Address) : IO (Option Verified) := do
  let some base := blockscoutBase? chainId | return none
  let some j ← getJson? s!"{base}/api/v2/smart-contracts/{hexOfAddress a}" | return none
  unless (j.getObjValAs? Bool "is_verified").toOption.getD false do return none
  let main := (strOr j "file_path", strOr j "source_code")
  let extra := (match (j.getObjVal? "additional_sources").toOption.getD .null |>.getArr? with
    | .ok xs => xs
    | .error _ => #[]).map fun s => (strOr s "file_path", strOr s "source_code")
  let main := if main.1 == "" then (strOr j "name" ++ ".sol", main.2) else main
  let keep := ["compiler_settings", "evm_version", "optimization_enabled", "optimization_runs",
    "language", "is_fully_verified", "verified_at", "license_type", "constructor_args"]
  return some {
    provider := "blockscout", name := strOr j "name", compiler := strOr j "compiler_version",
    abi := (j.getObjVal? "abi").toOption.getD (Json.arr #[]),
    info := Json.mkObj (keep.map fun k => (k, (j.getObjVal? k).toOption.getD .null)),
    sources := #[main] ++ extra }

/-- The verified sources of `a`, from the first provider that has them. -/
def verifiedSources? (chainId : Nat) (a : Address) : IO (Option Verified) := do
  if let some v ← sourcify? chainId a then return some v
  blockscout? chainId a

/-- Write a verified contract under `dir/contracts/<address>/` (replacing earlier files). -/
def Verified.save (v : Verified) (dir : System.FilePath) (a : Address) (codeHash : String)
    (label : String) : IO Unit := do
  let d := dir / "contracts" / hexOfAddress a
  if ← (d / "source").pathExists then IO.FS.removeDirAll (d / "source")
  IO.FS.createDirAll (d / "source")
  for (p, content) in v.sources do
    let some rel := safeRelPath p | continue
    let f := d / "source" / rel
    if let some parent := f.parent then IO.FS.createDirAll parent
    IO.FS.writeFile f content
  IO.FS.writeFile (d / "abi.json") (v.abi.pretty ++ "\n")
  IO.FS.writeFile (d / "verification.json") ((Json.mkObj [
    ("address", Json.str (hexOfAddress a)), ("label", Json.str label),
    ("provider", Json.str v.provider), ("name", Json.str v.name),
    ("compiler", Json.str v.compiler), ("codeHash", Json.str ("0x" ++ codeHash)),
    ("sourceFiles", toJson (v.sources.map (·.1))), ("details", v.info)]).pretty ++ "\n")

/-! ## Selectors of argument-free views -/

/-- `name()` of every function in `abi` without inputs that does not modify state. -/
def argFreeViews (abi : Json) : Array String :=
  let entries := match abi.getArr? with
    | .ok xs => xs
    | .error _ => #[]
  entries.filterMap fun e =>
    let isFn := strOr e "type" == "function"
    let noInputs := match (e.getObjVal? "inputs").toOption.getD (Json.arr #[]) |>.getArr? with
      | .ok xs => xs.isEmpty
      | .error _ => false
    let mut_ := strOr e "stateMutability"
    let view := mut_ == "view" || mut_ == "pure" ||
      (mut_ == "" && (e.getObjValAs? Bool "constant").toOption.getD false)
    if isFn && noInputs && view then some (strOr e "name" ++ "()") else none

/-- The 4-byte selector of a signature. -/
def selector (signature : String) : ByteArray :=
  (Bytes.ofWord (Crypto.real.keccak256 signature.toUTF8)).extract 0 4

end Snapshot
