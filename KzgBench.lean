import EvmLean.Crypto.Kzg
open EvmLean

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

def parseHex (s : String) : ByteArray := Id.run do
  let cs := (s.toList.drop 2).toArray
  let mut out := ByteArray.empty
  for i in [0:cs.size/2] do
    out := out.push (hexDigit cs[2*i]! * 16 + hexDigit cs[2*i+1]!).toUInt8
  return out

def field (txt : String) (k : String) : ByteArray :=
  match (txt.splitOn (k ++ ": '")) with
  | _ :: rest :: _ => parseHex ((rest.splitOn "'").head!)
  | _ => ByteArray.empty

def main (args : List String) : IO Unit := do
  let dir := args.head!
  let entries ← System.FilePath.readDir dir
  let mut ok := 0
  let mut bad := 0
  let mut maxMs := 0
  let t0 ← IO.monoMsNow
  for e in entries do
    let txt ← IO.FS.readFile e.path
    let out := (((txt.splitOn "output: ")[1]!).takeWhile Char.isAlpha).toString
    let exp : Option Bool := if out == "true" then some true else if out == "false" then some false else none
    let s ← IO.monoMsNow
    let got := Kzg.verifyProof (field txt "commitment") (field txt "z") (field txt "y") (field txt "proof")
    let gotS := toString (repr got)
    let ms := (← IO.monoMsNow) - s
    if ms > maxMs then maxMs := ms
    if got == exp then ok := ok + 1 else
      bad := bad + 1
      IO.println s!"FAIL {e.fileName} got {gotS} exp {repr exp}"
  let t1 ← IO.monoMsNow
  IO.println s!"ok {ok} bad {bad} total {t1 - t0} ms, max {maxMs} ms"
