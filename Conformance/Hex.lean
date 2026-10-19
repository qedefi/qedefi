import EvmLean

/-!
# Hex helpers for the conformance runner

Parsing of the `0x…` strings used throughout the fixtures, and hex printing for reports.
Malformed input is an `Except String` error, never a panic.
-/

namespace Conformance

open EvmLean

/-- The value of a hex digit. -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Strip an optional `0x`/`0X` prefix. -/
def stripHexPrefix (s : String) : String :=
  if s.startsWith "0x" || s.startsWith "0X" then s.drop 2 |>.toString else s

/-- Parse a hex number (`0x` prefix optional; `0x` alone is zero). -/
def parseHexNat (s : String) : Except String Nat := do
  let digits := stripHexPrefix s
  digits.foldl (init := .ok 0) fun acc c => do
    let n ← acc
    match hexDigit? c with
    | some d => pure (n * 16 + d)
    | none => throw s!"invalid hex digit '{c}' in \"{s}\""

/-- Parse a hex number that must fit in `bits` bits. -/
def parseHexBounded (bits : Nat) (s : String) : Except String Nat := do
  let n ← parseHexNat s
  if n < 2 ^ bits then pure n else throw s!"value {s} exceeds {bits} bits"

/-- Parse a 256-bit word. -/
def parseWord (s : String) : Except String Word := do
  return BitVec.ofNat 256 (← parseHexBounded 256 s)

/-- Parse a 160-bit address. -/
def parseAddress (s : String) : Except String Address := do
  return BitVec.ofNat 160 (← parseHexBounded 160 s)

/-- Parse a hex byte string (an even number of digits after the optional prefix). -/
def parseHexBytes (s : String) : Except String ByteArray := do
  let digits := (stripHexPrefix s).toList
  if digits.length % 2 ≠ 0 then throw s!"odd-length hex string \"{s.take 40}…\""
  let rec go : List Char → ByteArray → Except String ByteArray
    | a :: b :: rest, acc =>
      match hexDigit? a, hexDigit? b with
      | some x, some y => go rest (acc.push (x * 16 + y).toUInt8)
      | _, _ => .error s!"invalid hex digits '{a}{b}'"
    | [_], _ => .error "odd-length hex string"
    | [], acc => .ok acc
  go digits (ByteArray.emptyWithCapacity (digits.length / 2))

/-- Lower-case hex of a byte string, with `0x` prefix. -/
def hexOfBytes (b : ByteArray) : String :=
  let digits := "0123456789abcdef".toList
  let d (n : Nat) : Char := digits[n]?.getD '?'
  b.foldl (fun s x => s.push (d (x.toNat / 16)) |>.push (d (x.toNat % 16))) "0x"

/-- A word as 32-byte hex. -/
def hexOfWord (w : Word) : String := hexOfBytes (Bytes.ofWord w)

/-- An address as 20-byte hex. -/
def hexOfAddress (a : Address) : String := hexOfBytes (Bytes.ofAddress a)

/-- A number as minimal hex (`0x0` for zero). -/
def hexOfNat (n : Nat) : String :=
  if n = 0 then "0x0" else "0x" ++ String.ofList (Nat.toDigits 16 n)

end Conformance
