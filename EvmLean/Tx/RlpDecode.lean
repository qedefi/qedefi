import EvmLean.Prelude.Rlp

/-!
# RLP decoding

A strict, total RLP decoder: the inverse of `Rlp.encode` on canonical encodings. Blocks and
typed transactions arrive as RLP, and invalid blocks in the conformance suite are often only
given in that form, so the decoder must reject exactly what the reference rejects:

* truncated input, and trailing bytes after the top-level item;
* non-canonical encodings: a single byte below `0x80` wrapped in a length prefix, a long-form
  length below 56, or a length with leading zero bytes;
* (via the typed accessors below) integers with leading zero bytes, integers wider than
  their reference type, and fixed-size byte strings of the wrong width.

Recursion is on explicit structural fuel. Every call consumes at least one input byte or
descends one level, so `2 * size + 2` fuel always suffices (`decode` supplies it); running
out is nevertheless reported as an explicit error rather than a fake result.
-/

namespace EvmLean.Rlp

/-- Why RLP input was rejected. -/
inductive DecodeError where
  /-- The input ended inside an item. -/
  | truncated
  /-- Bytes remain after the top-level item. -/
  | trailingBytes
  /-- A non-canonical length prefix or integer encoding. -/
  | nonCanonical (what : String)
  /-- An item had the wrong shape (string vs. list, arity, width). -/
  | unexpected (what : String)
  /-- Decoder fuel ran out (unreachable with the fuel `decode` supplies). -/
  | outOfFuel
  deriving DecidableEq, Repr, Inhabited

/-- Human-readable description of a decoding error. -/
def DecodeError.toString : DecodeError → String
  | .truncated => "truncated RLP"
  | .trailingBytes => "trailing bytes after RLP item"
  | .nonCanonical w => s!"non-canonical RLP: {w}"
  | .unexpected w => s!"unexpected RLP item: {w}"
  | .outOfFuel => "RLP decoder out of fuel"

instance : ToString DecodeError := ⟨DecodeError.toString⟩

/-- The byte at `i`, if in range. -/
def byteAt? (b : ByteArray) (i : Nat) : Option UInt8 :=
  if h : i < b.size then some b[i] else none

/-- Big-endian length field of `n` bytes at `pos`, rejecting leading zeros and lengths
below 56 (which must use the short form). -/
def readLongLength (b : ByteArray) (pos n limit : Nat) : Except DecodeError Nat :=
  if pos + n > limit then .error .truncated
  else
    let lenBytes := b.extract pos (pos + n)
    match byteAt? lenBytes 0 with
    | some 0 => .error (.nonCanonical "length with leading zero")
    | _ =>
      let len := Bytes.toNat lenBytes
      if len < 56 then .error (.nonCanonical "long-form length below 56") else .ok len

mutual
/-- Decode one item starting at `pos`, which must end at or before `limit`. Returns the item
and the position just after it. -/
def decodeItem : Nat → ByteArray → Nat → Nat → Except DecodeError (Rlp × Nat)
  | 0, _, _, _ => .error .outOfFuel
  | fuel + 1, b, pos, limit =>
    if pos ≥ limit then .error .truncated else
    match byteAt? b pos with
    | none => .error .truncated
    | some p =>
      let p := p.toNat
      if p < 0x80 then .ok (.bytes (b.extract pos (pos + 1)), pos + 1)
      else if p ≤ 0xb7 then
        let len := p - 0x80
        let start := pos + 1
        if start + len > limit then .error .truncated
        else
          let raw := b.extract start (start + len)
          if len = 1 && (byteAt? raw 0).any (·.toNat < 0x80) then
            .error (.nonCanonical "single byte below 0x80 with length prefix")
          else .ok (.bytes raw, start + len)
      else if p ≤ 0xbf then
        let n := p - 0xb7
        match readLongLength b (pos + 1) n limit with
        | .error e => .error e
        | .ok len =>
          let start := pos + 1 + n
          if start + len > limit then .error .truncated
          else .ok (.bytes (b.extract start (start + len)), start + len)
      else if p ≤ 0xf7 then
        let len := p - 0xc0
        let start := pos + 1
        if start + len > limit then .error .truncated
        else match decodeItems fuel b start (start + len) [] with
          | .error e => .error e
          | .ok items => .ok (.list items, start + len)
      else
        let n := p - 0xf7
        match readLongLength b (pos + 1) n limit with
        | .error e => .error e
        | .ok len =>
          let start := pos + 1 + n
          if start + len > limit then .error .truncated
          else match decodeItems fuel b start (start + len) [] with
            | .error e => .error e
            | .ok items => .ok (.list items, start + len)

/-- Decode consecutive items filling exactly `[pos, limit)`; `acc` holds the items decoded
so far, in reverse. -/
def decodeItems : Nat → ByteArray → Nat → Nat → List Rlp → Except DecodeError (List Rlp)
  | 0, _, _, _, _ => .error .outOfFuel
  | fuel + 1, b, pos, limit, acc =>
    if pos ≥ limit then .ok acc.reverse
    else match decodeItem fuel b pos limit with
      | .error e => .error e
      | .ok (item, next) => decodeItems fuel b next limit (item :: acc)
end

/-- Decode a complete RLP encoding: exactly one item, no trailing bytes. -/
def decode (b : ByteArray) : Except DecodeError Rlp :=
  match decodeItem (2 * b.size + 2) b 0 b.size with
  | .error e => .error e
  | .ok (item, next) => if next = b.size then .ok item else .error .trailingBytes

/-! ## Typed accessors

These mirror how `ethereum_rlp.decode_to` interprets an item as a field of a given type. -/

/-- The item as a byte string. -/
def asBytes (what : String) : Rlp → Except DecodeError ByteArray
  | .bytes b => .ok b
  | .list _ => .error (.unexpected s!"{what}: expected bytes, got list")

/-- The item as a list. -/
def asList (what : String) : Rlp → Except DecodeError (List Rlp)
  | .list l => .ok l
  | .bytes _ => .error (.unexpected s!"{what}: expected list, got bytes")

/-- The item as an unsigned integer of at most `maxBytes` bytes, rejecting leading zeros.
Use `maxBytes := 8` for `U64`, `32` for `U256`, and `uintMaxBytes` for `Uint`. -/
def asNat (what : String) (maxBytes : Nat) (r : Rlp) : Except DecodeError Nat := do
  let b ← asBytes what r
  if byteAt? b 0 = some 0 then throw (.nonCanonical s!"{what}: integer with leading zero")
  if b.size > maxBytes then throw (.unexpected s!"{what}: integer wider than {maxBytes} bytes")
  return Bytes.toNat b

/-- Width bound used for the reference's unbounded `Uint` fields. RLP itself caps payloads
far below this, so it never rejects anything. -/
def uintMaxBytes : Nat := 2 ^ 64

/-- A `U64` field. -/
def asU64 (what : String) (r : Rlp) : Except DecodeError Nat := asNat what 8 r

/-- A `U256` field. -/
def asU256 (what : String) (r : Rlp) : Except DecodeError Nat := asNat what 32 r

/-- A `Uint` (unbounded) field. -/
def asUint (what : String) (r : Rlp) : Except DecodeError Nat := asNat what uintMaxBytes r

/-- A byte string of exactly `n` bytes (`Bytes8`, `Bytes32`, `Hash32`, `Bloom`, …). -/
def asFixed (what : String) (n : Nat) (r : Rlp) : Except DecodeError ByteArray := do
  let b ← asBytes what r
  if b.size = n then return b
  else throw (.unexpected s!"{what}: expected {n} bytes, got {b.size}")

/-- A 32-byte field as a word. -/
def asWord (what : String) (r : Rlp) : Except DecodeError Word := do
  return Bytes.toWord (← asFixed what 32 r)

/-- A 20-byte address field. -/
def asAddress (what : String) (r : Rlp) : Except DecodeError Address := do
  return BitVec.ofNat 160 (Bytes.toNat (← asFixed what 20 r))

/-- A `Bytes0 | Address` recipient field: empty for a contract creation. -/
def asTo (what : String) (r : Rlp) : Except DecodeError (Option Address) := do
  let b ← asBytes what r
  if b.size = 0 then return none
  else if b.size = 20 then return some (BitVec.ofNat 160 (Bytes.toNat b))
  else throw (.unexpected s!"{what}: recipient must be empty or 20 bytes, got {b.size}")

end EvmLean.Rlp
