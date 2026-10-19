import EvmLean.Prelude.Bytes

/-!
# RLP encoding

Recursive Length Prefix encoding, needed for `CREATE` address derivation and for
transaction / log hashing in the conformance harness.
-/

namespace EvmLean

/-- An RLP item: a byte string or a list of items. -/
inductive Rlp where
  /-- A byte string. -/
  | bytes (b : ByteArray)
  /-- A list of items. -/
  | list (items : List Rlp)
  deriving Inhabited

namespace Rlp

/-- An unsigned integer as a minimal big-endian byte string. -/
def nat (n : Nat) : Rlp := .bytes (Bytes.ofNatMinimal n)

/-- Length prefix: `offset + len` for short payloads, else `offset + 55 + |len|` then `len`. -/
def lengthPrefix (offset len : Nat) : ByteArray :=
  if len < 56 then ⟨#[(offset + len).toUInt8]⟩
  else
    let lenBytes := Bytes.ofNatMinimal len
    ⟨#[(offset + 55 + lenBytes.size).toUInt8]⟩ ++ lenBytes

mutual
/-- Encode an RLP item. -/
def encode : Rlp → ByteArray
  | .bytes b =>
    if h : b.size = 1 then
      if b[0]'(by omega) < 0x80 then b else lengthPrefix 0x80 1 ++ b
    else lengthPrefix 0x80 b.size ++ b
  | .list items =>
    let payload := encodeList items
    lengthPrefix 0xc0 payload.size ++ payload

/-- Concatenated encodings of a list of items. -/
def encodeList : List Rlp → ByteArray
  | [] => .empty
  | x :: xs => encode x ++ encodeList xs
end

end Rlp

end EvmLean
