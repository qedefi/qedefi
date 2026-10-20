import EvmLean.Prelude.Bytes

/-!
# Helpers for the hash tests

Hex decoding and deterministic inputs. Malformed hex decodes to garbage and fails the `#guard`.
-/

namespace EvmTest.HashUtil

/-- Value of one hex digit (garbage for non-hex characters). -/
def hexDigit (c : Char) : UInt8 :=
  if c ≤ '9' then (c.toNat - '0'.toNat).toUInt8
  else if c ≤ 'F' then (c.toNat - 'A'.toNat + 10).toUInt8
  else (c.toNat - 'a'.toNat + 10).toUInt8

def hexList : List Char → List UInt8
  | a :: b :: rest => (hexDigit a * 16 + hexDigit b) :: hexList rest
  | _ => []

/-- Decode a hex string (no `0x` prefix) into bytes. -/
def hex (s : String) : ByteArray := ⟨(hexList s.toList).toArray⟩

/-- The `n` bytes `0, 1, 2, …` (mod 256): a deterministic input of any length. -/
def seq (n : Nat) : ByteArray := ⟨Array.ofFn (n := n) fun i => i.val.toUInt8⟩

def ascii (s : String) : ByteArray := s.toUTF8

def rep (n : Nat) (b : UInt8) : ByteArray := ⟨Array.replicate n b⟩

end EvmTest.HashUtil
