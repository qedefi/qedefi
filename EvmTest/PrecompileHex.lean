import EvmLean.Prelude.Bytes

/-! Hex helpers shared by the precompile test files (`Secp256k1`, `Bn254`, `Precompile`). -/

namespace EvmTest.Precompile
open EvmLean

/-- Value of one hex digit (`0` for non-hex characters, which the vectors never contain). -/
def hexDigit (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Pair up hex digits into bytes. -/
def hexBytes : List Char → List UInt8
  | hi :: lo :: rest => (hexDigit hi * 16 + hexDigit lo).toUInt8 :: hexBytes rest
  | _ => []

/-- Decode a hex string (without `0x`) into bytes. -/
def hex (s : String) : ByteArray := ⟨(hexBytes s.toList).toArray⟩

end EvmTest.Precompile
