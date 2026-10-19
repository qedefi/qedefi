import EvmLean.Prelude.Bytes

/-!
# alt_bn128 (BN254) curve operations, for precompiles `0x06`–`0x08` (EIP-196/197).
-/

namespace EvmLean.Bn254

/-- `ECADD`: input is 128 bytes (two points), output 64 bytes; `none` on invalid input. -/
def add (input : ByteArray) : Option ByteArray := sorry

/-- `ECMUL`: input is 96 bytes (point, scalar), output 64 bytes; `none` on invalid input. -/
def mul (input : ByteArray) : Option ByteArray := sorry

/-- `ECPAIRING`: input is a multiple of 192 bytes; `some true` iff the pairing product is
one; `none` on invalid input. -/
def pairingCheck (input : ByteArray) : Option Bool := sorry

end EvmLean.Bn254
