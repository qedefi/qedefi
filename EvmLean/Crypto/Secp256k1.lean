import EvmLean.Prelude.Bytes

/-!
# secp256k1 public-key recovery, for `ECRECOVER` (precompile `0x01`).
-/

namespace EvmLean.Secp256k1

/-- Group order `n`. -/
def n : Nat := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

/-- Recover the 64-byte uncompressed public key (`x ‖ y`, no `0x04` prefix) from a
32-byte message hash, recovery id `recId ∈ {0, 1}` and signature `(r, s)`.
`none` if the signature is invalid or the point is not on the curve. -/
def recover (hash : ByteArray) (recId : Nat) (r s : Nat) : Option ByteArray := sorry

end EvmLean.Secp256k1
