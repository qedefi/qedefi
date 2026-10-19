import EvmLean.Prelude.Bytes

/-!
# KZG point evaluation (EIP-4844), for precompile `0x0a`, over BLS12-381.
-/

namespace EvmLean.Kzg

/-- Verify a KZG proof that the polynomial committed to by `commitment` (48 bytes)
evaluates to `y` at `z` (32-byte field elements), with a 48-byte `proof`.
`none` on malformed input (non-canonical field elements, invalid points). -/
def verifyProof (commitment z y proof : ByteArray) : Option Bool := sorry

end EvmLean.Kzg
