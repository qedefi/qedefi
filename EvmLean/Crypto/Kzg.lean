import EvmLean.Prelude.Bytes
import EvmLean.Crypto.Bls12381.Field
import EvmLean.Crypto.Bls12381.Curve
import EvmLean.Crypto.Bls12381.Pairing

/-!
# KZG point evaluation (EIP-4844), for precompile `0x0a`, over BLS12-381.

`verifyProof` is `verify_kzg_proof` of the Deneb consensus specs
(`polynomial-commitments.md`), as implemented in execution-specs `crypto/kzg.py`:

1. Inputs must be 48/32/32/48 bytes; `z` and `y` must be canonical scalars (`< r`);
   `commitment` and `proof` must be valid compressed `G1` points (the point at infinity is
   allowed). Otherwise the result is `none` (the precompile then fails).
2. The proof is accepted iff `e(C − [y]G1, −G2) · e(π, [τ]G2 − [z]G2) = 1`, i.e. the
   committed polynomial `p` satisfies `p(X) − y = q(X)(X − z)` with `π = [q(τ)]G1`.

All BLS12-381 arithmetic lives in `EvmLean/Crypto/Bls12381/`.
-/

namespace EvmLean.Kzg

open Bls12381

/-- `BLS_MODULUS`: the order of the scalar field, the bound for `z` and `y`. -/
def blsModulus : Nat := R

/-- The pairing equation of `verify_kzg_proof_impl`, on already validated inputs:
`e(C − [y]G1, −G2) · e(π, [τ]G2 − [z]G2) = 1`. -/
def verifyProofImpl (commitment : Affine Fp) (z y : Nat) (proof : Affine Fp) : Bool :=
  let xMinusZ := Affine.add tauG2 (Affine.mul g2Gen ((R - z) % R))
  let pMinusY := Affine.add commitment (Affine.mul g1Gen ((R - y) % R))
  pairingCheck [(pMinusY, Affine.neg g2Gen), (proof, xMinusZ)]

/-- Verify a KZG proof that the polynomial committed to by `commitment` (48 bytes)
evaluates to `y` at `z` (32-byte field elements), with a 48-byte `proof`.
`none` on malformed input (non-canonical field elements, invalid points). -/
def verifyProof (commitment z y proof : ByteArray) : Option Bool :=
  if commitment.size ≠ 48 || z.size ≠ 32 || y.size ≠ 32 || proof.size ≠ 48 then none
  else
    let zv := Bytes.toNat z
    let yv := Bytes.toNat y
    if zv ≥ blsModulus || yv ≥ blsModulus then none
    else do
      let c ← decompressG1 commitment
      let pi ← decompressG1 proof
      some (verifyProofImpl c zv yv pi)

end EvmLean.Kzg
