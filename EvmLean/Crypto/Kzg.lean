import EvmLean.Prelude.Bytes
import EvmLean.Crypto.Bls12381.Field
import EvmLean.Crypto.Bls12381.Curve
import EvmLean.Crypto.Bls12381.Pairing

/-!
# KZG point evaluation (EIP-4844), for precompile `0x0a`, over BLS12-381

`verifyProof` is `verify_kzg_proof` (execution-specs `crypto/kzg.py`): accept iff
`e(C − [y]G1, −G2) · e(π, [τ]G2 − [z]G2) = 1`; malformed input gives `none`.
-/

namespace EvmLean.Kzg

open Bls12381

/-- `BLS_MODULUS`: the order of the scalar field, the bound for `z` and `y`. -/
def blsModulus : Nat := R

/-- The pairing equation of `verify_kzg_proof_impl`, on already validated inputs. -/
def verifyProofImpl (commitment : Affine Fp) (z y : Nat) (proof : Affine Fp) : Bool :=
  let xMinusZ := Affine.add tauG2 (Affine.mul g2Gen ((R - z) % R))
  let pMinusY := Affine.add commitment (Affine.mul g1Gen ((R - y) % R))
  pairingCheck [(pMinusY, Affine.neg g2Gen), (proof, xMinusZ)]

/-- Verify that `commitment` opens to `y` at `z`; `none` on malformed input. -/
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
