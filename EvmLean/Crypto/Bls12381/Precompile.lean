import EvmLean.Prelude.Bytes
import EvmLean.Crypto.Bls12381.Curve
import EvmLean.Crypto.Bls12381.Pairing
import EvmLean.Crypto.Bls12381.HashToCurve

/-!
# EIP-2537 BLS12-381 precompiles: byte-level operations

Mirrors `prague/vm/precompiled_contracts/bls12_381/`; `none` means invalid input. `𝔽ₚ` is 64
bytes big-endian `< p`; the all-zero point is infinity. `ADD` does no subgroup check, `MSM` and
`PAIRING` check every point; `MSM` scalars are not reduced. Gas lives in `Precompile.lean`.
-/

namespace EvmLean.Bls12381

/-! ## Encoding -/

/-- Decode the 64-byte `𝔽ₚ` element at `off` (`bytes_to_fq`); caller ensures `off + 64 ≤ size`. -/
def decodeFp (b : ByteArray) (off : Nat) : Option Fp :=
  let n := Bytes.toNat (b.extract off (off + 64))
  if n < P then some ⟨n⟩ else none

/-- Decode the 128-byte `𝔽ₚ²` element `c0 ‖ c1` at `off` (`bytes_to_fq2`). -/
def decodeFp2 (b : ByteArray) (off : Nat) : Option Fp2 := do
  let c0 ← decodeFp b off
  let c1 ← decodeFp b (off + 64)
  pure ⟨c0, c1⟩

/-- Decode the 128-byte `G1` point at `off` (`bytes_to_g1`, on-curve check only). -/
def decodeG1 (b : ByteArray) (off : Nat) : Option (Affine Fp) := do
  let x ← decodeFp b off
  let y ← decodeFp b (off + 64)
  if x.isZero && y.isZero then pure .infinity
  else
    let pt := Affine.point x y
    if pt.isOnCurve b1 then pure pt else none

/-- Decode the 256-byte `G2` point at `off` (`bytes_to_g2`, on-curve check only). -/
def decodeG2 (b : ByteArray) (off : Nat) : Option (Affine Fp2) := do
  let x ← decodeFp2 b off
  let y ← decodeFp2 b (off + 128)
  if x.isZero && y.isZero then pure .infinity
  else
    let pt := Affine.point x y
    if pt.isOnCurve b2 then pure pt else none

/-- Keep a point only if it is in the order-`r` subgroup (`is_inf(multiply(p, curve_order))`). -/
def subgroupChecked {α : Type} [FieldOps α] [DecidableEq α] (p : Affine α) : Option (Affine α) :=
  if p.inSubgroup then some p else none

/-- Encode an `𝔽ₚ` element as 64 big-endian bytes. -/
def encodeFp (a : Fp) : ByteArray := Bytes.ofNatBE 64 a.val

/-- Encode a `G1` point (`g1_to_bytes`); infinity is 128 zero bytes. -/
def encodeG1 : Affine Fp → ByteArray
  | .infinity => Bytes.zeros 128
  | .point x y => encodeFp x ++ encodeFp y

/-- Encode a `G2` point (`g2_to_bytes`); infinity is 256 zero bytes. -/
def encodeG2 : Affine Fp2 → ByteArray
  | .infinity => Bytes.zeros 256
  | .point x y => encodeFp x.c0 ++ encodeFp x.c1 ++ encodeFp y.c0 ++ encodeFp y.c1

/-! ## The operations -/

/-- `BLS12_G1ADD` (`0x0b`): two `G1` points (no subgroup check) to their sum. -/
def g1AddBytes (input : ByteArray) : Option ByteArray :=
  if input.size ≠ 256 then none
  else do
    let p ← decodeG1 input 0
    let q ← decodeG1 input 128
    pure (encodeG1 (Affine.add p q))

/-- `BLS12_G2ADD` (`0x0d`): two `G2` points (no subgroup check) to their sum. -/
def g2AddBytes (input : ByteArray) : Option ByteArray :=
  if input.size ≠ 512 then none
  else do
    let p ← decodeG2 input 0
    let q ← decodeG2 input 256
    pure (encodeG2 (Affine.add p q))

/-- Naive MSM `Σ [mᵢ] Pᵢ` over `k` records of `stride` bytes (point ‖ 32-byte scalar). -/
def msm {α : Type} [FieldOps α] [DecidableEq α] (decode : ByteArray → Nat → Option (Affine α))
    (stride : Nat) (input : ByteArray) (k : Nat) : Option (Affine α) := do
  let acc ← (List.range k).foldlM (init := (Jac.infinity : Jac α)) fun acc i => do
    let off := stride * i
    let p ← subgroupChecked (← decode input off)
    let m := Bytes.toNat (input.extract (off + stride - 32) (off + stride))
    pure (Jac.add acc (Jac.mul (Jac.ofAffine p) m))
  pure acc.toAffine

/-- `BLS12_G1MSM` (`0x0c`): `k ≥ 1` records of 160 bytes. -/
def g1MsmBytes (input : ByteArray) : Option ByteArray :=
  if input.size = 0 || input.size % 160 ≠ 0 then none
  else (msm decodeG1 160 input (input.size / 160)).map encodeG1

/-- `BLS12_G2MSM` (`0x0e`): `k ≥ 1` records of 288 bytes. -/
def g2MsmBytes (input : ByteArray) : Option ByteArray :=
  if input.size = 0 || input.size % 288 ≠ 0 then none
  else (msm decodeG2 288 input (input.size / 288)).map encodeG2

/-- `BLS12_PAIRING_CHECK` (`0x0f`): `some true` iff `∏ e(Pᵢ, Qᵢ) = 1` (shared final exp). -/
def pairingCheckBytes (input : ByteArray) : Option Bool :=
  if input.size = 0 || input.size % 384 ≠ 0 then none
  else do
    let pairs ← (List.range (input.size / 384)).mapM fun i => do
      let p ← subgroupChecked (← decodeG1 input (384 * i))
      let q ← subgroupChecked (← decodeG2 input (384 * i + 128))
      pure (p, q)
    pure (pairingCheck pairs)

/-- `BLS12_MAP_FP_TO_G1` (`0x10`): a 64-byte `𝔽ₚ` element to a `G1` point. -/
def mapFpToG1Bytes (input : ByteArray) : Option ByteArray :=
  if input.size ≠ 64 then none
  else (decodeFp input 0).map fun t => encodeG1 (mapFpToG1 t)

/-- `BLS12_MAP_FP2_TO_G2` (`0x11`): a 128-byte `𝔽ₚ²` element to a `G2` point. -/
def mapFp2ToG2Bytes (input : ByteArray) : Option ByteArray :=
  if input.size ≠ 128 then none
  else do
    let t ← decodeFp2 input 0
    let q ← mapFp2ToG2 t
    pure (encodeG2 q)

end EvmLean.Bls12381
