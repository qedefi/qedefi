import EvmLean.Crypto.Bls12381.Field
import EvmLean.Prelude.Bytes

/-!
# BLS12-381 curve groups `G1` and `G2`

* `G1 ⊂ E(𝔽ₚ)`,   `E  : y² = x³ + 4`
* `G2 ⊂ E'(𝔽ₚ²)`, `E' : y² = x³ + 4(1 + u)` (the M-type sextic twist)

Points are handled in two forms. `Affine α` is the user-facing form (with an explicit point at
infinity). `Jac α` holds Jacobian coordinates `(X, Y, Z) ↦ (X/Z², Y/Z³)` and is used for scalar
multiplication so that no field inversion is needed per step. The group law is written once,
generically over `FieldOps`, for curves `y² = x³ + b` (`a = 0`), using the standard
`dbl-2009-l` / `add-2007-bl` formulas from the Explicit-Formulas Database.

Also here: ZCash-format compressed `G1` decoding with all the checks that EIP-4844's
`validate_kzg_g1` / py_ecc `pubkey_to_G1` + `KeyValidate` perform, and the generator and
trusted-setup constants.
-/

namespace EvmLean.Bls12381

open FieldOps

/-- A curve point in affine coordinates, or the point at infinity. -/
inductive Affine (α : Type) where
  /-- The point at infinity (the group identity). -/
  | infinity
  /-- The affine point `(x, y)`. -/
  | point (x y : α)
  deriving DecidableEq, Repr, Inhabited

/-- A curve point in Jacobian coordinates, representing `(X/Z², Y/Z³)`; `Z = 0` is the point
at infinity. -/
structure Jac (α : Type) where
  /-- `X = x·Z²`. -/
  x : α
  /-- `Y = y·Z³`. -/
  y : α
  /-- The projective scaling coordinate. -/
  z : α

namespace Jac

variable {α : Type} [FieldOps α]

/-- The point at infinity. -/
def infinity : Jac α := ⟨one, one, zero⟩

/-- Is this the point at infinity? -/
def isInfinity (p : Jac α) : Bool := isZero p.z

/-- Lift an affine point. -/
def ofAffine : Affine α → Jac α
  | .infinity => infinity
  | .point x y => ⟨x, y, one⟩

/-- Convert back to affine coordinates (one field inversion). -/
def toAffine (p : Jac α) : Affine α :=
  if isZero p.z then .infinity
  else
    let zi := inv p.z
    let zi2 := zi * zi
    .point (p.x * zi2) (p.y * zi2 * zi)

/-- Negation `(X, Y, Z) ↦ (X, −Y, Z)`. -/
def neg (p : Jac α) : Jac α := ⟨p.x, -p.y, p.z⟩

/-- Point doubling on `y² = x³ + b` (EFD `dbl-2009-l`; independent of `b`). -/
def double (p : Jac α) : Jac α :=
  if isZero p.z then p
  else
    let a := p.x * p.x
    let b := p.y * p.y
    let c := b * b
    let t := p.x + b
    let d0 := t * t - a - c
    let d := d0 + d0
    let e := a + a + a
    let f := e * e
    let x3 := f - d - d
    let c2 := c + c
    let c4 := c2 + c2
    let c8 := c4 + c4
    let y3 := e * (d - x3) - c8
    let yz := p.y * p.z
    ⟨x3, y3, yz + yz⟩

/-- Point addition (EFD `add-2007-bl`), falling back to `double` when the inputs are equal and
returning infinity when they are opposite. -/
def add (p q : Jac α) : Jac α :=
  if isZero p.z then q
  else if isZero q.z then p
  else
    let z1z1 := p.z * p.z
    let z2z2 := q.z * q.z
    let u1 := p.x * z2z2
    let u2 := q.x * z1z1
    let s1 := p.y * q.z * z2z2
    let s2 := q.y * p.z * z1z1
    let h := u2 - u1
    let r := s2 - s1
    if isZero h then
      if isZero r then double p else infinity
    else
      let hh := h * h
      let hhh := h * hh
      let v := u1 * hh
      let x3 := r * r - hhh - v - v
      let y3 := r * (v - x3) - s1 * hhh
      ⟨x3, y3, p.z * q.z * h⟩

/-- Scalar multiplication `[k] p` by double-and-add over the bits of `k`, most significant
first (`k = 0` gives infinity). -/
def mul (p : Jac α) (k : Nat) : Jac α :=
  if _h : k = 0 then infinity
  else
    let r := double (mul p (k / 2))
    if k % 2 = 1 then add r p else r
termination_by k
decreasing_by omega

end Jac

namespace Affine

variable {α : Type} [FieldOps α] [DecidableEq α]

/-- Negation. -/
def neg : Affine α → Affine α
  | .infinity => .infinity
  | .point x y => .point x (-y)

/-- Is the point on `y² = x³ + b`? (Infinity is.) -/
def isOnCurve (b : α) : Affine α → Bool
  | .infinity => true
  | .point x y => decide (y * y = x * x * x + b)

/-- Is `p` in the order-`r` subgroup, i.e. `[r] p = ∞`? This is the subgroup check of
py_ecc's `KeyValidate` (`subgroup_check`). -/
def inSubgroup (p : Affine α) : Bool := (Jac.mul (Jac.ofAffine p) R).isInfinity

/-- Scalar multiplication `[k] p`. -/
def mul (p : Affine α) (k : Nat) : Affine α := (Jac.mul (Jac.ofAffine p) k).toAffine

/-- Point addition. -/
def add (p q : Affine α) : Affine α := (Jac.add (Jac.ofAffine p) (Jac.ofAffine q)).toAffine

end Affine

/-- The `b` coefficient of `E : y² = x³ + 4`. -/
def b1 : Fp := ⟨4⟩

/-- The `b` coefficient of the twist `E' : y² = x³ + 4(1 + u)`. -/
def b2 : Fp2 := ⟨⟨4⟩, ⟨4⟩⟩

/-- The standard generator of `G1` (py_ecc `G1`, consensus-specs `G1_POINT`). -/
def g1Gen : Affine Fp :=
  .point
    ⟨0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb⟩
    ⟨0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1⟩

/-- The standard generator of `G2` (py_ecc `G2`; its compression is `KZG_SETUP_G2[0]`). -/
def g2Gen : Affine Fp2 :=
  .point
    ⟨⟨0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8⟩,
     ⟨0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e⟩⟩
    ⟨⟨0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801⟩,
     ⟨0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be⟩⟩

/-- `[τ] G2` from the mainnet KZG ceremony: `KZG_SETUP_G2_MONOMIAL[1]`, whose compressed form
is `KZG_SETUP_G2_MONOMIAL_1` in execution-specs `crypto/kzg.py` (and line 2 of the G2 section
of c-kzg-4844's `trusted_setup.txt`):
`b5bfd7dd…a20c1def2`. Stored decompressed so no `𝔽ₚ²` square root is needed at runtime;
the test suite checks that it lies on the twist, is in `G2`, and compresses to those bytes. -/
def tauG2 : Affine Fp2 :=
  .point
    ⟨⟨0x185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2⟩,
     ⟨0x15bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72⟩⟩
    ⟨⟨0x014353bdb96b626dd7d5ee8599d1fca2131569490e28de18e82451a496a9c9794ce26d105941f383ee689bfbbb832a99⟩,
     ⟨0x1666c54b0a32529503432fcae0181b4bef79de09fc63671fda5ed1ba9bfa07899495346f3d7ac9cd23048ef30d0a154f⟩⟩

/-- `2³⁸¹`: the three top bits of a 48-byte compressed point are flags, the rest is `x`. -/
def pow2_381 : Nat := 1 <<< 381

/-- Decode a 48-byte ZCash-format compressed `G1` point, as py_ecc `decompress_G1`, followed
by the subgroup check of `KeyValidate`. Mirrors `validate_kzg_g1` + `pubkey_to_G1` in
execution-specs `crypto/kzg.py` (which accept the point at infinity).

`none` when: the length is not 48; the compression flag (bit 383) is clear; the infinity flag
(bit 382) disagrees with whether the 381 low bits are all zero; the infinity flag is set
together with the sign flag (bit 381); `x ≥ p`; `x³ + 4` is not a square (not on the curve);
or the point is not in the order-`r` subgroup. -/
def decompressG1 (bytes : ByteArray) : Option (Affine Fp) :=
  if bytes.size ≠ 48 then none
  else
    let z := Bytes.toNat bytes
    let cFlag := z.testBit 383
    let infFlag := z.testBit 382
    let signFlag := z.testBit 381
    let x := z % pow2_381
    if !cFlag then none
    else if infFlag then
      if signFlag || x ≠ 0 then none else some .infinity
    else if x = 0 || x ≥ P then none
    else
      let xf : Fp := ⟨x⟩
      let rhs := xf * xf * xf + b1
      let y0 := rhs.sqrtCandidate
      if y0 * y0 ≠ rhs then none
      else
        let y := if y0.isLargest == signFlag then y0 else -y0
        let pt : Affine Fp := .point xf y
        if pt.inSubgroup then some pt else none

end EvmLean.Bls12381
