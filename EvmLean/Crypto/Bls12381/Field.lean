/-!
# BLS12-381 field tower

The base field `𝔽ₚ` of BLS12-381 and the extension tower used by the pairing:

* `Fp2  = 𝔽ₚ[u] / (u² + 1)`
* `Fp6  = Fp2[v] / (v³ − ξ)` with `ξ = u + 1`
* `Fp12 = Fp6[w] / (w² − v)`

This is the tower of the IETF pairing-friendly-curves draft, zkcrypto/bls12_381 and blst.
(py_ecc instead represents `𝔽ₚ¹²` as a degree-12 polynomial ring; the two are isomorphic and
the pairing-check result does not depend on the representation.)

Elements are plain `Nat`s kept reduced modulo `p`. `Nat` arithmetic is GMP-backed at runtime,
and inversion uses Fermat's little theorem through `Nat.powMod`, so everything here is plain,
total Lean that the kernel can also unfold.

`FieldOps` is a small interface (zero, one, inverse, zero test) that lets the curve code in
`Curve.lean` be written once for `Fp` (the group `G1`) and `Fp2` (the twist group `G2`).
-/

namespace EvmLean.Bls12381

/-- The BLS12-381 base field modulus `p` (381 bits). -/
def P : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- The order `r` of the groups `G1`, `G2`, `GT` (255 bits); `BLS_MODULUS` in EIP-4844. -/
def R : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- The operations the generic curve code needs from a field. -/
class FieldOps (α : Type) extends Add α, Sub α, Mul α, Neg α where
  /-- The additive identity. -/
  zero : α
  /-- The multiplicative identity. -/
  one : α
  /-- Is this element zero? -/
  isZero : α → Bool
  /-- The multiplicative inverse (the inverse of zero is zero). -/
  inv : α → α

/-! ## The base field `𝔽ₚ` -/

/-- An element of `𝔽ₚ`, represented by its canonical residue `val < p`. All operations below
preserve that invariant, so the derived equality is field equality. -/
structure Fp where
  /-- The canonical residue in `[0, p)`. -/
  val : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Fp

/-- Reduce a natural number into `𝔽ₚ`. -/
def ofNat (n : Nat) : Fp := ⟨n % P⟩

/-- Zero. -/
def zero : Fp := ⟨0⟩

/-- One. -/
def one : Fp := ⟨1⟩

/-- Addition modulo `p` (one conditional subtraction, no division). -/
protected def add (a b : Fp) : Fp :=
  let s := a.val + b.val
  if s < P then ⟨s⟩ else ⟨s - P⟩

/-- Subtraction modulo `p`. -/
protected def sub (a b : Fp) : Fp :=
  if b.val ≤ a.val then ⟨a.val - b.val⟩ else ⟨a.val + P - b.val⟩

/-- Negation modulo `p`. -/
protected def neg (a : Fp) : Fp :=
  if a.val = 0 then a else ⟨P - a.val⟩

/-- Multiplication modulo `p`. -/
protected def mul (a b : Fp) : Fp := ⟨a.val * b.val % P⟩

/-- `a ^ e` by `Nat.powMod`. -/
def pow (a : Fp) (e : Nat) : Fp := ⟨Nat.powMod a.val e P⟩

/-- Inverse by Fermat, `a⁻¹ = a ^ (p − 2)`; the inverse of zero is zero. -/
def inv (a : Fp) : Fp := a.pow (P - 2)

/-- Is this element zero? -/
def isZero (a : Fp) : Bool := a.val == 0

/-- Candidate square root `a ^ ((p + 1) / 4)`, valid because `p ≡ 3 (mod 4)`. It is a square
root of `a` exactly when `a` is a square; callers must check `sqrt a * sqrt a = a`. -/
def sqrtCandidate (a : Fp) : Fp := a.pow ((P + 1) / 4)

/-- `y` is the "lexicographically largest" of `±y`, i.e. `y > (p − 1) / 2`. This is the sign
convention of the ZCash point compression used by Ethereum (`(y * 2) // q` in py_ecc). -/
def isLargest (a : Fp) : Bool := decide (a.val * 2 ≥ P)

/-- `𝔽ₚ` addition. -/
instance : Add Fp := ⟨Fp.add⟩
/-- `𝔽ₚ` subtraction. -/
instance : Sub Fp := ⟨Fp.sub⟩
/-- `𝔽ₚ` multiplication. -/
instance : Mul Fp := ⟨Fp.mul⟩
/-- `𝔽ₚ` negation. -/
instance : Neg Fp := ⟨Fp.neg⟩

/-- `𝔽ₚ` as a `FieldOps`. -/
instance : FieldOps Fp where
  zero := zero
  one := one
  isZero := isZero
  inv := inv

end Fp

/-! ## `Fp2 = 𝔽ₚ[u]/(u² + 1)` -/

/-- An element `c0 + c1·u` of `𝔽ₚ²`, with `u² = −1`. -/
structure Fp2 where
  /-- The real coefficient. -/
  c0 : Fp
  /-- The coefficient of `u`. -/
  c1 : Fp
  deriving DecidableEq, Repr, Inhabited

namespace Fp2

/-- Zero. -/
def zero : Fp2 := ⟨Fp.zero, Fp.zero⟩

/-- One. -/
def one : Fp2 := ⟨Fp.one, Fp.zero⟩

/-- Embed `𝔽ₚ` into `𝔽ₚ²`. -/
def ofFp (a : Fp) : Fp2 := ⟨a, Fp.zero⟩

/-- Component-wise addition. -/
protected def add (a b : Fp2) : Fp2 := ⟨a.c0 + b.c0, a.c1 + b.c1⟩

/-- Component-wise subtraction. -/
protected def sub (a b : Fp2) : Fp2 := ⟨a.c0 - b.c0, a.c1 - b.c1⟩

/-- Component-wise negation. -/
protected def neg (a : Fp2) : Fp2 := ⟨-a.c0, -a.c1⟩

/-- `(a0 + a1 u)(b0 + b1 u) = (a0 b0 − a1 b1) + (a0 b1 + a1 b0) u`, with one reduction per
coefficient (lazy reduction: the unreduced products are combined first). -/
protected def mul (a b : Fp2) : Fp2 :=
  let t0 := a.c0.val * b.c0.val
  let t1 := a.c1.val * b.c1.val
  -- `t1 < p²`, so adding `p²` keeps the real part non-negative before reducing.
  ⟨⟨(t0 + P * P - t1) % P⟩, ⟨(a.c0.val * b.c1.val + a.c1.val * b.c0.val) % P⟩⟩

/-- Squaring: `(a0 + a1 u)² = (a0 + a1)(a0 − a1) + 2 a0 a1 u`. -/
def sq (a : Fp2) : Fp2 :=
  ⟨(a.c0 + a.c1) * (a.c0 - a.c1), ⟨2 * a.c0.val * a.c1.val % P⟩⟩

/-- Multiply by `ξ = 1 + u`: `(a0 + a1 u)(1 + u) = (a0 − a1) + (a0 + a1) u`. -/
def mulXi (a : Fp2) : Fp2 := ⟨a.c0 - a.c1, a.c0 + a.c1⟩

/-- Multiply by a base-field scalar. -/
def mulFp (a : Fp2) (s : Fp) : Fp2 := ⟨a.c0 * s, a.c1 * s⟩

/-- Conjugation `a0 − a1 u`, which is the Frobenius map `a ↦ aᵖ`. -/
def conj (a : Fp2) : Fp2 := ⟨a.c0, -a.c1⟩

/-- Inverse: `(a0 + a1 u)⁻¹ = (a0 − a1 u) / (a0² + a1²)`; the inverse of zero is zero. -/
def inv (a : Fp2) : Fp2 :=
  let t := Fp.inv ⟨(a.c0.val * a.c0.val + a.c1.val * a.c1.val) % P⟩
  ⟨a.c0 * t, -(a.c1 * t)⟩

/-- Is this element zero? -/
def isZero (a : Fp2) : Bool := a.c0.isZero && a.c1.isZero

/-- `a ^ e` by square-and-multiply over the bits of `e` (least significant first). -/
def pow (a : Fp2) (e : Nat) : Fp2 :=
  if _h : e = 0 then one
  else
    let r := pow (sq a) (e / 2)
    if e % 2 = 1 then Fp2.mul r a else r
termination_by e
decreasing_by omega

/-- The sign of an `𝔽ₚ²` element in the ZCash compression convention: the sign of `c1`, or of
`c0` when `c1 = 0` (py_ecc `compress_G2`). -/
def isLargest (a : Fp2) : Bool :=
  if a.c1.isZero then a.c0.isLargest else a.c1.isLargest

/-- `𝔽ₚ²` addition. -/
instance : Add Fp2 := ⟨Fp2.add⟩
/-- `𝔽ₚ²` subtraction. -/
instance : Sub Fp2 := ⟨Fp2.sub⟩
/-- `𝔽ₚ²` multiplication. -/
instance : Mul Fp2 := ⟨Fp2.mul⟩
/-- `𝔽ₚ²` negation. -/
instance : Neg Fp2 := ⟨Fp2.neg⟩

/-- `𝔽ₚ²` as a `FieldOps`. -/
instance : FieldOps Fp2 where
  zero := zero
  one := one
  isZero := isZero
  inv := inv

end Fp2

/-! ## `Fp6 = Fp2[v]/(v³ − ξ)` -/

/-- An element `c0 + c1·v + c2·v²` of `𝔽ₚ⁶`, with `v³ = ξ = 1 + u`. -/
structure Fp6 where
  /-- The constant coefficient. -/
  c0 : Fp2
  /-- The coefficient of `v`. -/
  c1 : Fp2
  /-- The coefficient of `v²`. -/
  c2 : Fp2
  deriving DecidableEq, Repr, Inhabited

namespace Fp6

/-- Zero. -/
def zero : Fp6 := ⟨Fp2.zero, Fp2.zero, Fp2.zero⟩

/-- One. -/
def one : Fp6 := ⟨Fp2.one, Fp2.zero, Fp2.zero⟩

/-- Component-wise addition. -/
protected def add (a b : Fp6) : Fp6 := ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩

/-- Component-wise subtraction. -/
protected def sub (a b : Fp6) : Fp6 := ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2⟩

/-- Component-wise negation. -/
protected def neg (a : Fp6) : Fp6 := ⟨-a.c0, -a.c1, -a.c2⟩

/-- Karatsuba multiplication (6 `Fp2` products), reducing `v³ = ξ`. -/
protected def mul (a b : Fp6) : Fp6 :=
  let v0 := a.c0 * b.c0
  let v1 := a.c1 * b.c1
  let v2 := a.c2 * b.c2
  ⟨v0 + Fp2.mulXi ((a.c1 + a.c2) * (b.c1 + b.c2) - v1 - v2),
   (a.c0 + a.c1) * (b.c0 + b.c1) - v0 - v1 + Fp2.mulXi v2,
   (a.c0 + a.c2) * (b.c0 + b.c2) - v0 - v2 + v1⟩

/-- Multiply by `v`: `(c0 + c1 v + c2 v²) v = ξ c2 + c0 v + c1 v²`. -/
def mulV (a : Fp6) : Fp6 := ⟨Fp2.mulXi a.c2, a.c0, a.c1⟩

/-- Multiply every coefficient by an `Fp2` scalar. -/
def mulFp2 (a : Fp6) (s : Fp2) : Fp6 := ⟨a.c0 * s, a.c1 * s, a.c2 * s⟩

/-- Inverse via the norm to `Fp2` (the inverse of zero is zero). -/
def inv (a : Fp6) : Fp6 :=
  let A := Fp2.sq a.c0 - Fp2.mulXi (a.c1 * a.c2)
  let B := Fp2.mulXi (Fp2.sq a.c2) - a.c0 * a.c1
  let C := Fp2.sq a.c1 - a.c0 * a.c2
  let F := a.c0 * A + Fp2.mulXi (a.c2 * B + a.c1 * C)
  let t := Fp2.inv F
  ⟨A * t, B * t, C * t⟩

/-- `𝔽ₚ⁶` addition. -/
instance : Add Fp6 := ⟨Fp6.add⟩
/-- `𝔽ₚ⁶` subtraction. -/
instance : Sub Fp6 := ⟨Fp6.sub⟩
/-- `𝔽ₚ⁶` multiplication. -/
instance : Mul Fp6 := ⟨Fp6.mul⟩
/-- `𝔽ₚ⁶` negation. -/
instance : Neg Fp6 := ⟨Fp6.neg⟩

end Fp6

/-! ## `Fp12 = Fp6[w]/(w² − v)` -/

/-- An element `c0 + c1·w` of `𝔽ₚ¹²`, with `w² = v` (so `w⁶ = ξ`). -/
structure Fp12 where
  /-- The constant coefficient. -/
  c0 : Fp6
  /-- The coefficient of `w`. -/
  c1 : Fp6
  deriving DecidableEq, Repr, Inhabited

namespace Fp12

/-- One. -/
def one : Fp12 := ⟨Fp6.one, Fp6.zero⟩

/-- Karatsuba multiplication (3 `Fp6` products), reducing `w² = v`. -/
protected def mul (a b : Fp12) : Fp12 :=
  let t0 := a.c0 * b.c0
  let t1 := a.c1 * b.c1
  ⟨t0 + Fp6.mulV t1, (a.c0 + a.c1) * (b.c0 + b.c1) - t0 - t1⟩

/-- Squaring with 2 `Fp6` products:
`(a + b w)² = (a + b)(a + v b) − a b − v a b + 2 a b w`. -/
def sq (a : Fp12) : Fp12 :=
  let ab := a.c0 * a.c1
  ⟨(a.c0 + a.c1) * (a.c0 + Fp6.mulV a.c1) - ab - Fp6.mulV ab, ab + ab⟩

/-- Conjugation `c0 − c1 w`, which is the Frobenius power `a ↦ a^(p⁶)`. -/
def conj (a : Fp12) : Fp12 := ⟨a.c0, -a.c1⟩

/-- Inverse: `(a + b w)⁻¹ = (a − b w) / (a² − v b²)`; the inverse of zero is zero. -/
def inv (a : Fp12) : Fp12 :=
  let t := Fp6.inv (a.c0 * a.c0 - Fp6.mulV (a.c1 * a.c1))
  ⟨a.c0 * t, -(a.c1 * t)⟩

/-- `𝔽ₚ¹²` multiplication. -/
instance : Mul Fp12 := ⟨Fp12.mul⟩

/-- `a ^ e` by square-and-multiply over the bits of `e` (least significant first). -/
def pow (a : Fp12) (e : Nat) : Fp12 :=
  if _h : e = 0 then one
  else
    let r := pow (sq a) (e / 2)
    if e % 2 = 1 then r * a else r
termination_by e
decreasing_by omega

end Fp12

end EvmLean.Bls12381
