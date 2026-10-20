/-!
# secp256r1 (NIST P-256) ECDSA verification, for EIP-7951 `P256VERIFY`

Mirrors `p256verify` + `secp256r1_verify` (SEC 1 §4.1.4, pre-hashed digest). Since `a = −3`,
points use Jacobian coordinates with EFD `dbl-2001-b` doubling and `add-2007-bl` addition.
-/

namespace EvmLean.P256

/-- The field modulus `p` (`SECP256R1P`). -/
def p : Nat := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

/-- The group order `n` (`SECP256R1N`). -/
def n : Nat := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

/-- The curve coefficient `b` (`SECP256R1B`); `a = −3` (`SECP256R1A = p − 3`). -/
def b : Nat := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

/-- `x` of the standard base point `G` (SEC 2). -/
def gx : Nat := 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296

/-- `y` of the standard base point `G` (SEC 2). -/
def gy : Nat := 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5

/-! ## Field arithmetic mod `p` (arguments are reduced) -/

/-- Addition mod `p`. -/
def fadd (x y : Nat) : Nat := (x + y) % p

/-- Subtraction mod `p`. -/
def fsub (x y : Nat) : Nat := (x + p - y) % p

/-- Multiplication mod `p`. -/
def fmul (x y : Nat) : Nat := x * y % p

/-- Inverse mod `p` by Fermat (`0` maps to `0`). -/
def finv (x : Nat) : Nat := Nat.powMod x (p - 2) p

/-- Is `(x, y)` on `y² = x³ − 3x + b`? Mirrors `is_on_curve_secp256r1` (inputs `< p`). -/
def isOnCurve (x y : Nat) : Bool :=
  y * y % p == (x * x * x + (p - 3) * x + b) % p

/-! ## Jacobian points -/

/-- A point in Jacobian coordinates `(X/Z², Y/Z³)`; `Z = 0` is the point at infinity. -/
structure Jac where
  /-- `X = x·Z²`. -/
  x : Nat
  /-- `Y = y·Z³`. -/
  y : Nat
  /-- The scaling coordinate. -/
  z : Nat

namespace Jac

/-- The point at infinity. -/
def infinity : Jac := ⟨1, 1, 0⟩

/-- Doubling for `a = −3` (EFD `dbl-2001-b`). -/
def double (q : Jac) : Jac :=
  if q.z = 0 then q
  else
    let delta := fmul q.z q.z
    let gamma := fmul q.y q.y
    let beta := fmul q.x gamma
    let alpha := fmul 3 (fmul (fsub q.x delta) (fadd q.x delta))
    let x3 := fsub (fmul alpha alpha) (fmul 8 beta)
    let yz := fadd q.y q.z
    let z3 := fsub (fsub (fmul yz yz) gamma) delta
    let y3 := fsub (fmul alpha (fsub (fmul 4 beta) x3)) (fmul 8 (fmul gamma gamma))
    ⟨x3, y3, z3⟩

/-- Addition (EFD `add-2007-bl`), handling the doubling and inverse cases. -/
def add (q₁ q₂ : Jac) : Jac :=
  if q₁.z = 0 then q₂
  else if q₂.z = 0 then q₁
  else
    let z1z1 := fmul q₁.z q₁.z
    let z2z2 := fmul q₂.z q₂.z
    let u1 := fmul q₁.x z2z2
    let u2 := fmul q₂.x z1z1
    let s1 := fmul (fmul q₁.y q₂.z) z2z2
    let s2 := fmul (fmul q₂.y q₁.z) z1z1
    let h := fsub u2 u1
    let r := fsub s2 s1
    if h = 0 then
      if r = 0 then double q₁ else infinity
    else
      let hh := fmul h h
      let hhh := fmul h hh
      let v := fmul u1 hh
      let x3 := fsub (fsub (fsub (fmul r r) hhh) v) v
      let y3 := fsub (fmul r (fsub v x3)) (fmul s1 hhh)
      ⟨x3, y3, fmul (fmul q₁.z q₂.z) h⟩

/-- Scalar multiplication `[k] q` by double-and-add, most significant bit first. -/
def mul (q : Jac) (k : Nat) : Jac :=
  if _h : k = 0 then infinity
  else
    let r := double (mul q (k / 2))
    if k % 2 = 1 then add r q else r
termination_by k
decreasing_by omega

/-- The affine `x` coordinate, or `none` at infinity. -/
def affineX (q : Jac) : Option Nat :=
  if q.z = 0 then none
  else
    let zi := finv q.z
    some (fmul q.x (fmul zi zi))

end Jac

/-- `true` iff the inputs are in range, `Q ≠ (0, 0)` is on the curve, and `(r, s)` verifies. -/
def verify (hash : ByteArray) (r s qx qy : Nat) : Bool :=
  if r = 0 || r ≥ n || s = 0 || s ≥ n then false
  else if qx ≥ p || qy ≥ p || (qx = 0 && qy = 0) then false
  else if !isOnCurve qx qy then false
  else
    let e := hash.foldl (fun acc x => acc * 256 + x.toNat) 0
    let w := Nat.powMod s (n - 2) n
    let u1 := e * w % n
    let u2 := r * w % n
    let pt := Jac.add (Jac.mul ⟨gx, gy, 1⟩ u1) (Jac.mul ⟨qx, qy, 1⟩ u2)
    match pt.affineX with
    | none => false
    | some x => x % n == r

end EvmLean.P256
