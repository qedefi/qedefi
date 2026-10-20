import EvmLean.Prelude.Bytes

/-!
# secp256k1 public-key recovery, for `ECRECOVER` (precompile `0x01`)

SEC 1 v2 §4.1.6 for recovery ids `0`/`1`: `Q = r⁻¹ · (s·R − e·G)`. Mirrors
`secp256k1_recover` in `ethereum/crypto/elliptic_curve.py`; a recovered point at infinity is an
invalid signature. Jacobian coordinates over `Nat` mod `p`; square roots use `p ≡ 3 (mod 4)`.
-/

namespace EvmLean.Secp256k1

/-- Group order `n`. -/
def n : Nat := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

/-- Field prime `p = 2²⁵⁶ − 2³² − 977`. -/
def p : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

/-- Curve constant `b = 7` in `y² = x³ + b`. -/
def b : Nat := 7

/-- Affine `x` coordinate of the generator `G`. -/
def gx : Nat := 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798

/-- Affine `y` coordinate of the generator `G`. -/
def gy : Nat := 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

/-- A point in Jacobian coordinates (reduced mod `p`); `z = 0` is infinity. -/
structure Point where
  /-- Jacobian `X`. -/
  x : Nat
  /-- Jacobian `Y`. -/
  y : Nat
  /-- Jacobian `Z` (`0` at infinity). -/
  z : Nat

namespace Point

/-- The point at infinity. -/
def infinity : Point := ⟨1, 1, 0⟩

/-- Embed an affine point. -/
def ofAffine (x y : Nat) : Point := ⟨x, y, 1⟩

/-- Field subtraction modulo `p` (arguments already reduced). -/
private def fsub (a c : Nat) : Nat := (a + p - c) % p

/-- Point doubling (`dbl-2009-l`, valid for `a = 0`). -/
def double (q : Point) : Point :=
  if q.z = 0 || q.y = 0 then infinity
  else
    let a := q.x * q.x % p
    let bb := q.y * q.y % p
    let c := bb * bb % p
    let d := 2 * fsub (fsub ((q.x + bb) * (q.x + bb) % p) a) c % p
    let e := 3 * a % p
    let f := e * e % p
    let x3 := fsub f (2 * d % p)
    let y3 := fsub (e * fsub d x3 % p) (8 * c % p)
    let z3 := 2 * q.y * q.z % p
    ⟨x3, y3, z3⟩

/-- Point addition, handling the doubling and inverse cases explicitly. -/
def add (q₁ q₂ : Point) : Point :=
  if q₁.z = 0 then q₂
  else if q₂.z = 0 then q₁
  else
    let z1z1 := q₁.z * q₁.z % p
    let z2z2 := q₂.z * q₂.z % p
    let u1 := q₁.x * z2z2 % p
    let u2 := q₂.x * z1z1 % p
    let s1 := q₁.y * q₂.z % p * z2z2 % p
    let s2 := q₂.y * q₁.z % p * z1z1 % p
    if u1 = u2 then
      if s1 = s2 then double q₁ else infinity
    else
      let h := fsub u2 u1
      let rr := fsub s2 s1
      let hh := h * h % p
      let hhh := hh * h % p
      let v := u1 * hh % p
      let x3 := fsub (fsub (rr * rr % p) hhh) (2 * v % p)
      let y3 := fsub (rr * fsub v x3 % p) (s1 * hhh % p)
      let z3 := h * q₁.z % p * q₂.z % p
      ⟨x3, y3, z3⟩

/-- Right-to-left double-and-add: `acc + k · q`, consuming at most `fuel` bits of `k`. -/
def mulAux : Nat → Nat → Point → Point → Point
  | 0, _, _, acc => acc
  | fuel + 1, k, q, acc =>
    if k = 0 then acc
    else mulAux fuel (k / 2) (double q) (if k % 2 = 1 then add acc q else acc)

/-- Scalar multiplication `k · q` for `k < 2²⁵⁶`. -/
def mul (k : Nat) (q : Point) : Point := mulAux 256 k q infinity

/-- Affine coordinates, or `none` for the point at infinity. -/
def toAffine (q : Point) : Option (Nat × Nat) :=
  if q.z = 0 then none
  else
    let zi := Nat.powMod q.z (p - 2) p
    let zi2 := zi * zi % p
    some (q.x * zi2 % p, q.y * zi2 % p * zi % p)

end Point

/-- The generator `G`. -/
def g : Point := .ofAffine gx gy

/-- Recover the 64-byte public key `x ‖ y` (no `0x04` prefix); `none` if invalid. -/
def recover (hash : ByteArray) (recId : Nat) (r s : Nat) : Option ByteArray :=
  if recId > 1 || r = 0 || r ≥ n || s = 0 || s ≥ n then none
  else
    -- `R.x = r`; recovery ids 2 and 3 (`R.x = r + n`) are not used by Ethereum.
    let alpha := (Nat.powMod r 3 p + b) % p
    let beta := Nat.powMod alpha ((p + 1) / 4) p
    if beta * beta % p ≠ alpha then none
    else
      let y := if beta % 2 = recId then beta else (p - beta) % p
      let e := Bytes.toNat hash % n
      let rInv := Nat.powMod r (n - 2) n
      let u1 := (n - e) % n * rInv % n
      let u2 := s * rInv % n
      let q := (Point.mul u1 g).add (Point.mul u2 (.ofAffine r y))
      match q.toAffine with
      | none => none
      | some (qx, qy) => some (Bytes.ofNatBE 32 qx ++ Bytes.ofNatBE 32 qy)

end EvmLean.Secp256k1
