import EvmLean.Prelude.Bytes

/-!
# alt_bn128 (BN254) curve operations, for precompiles `0x06`–`0x08` (EIP-196/197).

* **EIP-196** (`ECADD`, `ECMUL`): the group `G₁` is `y² = x³ + 3` over `𝔽ₚ`. Inputs are
  big-endian 32-byte coordinates, `(0, 0)` encodes the point at infinity, and coordinates
  `≥ p` or points off the curve are invalid. Short inputs are zero-padded and extra bytes are
  ignored.
* **EIP-197** (`ECPAIRING`): `G₂` is the order-`r` subgroup of the sextic twist
  `y² = x³ + 3/(9 + i)` over `𝔽ₚ₂ = 𝔽ₚ[i]/(i² + 1)`. A `G₂` coordinate `a + b·i` is encoded
  imaginary part first (`b ‖ a`). The check is `∏ e(Pᵢ, Qᵢ) = 1`.

This mirrors `alt_bn128.py` in `cancun/vm/precompiled_contracts/`, which uses py_ecc's
`optimized_bn128`. As there, every `G₂` point must satisfy `r · Q = O` (the twist has a large
cofactor), while `G₁` has cofactor one so being on the curve suffices.

## Implementation

Field elements are `Nat`s reduced modulo `p` (GMP-backed at runtime), with Fermat inverses
via `Nat.powMod`. `𝔽ₚ₁₂` is the usual tower `𝔽ₚ₆ = 𝔽ₚ₂[v]/(v³ − ξ)`, `𝔽ₚ₁₂ = 𝔽ₚ₆[w]/(w² − v)`
with `ξ = 9 + i`, so `w⁶ = ξ` and the twist map is `(x, y) ↦ (x·w², y·w³)`.

The pairing is the optimal ate pairing: a Miller loop over the bits of `6u + 2` with `Q` in
affine twist coordinates (lines evaluated directly at `P`, vertical lines dropped since they
lie in `𝔽ₚ₆` and vanish under the final exponentiation), two Frobenius correction steps, and
a final exponentiation `(p¹² − 1)/r`, split into the easy part `(p⁶ − 1)(p² + 1)` and the hard
part `(p⁴ − p² + 1)/r = λ₀ + λ₁p + λ₂p² + λ₃p³` with the `u`-polynomial coefficients of
Scott et al., "On the final exponentiation for calculating pairings on ordinary elliptic
curves" (2009). The decomposition is checked by a unit test. Only the predicate "the product
is one" is observable, and any correct reduced pairing gives the same answer.
-/

namespace EvmLean.Bn254

/-- Field prime `p`. -/
def p : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- Group order `r` of `G₁` and `G₂`. -/
def r : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- The BN parameter `u` (with `p = 36u⁴ + 36u³ + 24u² + 6u + 1`). -/
def u : Nat := 4965661367192848881

/-- Optimal ate loop count `6u + 2` (65 bits). -/
def ateLoopCount : Nat := 29793968203157093288

/-! ## The base field `𝔽ₚ` -/

namespace Fp

/-- Addition modulo `p` (arguments reduced; a conditional subtraction is much cheaper than
a division). -/
def add (a b : Nat) : Nat := let s := a + b; if s < p then s else s - p

/-- Subtraction modulo `p` (arguments reduced). -/
def sub (a b : Nat) : Nat := if b ≤ a then a - b else a + p - b

/-- Negation modulo `p` (argument reduced). -/
def neg (a : Nat) : Nat := if a = 0 then 0 else p - a

/-- Multiplication modulo `p`. -/
def mul (a b : Nat) : Nat := a * b % p

/-- Fermat inverse (`inv 0 = 0`). -/
def inv (a : Nat) : Nat := Nat.powMod a (p - 2) p

end Fp

/-! ## `𝔽ₚ₂ = 𝔽ₚ[i]/(i² + 1)` -/

/-- `c0 + c1·i`, coefficients reduced modulo `p`. -/
structure Fp2 where
  /-- Real part. -/
  c0 : Nat
  /-- Imaginary part. -/
  c1 : Nat
  deriving DecidableEq, Repr

namespace Fp2

/-- Zero. -/
def zero : Fp2 := ⟨0, 0⟩

/-- One. -/
def one : Fp2 := ⟨1, 0⟩

/-- Embed a base-field element. -/
def ofFp (a : Nat) : Fp2 := ⟨a, 0⟩

/-- Addition. -/
def add (a b : Fp2) : Fp2 := ⟨Fp.add a.c0 b.c0, Fp.add a.c1 b.c1⟩

/-- Subtraction. -/
def sub (a b : Fp2) : Fp2 := ⟨Fp.sub a.c0 b.c0, Fp.sub a.c1 b.c1⟩

/-- Negation. -/
def neg (a : Fp2) : Fp2 := ⟨Fp.neg a.c0, Fp.neg a.c1⟩

/-- Multiplication (Karatsuba). -/
def mul (a b : Fp2) : Fp2 :=
  let t0 := a.c0 * b.c0
  let t1 := a.c1 * b.c1
  ⟨(t0 + p * p - t1) % p, ((a.c0 + a.c1) * (b.c0 + b.c1) - t0 - t1) % p⟩

/-- Squaring: `(a + b)(a − b) + 2ab·i`. -/
def sqr (a : Fp2) : Fp2 :=
  ⟨(a.c0 + a.c1) * (a.c0 + p - a.c1) % p, 2 * a.c0 * a.c1 % p⟩

/-- Multiplication by a base-field element. -/
def mulFp (a : Fp2) (k : Nat) : Fp2 := ⟨a.c0 * k % p, a.c1 * k % p⟩

/-- Multiplication by the non-residue `ξ = 9 + i`. -/
def mulXi (a : Fp2) : Fp2 := ⟨(9 * a.c0 + p - a.c1) % p, (a.c0 + 9 * a.c1) % p⟩

/-- Conjugation `a + b·i ↦ a − b·i`, which is the Frobenius `x ↦ xᵖ` on `𝔽ₚ₂`. -/
def conj (a : Fp2) : Fp2 := ⟨a.c0, Fp.neg a.c1⟩

/-- Inverse `(a − b·i)/(a² + b²)` (`inv 0 = 0`). -/
def inv (a : Fp2) : Fp2 :=
  let d := Fp.inv ((a.c0 * a.c0 + a.c1 * a.c1) % p)
  ⟨a.c0 * d % p, Fp.neg (a.c1 * d % p)⟩

/-- Right-to-left square-and-multiply: `acc · aᵏ`, consuming at most `fuel` bits of `k`. -/
def powAux : Nat → Fp2 → Nat → Fp2 → Fp2
  | 0, _, _, acc => acc
  | fuel + 1, a, k, acc =>
    if k = 0 then acc
    else powAux fuel (sqr a) (k / 2) (if k % 2 = 1 then mul acc a else acc)

/-- `aᵏ` for `k < 2²⁵⁶`. -/
def pow (a : Fp2) (k : Nat) : Fp2 := powAux 256 a k one

end Fp2

/-- The sextic non-residue `ξ = 9 + i`. -/
def xi : Fp2 := ⟨9, 1⟩

/-- Frobenius coefficient `γₖ = ξ^(k(p−1)/6)`, so that `(a·wᵏ)ᵖ = āγₖ·wᵏ` for `a ∈ 𝔽ₚ₂`. -/
def gamma (k : Nat) : Fp2 := xi.pow (k * (p - 1) / 6)

/-- `γ₁`. -/
def gamma1 : Fp2 := gamma 1
/-- `γ₂ = ξ^((p−1)/3)`. -/
def gamma2 : Fp2 := gamma 2
/-- `γ₃ = ξ^((p−1)/2)`. -/
def gamma3 : Fp2 := gamma 3
/-- `γ₄`. -/
def gamma4 : Fp2 := gamma 4
/-- `γ₅`. -/
def gamma5 : Fp2 := gamma 5

/-! ## `𝔽ₚ₆ = 𝔽ₚ₂[v]/(v³ − ξ)` -/

/-- `c0 + c1·v + c2·v²`. -/
structure Fp6 where
  /-- Coefficient of `1`. -/
  c0 : Fp2
  /-- Coefficient of `v`. -/
  c1 : Fp2
  /-- Coefficient of `v²`. -/
  c2 : Fp2
  deriving DecidableEq, Repr

namespace Fp6

/-- Zero. -/
def zero : Fp6 := ⟨.zero, .zero, .zero⟩

/-- One. -/
def one : Fp6 := ⟨.one, .zero, .zero⟩

/-- Addition. -/
def add (a b : Fp6) : Fp6 := ⟨a.c0.add b.c0, a.c1.add b.c1, a.c2.add b.c2⟩

/-- Subtraction. -/
def sub (a b : Fp6) : Fp6 := ⟨a.c0.sub b.c0, a.c1.sub b.c1, a.c2.sub b.c2⟩

/-- Negation. -/
def neg (a : Fp6) : Fp6 := ⟨a.c0.neg, a.c1.neg, a.c2.neg⟩

/-- Multiplication (Karatsuba-style, 6 `𝔽ₚ₂` products). -/
def mul (a b : Fp6) : Fp6 :=
  let t0 := a.c0.mul b.c0
  let t1 := a.c1.mul b.c1
  let t2 := a.c2.mul b.c2
  let c0 := t0.add (((a.c1.add a.c2).mul (b.c1.add b.c2)).sub (t1.add t2)).mulXi
  let c1 := (((a.c0.add a.c1).mul (b.c0.add b.c1)).sub (t0.add t1)).add t2.mulXi
  let c2 := (((a.c0.add a.c2).mul (b.c0.add b.c2)).sub (t0.add t2)).add t1
  ⟨c0, c1, c2⟩

/-- Multiplication by a sparse element `b + c·v` (5 `𝔽ₚ₂` products):
`(x₀ + x₁v + x₂v²)(b + cv) = (x₀b + ξx₂c) + (x₀c + x₁b)v + (x₁c + x₂b)v²`. -/
def mulBC (a : Fp6) (b c : Fp2) : Fp6 :=
  let t0 := a.c0.mul b
  let t1 := a.c1.mul c
  ⟨t0.add (a.c2.mul c).mulXi,
   ((a.c0.add a.c1).mul (b.add c)).sub (t0.add t1),
   t1.add (a.c2.mul b)⟩

/-- Multiplication by `v`: `(c0, c1, c2) ↦ (ξc2, c0, c1)`. -/
def mulV (a : Fp6) : Fp6 := ⟨a.c2.mulXi, a.c0, a.c1⟩

/-- Inverse (`inv 0 = 0`). -/
def inv (a : Fp6) : Fp6 :=
  let t0 := a.c0.sqr.sub (a.c1.mul a.c2).mulXi
  let t1 := a.c2.sqr.mulXi.sub (a.c0.mul a.c1)
  let t2 := a.c1.sqr.sub (a.c0.mul a.c2)
  let d := (a.c0.mul t0).add ((a.c2.mul t1).add (a.c1.mul t2)).mulXi
  let di := d.inv
  ⟨t0.mul di, t1.mul di, t2.mul di⟩

end Fp6

/-! ## `𝔽ₚ₁₂ = 𝔽ₚ₆[w]/(w² − v)` -/

/-- `g0 + g1·w`. Equivalently `∑ₖ aₖwᵏ` with `g0 = (a₀, a₂, a₄)` and `g1 = (a₁, a₃, a₅)`. -/
structure Fp12 where
  /-- Coefficient of `1`. -/
  g0 : Fp6
  /-- Coefficient of `w`. -/
  g1 : Fp6
  deriving DecidableEq, Repr

namespace Fp12

/-- One. -/
def one : Fp12 := ⟨.one, .zero⟩

/-- Multiplication (3 `𝔽ₚ₆` products). -/
def mul (a b : Fp12) : Fp12 :=
  let t0 := a.g0.mul b.g0
  let t1 := a.g1.mul b.g1
  ⟨t0.add t1.mulV, ((a.g0.add a.g1).mul (b.g0.add b.g1)).sub (t0.add t1)⟩

/-- Multiplication by a line value `a + (b + c·v)·w` with `a ∈ 𝔽ₚ` (as produced by
`lineValue`), exploiting its sparsity. Equal to `mul` with the full element. -/
def mulLine (f : Fp12) (a : Nat) (b c : Fp2) : Fp12 :=
  let t0 : Fp6 := ⟨f.g0.c0.mulFp a, f.g0.c1.mulFp a, f.g0.c2.mulFp a⟩
  let t1 := f.g1.mulBC b c
  let s := (f.g0.add f.g1).mulBC (b.add (.ofFp a)) c
  ⟨t0.add t1.mulV, s.sub (t0.add t1)⟩

/-- Squaring (2 `𝔽ₚ₆` products). -/
def sqr (a : Fp12) : Fp12 :=
  let t := a.g0.mul a.g1
  let c0 := ((a.g0.add a.g1).mul (a.g0.add a.g1.mulV)).sub (t.add t.mulV)
  ⟨c0, t.add t⟩

/-- Conjugation `g0 + g1·w ↦ g0 − g1·w`, the Frobenius `x ↦ x^(p⁶)`; it inverts elements of
the cyclotomic subgroup. -/
def conj (a : Fp12) : Fp12 := ⟨a.g0, a.g1.neg⟩

/-- Inverse `(g0 − g1·w)/(g0² − v·g1²)` (`inv 0 = 0`). -/
def inv (a : Fp12) : Fp12 :=
  let d := (a.g0.mul a.g0).sub (a.g1.mul a.g1).mulV
  let di := d.inv
  ⟨a.g0.mul di, (a.g1.mul di).neg⟩

/-- Frobenius `x ↦ xᵖ`: `aₖwᵏ ↦ āₖγₖwᵏ`. -/
def frob (a : Fp12) : Fp12 :=
  ⟨⟨a.g0.c0.conj, a.g0.c1.conj.mul gamma2, a.g0.c2.conj.mul gamma4⟩,
   ⟨a.g1.c0.conj.mul gamma1, a.g1.c1.conj.mul gamma3, a.g1.c2.conj.mul gamma5⟩⟩

/-- Right-to-left square-and-multiply: `acc · aᵏ`, consuming at most `fuel` bits of `k`. -/
def powAux : Nat → Fp12 → Nat → Fp12 → Fp12
  | 0, _, _, acc => acc
  | fuel + 1, a, k, acc =>
    if k = 0 then acc
    else powAux fuel (sqr a) (k / 2) (if k % 2 = 1 then mul acc a else acc)

/-- `aᵏ` for `k < 2²⁵⁶` (used with `k = u` and small constants). -/
def pow (a : Fp12) (k : Nat) : Fp12 := powAux 256 a k one

/-- Generic `aᵏ` for exponents below `2^fuel`; only used to cross-check the fast final
exponentiation in tests. -/
def powBig (fuel : Nat) (a : Fp12) (k : Nat) : Fp12 := powAux fuel a k one

end Fp12

/-! ## Affine points -/

/-- An affine point, or the point at infinity. -/
inductive Affine (α : Type) where
  /-- The point at infinity. -/
  | infinity
  /-- A finite point `(x, y)`. -/
  | point (x y : α)
  deriving DecidableEq, Repr

/-! ## `G₁`: `y² = x³ + 3` over `𝔽ₚ`, Jacobian coordinates -/

/-- A `G₁` point in Jacobian coordinates `(X/Z², Y/Z³)`; `z = 0` is infinity. -/
structure G1 where
  /-- Jacobian `X`. -/
  x : Nat
  /-- Jacobian `Y`. -/
  y : Nat
  /-- Jacobian `Z`. -/
  z : Nat

namespace G1

/-- The point at infinity. -/
def infinity : G1 := ⟨1, 1, 0⟩

/-- Embed an affine point. -/
def ofAffine : Affine Nat → G1
  | .infinity => infinity
  | .point x y => ⟨x, y, 1⟩

/-- Point doubling (`dbl-2009-l`, `a = 0`). -/
def double (q : G1) : G1 :=
  if q.z = 0 || q.y = 0 then infinity
  else
    let a := Fp.mul q.x q.x
    let bb := Fp.mul q.y q.y
    let c := Fp.mul bb bb
    let d := Fp.mul 2 (Fp.sub (Fp.sub (Fp.mul (q.x + bb) (q.x + bb)) a) c)
    let e := Fp.mul 3 a
    let x3 := Fp.sub (Fp.mul e e) (Fp.mul 2 d)
    let y3 := Fp.sub (Fp.mul e (Fp.sub d x3)) (Fp.mul 8 c)
    ⟨x3, y3, Fp.mul (2 * q.y) q.z⟩

/-- Point addition, handling doubling and inverse cases. -/
def add (q₁ q₂ : G1) : G1 :=
  if q₁.z = 0 then q₂
  else if q₂.z = 0 then q₁
  else
    let z1z1 := Fp.mul q₁.z q₁.z
    let z2z2 := Fp.mul q₂.z q₂.z
    let u1 := Fp.mul q₁.x z2z2
    let u2 := Fp.mul q₂.x z1z1
    let s1 := Fp.mul (Fp.mul q₁.y q₂.z) z2z2
    let s2 := Fp.mul (Fp.mul q₂.y q₁.z) z1z1
    if u1 = u2 then
      if s1 = s2 then double q₁ else infinity
    else
      let h := Fp.sub u2 u1
      let rr := Fp.sub s2 s1
      let hh := Fp.mul h h
      let hhh := Fp.mul hh h
      let v := Fp.mul u1 hh
      let x3 := Fp.sub (Fp.sub (Fp.mul rr rr) hhh) (Fp.mul 2 v)
      let y3 := Fp.sub (Fp.mul rr (Fp.sub v x3)) (Fp.mul s1 hhh)
      ⟨x3, y3, Fp.mul (Fp.mul h q₁.z) q₂.z⟩

/-- `acc + k · q`, consuming at most `fuel` bits of `k`. -/
def mulAux : Nat → Nat → G1 → G1 → G1
  | 0, _, _, acc => acc
  | fuel + 1, k, q, acc =>
    if k = 0 then acc
    else mulAux fuel (k / 2) (double q) (if k % 2 = 1 then add acc q else acc)

/-- Scalar multiplication `k · q` for `k < 2²⁵⁶`. -/
def mul (k : Nat) (q : G1) : G1 := mulAux 256 k q infinity

/-- Affine form. -/
def toAffine (q : G1) : Affine Nat :=
  if q.z = 0 then .infinity
  else
    let zi := Fp.inv q.z
    let zi2 := Fp.mul zi zi
    .point (Fp.mul q.x zi2) (Fp.mul (Fp.mul q.y zi2) zi)

end G1

/-! ## `G₂`: the twist `y² = x³ + 3/ξ` over `𝔽ₚ₂` -/

/-- The twist constant `b' = 3/ξ = 3/(9 + i)`. -/
def twistB : Fp2 := (Fp2.ofFp 3).mul xi.inv

/-- A twist point in Jacobian coordinates; `z = 0` is infinity. -/
structure G2 where
  /-- Jacobian `X`. -/
  x : Fp2
  /-- Jacobian `Y`. -/
  y : Fp2
  /-- Jacobian `Z`. -/
  z : Fp2

namespace G2

/-- The point at infinity. -/
def infinity : G2 := ⟨.one, .one, .zero⟩

/-- Embed an affine point. -/
def ofAffine : Affine Fp2 → G2
  | .infinity => infinity
  | .point x y => ⟨x, y, .one⟩

/-- Point doubling (`dbl-2009-l`, `a = 0`). -/
def double (q : G2) : G2 :=
  if q.z = .zero || q.y = .zero then infinity
  else
    let a := q.x.sqr
    let bb := q.y.sqr
    let c := bb.sqr
    let d := (((q.x.add bb).sqr.sub a).sub c).mulFp 2
    let e := a.mulFp 3
    let x3 := e.sqr.sub (d.mulFp 2)
    let y3 := (e.mul (d.sub x3)).sub (c.mulFp 8)
    ⟨x3, y3, (q.y.mul q.z).mulFp 2⟩

/-- Point addition, handling doubling and inverse cases. -/
def add (q₁ q₂ : G2) : G2 :=
  if q₁.z = .zero then q₂
  else if q₂.z = .zero then q₁
  else
    let z1z1 := q₁.z.sqr
    let z2z2 := q₂.z.sqr
    let u1 := q₁.x.mul z2z2
    let u2 := q₂.x.mul z1z1
    let s1 := (q₁.y.mul q₂.z).mul z2z2
    let s2 := (q₂.y.mul q₁.z).mul z1z1
    if u1 = u2 then
      if s1 = s2 then double q₁ else infinity
    else
      let h := u2.sub u1
      let rr := s2.sub s1
      let hh := h.sqr
      let hhh := hh.mul h
      let v := u1.mul hh
      let x3 := (rr.sqr.sub hhh).sub (v.mulFp 2)
      let y3 := (rr.mul (v.sub x3)).sub (s1.mul hhh)
      ⟨x3, y3, (h.mul q₁.z).mul q₂.z⟩

/-- `acc + k · q`, consuming at most `fuel` bits of `k`. -/
def mulAux : Nat → Nat → G2 → G2 → G2
  | 0, _, _, acc => acc
  | fuel + 1, k, q, acc =>
    if k = 0 then acc
    else mulAux fuel (k / 2) (double q) (if k % 2 = 1 then add acc q else acc)

/-- Scalar multiplication `k · q` for `k < 2²⁵⁶`. -/
def mul (k : Nat) (q : G2) : G2 := mulAux 256 k q infinity

/-- Is this the point at infinity? -/
def isInfinity (q : G2) : Bool := q.z = .zero

end G2

/-! ## The optimal ate pairing -/

/-- A line function value `a + b·w + c·w³` with `a ∈ 𝔽ₚ` and `b, c ∈ 𝔽ₚ₂`: the shape of every
line through points of `ψ(G₂)` evaluated at a point of `G₁`. -/
structure Line where
  /-- Coefficient of `1` (in `𝔽ₚ`). -/
  a : Nat
  /-- Coefficient of `w`. -/
  b : Fp2
  /-- Coefficient of `w³`. -/
  c : Fp2

namespace Line

/-- The constant line `1` (used for vertical lines, which the final exponentiation kills). -/
def one : Line := ⟨1, .zero, .zero⟩

/-- The line as a full `𝔽ₚ₁₂` element. -/
def toFp12 (l : Line) : Fp12 := ⟨⟨.ofFp l.a, .zero, .zero⟩, ⟨l.b, l.c, .zero⟩⟩

end Line

/-- `f · l` using the sparsity of `l`. -/
def Fp12.mulBy (f : Fp12) (l : Line) : Fp12 := f.mulLine l.a l.b l.c

/-- The line through the untwisted points `ψ(T)` and `ψ(T')` with twist slope `λ`,
evaluated at `P = (xP, yP)`: `yP − λxP·w + (λxT − yT)·w³`. -/
def lineValue (lam xT yT : Fp2) (xP yP : Nat) : Line :=
  ⟨yP, (lam.mulFp xP).neg, (lam.mul xT).sub yT⟩

/-- Tangent line at `T` evaluated at `P`, and `2T`. Vertical tangents (only at infinity or
2-torsion, impossible in `G₂`) contribute `1`. -/
def lineDouble (t : Affine Fp2) (xP yP : Nat) : Line × Affine Fp2 :=
  match t with
  | .infinity => (.one, .infinity)
  | .point xT yT =>
    if yT = .zero then (.one, .infinity)
    else
      let lam := (xT.sqr.mulFp 3).mul (yT.mulFp 2).inv
      let x3 := lam.sqr.sub (xT.mulFp 2)
      let y3 := (lam.mul (xT.sub x3)).sub yT
      (lineValue lam xT yT xP yP, .point x3 y3)

/-- Line through `T` and `Q` evaluated at `P`, and `T + Q`. Vertical lines contribute `1`. -/
def lineAdd (t q : Affine Fp2) (xP yP : Nat) : Line × Affine Fp2 :=
  match t, q with
  | .infinity, _ => (.one, q)
  | _, .infinity => (.one, t)
  | .point xT yT, .point xQ yQ =>
    if xT = xQ then
      if yT = yQ then lineDouble t xP yP else (.one, .infinity)
    else
      let lam := (yQ.sub yT).mul (xQ.sub xT).inv
      let x3 := (lam.sqr.sub xT).sub xQ
      let y3 := (lam.mul (xT.sub x3)).sub yT
      (lineValue lam xT yT xP yP, .point x3 y3)

/-- Miller loop body over bits `i-1, …, 0` of `6u + 2`. -/
def millerAux (q : Affine Fp2) (xP yP : Nat) : Nat → Fp12 → Affine Fp2 → Fp12 × Affine Fp2
  | 0, f, t => (f, t)
  | i + 1, f, t =>
    let (l, t) := lineDouble t xP yP
    let f := f.sqr.mulBy l
    if ateLoopCount.testBit i then
      let (l, t) := lineAdd t q xP yP
      millerAux q xP yP i (f.mulBy l) t
    else millerAux q xP yP i f t

/-- The Frobenius endomorphism on the twist: `ψ⁻¹ ∘ π ∘ ψ`, i.e. `(x, y) ↦ (x̄γ₂, ȳγ₃)`. -/
def twistFrob : Affine Fp2 → Affine Fp2
  | .infinity => .infinity
  | .point x y => .point (x.conj.mul gamma2) (y.conj.mul gamma3)

/-- Negation on the twist. -/
def affineNeg : Affine Fp2 → Affine Fp2
  | .infinity => .infinity
  | .point x y => .point x y.neg

/-- The optimal ate Miller loop `f_{6u+2,Q}(P) · l_{T,π(Q)}(P) · l_{T',−π²(Q)}(P)` for a
finite `P = (xP, yP) ∈ G₁` and `Q ∈ G₂` (before the final exponentiation). -/
def miller (q : Affine Fp2) (xP yP : Nat) : Fp12 :=
  match q with
  | .infinity => .one
  | .point _ _ =>
    let (f, t) := millerAux q xP yP 64 .one q
    let q1 := twistFrob q
    let nq2 := affineNeg (twistFrob q1)
    let (l1, t) := lineAdd t q1 xP yP
    let (l2, _) := lineAdd t nq2 xP yP
    (f.mulBy l1).mulBy l2

/-- Final exponentiation `f^((p¹² − 1)/r)`. -/
def finalExp (f : Fp12) : Fp12 :=
  -- Easy part: `f^((p⁶ − 1)(p² + 1))`; afterwards `conj` is inversion.
  let f := f.conj.mul f.inv
  let f := (f.frob.frob).mul f
  -- Hard part: `f^(λ₀ + λ₁p + λ₂p² + λ₃p³)` with
  -- `λ₃ = 1`, `λ₂ = 6u² + 1`, `λ₁ = −36u³ − 18u² − 12u + 1`, `λ₀ = −36u³ − 30u² − 18u − 2`.
  let a := f.pow u
  let b := a.pow u
  let c := b.pow u
  let c36 := c.pow 36
  let f0 := (((c36.mul (b.pow 30)).mul (a.pow 18)).mul f.sqr).conj
  let f1 := (((c36.mul (b.pow 18)).mul (a.pow 12)).conj).mul f
  let f2 := (b.pow 6).mul f
  let f3 := f
  ((f0.mul f1.frob).mul f2.frob.frob).mul f3.frob.frob.frob

/-- The reduced optimal ate pairing `e(P, Q)` for finite `P`; used by tests. -/
def pairing (q : Affine Fp2) (xP yP : Nat) : Fp12 := finalExp (miller q xP yP)

/-! ## Encoding and the precompile entry points -/

/-- Big-endian 32-byte word at `off`, zero-padded. -/
def readWord (input : ByteArray) (off : Nat) : Nat := Bytes.toNat (Bytes.readPadded input off 32)

/-- Is `(x, y)` on `y² = x³ + 3`? -/
def onCurveG1 (x y : Nat) : Bool := Fp.mul y y = Fp.add (Fp.mul (Fp.mul x x) x) 3

/-- Decode a `G₁` point from 64 bytes at `off` (`bytes_to_g1`). -/
def decodeG1 (input : ByteArray) (off : Nat) : Option (Affine Nat) :=
  let x := readWord input off
  let y := readWord input (off + 32)
  if x ≥ p || y ≥ p then none
  else if x = 0 && y = 0 then some .infinity
  else if onCurveG1 x y then some (.point x y)
  else none

/-- Is `(x, y)` on the twist `y² = x³ + 3/ξ`? -/
def onCurveG2 (x y : Fp2) : Bool := y.sqr = (x.sqr.mul x).add twistB

/-- Decode a twist point from 128 bytes at `off` (`bytes_to_g2`): each coordinate is
`imaginary ‖ real`. On-curve check only; the subgroup check is separate. -/
def decodeG2 (input : ByteArray) (off : Nat) : Option (Affine Fp2) :=
  let x1 := readWord input off
  let x0 := readWord input (off + 32)
  let y1 := readWord input (off + 64)
  let y0 := readWord input (off + 96)
  if x0 ≥ p || x1 ≥ p || y0 ≥ p || y1 ≥ p then none
  else
    let x : Fp2 := ⟨x0, x1⟩
    let y : Fp2 := ⟨y0, y1⟩
    if x = .zero && y = .zero then some .infinity
    else if onCurveG2 x y then some (.point x y)
    else none

/-- Is a twist point in the order-`r` subgroup `G₂`? -/
def inG2 (q : Affine Fp2) : Bool := (G2.mul r (G2.ofAffine q)).isInfinity

/-- 64-byte encoding of a `G₁` point (infinity is `(0, 0)`). -/
def encodeG1 : Affine Nat → ByteArray
  | .infinity => Bytes.zeros 64
  | .point x y => Bytes.ofNatBE 32 x ++ Bytes.ofNatBE 32 y

/-- `ECADD`: input is 128 bytes (two points), output 64 bytes; `none` on invalid input. -/
def add (input : ByteArray) : Option ByteArray := do
  let a ← decodeG1 input 0
  let b ← decodeG1 input 64
  pure (encodeG1 ((G1.ofAffine a).add (G1.ofAffine b)).toAffine)

/-- `ECMUL`: input is 96 bytes (point, scalar), output 64 bytes; `none` on invalid input. -/
def mul (input : ByteArray) : Option ByteArray := do
  let a ← decodeG1 input 0
  pure (encodeG1 ((G1.ofAffine a).mul (readWord input 64)).toAffine)

/-- Accumulate the Miller loops of the pairs at indices `i, i+1, …` (`count` of them). -/
def pairingAux (input : ByteArray) : Nat → Nat → Fp12 → Option Fp12
  | 0, _, f => some f
  | count + 1, i, f => do
    let pt ← decodeG1 input (192 * i)
    let q ← decodeG2 input (192 * i + 64)
    if !inG2 q then none
    else
      let f := match pt with
        | .infinity => f
        | .point xP yP => f.mul (miller q xP yP)
      pairingAux input count (i + 1) f

/-- `ECPAIRING`: input is a multiple of 192 bytes; `some true` iff the pairing product is
one; `none` on invalid input. -/
def pairingCheck (input : ByteArray) : Option Bool :=
  if input.size % 192 ≠ 0 then none
  else (pairingAux input (input.size / 192) 0 .one).map fun f => finalExp f = .one

end EvmLean.Bn254
