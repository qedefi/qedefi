import EvmLean.Crypto.Bls12381.Curve

/-!
# The optimal ate pairing on BLS12-381

Miller loop over `|x|` (`x = −0xd201000000010000`, result conjugated as in py_ecc) with `Q`
affine on the twist; the `w³` line factor and vertical lines are dropped since the final
exponentiation kills subfield elements. The hard part uses Hayashida–Hayasaka–Teruya (ePrint
2020/875): `(p⁴ − p² + 1)/r = ((x − 1)²/3)·(x + p)·(x² + p² − 1) + 1`.
-/

namespace EvmLean.Bls12381

/-- `|x|` for the BLS12-381 parameter `x = −0xd201000000010000`: the Miller loop length. -/
def xAbs : Nat := 0xd201000000010000

/-- The binary digits of `n`, most significant first (`[]` for `0`). -/
def bitsMsbFirst (n : Nat) : List Bool := go n []
where
  /-- Prepend the bits of `n` (least significant last) to `acc`. -/
  go (n : Nat) (acc : List Bool) : List Bool :=
    if _h : n = 0 then acc else go (n / 2) ((n % 2 == 1) :: acc)
  termination_by n
  decreasing_by omega

/-- The Miller loop bits: the bits of `|x|` after the leading one. -/
def millerBits : List Bool := (bitsMsbFirst xAbs).tail

/-- Line through `ψ(T)` with twist slope `λ'` at `P`, times `w³`: `(λ'xT − yT) − λ'xP·v + yP·vw`. -/
def lineEval (tx ty lam : Fp2) (xP yP : Fp) : Fp12 :=
  ⟨⟨lam * tx - ty, -(Fp2.mulFp lam xP), Fp2.zero⟩,
   ⟨Fp2.zero, Fp2.ofFp yP, Fp2.zero⟩⟩

/-- Miller loop state: the accumulator and the running point `T` (affine, on the twist). -/
structure MillerState where
  /-- The accumulated Miller function value. -/
  f : Fp12
  /-- `x` of the running point `T`. -/
  tx : Fp2
  /-- `y` of the running point `T`. -/
  ty : Fp2

/-- One Miller-loop iteration: double `T` with its tangent line, then add `Q` if `bit` is set. -/
def millerStep (qx qy : Fp2) (xP yP : Fp) (s : MillerState) (bit : Bool) : MillerState :=
  let three : Fp2 := ⟨⟨3⟩, Fp.zero⟩
  let lam := three * Fp2.sq s.tx * Fp2.inv (s.ty + s.ty)
  let f := Fp12.sq s.f * lineEval s.tx s.ty lam xP yP
  let x3 := Fp2.sq lam - s.tx - s.tx
  let y3 := lam * (s.tx - x3) - s.ty
  if bit then
    let lam' := (qy - y3) * Fp2.inv (qx - x3)
    let f' := f * lineEval x3 y3 lam' xP yP
    let x4 := Fp2.sq lam' - x3 - qx
    let y4 := lam' * (x3 - x4) - y3
    ⟨f', x4, y4⟩
  else ⟨f, x3, y3⟩

/-- The Miller loop `f_{x,Q}(P)` (before final exponentiation); `1` if either point is infinity. -/
def millerLoop (q : Affine Fp2) (p : Affine Fp) : Fp12 :=
  match q, p with
  | .point qx qy, .point xP yP =>
    Fp12.conj (millerBits.foldl (millerStep qx qy xP yP) ⟨Fp12.one, qx, qy⟩).f
  | .infinity, _ => Fp12.one
  | .point _ _, .infinity => Fp12.one

/-- The hard-part exponent `(p⁴ − p² + 1) / r` (exact); used to test `finalExp`. -/
def hardExp : Nat := (P * P * P * P - P * P + 1) / R

/-- `(x − 1)²/3 = (|x| + 1)²/3` (exact), the first factor of the hard-part decomposition. -/
def hardExp0 : Nat := (xAbs + 1) * (xAbs + 1) / 3

/-- The final exponentiation `f ↦ f^((p¹² − 1)/r)` (see the module doc). -/
def finalExp (f : Fp12) : Fp12 :=
  -- f^(p⁶ − 1): conjugation is the p⁶-power Frobenius.
  let f1 := Fp12.conj f * Fp12.inv f
  -- ^(p² + 1)
  let f2 := Fp12.frobenius2 f1 * f1
  -- ^((x − 1)²/3)
  let a := Fp12.pow f2 hardExp0
  -- ^(x + p), with x < 0: a^x = conj (a^|x|) in the cyclotomic subgroup.
  let b := Fp12.conj (Fp12.pow a xAbs) * Fp12.frobenius a
  -- ^(x² + p² − 1)
  let c := Fp12.pow (Fp12.pow b xAbs) xAbs * Fp12.frobenius2 b * Fp12.conj b
  -- + 1
  c * f2

/-- The optimal ate pairing `e(P, Q)` for `P ∈ G1`, `Q ∈ G2`. -/
def pairing (p : Affine Fp) (q : Affine Fp2) : Fp12 := finalExp (millerLoop q p)

/-- Is `∏ e(Pᵢ, Qᵢ) = 1`? One final exponentiation; points must already be in `G1`/`G2`. -/
def pairingCheck (pairs : List (Affine Fp × Affine Fp2)) : Bool :=
  finalExp (pairs.foldl (fun acc pq => acc * millerLoop pq.2 pq.1) Fp12.one) == Fp12.one

end EvmLean.Bls12381
