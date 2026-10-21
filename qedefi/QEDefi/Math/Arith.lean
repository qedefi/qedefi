module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Tactic.Linarith

/-!
# uint256 arithmetic of the vault libraries

Solmate's `mulDivDown`/`mulDivUp` and OpenZeppelin's `Math.mulDiv` as `ℕ → Option ℕ`
(`none` = revert), mirroring the Solidity source, plus floor/ceiling characterisations.
-/

section

@[expose] public section

namespace QEDefi.Math

/-- `2^256`: one more than the largest `uint256`. -/
def U256 : ℕ := 2 ^ 256

/-- `type(uint256).max = 2^256 - 1`. -/
def MAX : ℕ := 2 ^ 256 - 1

theorem MAX_lt_U256 : MAX < U256 := by unfold MAX U256; omega

theorem MAX_add_one : MAX + 1 = U256 := by unfold MAX U256; omega

/-- `x` fits in a `uint256`. -/
def Fits (x : ℕ) : Prop := x ≤ MAX

/-- Ceiling division as Solmate computes it: `add(gt(mod(m, d), 0), div(m, d))`. -/
def ceilDiv (m d : ℕ) : ℕ := (if 0 < m % d then 1 else 0) + m / d

/-- Solmate `FixedPointMathLib.mulDivDown`; the overflow test is the source's
`y ≠ 0 ∧ x > MAX / y`. -/
def mulDivDown (x y d : ℕ) : Option ℕ :=
  if d = 0 ∨ (y ≠ 0 ∧ MAX / y < x) then none else some (x * y / d)

/-- Solmate `FixedPointMathLib.mulDivUp(x, y, denominator)`. -/
def mulDivUp (x y d : ℕ) : Option ℕ :=
  if d = 0 ∨ (y ≠ 0 ∧ MAX / y < x) then none else some (ceilDiv (x * y) d)

/-- OpenZeppelin `Math.mulDiv(x, y, d, rounding)` (512-bit precision, checked rounding
add); `up = true` is `Rounding.Ceil`. -/
def ozMulDiv (x y d : ℕ) (up : Bool) : Option ℕ :=
  if d = 0 ∨ MAX < x * y / d then none
  else
    let r := x * y / d + (if up = true ∧ 0 < x * y % d then 1 else 0)
    if MAX < r then none else some r

/-- Solidity checked `a + b` on `uint256`. -/
def checkedAdd (a b : ℕ) : Option ℕ := if MAX < a + b then none else some (a + b)

/-! ## Characterisations -/

theorem overflow_test_iff (x y : ℕ) : (y ≠ 0 ∧ MAX / y < x) ↔ MAX < x * y := by
  constructor
  · rintro ⟨hy, h⟩
    exact (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hy)).1 h
  · intro h
    have hy : y ≠ 0 := by rintro rfl; simp at h
    exact ⟨hy, (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hy)).2 h⟩

theorem mulDivDown_eq_some {x y d z : ℕ} :
    mulDivDown x y d = some z ↔ d ≠ 0 ∧ x * y ≤ MAX ∧ z = x * y / d := by
  unfold mulDivDown
  simp only [overflow_test_iff]
  split_ifs with h
  · simp only [false_iff, not_and]
    omega
  · simp only [Option.some.injEq]
    omega

theorem mulDivDown_eq_none {x y d : ℕ} :
    mulDivDown x y d = none ↔ d = 0 ∨ MAX < x * y := by
  unfold mulDivDown
  simp only [overflow_test_iff]
  split_ifs with h <;> simp_all

theorem mulDivUp_eq_some {x y d z : ℕ} :
    mulDivUp x y d = some z ↔ d ≠ 0 ∧ x * y ≤ MAX ∧ z = ceilDiv (x * y) d := by
  unfold mulDivUp
  simp only [overflow_test_iff]
  split_ifs with h
  · simp only [false_iff, not_and]
    omega
  · simp only [Option.some.injEq]
    omega

theorem mulDivUp_eq_none {x y d : ℕ} :
    mulDivUp x y d = none ↔ d = 0 ∨ MAX < x * y := by
  unfold mulDivUp
  simp only [overflow_test_iff]
  split_ifs with h <;> simp_all

theorem div_mul_le' (m d : ℕ) : m / d * d ≤ m := Nat.div_mul_le_self m d

theorem lt_div_add_one_mul (m d : ℕ) (hd : 0 < d) : m < (m / d + 1) * d := by
  have := Nat.lt_div_mul_add (a := m) hd
  nlinarith

theorem ceilDiv_eq (m d : ℕ) : ceilDiv m d = m / d + (if 0 < m % d then 1 else 0) := by
  unfold ceilDiv; omega

theorem le_ceilDiv_mul (m d : ℕ) (hd : 0 < d) : m ≤ ceilDiv m d * d := by
  have h := Nat.div_add_mod m d
  have h2 := Nat.mod_lt m hd
  unfold ceilDiv
  split_ifs with h3
  · nlinarith
  · have : m % d = 0 := by omega
    rw [this] at h; nlinarith

theorem ceilDiv_mul_lt (m d : ℕ) (hd : 0 < d) : ceilDiv m d * d < m + d := by
  have h := Nat.div_add_mod m d
  unfold ceilDiv
  split_ifs with h3
  · nlinarith
  · have : m % d = 0 := by omega
    rw [this] at h; simp only [zero_add]; nlinarith

theorem ceilDiv_le_iff (m d z : ℕ) (hd : 0 < d) : ceilDiv m d ≤ z ↔ m ≤ z * d := by
  constructor
  · intro h; exact (le_ceilDiv_mul m d hd).trans (Nat.mul_le_mul_right d h)
  · intro h
    by_contra hc
    push Not at hc
    have h1 := ceilDiv_mul_lt m d hd
    have : (z + 1) * d ≤ ceilDiv m d * d := Nat.mul_le_mul_right d hc
    nlinarith

theorem lt_ceilDiv_iff (m d z : ℕ) (hd : 0 < d) : z < ceilDiv m d ↔ z * d < m := by
  rw [← not_le, ceilDiv_le_iff m d z hd, not_le]

theorem ceilDiv_zero_left (d : ℕ) : ceilDiv 0 d = 0 := by simp [ceilDiv]

theorem le_div_iff (m d z : ℕ) (hd : 0 < d) : z ≤ m / d ↔ z * d ≤ m :=
  Nat.le_div_iff_mul_le hd

theorem ozMulDiv_eq_some {x y d z : ℕ} {up : Bool} :
    ozMulDiv x y d up = some z ↔
      d ≠ 0 ∧ z ≤ MAX ∧
        z = (if up then ceilDiv (x * y) d else x * y / d) := by
  unfold ozMulDiv
  cases up <;> simp only [Bool.false_eq_true, false_and, ↓reduceIte, add_zero, true_and,
    ceilDiv_eq] <;> split_ifs <;> simp_all <;> omega

end QEDefi.Math
end

end

section

/-!
## The arithmetic behind the round-trip properties

One inequality per round-trip shape, over cross-multiplied rounding facts (`T, S` = assets
and supply before; for OpenZeppelin apply to `T + 1`, `S + 10^δ`).
-/

@[expose] public section

namespace QEDefi.Math

theorem rt_in_out_assets {T S a n a' : ℕ} (hpos : 0 < S + n) (h1 : n * T ≤ a * S)
    (h2 : a' * (S + n) ≤ n * (T + a)) : a' ≤ a := by
  by_contra hc
  push Not at hc
  have : (a + 1) * (S + n) ≤ a' * (S + n) := Nat.mul_le_mul_right _ hc
  nlinarith

theorem rt_in_out_shares {T S a n n' : ℕ} (hpos : 0 < T + a) (h1 : n * T ≤ a * S)
    (h2 : a * (S + n) ≤ n' * (T + a)) : n ≤ n' := by
  by_contra hc
  push Not at hc
  have : (n' + 1) * (T + a) ≤ n * (T + a) := Nat.mul_le_mul_right _ hc
  nlinarith

theorem rt_out_in_shares {T₁ S₁ a n n' : ℕ} (hpos : 0 < T₁) (h1 : a * (n + S₁) ≤ n * (a + T₁))
    (h2 : n' * T₁ ≤ a * S₁) : n' ≤ n := by
  by_contra hc
  push Not at hc
  have : (n + 1) * T₁ ≤ n' * T₁ := Nat.mul_le_mul_right _ hc
  nlinarith

theorem rt_out_in_assets {T₁ S₁ a n a' : ℕ} (hpos : 0 < S₁) (h1 : a * (n + S₁) ≤ n * (a + T₁))
    (h2 : n * T₁ ≤ a' * S₁) : a ≤ a' := by
  by_contra hc
  push Not at hc
  have : (a' + 1) * S₁ ≤ a * S₁ := Nat.mul_le_mul_right _ hc
  nlinarith

end QEDefi.Math
end

end
