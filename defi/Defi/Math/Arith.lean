module

public import Mathlib

/-!
# uint256 arithmetic of the vault libraries

The two `mulDiv` flavours used by the verification targets, as functions `ℕ → Option ℕ`
(`none` = the EVM call reverts), written to mirror the Solidity source line by line:

* Solmate `FixedPointMathLib.mulDivDown` / `mulDivUp` (assembly): revert iff
  `denominator = 0` or `x * y` overflows 256 bits, the latter tested as
  `y ≠ 0 ∧ x > MAX / y` exactly as in the source.
* OpenZeppelin `Math.mulDiv(x, y, d, rounding)` (v5.x): full 512-bit precision, reverts iff
  `d = 0` or the floor quotient does not fit, then adds the rounding bit with a *checked*
  addition (`SafeCast.toUint` + Solidity `+`).

The characterisation lemmas (`mulDivDown_eq_some`, `ceilDiv_mul_ge`, …) turn these into
plain floor/ceiling statements for the proofs.
-/

@[expose] public section

namespace EvmLeanSpecs.Vault

/-- `2^256`: one more than the largest `uint256`. -/
def U256 : ℕ := 2 ^ 256

/-- `type(uint256).max = 2^256 - 1`. -/
def MAX : ℕ := 2 ^ 256 - 1

theorem MAX_lt_U256 : MAX < U256 := by unfold MAX U256; omega

theorem MAX_add_one : MAX + 1 = U256 := by unfold MAX U256; omega

/-- `x` fits in a `uint256`. -/
def Fits (x : ℕ) : Prop := x ≤ MAX

/-- Ceiling division as computed by Solmate's `mulDivUp`: the floor quotient plus one when
the remainder is non-zero (`add(gt(mod(m, d), 0), div(m, d))`). -/
def ceilDiv (m d : ℕ) : ℕ := (if 0 < m % d then 1 else 0) + m / d

/-- Solmate `FixedPointMathLib.mulDivDown(x, y, denominator)`. -/
def mulDivDown (x y d : ℕ) : Option ℕ :=
  if d = 0 ∨ (y ≠ 0 ∧ MAX / y < x) then none else some (x * y / d)

/-- Solmate `FixedPointMathLib.mulDivUp(x, y, denominator)`. -/
def mulDivUp (x y d : ℕ) : Option ℕ :=
  if d = 0 ∨ (y ≠ 0 ∧ MAX / y < x) then none else some (ceilDiv (x * y) d)

/-- OpenZeppelin `Math.mulDiv(x, y, denominator, rounding)`; `up = true` is
`Rounding.Ceil`. -/
def ozMulDiv (x y d : ℕ) (up : Bool) : Option ℕ :=
  if d = 0 ∨ MAX < x * y / d then none
  else
    let r := x * y / d + (if up = true ∧ 0 < x * y % d then 1 else 0)
    if MAX < r then none else some r

/-- Solidity checked `a + b` on `uint256`. -/
def checkedAdd (a b : ℕ) : Option ℕ := if MAX < a + b then none else some (a + b)

/-! ## Characterisations -/

/-- Solmate's overflow test is exactly "the product does not fit". -/
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

/-- Floor division: `(m / d) * d ≤ m`. -/
theorem div_mul_le' (m d : ℕ) : m / d * d ≤ m := Nat.div_mul_le_self m d

/-- Floor division: `m < (m / d + 1) * d`. -/
theorem lt_div_add_one_mul (m d : ℕ) (hd : 0 < d) : m < (m / d + 1) * d := by
  have := Nat.lt_div_mul_add (a := m) hd
  nlinarith

theorem ceilDiv_eq (m d : ℕ) : ceilDiv m d = m / d + (if 0 < m % d then 1 else 0) := by
  unfold ceilDiv; omega

/-- Ceiling division rounds up: `m ≤ ceilDiv m d * d` (for `d > 0`). -/
theorem le_ceilDiv_mul (m d : ℕ) (hd : 0 < d) : m ≤ ceilDiv m d * d := by
  have h := Nat.div_add_mod m d
  have h2 := Nat.mod_lt m hd
  unfold ceilDiv
  split_ifs with h3
  · nlinarith
  · have : m % d = 0 := by omega
    rw [this] at h; nlinarith

/-- Ceiling division is tight: `ceilDiv m d * d < m + d`. -/
theorem ceilDiv_mul_lt (m d : ℕ) (hd : 0 < d) : ceilDiv m d * d < m + d := by
  have h := Nat.div_add_mod m d
  unfold ceilDiv
  split_ifs with h3
  · nlinarith
  · have : m % d = 0 := by omega
    rw [this] at h; simp only [zero_add]; nlinarith

/-- `ceilDiv` is the least `z` with `m ≤ z * d`. -/
theorem ceilDiv_le_iff (m d z : ℕ) (hd : 0 < d) : ceilDiv m d ≤ z ↔ m ≤ z * d := by
  constructor
  · intro h; exact (le_ceilDiv_mul m d hd).trans (Nat.mul_le_mul_right d h)
  · intro h
    by_contra hc
    push Not at hc
    have h1 := ceilDiv_mul_lt m d hd
    have : (z + 1) * d ≤ ceilDiv m d * d := Nat.mul_le_mul_right d hc
    nlinarith

/-- `z ≤ ceilDiv m d` whenever `(z - 1) * d < m`, stated without subtraction. -/
theorem lt_ceilDiv_iff (m d z : ℕ) (hd : 0 < d) : z < ceilDiv m d ↔ z * d < m := by
  rw [← not_le, ceilDiv_le_iff m d z hd, not_le]

theorem ceilDiv_zero_left (d : ℕ) : ceilDiv 0 d = 0 := by simp [ceilDiv]

/-- Floor characterisation: `z ≤ m / d ↔ z * d ≤ m`. -/
theorem le_div_iff (m d z : ℕ) (hd : 0 < d) : z ≤ m / d ↔ z * d ≤ m :=
  Nat.le_div_iff_mul_le hd

theorem ozMulDiv_eq_some {x y d z : ℕ} {up : Bool} :
    ozMulDiv x y d up = some z ↔
      d ≠ 0 ∧ z ≤ MAX ∧
        z = (if up then ceilDiv (x * y) d else x * y / d) := by
  unfold ozMulDiv
  cases up <;> simp only [Bool.false_eq_true, false_and, ↓reduceIte, add_zero, true_and,
    ceilDiv_eq] <;> split_ifs <;> simp_all <;> omega

end EvmLeanSpecs.Vault
