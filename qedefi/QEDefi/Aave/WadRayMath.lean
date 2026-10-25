module

public import QEDefi.Math.Arith

/-!
# Aave v3 `WadRayMath`, `PercentageMath` and `MathUtils.mulDivCeil`

The fixed-point libraries of the deployed Aave v3.7 Pool (`PoolInstance`, `POOL_REVISION = 11`),
as `ℕ → ℕ → Option ℕ` (`none` = revert), mirroring the assembly of each function including its
overflow test, evaluated on words (`a, b ≤ MAX`).

The three libraries share five shapes, defined once with the unit `U` as a parameter:

* `halfUpMul U a b`: `rayMul`/`wadMul`/`percentMul`. Revert iff `b ≠ 0 ∧ a > (MAX - U/2) / b`,
  result `(a*b + U/2) / U` (`HALF_RAY = RAY/2`, `HALF_WAD = WAD/2`, `HALF_PERCENTAGE_FACTOR =
  PERCENTAGE_FACTOR/2`).
* `floorMul U`/`ceilMul U`: `rayMulFloor`/`rayMulCeil`/`percentMulFloor`/`percentMulCeil`.
  Revert iff `b ≠ 0 ∧ a > MAX / b`; result `a*b / U`, resp. `a*b / U + (a*b % U ≠ 0)`.
* `halfUpDiv U a b`: `rayDiv`/`wadDiv`/`percentDiv`. Revert iff `b = 0 ∨ a > (MAX - b/2) / U`,
  result `(a*U + b/2) / b`.
* `floorDiv U`/`ceilDivU U`: `rayDivFloor`/`rayDivCeil`/`percentDivFloor`/`percentDivCeil`.
  Revert iff `b = 0 ∨ a > MAX / U`; result `a*U / b`, resp. rounded up.

The theorems give for each shape the exact success/revert condition (`*_eq_some`, `*_eq_none`),
the rounding error bounds (`*_bounds`) and monotonicity (`*_mono`).
-/

section

@[expose] public section

namespace QEDefi.Aave
open QEDefi.Math

/-- `WadRayMath.WAD = 1e18`. -/
def WAD : ℕ := 10 ^ 18

/-- `WadRayMath.RAY = 1e27`. -/
def RAY : ℕ := 10 ^ 27

/-- `PercentageMath.PERCENTAGE_FACTOR = 1e4` (100.00%). -/
def PERCENTAGE_FACTOR : ℕ := 10 ^ 4

/-- `WadRayMath.WAD_RAY_RATIO = 1e9`. -/
def WAD_RAY_RATIO : ℕ := 10 ^ 9

theorem RAY_pos : 0 < RAY := by unfold RAY; norm_num
theorem WAD_pos : 0 < WAD := by unfold WAD; norm_num
theorem PERCENTAGE_FACTOR_pos : 0 < PERCENTAGE_FACTOR := by unfold PERCENTAGE_FACTOR; norm_num

/-! ## The five shapes -/

/-- Half-up multiplication `a ⊗ b` in unit `U` (`rayMul`, `wadMul`, `percentMul`):
`if iszero(or(iszero(b), iszero(gt(a, div(sub(not(0), HALF), b))))) { revert }`,
`c := div(add(mul(a, b), HALF), U)` with `HALF = U / 2`. -/
def halfUpMul (U a b : ℕ) : Option ℕ :=
  if b ≠ 0 ∧ (MAX - U / 2) / b < a then none else some ((a * b + U / 2) / U)

/-- Floor multiplication (`rayMulFloor`, `percentMulFloor`):
revert iff `b ≠ 0 ∧ a > MAX / b`, `c := div(mul(a, b), U)`. -/
def floorMul (U a b : ℕ) : Option ℕ :=
  if b ≠ 0 ∧ MAX / b < a then none else some (a * b / U)

/-- Ceiling multiplication (`rayMulCeil`, `percentMulCeil`):
revert iff `b ≠ 0 ∧ a > MAX / b`, `c := add(div(p, U), iszero(iszero(mod(p, U))))`. -/
def ceilMul (U a b : ℕ) : Option ℕ :=
  if b ≠ 0 ∧ MAX / b < a then none else some (ceilDiv (a * b) U)

/-- Half-up division (`rayDiv`, `wadDiv`, `percentDiv`):
`if or(iszero(b), gt(a, div(sub(not(0), div(b, 2)), U))) { revert }`,
`c := div(add(mul(a, U), div(b, 2)), b)`. -/
def halfUpDiv (U a b : ℕ) : Option ℕ :=
  if b = 0 ∨ (MAX - b / 2) / U < a then none else some ((a * U + b / 2) / b)

/-- Floor division (`rayDivFloor`, `percentDivFloor`):
revert iff `b = 0 ∨ a > MAX / U`, `c := div(mul(a, U), b)`. -/
def floorDiv (U a b : ℕ) : Option ℕ :=
  if b = 0 ∨ MAX / U < a then none else some (a * U / b)

/-- Ceiling division (`rayDivCeil`, `percentDivCeil`):
revert iff `b = 0 ∨ a > MAX / U`, `c := add(div(s, b), iszero(iszero(mod(s, b))))`, `s = a*U`. -/
def ceilDivU (U a b : ℕ) : Option ℕ :=
  if b = 0 ∨ MAX / U < a then none else some (ceilDiv (a * U) b)

/-! ## The library functions -/

/-- `WadRayMath.wadMul`. -/
def wadMul (a b : ℕ) : Option ℕ := halfUpMul WAD a b
/-- `WadRayMath.wadDiv`. -/
def wadDiv (a b : ℕ) : Option ℕ := halfUpDiv WAD a b
/-- `WadRayMath.rayMul`. -/
def rayMul (a b : ℕ) : Option ℕ := halfUpMul RAY a b
/-- `WadRayMath.rayMulFloor`. -/
def rayMulFloor (a b : ℕ) : Option ℕ := floorMul RAY a b
/-- `WadRayMath.rayMulCeil`. -/
def rayMulCeil (a b : ℕ) : Option ℕ := ceilMul RAY a b
/-- `WadRayMath.rayDiv`. -/
def rayDiv (a b : ℕ) : Option ℕ := halfUpDiv RAY a b
/-- `WadRayMath.rayDivFloor`. -/
def rayDivFloor (a b : ℕ) : Option ℕ := floorDiv RAY a b
/-- `WadRayMath.rayDivCeil`. -/
def rayDivCeil (a b : ℕ) : Option ℕ := ceilDivU RAY a b
/-- `PercentageMath.percentMul`. -/
def percentMul (v p : ℕ) : Option ℕ := halfUpMul PERCENTAGE_FACTOR v p
/-- `PercentageMath.percentMulFloor`. -/
def percentMulFloor (v p : ℕ) : Option ℕ := floorMul PERCENTAGE_FACTOR v p
/-- `PercentageMath.percentMulCeil`. -/
def percentMulCeil (v p : ℕ) : Option ℕ := ceilMul PERCENTAGE_FACTOR v p
/-- `PercentageMath.percentDiv`. -/
def percentDiv (v p : ℕ) : Option ℕ := halfUpDiv PERCENTAGE_FACTOR v p
/-- `PercentageMath.percentDivFloor`. -/
def percentDivFloor (v p : ℕ) : Option ℕ := floorDiv PERCENTAGE_FACTOR v p
/-- `PercentageMath.percentDivCeil`. -/
def percentDivCeil (v p : ℕ) : Option ℕ := ceilDivU PERCENTAGE_FACTOR v p

/-- `WadRayMath.rayToWad`: `b := div(a, 1e9)`, plus one if `mod(a, 1e9) ≥ 1e9 / 2`. -/
def rayToWad (a : ℕ) : ℕ :=
  a / WAD_RAY_RATIO + (if a % WAD_RAY_RATIO < WAD_RAY_RATIO / 2 then 0 else 1)

/-- `WadRayMath.wadToRay`: `b := mul(a, 1e9)` (mod `2^256`), revert iff `div(b, 1e9) ≠ a`. -/
def wadToRay (a : ℕ) : Option ℕ :=
  let b := a * WAD_RAY_RATIO % U256
  if b / WAD_RAY_RATIO ≠ a then none else some b

/-- `MathUtils.mulDivCeil(a, b, c)`: revert iff `c = 0` or `a * b` overflows; result
`⌈a*b / c⌉`. -/
def mulDivCeil (a b c : ℕ) : Option ℕ :=
  if c = 0 then none else if b ≠ 0 ∧ MAX / b < a then none else some (ceilDiv (a * b) c)

/-! ## Exact characterisations -/

theorem halfUpMul_eq_some {U a b c : ℕ} (hU : U / 2 ≤ MAX) :
    halfUpMul U a b = some c ↔ a * b + U / 2 ≤ MAX ∧ c = (a * b + U / 2) / U := by
  unfold halfUpMul
  by_cases hb : b = 0
  · subst hb; simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, mul_zero, zero_add,
      Option.some.injEq]; constructor
    · rintro rfl; exact ⟨hU, rfl⟩
    · rintro ⟨-, rfl⟩; rfl
  · have key : (MAX - U / 2) / b < a ↔ MAX < a * b + U / 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hb)]; omega
    simp only [ne_eq, hb, not_false_eq_true, true_and, key]
    split_ifs with h
    · simp only [false_iff, not_and]; omega
    · simp only [Option.some.injEq]; constructor
      · rintro rfl; exact ⟨by omega, rfl⟩
      · rintro ⟨-, rfl⟩; rfl

theorem halfUpMul_eq_none {U a b : ℕ} (hU : U / 2 ≤ MAX) :
    halfUpMul U a b = none ↔ MAX < a * b + U / 2 := by
  rcases h : halfUpMul U a b with _ | c
  · simp only [true_iff]
    by_contra hc
    have := (halfUpMul_eq_some (a := a) (b := b) (c := (a * b + U / 2) / U) hU).2 ⟨by omega, rfl⟩
    rw [h] at this; exact absurd this (by simp)
  · simp only [reduceCtorEq, false_iff, not_lt]
    exact ((halfUpMul_eq_some hU).1 h).1

theorem floorMul_eq_some {U a b c : ℕ} :
    floorMul U a b = some c ↔ a * b ≤ MAX ∧ c = a * b / U := by
  unfold floorMul
  simp only [overflow_test_iff]
  split_ifs with h
  · simp only [false_iff, not_and]; omega
  · simp only [Option.some.injEq]; omega

theorem floorMul_eq_none {U a b : ℕ} : floorMul U a b = none ↔ MAX < a * b := by
  unfold floorMul; simp only [overflow_test_iff]; split_ifs with h <;> simp_all

theorem ceilMul_eq_some {U a b c : ℕ} :
    ceilMul U a b = some c ↔ a * b ≤ MAX ∧ c = ceilDiv (a * b) U := by
  unfold ceilMul
  simp only [overflow_test_iff]
  split_ifs with h
  · simp only [false_iff, not_and]; omega
  · simp only [Option.some.injEq]; omega

theorem ceilMul_eq_none {U a b : ℕ} : ceilMul U a b = none ↔ MAX < a * b := by
  unfold ceilMul; simp only [overflow_test_iff]; split_ifs with h <;> simp_all

theorem halfUpDiv_eq_some {U a b c : ℕ} (hU : 0 < U) (hb : b ≤ MAX) :
    halfUpDiv U a b = some c ↔ b ≠ 0 ∧ a * U + b / 2 ≤ MAX ∧ c = (a * U + b / 2) / b := by
  unfold halfUpDiv
  have key : (MAX - b / 2) / U < a ↔ MAX < a * U + b / 2 := by
    rw [Nat.div_lt_iff_lt_mul hU]; omega
  simp only [key]
  split_ifs with h
  · simp only [false_iff, not_and]; omega
  · simp only [Option.some.injEq]; omega

theorem halfUpDiv_eq_none {U a b : ℕ} (hU : 0 < U) (hb : b ≤ MAX) :
    halfUpDiv U a b = none ↔ b = 0 ∨ MAX < a * U + b / 2 := by
  unfold halfUpDiv
  have key : (MAX - b / 2) / U < a ↔ MAX < a * U + b / 2 := by
    rw [Nat.div_lt_iff_lt_mul hU]; omega
  simp only [key]; split_ifs with h <;> simp_all

theorem floorDiv_eq_some {U a b c : ℕ} (hU : 0 < U) :
    floorDiv U a b = some c ↔ b ≠ 0 ∧ a * U ≤ MAX ∧ c = a * U / b := by
  unfold floorDiv
  have key : MAX / U < a ↔ MAX < a * U := Nat.div_lt_iff_lt_mul hU
  simp only [key]
  split_ifs with h
  · simp only [false_iff, not_and]; omega
  · simp only [Option.some.injEq]; omega

theorem floorDiv_eq_none {U a b : ℕ} (hU : 0 < U) :
    floorDiv U a b = none ↔ b = 0 ∨ MAX < a * U := by
  unfold floorDiv
  have key : MAX / U < a ↔ MAX < a * U := Nat.div_lt_iff_lt_mul hU
  simp only [key]; split_ifs with h <;> simp_all

theorem ceilDivU_eq_some {U a b c : ℕ} (hU : 0 < U) :
    ceilDivU U a b = some c ↔ b ≠ 0 ∧ a * U ≤ MAX ∧ c = ceilDiv (a * U) b := by
  unfold ceilDivU
  have key : MAX / U < a ↔ MAX < a * U := Nat.div_lt_iff_lt_mul hU
  simp only [key]
  split_ifs with h
  · simp only [false_iff, not_and]; omega
  · simp only [Option.some.injEq]; omega

theorem ceilDivU_eq_none {U a b : ℕ} (hU : 0 < U) :
    ceilDivU U a b = none ↔ b = 0 ∨ MAX < a * U := by
  unfold ceilDivU
  have key : MAX / U < a ↔ MAX < a * U := Nat.div_lt_iff_lt_mul hU
  simp only [key]; split_ifs with h <;> simp_all

theorem mulDivCeil_eq_some {a b c d : ℕ} :
    mulDivCeil a b c = some d ↔ c ≠ 0 ∧ a * b ≤ MAX ∧ d = ceilDiv (a * b) c := by
  unfold mulDivCeil
  simp only [overflow_test_iff]
  split_ifs with h1 h2
  · simp only [false_iff, not_and]; omega
  · simp only [false_iff, not_and]; omega
  · simp only [Option.some.injEq]; omega

theorem wadToRay_eq_some {a b : ℕ} (ha : a ≤ MAX) :
    wadToRay a = some b ↔ a * WAD_RAY_RATIO ≤ MAX ∧ b = a * WAD_RAY_RATIO := by
  unfold wadToRay
  simp only [ne_eq, ite_not, Option.ite_none_right_eq_some, Option.some.injEq]
  unfold WAD_RAY_RATIO MAX U256 at *
  constructor
  · rintro ⟨h1, rfl⟩
    by_contra hc
    have hlt : a * 10 ^ 9 % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ (by norm_num)
    have hge : 2 ^ 256 ≤ a * 10 ^ 9 := by omega
    have hq : a * 10 ^ 9 % 2 ^ 256 ≤ a * 10 ^ 9 - 2 ^ 256 := by
      rw [Nat.mod_eq_sub_mod hge]; exact Nat.mod_le _ _
    have : a * 10 ^ 9 % 2 ^ 256 / 10 ^ 9 < a := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]; omega
    omega
  · rintro ⟨h1, rfl⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    exact ⟨Nat.mul_div_cancel _ (by norm_num), rfl⟩

/-! ## Rounding error bounds -/

theorem halfUpMul_bounds {U a b c : ℕ} (hU : 0 < U) (h : halfUpMul U a b = some c) :
    c * U ≤ a * b + U / 2 ∧ a * b + U / 2 < (c + 1) * U := by
  unfold halfUpMul at h
  split_ifs at h with h0
  cases h
  exact ⟨Nat.div_mul_le_self _ _, lt_div_add_one_mul _ _ hU⟩

theorem floorMul_bounds {U a b c : ℕ} (hU : 0 < U) (h : floorMul U a b = some c) :
    c * U ≤ a * b ∧ a * b < (c + 1) * U := by
  obtain ⟨-, rfl⟩ := floorMul_eq_some.1 h
  exact ⟨Nat.div_mul_le_self _ _, lt_div_add_one_mul _ _ hU⟩

theorem ceilMul_bounds {U a b c : ℕ} (hU : 0 < U) (h : ceilMul U a b = some c) :
    a * b ≤ c * U ∧ c * U < a * b + U := by
  obtain ⟨-, rfl⟩ := ceilMul_eq_some.1 h
  exact ⟨le_ceilDiv_mul _ _ hU, ceilDiv_mul_lt _ _ hU⟩

theorem halfUpDiv_bounds {U a b c : ℕ} (hU : 0 < U) (hb : b ≤ MAX)
    (h : halfUpDiv U a b = some c) :
    c * b ≤ a * U + b / 2 ∧ a * U + b / 2 < (c + 1) * b := by
  obtain ⟨hb0, -, rfl⟩ := (halfUpDiv_eq_some hU hb).1 h
  exact ⟨Nat.div_mul_le_self _ _, lt_div_add_one_mul _ _ (Nat.pos_of_ne_zero hb0)⟩

theorem floorDiv_bounds {U a b c : ℕ} (hU : 0 < U) (h : floorDiv U a b = some c) :
    c * b ≤ a * U ∧ a * U < (c + 1) * b := by
  obtain ⟨hb0, -, rfl⟩ := (floorDiv_eq_some hU).1 h
  exact ⟨Nat.div_mul_le_self _ _, lt_div_add_one_mul _ _ (Nat.pos_of_ne_zero hb0)⟩

theorem ceilDivU_bounds {U a b c : ℕ} (hU : 0 < U) (h : ceilDivU U a b = some c) :
    a * U ≤ c * b ∧ c * b < a * U + b := by
  obtain ⟨hb0, -, rfl⟩ := (ceilDivU_eq_some hU).1 h
  exact ⟨le_ceilDiv_mul _ _ (Nat.pos_of_ne_zero hb0),
    ceilDiv_mul_lt _ _ (Nat.pos_of_ne_zero hb0)⟩

/-! ## Monotonicity

No-overflow is downward closed and the result is monotone: if the larger arguments succeed,
so do the smaller ones, with a smaller or equal result. Divisions are monotone in the
numerator and antitone in the denominator. -/

theorem halfUpMul_mono {U a b a' b' c' : ℕ} (hU : U / 2 ≤ MAX) (h : halfUpMul U a' b' = some c')
    (ha : a ≤ a') (hb : b ≤ b') : ∃ c, halfUpMul U a b = some c ∧ c ≤ c' := by
  obtain ⟨h1, rfl⟩ := (halfUpMul_eq_some hU).1 h
  have hm : a * b ≤ a' * b' := Nat.mul_le_mul ha hb
  exact ⟨_, (halfUpMul_eq_some hU).2 ⟨by omega, rfl⟩, Nat.div_le_div_right (by omega)⟩

theorem floorMul_mono {U a b a' b' c' : ℕ} (h : floorMul U a' b' = some c')
    (ha : a ≤ a') (hb : b ≤ b') : ∃ c, floorMul U a b = some c ∧ c ≤ c' := by
  obtain ⟨h1, rfl⟩ := floorMul_eq_some.1 h
  have hm : a * b ≤ a' * b' := Nat.mul_le_mul ha hb
  exact ⟨_, floorMul_eq_some.2 ⟨by omega, rfl⟩, Nat.div_le_div_right hm⟩

theorem ceilDiv_mono {m m' d : ℕ} (hd : 0 < d) (h : m ≤ m') : ceilDiv m d ≤ ceilDiv m' d :=
  (ceilDiv_le_iff m d _ hd).2 (h.trans (le_ceilDiv_mul m' d hd))

theorem ceilMul_mono {U a b a' b' c' : ℕ} (hU : 0 < U) (h : ceilMul U a' b' = some c')
    (ha : a ≤ a') (hb : b ≤ b') : ∃ c, ceilMul U a b = some c ∧ c ≤ c' := by
  obtain ⟨h1, rfl⟩ := ceilMul_eq_some.1 h
  have hm : a * b ≤ a' * b' := Nat.mul_le_mul ha hb
  exact ⟨_, ceilMul_eq_some.2 ⟨by omega, rfl⟩, ceilDiv_mono hU hm⟩

theorem halfUpDiv_mono_left {U a a' b c' : ℕ} (hU : 0 < U) (hb : b ≤ MAX)
    (h : halfUpDiv U a' b = some c') (ha : a ≤ a') : ∃ c, halfUpDiv U a b = some c ∧ c ≤ c' := by
  obtain ⟨hb0, h1, rfl⟩ := (halfUpDiv_eq_some hU hb).1 h
  have hm : a * U ≤ a' * U := Nat.mul_le_mul_right U ha
  exact ⟨_, (halfUpDiv_eq_some hU hb).2 ⟨hb0, by omega, rfl⟩, Nat.div_le_div_right (by omega)⟩

/-- Antitone in the denominator when both succeed. (Success itself is not downward closed in
the denominator: the overflow test `a*U + b/2 ≤ MAX` gets harder as `b` grows.) -/
theorem halfUpDiv_anti_right {U a b b' c c' : ℕ} (hU : 0 < U) (hb' : b' ≤ MAX)
    (h : halfUpDiv U a b = some c) (h' : halfUpDiv U a b' = some c') (hbb : b ≤ b') :
    c' ≤ c := by
  have hb : b ≤ MAX := hbb.trans hb'
  obtain ⟨hb0, -, rfl⟩ := (halfUpDiv_eq_some hU hb).1 h
  obtain ⟨-, -, rfl⟩ := (halfUpDiv_eq_some hU hb').1 h'
  set c' := (a * U + b' / 2) / b'
  rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hb0)]
  have hc' : c' * b' ≤ a * U + b' / 2 := Nat.div_mul_le_self _ _
  rcases Nat.eq_zero_or_pos c' with h0 | hpos
  · rw [h0]; omega
  · have hsplit : c' * b' = c' * b + c' * (b' - b) := by
      rw [← Nat.mul_add]; congr 1; omega
    have : b' - b ≤ c' * (b' - b) := Nat.le_mul_of_pos_left _ hpos
    omega

theorem floorDiv_mono_left {U a a' b c' : ℕ} (hU : 0 < U) (h : floorDiv U a' b = some c')
    (ha : a ≤ a') : ∃ c, floorDiv U a b = some c ∧ c ≤ c' := by
  obtain ⟨hb0, h1, rfl⟩ := (floorDiv_eq_some hU).1 h
  have hm : a * U ≤ a' * U := Nat.mul_le_mul_right U ha
  exact ⟨_, (floorDiv_eq_some hU).2 ⟨hb0, by omega, rfl⟩, Nat.div_le_div_right hm⟩

theorem floorDiv_anti_right {U a b b' c : ℕ} (hU : 0 < U) (h : floorDiv U a b = some c)
    (hbb : b ≤ b') : ∃ c', floorDiv U a b' = some c' ∧ c' ≤ c := by
  obtain ⟨hb0, h1, rfl⟩ := (floorDiv_eq_some hU).1 h
  exact ⟨_, (floorDiv_eq_some hU).2 ⟨by omega, h1, rfl⟩,
    Nat.div_le_div_left hbb (Nat.pos_of_ne_zero hb0)⟩

theorem ceilDivU_mono_left {U a a' b c' : ℕ} (hU : 0 < U) (h : ceilDivU U a' b = some c')
    (ha : a ≤ a') : ∃ c, ceilDivU U a b = some c ∧ c ≤ c' := by
  obtain ⟨hb0, h1, rfl⟩ := (ceilDivU_eq_some hU).1 h
  have hm : a * U ≤ a' * U := Nat.mul_le_mul_right U ha
  exact ⟨_, (ceilDivU_eq_some hU).2 ⟨hb0, by omega, rfl⟩,
    ceilDiv_mono (Nat.pos_of_ne_zero hb0) hm⟩

theorem ceilDivU_anti_right {U a b b' c : ℕ} (hU : 0 < U) (h : ceilDivU U a b = some c)
    (hbb : b ≤ b') : ∃ c', ceilDivU U a b' = some c' ∧ c' ≤ c := by
  obtain ⟨hb0, h1, rfl⟩ := (ceilDivU_eq_some hU).1 h
  have hb' : 0 < b' := by omega
  refine ⟨_, (ceilDivU_eq_some hU).2 ⟨by omega, h1, rfl⟩, ?_⟩
  rw [ceilDiv_le_iff _ _ _ hb']
  exact (le_ceilDiv_mul _ _ (Nat.pos_of_ne_zero hb0)).trans (Nat.mul_le_mul_left _ hbb)

/-! ## Rounding order: floor ≤ half-up ≤ ceil -/

theorem floorMul_le_halfUpMul {U a b c₁ c₂ : ℕ} (h₁ : floorMul U a b = some c₁)
    (h₂ : halfUpMul U a b = some c₂) : c₁ ≤ c₂ := by
  obtain ⟨-, rfl⟩ := floorMul_eq_some.1 h₁
  unfold halfUpMul at h₂
  split_ifs at h₂ with h
  cases h₂
  exact Nat.div_le_div_right (by omega)

theorem halfUpMul_le_ceilMul {U a b c₁ c₂ : ℕ} (hU : 0 < U) (h₁ : halfUpMul U a b = some c₁)
    (h₂ : ceilMul U a b = some c₂) : c₁ ≤ c₂ := by
  obtain ⟨-, rfl⟩ := ceilMul_eq_some.1 h₂
  unfold halfUpMul at h₁
  split_ifs at h₁ with h
  cases h₁
  have h1 := le_ceilDiv_mul (a * b) U hU
  have h2 : a * b + U / 2 < (ceilDiv (a * b) U + 1) * U := by
    rw [Nat.add_mul]; have : U / 2 < U := Nat.div_lt_self hU (by norm_num)
    omega
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hU).2 h2)

/-! ## Specialisations used by the reserve logic -/

theorem rayMul_eq_some {a b c : ℕ} :
    rayMul a b = some c ↔ a * b + RAY / 2 ≤ MAX ∧ c = (a * b + RAY / 2) / RAY :=
  halfUpMul_eq_some (by unfold RAY MAX; norm_num)

theorem rayMul_eq_none {a b : ℕ} : rayMul a b = none ↔ MAX < a * b + RAY / 2 :=
  halfUpMul_eq_none (by unfold RAY MAX; norm_num)

theorem wadMul_eq_some {a b c : ℕ} :
    wadMul a b = some c ↔ a * b + WAD / 2 ≤ MAX ∧ c = (a * b + WAD / 2) / WAD :=
  halfUpMul_eq_some (by unfold WAD MAX; norm_num)

theorem percentMul_eq_some {a b c : ℕ} :
    percentMul a b = some c ↔
      a * b + PERCENTAGE_FACTOR / 2 ≤ MAX ∧ c = (a * b + PERCENTAGE_FACTOR / 2) / PERCENTAGE_FACTOR :=
  halfUpMul_eq_some (by unfold PERCENTAGE_FACTOR MAX; norm_num)

theorem rayDiv_eq_some {a b c : ℕ} (hb : b ≤ MAX) :
    rayDiv a b = some c ↔ b ≠ 0 ∧ a * RAY + b / 2 ≤ MAX ∧ c = (a * RAY + b / 2) / b :=
  halfUpDiv_eq_some RAY_pos hb

theorem wadDiv_eq_some {a b c : ℕ} (hb : b ≤ MAX) :
    wadDiv a b = some c ↔ b ≠ 0 ∧ a * WAD + b / 2 ≤ MAX ∧ c = (a * WAD + b / 2) / b :=
  halfUpDiv_eq_some WAD_pos hb

theorem rayMulFloor_eq_some {a b c : ℕ} :
    rayMulFloor a b = some c ↔ a * b ≤ MAX ∧ c = a * b / RAY := floorMul_eq_some

theorem rayMulCeil_eq_some {a b c : ℕ} :
    rayMulCeil a b = some c ↔ a * b ≤ MAX ∧ c = ceilDiv (a * b) RAY := ceilMul_eq_some

theorem rayDivFloor_eq_some {a b c : ℕ} :
    rayDivFloor a b = some c ↔ b ≠ 0 ∧ a * RAY ≤ MAX ∧ c = a * RAY / b :=
  floorDiv_eq_some RAY_pos

theorem rayDivCeil_eq_some {a b c : ℕ} :
    rayDivCeil a b = some c ↔ b ≠ 0 ∧ a * RAY ≤ MAX ∧ c = ceilDiv (a * RAY) b :=
  ceilDivU_eq_some RAY_pos

theorem rayMul_bounds {a b c : ℕ} (h : rayMul a b = some c) :
    c * RAY ≤ a * b + RAY / 2 ∧ a * b + RAY / 2 < (c + 1) * RAY := halfUpMul_bounds RAY_pos h

theorem rayMulFloor_bounds {a b c : ℕ} (h : rayMulFloor a b = some c) :
    c * RAY ≤ a * b ∧ a * b < (c + 1) * RAY := floorMul_bounds RAY_pos h

theorem rayMulCeil_bounds {a b c : ℕ} (h : rayMulCeil a b = some c) :
    a * b ≤ c * RAY ∧ c * RAY < a * b + RAY := ceilMul_bounds RAY_pos h

theorem rayDiv_bounds {a b c : ℕ} (hb : b ≤ MAX) (h : rayDiv a b = some c) :
    c * b ≤ a * RAY + b / 2 ∧ a * RAY + b / 2 < (c + 1) * b := halfUpDiv_bounds RAY_pos hb h

theorem rayDivFloor_bounds {a b c : ℕ} (h : rayDivFloor a b = some c) :
    c * b ≤ a * RAY ∧ a * RAY < (c + 1) * b := floorDiv_bounds RAY_pos h

theorem rayDivCeil_bounds {a b c : ℕ} (h : rayDivCeil a b = some c) :
    a * RAY ≤ c * b ∧ c * b < a * RAY + b := ceilDivU_bounds RAY_pos h

/-- Multiplying by a factor `≥ RAY` (an interest factor) never decreases: the index update
`rayMul(factor, index) ≥ index`. -/
theorem le_rayMul_of_ray_le {a b c : ℕ} (ha : RAY ≤ a) (h : rayMul a b = some c) : b ≤ c := by
  obtain ⟨-, rfl⟩ := rayMul_eq_some.1 h
  rw [Nat.le_div_iff_mul_le RAY_pos]
  have : RAY * b ≤ a * b := Nat.mul_le_mul_right b ha
  rw [Nat.mul_comm] at this; omega

/-- `rayMul(RAY, b) = b`. -/
theorem rayMul_ray {b : ℕ} (hb : b * RAY + RAY / 2 ≤ MAX) : rayMul RAY b = some b := by
  rw [rayMul_eq_some, Nat.mul_comm]
  refine ⟨hb, ?_⟩
  unfold RAY; omega

end QEDefi.Aave
end

end
