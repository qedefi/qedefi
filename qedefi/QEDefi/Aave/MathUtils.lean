module

public import QEDefi.Aave.WadRayMath

/-!
# Aave v3 `MathUtils`: linear and compounded interest

`calculateLinearInterest(rate, last)` (checked arithmetic) and
`calculateCompoundedInterest(rate, last, now)`, whose body is `unchecked`: `rate * exp` and the
final sums wrap modulo `2^256`, while the two `rayMul` calls keep their own overflow revert.
Both take `block.timestamp` explicitly as `now`; `now - last` is checked in both.

Results: both factors are `≥ RAY`, monotone in the rate and the elapsed time, and
`compounded ≥ linear` for the same rate and period. The wrap-around of the `unchecked` block
never happens on a successful call (`calculateCompoundedInterest_eq_some`): the `rayMul`
overflow tests bound `x` well below `2^256`.
-/

section

@[expose] public section

namespace QEDefi.Aave
open QEDefi.Math

/-- `MathUtils.SECONDS_PER_YEAR = 365 days`. -/
def SECONDS_PER_YEAR : ℕ := 365 * 24 * 3600

/-- `MathUtils.calculateLinearInterest(rate, lastUpdateTimestamp)` at `block.timestamp = now`:
`RAY + rate * (now - last) / SECONDS_PER_YEAR`, all checked. -/
def calculateLinearInterest (rate last now : ℕ) : Option ℕ :=
  if now < last then none else
  if MAX < rate * (now - last) then none else
  let result := rate * (now - last) / SECONDS_PER_YEAR
  if MAX < RAY + result then none else some (RAY + result)

/-- `MathUtils.calculateCompoundedInterest(rate, lastUpdateTimestamp, currentTimestamp)`:
`exp = now - last` (checked); `RAY` if `exp = 0`; otherwise, unchecked,
`x = rate * exp / SECONDS_PER_YEAR` and `RAY + x + x.rayMul(x / 2 + x.rayMul(x / 6))`. -/
def calculateCompoundedInterest (rate last now : ℕ) : Option ℕ :=
  if now < last then none else
  let exp := now - last
  if exp = 0 then some RAY else
  let x := rate * exp % U256 / SECONDS_PER_YEAR
  (rayMul x (x / 6)).bind fun t1 =>
  (rayMul x ((x / 2 + t1) % U256)).map fun t2 => (RAY + x + t2) % U256

/-- The rate-time product scaled to a year, as both interest functions compute it. -/
def yearFrac (rate dt : ℕ) : ℕ := rate * dt / SECONDS_PER_YEAR

/-- The second- and third-order Taylor terms of the compounded factor,
`x ⊗ (x/2 + x ⊗ (x/6))` with half-up `rayMul` (no overflow). -/
def taylorTail (x : ℕ) : ℕ :=
  (x * (x / 2 + (x * (x / 6) + RAY / 2) / RAY) + RAY / 2) / RAY

theorem SECONDS_PER_YEAR_pos : 0 < SECONDS_PER_YEAR := by unfold SECONDS_PER_YEAR; norm_num

/-! ## Linear interest -/

theorem calculateLinearInterest_eq_some {rate last now f : ℕ} :
    calculateLinearInterest rate last now = some f ↔
      last ≤ now ∧ rate * (now - last) ≤ MAX ∧ RAY + yearFrac rate (now - last) ≤ MAX ∧
        f = RAY + yearFrac rate (now - last) := by
  unfold calculateLinearInterest yearFrac
  dsimp only
  split_ifs with h1 h2 h3 <;> simp only [false_iff, not_and, Option.some.injEq] <;> omega

theorem ray_le_calculateLinearInterest {rate last now f : ℕ}
    (h : calculateLinearInterest rate last now = some f) : RAY ≤ f := by
  obtain ⟨-, -, -, rfl⟩ := calculateLinearInterest_eq_some.1 h
  omega

/-- Linear interest is monotone in the rate and the elapsed time; success of the larger call
implies success of the smaller one. -/
theorem calculateLinearInterest_mono {rate rate' last now last' now' f' : ℕ}
    (h' : calculateLinearInterest rate' last' now' = some f') (hr : rate ≤ rate')
    (hle : last ≤ now) (hdt : now - last ≤ now' - last') :
    ∃ f, calculateLinearInterest rate last now = some f ∧ f ≤ f' := by
  obtain ⟨-, h1, h2, rfl⟩ := calculateLinearInterest_eq_some.1 h'
  have hm : rate * (now - last) ≤ rate' * (now' - last') := Nat.mul_le_mul hr hdt
  have hy : yearFrac rate (now - last) ≤ yearFrac rate' (now' - last') :=
    Nat.div_le_div_right hm
  exact ⟨_, calculateLinearInterest_eq_some.2 ⟨hle, by omega, by omega, rfl⟩, by omega⟩

/-! ## Compounded interest -/

private theorem lt_of_mul_div6_le {x : ℕ} (h : x * (x / 6) + RAY / 2 ≤ MAX) : x < 2 ^ 131 := by
  by_contra hc
  push Not at hc
  have h6 : 2 ^ 128 ≤ x / 6 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
  have : 2 ^ 131 * 2 ^ 128 ≤ x * (x / 6) := Nat.mul_le_mul hc h6
  unfold MAX at h; norm_num at this h; omega

private theorem rayMul_le_div {a b c : ℕ} (h : rayMul a b = some c) : c ≤ MAX / RAY := by
  obtain ⟨h1, rfl⟩ := rayMul_eq_some.1 h
  exact Nat.div_le_div_right h1

private theorem MAX_div_RAY_lt : MAX / RAY < 2 ^ 167 := by
  unfold MAX RAY; norm_num

/-- A successful compounded-interest call never wraps: it returns `RAY` for `now = last` and
`RAY + x + taylorTail x` otherwise, `x = (rate * exp mod 2^256) / SECONDS_PER_YEAR`, with both
`rayMul` overflow tests passing. -/
theorem calculateCompoundedInterest_eq_some {rate last now f : ℕ} :
    calculateCompoundedInterest rate last now = some f ↔
      last ≤ now ∧
        (now = last ∧ f = RAY ∨
          now ≠ last ∧
            let x := rate * (now - last) % U256 / SECONDS_PER_YEAR
            x * (x / 6) + RAY / 2 ≤ MAX ∧
              x * (x / 2 + (x * (x / 6) + RAY / 2) / RAY) + RAY / 2 ≤ MAX ∧
              f = RAY + x + taylorTail x) := by
  unfold calculateCompoundedInterest
  dsimp only
  split_ifs with h1 h2
  · simp only [false_iff, not_and]; omega
  · simp only [Option.some.injEq]; constructor
    · rintro rfl; exact ⟨by omega, Or.inl ⟨by omega, rfl⟩⟩
    · rintro ⟨-, ⟨-, rfl⟩ | ⟨h, -⟩⟩
      · rfl
      · omega
  · set x := rate * (now - last) % U256 / SECONDS_PER_YEAR with hx
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff]
    constructor
    · rintro ⟨t1, ht1, t2, ht2, rfl⟩
      obtain ⟨ha, rfl⟩ := rayMul_eq_some.1 ht1
      have hx131 := lt_of_mul_div6_le ha
      have ht1le := rayMul_le_div ht1
      have hlt : x / 2 + (x * (x / 6) + RAY / 2) / RAY < U256 := by
        have := MAX_div_RAY_lt; unfold U256; omega
      rw [Nat.mod_eq_of_lt hlt] at ht2
      obtain ⟨hb, rfl⟩ := rayMul_eq_some.1 ht2
      have ht2le : (x * (x / 2 + (x * (x / 6) + RAY / 2) / RAY) + RAY / 2) / RAY ≤ MAX / RAY :=
        Nat.div_le_div_right hb
      refine ⟨by omega, Or.inr ⟨by omega, ha, hb, ?_⟩⟩
      unfold taylorTail
      rw [Nat.mod_eq_of_lt]
      have := MAX_div_RAY_lt; unfold U256 RAY at *; omega
    · rintro ⟨-, ⟨h, -⟩ | ⟨-, ha, hb, rfl⟩⟩
      · omega
      have hx131 := lt_of_mul_div6_le ha
      have ht1le : (x * (x / 6) + RAY / 2) / RAY ≤ MAX / RAY := Nat.div_le_div_right ha
      have hlt : x / 2 + (x * (x / 6) + RAY / 2) / RAY < U256 := by
        have := MAX_div_RAY_lt; unfold U256; omega
      refine ⟨_, rayMul_eq_some.2 ⟨ha, rfl⟩, taylorTail x, ?_, ?_⟩
      · rw [Nat.mod_eq_of_lt hlt]; exact rayMul_eq_some.2 ⟨hb, rfl⟩
      · have ht2le : taylorTail x ≤ MAX / RAY := Nat.div_le_div_right hb
        unfold taylorTail at ht2le ⊢
        rw [Nat.mod_eq_of_lt]
        have := MAX_div_RAY_lt; unfold U256 RAY at *; omega

theorem ray_le_calculateCompoundedInterest {rate last now f : ℕ}
    (h : calculateCompoundedInterest rate last now = some f) : RAY ≤ f := by
  obtain ⟨-, ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩⟩ := calculateCompoundedInterest_eq_some.1 h
  · exact le_refl _
  · rw [Nat.add_assoc]; exact Nat.le_add_right _ _

/-- The compounded factor dominates the linear one for the same rate and period. -/
theorem calculateLinearInterest_le_compounded {rate last now l c : ℕ}
    (hl : calculateLinearInterest rate last now = some l)
    (hc : calculateCompoundedInterest rate last now = some c) : l ≤ c := by
  obtain ⟨-, hm, -, rfl⟩ := calculateLinearInterest_eq_some.1 hl
  obtain ⟨-, ⟨he, rfl⟩ | ⟨-, -, -, rfl⟩⟩ := calculateCompoundedInterest_eq_some.1 hc
  · subst he; simp [yearFrac]
  · have hmod : rate * (now - last) % U256 = rate * (now - last) :=
      Nat.mod_eq_of_lt (by unfold MAX U256 at *; omega)
    rw [hmod]; unfold yearFrac; omega

theorem taylorTail_mono {x y : ℕ} (h : x ≤ y) : taylorTail x ≤ taylorTail y := by
  unfold taylorTail
  apply Nat.div_le_div_right
  have h1 : x * (x / 6) ≤ y * (y / 6) := Nat.mul_le_mul h (Nat.div_le_div_right h)
  have h2 : (x * (x / 6) + RAY / 2) / RAY ≤ (y * (y / 6) + RAY / 2) / RAY :=
    Nat.div_le_div_right (by omega)
  have h3 : x / 2 ≤ y / 2 := Nat.div_le_div_right h
  have := Nat.mul_le_mul h (Nat.add_le_add h3 h2)
  omega

/-- Compounded interest is monotone in the rate and the elapsed time, provided the larger
`rate * exp` does not wrap (it never does for a `uint128` rate and `uint40` timestamps);
success of the larger call implies success of the smaller one. -/
theorem calculateCompoundedInterest_mono {rate rate' last now last' now' f' : ℕ}
    (h' : calculateCompoundedInterest rate' last' now' = some f')
    (hw : rate' * (now' - last') ≤ MAX) (hr : rate ≤ rate')
    (hle : last ≤ now) (hdt : now - last ≤ now' - last') :
    ∃ f, calculateCompoundedInterest rate last now = some f ∧ f ≤ f' := by
  have hray := ray_le_calculateCompoundedInterest h'
  by_cases h0 : now = last
  · refine ⟨RAY, calculateCompoundedInterest_eq_some.2 ⟨hle, Or.inl ⟨h0, rfl⟩⟩, hray⟩
  obtain ⟨-, ⟨h0', -⟩ | ⟨-, ha', hb', rfl⟩⟩ := calculateCompoundedInterest_eq_some.1 h'
  · omega
  have hm : rate * (now - last) ≤ rate' * (now' - last') := Nat.mul_le_mul hr hdt
  have hU : MAX < U256 := MAX_lt_U256
  rw [Nat.mod_eq_of_lt (by omega)] at ha' hb' ⊢
  set x := rate * (now - last) / SECONDS_PER_YEAR with hx
  set y := rate' * (now' - last') / SECONDS_PER_YEAR
  have hxy : x ≤ y := Nat.div_le_div_right hm
  have h1 : x * (x / 6) ≤ y * (y / 6) := Nat.mul_le_mul hxy (Nat.div_le_div_right hxy)
  have h2 : (x * (x / 6) + RAY / 2) / RAY ≤ (y * (y / 6) + RAY / 2) / RAY :=
    Nat.div_le_div_right (by omega)
  have h3 : x / 2 ≤ y / 2 := Nat.div_le_div_right hxy
  have h4 := Nat.mul_le_mul hxy (Nat.add_le_add h3 h2)
  refine ⟨RAY + x + taylorTail x, ?_, ?_⟩
  · refine calculateCompoundedInterest_eq_some.2 ⟨hle, Or.inr ⟨h0, ?_, ?_, ?_⟩⟩
    · rw [Nat.mod_eq_of_lt (by omega), ← hx]; omega
    · rw [Nat.mod_eq_of_lt (by omega), ← hx]; omega
    · rw [Nat.mod_eq_of_lt (by omega), ← hx]
  · have := taylorTail_mono hxy; omega

end QEDefi.Aave
end

end
