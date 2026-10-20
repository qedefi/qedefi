import EvmLogic.Word
import EvmLogic.Solidity.Word

/-!
# More word idioms of solc output

Facts about the words that symbolic execution of the compiled Solmate vault produces, in the
exact form (`n#256` literals, `Word.*` operations) in which they appear on the stack, so that
they can be passed to `wp_steps` / `sol_steps` as rewrite rules or used as hypotheses for
`JUMPI` conditions:

* `iszero_slt_calldatasize`: the ABI decoder's length check
  `iszero(slt(sub(calldatasize(), 4), n))` passes for long enough calldata;
* Solmate's `FixedPointMathLib` (`mulDivDown`, `mulDivUp`, assembly): the overflow /
  zero-denominator guard `mul(d, iszero(mul(y, gt(x, div(not(0), y)))))` is zero exactly
  when the Solidity source reverts (`mulDivGuard_eq_zero_iff`), and the results
  `div(mul(x, y), d)` and `add(gt(mod(z, d), 0), div(z, d))` are the floor and ceiling of
  `x * y / d` when the product fits (`toNat_mulDivDownWord`, `toNat_mulDivUpWord`).

`MAXW` is `type(uint256).max` as a literal (`PUSH0 NOT`, after constant folding).
-/

namespace EvmLean.Solidity

/-- `type(uint256).max = 2²⁵⁶ - 1` as the literal symbolic execution produces. -/
abbrev MAXW : Word :=
  115792089237316195423570985008687907853269984665640564039457584007913129639935#256

/-- `MAXW` is `2²⁵⁶ - 1`. -/
theorem toNat_MAXW : MAXW.toNat = 2 ^ 256 - 1 := rfl

/-- `PUSH0 NOT` is `MAXW`. -/
theorem not_zero_eq_MAXW : ~~~(0#256) = MAXW := by decide

/-- The ABI decoder's calldata-length check `iszero(slt(sub(calldatasize(), 4), n))` passes
when the calldata holds the selector and `n` bytes of arguments. -/
theorem iszero_slt_calldatasize {size n : Nat} (h1 : 4 + n ≤ size) (h2 : size < 2 ^ 255) :
    Word.iszero (Word.slt (BitVec.ofNat 256 size - 4#256) (BitVec.ofNat 256 n)) = 1 := by
  have hn : n < 2 ^ 255 := by omega
  have hx : (BitVec.ofNat 256 size - 4#256).toNat = size - 4 := by
    rw [BitVec.toNat_sub_of_le] <;> simp [BitVec.le_def] <;> omega
  simp only [Word.iszero, Word.slt, Word.ofBool, BitVec.slt_eq_ult, BitVec.msb_eq_decide, hx,
    BitVec.ult, BitVec.toNat_ofNat]
  simp (disch := omega) [Nat.mod_eq_of_lt]
  rw [decide_eq_false (by omega), decide_eq_false (by omega), decide_eq_false (by omega)]
  rfl

/-- `Word.ofBool b` is `0` iff `b` is false. -/
theorem ofBool_eq_zero_iff (b : Bool) : Word.ofBool b = 0#256 ↔ b = false := by
  cases b <;> decide

/-- The `toNat` of `Word.ofBool`. -/
theorem toNat_ofBool (b : Bool) : (Word.ofBool b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

/-- The guard of Solmate's `mulDivDown`/`mulDivUp`,
`mul(denominator, iszero(mul(y, gt(x, div(MAX_UINT256, y)))))`, as it appears on the stack. -/
abbrev mulDivGuard (x y d : Word) : Word :=
  d * Word.iszero (y * Word.gt x (Word.div MAXW y))

/-- `ISZERO` in `toNat` form. -/
theorem toNat_iszero (w : Word) : (Word.iszero w).toNat = if w.toNat = 0 then 1 else 0 := by
  by_cases h : w = 0#256
  · subst h; rfl
  · have h' : w.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have hb : (w == 0) = false := by simpa using h
    simp only [Word.iszero, Word.ofBool, hb, h']
    rfl

/-- `GT` as `ofBool` of a `Nat` comparison. -/
theorem gt_eq_ofBool (x z : Word) : Word.gt x z = Word.ofBool (decide (z.toNat < x.toNat)) := by
  simp only [Word.gt, BitVec.ult]

/-- Multiplying by `0`/`1` does not wrap. -/
theorem toNat_mul_ofBool (y : Word) (b : Bool) :
    (y * Word.ofBool b).toNat = if b then y.toNat else 0 := by
  cases b
  · simp [Word.ofBool]
  · simp [Word.ofBool]

/-- **The `mulDiv` guard is zero exactly when the Solidity source reverts**: on a zero
denominator, or when `y ≠ 0` and `x > MAX / y` (the product overflows). -/
theorem mulDivGuard_eq_zero_iff (x y d : Word) :
    mulDivGuard x y d = 0#256 ↔
      (d.toNat = 0 ∨ (y.toNat ≠ 0 ∧ (2 ^ 256 - 1) / y.toNat < x.toNat)) := by
  have hdiv : (Word.div MAXW y).toNat = (2 ^ 256 - 1) / y.toNat := by
    simp only [Word.div, BitVec.toNat_udiv, toNat_MAXW]
  have hiz : (Word.iszero (y * Word.gt x (Word.div MAXW y))).toNat =
      if (y.toNat ≠ 0 ∧ (2 ^ 256 - 1) / y.toNat < x.toNat) then 0 else 1 := by
    rw [toNat_iszero, gt_eq_ofBool, toNat_mul_ofBool, hdiv]
    by_cases h1 : (2 ^ 256 - 1) / y.toNat < x.toNat <;> by_cases h2 : y.toNat = 0 <;>
      simp [h1, h2]
  have hd := d.isLt
  have hprod : (mulDivGuard x y d).toNat =
      d.toNat * (if (y.toNat ≠ 0 ∧ (2 ^ 256 - 1) / y.toNat < x.toNat) then 0 else 1) := by
    unfold mulDivGuard
    rw [BitVec.toNat_mul, hiz]
    split <;> simp [Nat.mod_eq_of_lt hd]
  constructor
  · intro h
    have h0 : (mulDivGuard x y d).toNat = 0 := by rw [h]; rfl
    rw [hprod] at h0
    split at h0
    · exact .inr ‹_›
    · exact .inl (by simpa using h0)
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [hprod]
    split
    · simp
    · rcases h with h | h
      · simp [h]
      · contradiction

/-- The guard passes (`JUMPI` taken) when the Solidity source does not revert. -/
theorem mulDivGuard_ne_zero {x y d : Word} (hd : d.toNat ≠ 0)
    (h : ¬ (y.toNat ≠ 0 ∧ (2 ^ 256 - 1) / y.toNat < x.toNat)) : mulDivGuard x y d ≠ 0#256 := by
  rw [Ne, mulDivGuard_eq_zero_iff]; omega

/-- The guard fails (no jump: `revert(0, 0)`) when the Solidity source reverts. -/
theorem mulDivGuard_eq_zero {x y d : Word}
    (h : d.toNat = 0 ∨ (y.toNat ≠ 0 ∧ (2 ^ 256 - 1) / y.toNat < x.toNat)) :
    mulDivGuard x y d = 0#256 :=
  (mulDivGuard_eq_zero_iff x y d).2 h

/-- The overflow test `y ≠ 0 ∧ MAX / y < x` is exactly `MAX < x * y`. -/
theorem overflow_test_iff' (x y : Nat) :
    (y ≠ 0 ∧ (2 ^ 256 - 1) / y < x) ↔ 2 ^ 256 - 1 < x * y := by
  constructor
  · rintro ⟨hy, h⟩
    exact (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hy)).1 h
  · intro h
    have hy : y ≠ 0 := by rintro rfl; simp at h
    exact ⟨hy, (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hy)).2 h⟩

/-- A product that passes the guard does not wrap. -/
theorem toNat_mul_of_guard {x y : Word} (h : ¬ (y.toNat ≠ 0 ∧ (2 ^ 256 - 1) / y.toNat < x.toNat)) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [overflow_test_iff'] at h
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]

/-- `mulDivDown`'s result `div(mul(x, y), d)` is `⌊x · y / d⌋` when the guard passes. -/
theorem mulDivDownWord_eq {x y d : Word}
    (h : ¬ (y.toNat ≠ 0 ∧ (2 ^ 256 - 1) / y.toNat < x.toNat)) :
    Word.div (x * y) d = BitVec.ofNat 256 (x.toNat * y.toNat / d.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hlt : x.toNat * y.toNat / d.toNat < 2 ^ 256 := by
    have := toNat_mul_of_guard h ▸ (x * y).isLt
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) this
  simp only [Word.div, BitVec.toNat_udiv, toNat_mul_of_guard h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt]

/-- Ceiling division as Solmate's `mulDivUp` computes it: the floor quotient plus one when
the remainder is non-zero. -/
def ceilDivN (z d : Nat) : Nat := (if 0 < z % d then 1 else 0) + z / d

/-- `mulDivUp`'s result `add(iszero(iszero(mod(z, d))), div(z, d))` with `z = mul(x, y)` is
`⌈x · y / d⌉` when the guard passes and `d ≠ 0`. -/
theorem mulDivUpWord_eq {x y d : Word} (hd : d.toNat ≠ 0)
    (h : ¬ (y.toNat ≠ 0 ∧ (2 ^ 256 - 1) / y.toNat < x.toNat)) :
    Word.div (x * y) d + Word.iszero (Word.iszero (Word.mod (x * y) d)) =
      BitVec.ofNat 256 (ceilDivN (x.toNat * y.toNat) d.toNat) := by
  have hm := toNat_mul_of_guard h
  have hz := (x * y).isLt
  rw [hm] at hz
  have hd0 : d ≠ 0#256 := fun e => hd (by simp [e])
  have hdpos : 0 < d.toNat := Nat.pos_of_ne_zero hd
  apply BitVec.eq_of_toNat_eq
  have hmod : (Word.mod (x * y) d).toNat = x.toNat * y.toNat % d.toNat := by
    rw [Word.mod_of_ne_zero _ hd0, BitVec.toNat_umod, hm]
  have hiz : (Word.iszero (Word.iszero (Word.mod (x * y) d))).toNat =
      if 0 < x.toNat * y.toNat % d.toNat then 1 else 0 := by
    rw [toNat_iszero, toNat_iszero, hmod]
    by_cases h0 : x.toNat * y.toNat % d.toNat = 0 <;> simp [h0] <;> omega
  have hq : (Word.div (x * y) d).toNat = x.toNat * y.toNat / d.toNat := by
    simp only [Word.div, BitVec.toNat_udiv, hm]
  have hle : x.toNat * y.toNat / d.toNat < 2 ^ 256 - 1 ∨ x.toNat * y.toNat % d.toNat = 0 := by
    by_cases hd1 : d.toNat = 1
    · right; rw [hd1, Nat.mod_one]
    · left
      have : x.toNat * y.toNat / d.toNat ≤ x.toNat * y.toNat / 2 :=
        Nat.div_le_div_left (by omega) (by omega)
      omega
  rw [BitVec.toNat_add, hq, hiz, ceilDivN, BitVec.toNat_ofNat]
  congr 1
  omega

/-- `ISZERO 0 = 1`. -/
theorem iszero_zero : Word.iszero 0#256 = 1#256 := by decide

/-- `ISZERO 1 = 0`. -/
theorem iszero_one : Word.iszero 1#256 = 0#256 := by decide

/-- `ISZERO x = 0` for `x ≠ 0`. -/
theorem iszero_of_ne {x : Word} (h : x ≠ 0#256) : Word.iszero x = 0#256 := by
  have hb : (x == 0) = false := by simpa using h
  simp only [Word.iszero, Word.ofBool, hb]
  rfl

/-- `EQ x y = 0` for `x ≠ y`. -/
theorem eq_of_ne {x y : Word} (h : x ≠ y) : Word.eq x y = 0#256 := by
  have hb : (x == y) = false := by simpa using h
  simp only [Word.eq, Word.ofBool, hb]
  rfl

/-- A word is the `ofNat` of its value. -/
theorem ofNat_toNat_word (x : Word) : BitVec.ofNat 256 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

end EvmLean.Solidity
