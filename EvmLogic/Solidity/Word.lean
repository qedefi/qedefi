import EvmLogic.Word
import EvmLogic.Solidity.SimpAttr

/-!
# Word idioms of solc output

Evaluations of solc's word idioms (address masks, `EQ x x`, checked-arithmetic tests,
Solmate's `mulDiv` guard) on the symbolic values that occur during symbolic execution. Literals
are stated as `BitVec.ofNat 256 n` (`n#256`), the simp normal form of the step lemmas.
-/

section

namespace EvmLogic.Solidity
open EvmLean

/-- `2¹⁶⁰ - 1`, the mask of an address in a word. -/
def addressMask : Word := BitVec.ofNat 256 (2 ^ 160 - 1)

theorem addressMask_eq : addressMask = 1461501637330902918203684832716283019655932542975#256 :=
  rfl

@[sol_norm] theorem shl_ofNat (s x : Nat) :
    Word.shl (BitVec.ofNat 256 s) (BitVec.ofNat 256 x) =
      if s % 2 ^ 256 < 256 then BitVec.ofNat 256 (x * 2 ^ (s % 2 ^ 256)) else 0 := by
  have hs : (BitVec.ofNat 256 s).toNat = s % 2 ^ 256 := BitVec.toNat_ofNat _ _
  by_cases h : s % 2 ^ 256 < 256
  · apply BitVec.eq_of_toNat_eq
    simp only [Word.shl, hs, h, ↓reduceIte, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    rw [Nat.mod_mul_mod]
  · simp only [h, ↓reduceIte]
    exact Word.shl_of_le _ _ (by omega)

theorem ofAddress_and_mask (a : Address) : Word.ofAddress a &&& addressMask = Word.ofAddress a := by
  apply BitVec.eq_of_toNat_eq
  have h := a.isLt
  have h' : a.toNat < 2 ^ 256 := by omega
  simp only [addressMask, Word.ofAddress, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by decide : 2 ^ 160 - 1 < 2 ^ 256), Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt h', Nat.mod_eq_of_lt h]

@[sol_norm] theorem ofAddress_and_addressMask (a : Address) :
    Word.ofAddress a &&& 1461501637330902918203684832716283019655932542975#256 =
      Word.ofAddress a :=
  ofAddress_and_mask a

@[sol_norm] theorem addressMask_and_ofAddress (a : Address) :
    1461501637330902918203684832716283019655932542975#256 &&& Word.ofAddress a =
      Word.ofAddress a := by
  rw [BitVec.and_comm]; exact ofAddress_and_mask a

@[sol_norm] theorem eq_self (x : Word) : Word.eq x x = 1#256 := by
  simp [Word.eq, Word.ofBool]

theorem gt_sub_self_of_le {x y : Word} (h : y.toNat ≤ x.toNat) :
    Word.gt (x - y) x = 0#256 := by
  simp only [Word.gt, Word.ofBool, BitVec.ult, decide_eq_true_eq]
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)]
  simp

theorem gt_sub_self_of_lt {x y : Word} (h : x.toNat < y.toNat) :
    Word.gt (x - y) x = 1#256 := by
  simp only [Word.gt, Word.ofBool, BitVec.ult, decide_eq_true_eq]
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.toNat_sub]
  have : x.toNat < (2 ^ 256 - y.toNat + x.toNat) % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp [this]

end EvmLogic.Solidity

end

section

/-! ## ABI length checks and Solmate's `FixedPointMathLib` -/

namespace EvmLogic.Solidity
open EvmLean

/-- `type(uint256).max = 2²⁵⁶ - 1` as the literal symbolic execution produces. -/
abbrev MAXW : Word :=
  115792089237316195423570985008687907853269984665640564039457584007913129639935#256

theorem toNat_MAXW : MAXW.toNat = 2 ^ 256 - 1 := rfl

theorem not_zero_eq_MAXW : ~~~(0#256) = MAXW := by decide

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

theorem ofBool_eq_zero_iff (b : Bool) : Word.ofBool b = 0#256 ↔ b = false := by
  cases b <;> decide

theorem toNat_ofBool (b : Bool) : (Word.ofBool b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

/-- The guard of Solmate's `mulDivDown`/`mulDivUp`,
`mul(denominator, iszero(mul(y, gt(x, div(MAX_UINT256, y)))))`, as it appears on the stack. -/
abbrev mulDivGuard (x y d : Word) : Word :=
  d * Word.iszero (y * Word.gt x (Word.div MAXW y))

theorem toNat_iszero (w : Word) : (Word.iszero w).toNat = if w.toNat = 0 then 1 else 0 := by
  by_cases h : w = 0#256
  · subst h; rfl
  · have h' : w.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have hb : (w == 0) = false := by simpa using h
    simp only [Word.iszero, Word.ofBool, hb, h']
    rfl

theorem gt_eq_ofBool (x z : Word) : Word.gt x z = Word.ofBool (decide (z.toNat < x.toNat)) := by
  simp only [Word.gt, BitVec.ult]

theorem toNat_mul_ofBool (y : Word) (b : Bool) :
    (y * Word.ofBool b).toNat = if b then y.toNat else 0 := by
  cases b
  · simp [Word.ofBool]
  · simp [Word.ofBool]

/-- **The `mulDiv` guard is zero exactly when the Solidity source reverts** (zero
denominator, or the product overflows). -/
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

theorem mulDivGuard_ne_zero {x y d : Word} (hd : d.toNat ≠ 0)
    (h : ¬ (y.toNat ≠ 0 ∧ (2 ^ 256 - 1) / y.toNat < x.toNat)) : mulDivGuard x y d ≠ 0#256 := by
  rw [Ne, mulDivGuard_eq_zero_iff]; omega

theorem mulDivGuard_eq_zero {x y d : Word}
    (h : d.toNat = 0 ∨ (y.toNat ≠ 0 ∧ (2 ^ 256 - 1) / y.toNat < x.toNat)) :
    mulDivGuard x y d = 0#256 :=
  (mulDivGuard_eq_zero_iff x y d).2 h

theorem overflow_test_iff' (x y : Nat) :
    (y ≠ 0 ∧ (2 ^ 256 - 1) / y < x) ↔ 2 ^ 256 - 1 < x * y := by
  constructor
  · rintro ⟨hy, h⟩
    exact (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hy)).1 h
  · intro h
    have hy : y ≠ 0 := by rintro rfl; simp at h
    exact ⟨hy, (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hy)).2 h⟩

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

/-- Ceiling division as Solmate's `mulDivUp` computes it. -/
def ceilDivN (z d : Nat) : Nat := (if 0 < z % d then 1 else 0) + z / d

/-- `mulDivUp`'s result is `⌈x · y / d⌉` when the guard passes and `d ≠ 0`. -/
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

theorem iszero_zero : Word.iszero 0#256 = 1#256 := by decide

theorem iszero_one : Word.iszero 1#256 = 0#256 := by decide

theorem iszero_of_ne {x : Word} (h : x ≠ 0#256) : Word.iszero x = 0#256 := by
  have hb : (x == 0) = false := by simpa using h
  simp only [Word.iszero, Word.ofBool, hb]
  rfl

theorem eq_of_ne {x y : Word} (h : x ≠ y) : Word.eq x y = 0#256 := by
  have hb : (x == y) = false := by simpa using h
  simp only [Word.eq, Word.ofBool, hb]
  rfl

theorem ofNat_toNat_word (x : Word) : BitVec.ofNat 256 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

end EvmLogic.Solidity

end

section

/-! ## Checked `x + 1` (`if iszero(add(x, 1)) { panic(0x11) }`) -/

namespace EvmLogic.Solidity
open EvmLean

theorem toNat_add_of_lt {x y : Word} (h : x.toNat + y.toNat < 2 ^ 256) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem add_one_ne_zero_of_lt {x : Word} (h : x.toNat + 1 < 2 ^ 256) : x + 1#256 ≠ 0#256 := by
  intro he
  have := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simpa using h)] at this
  simp at this

theorem add_one_eq_zero_of_eq {x : Word} (h : x.toNat + 1 = 2 ^ 256) : x + 1#256 = 0#256 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  simp [h]

end EvmLogic.Solidity

end

section

/-! ## Word identities of solc's storage-string encoder (`abi_encode_t_string_storage`) -/

namespace EvmLean.Word
open EvmLogic

theorem mul_iszero_iszero (x : Word) : x * Word.iszero (Word.iszero x) = x := by
  by_cases h : x = 0
  · subst h; decide
  · have h1 : Word.iszero x = 0 := by
      unfold Word.iszero Word.ofBool; simp; exact h
    rw [h1]
    have h2 : Word.iszero 0 = 1 := by decide
    rw [h2]; exact BitVec.mul_one x

theorem add_sub_cancel_left' (a x : Word) : a + x - a = x := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

end EvmLean.Word

end
