import Verified.WeirdERC20.USDT.Spec.Basic

/-!
# USDT: deciding the code's comparisons

The `JUMPI` conditions of SafeMath and of the fee computation, as numbers: `GT`/`LT` by the
order of the words, SafeMath `mul`'s `c / a == b` by whether `a · b` fits a word.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Solidity

theorem gt_one {x y : Word} (h : y.toNat < x.toNat) : Word.gt x y = 1#256 :=
  (Word.gt_eq_one_iff x y).2 h

theorem gt_zero {x y : Word} (h : x.toNat ≤ y.toNat) : Word.gt x y = 0#256 := by
  rw [gt_eq_ofBool, decide_eq_false (by omega)]; rfl

theorem lt_one {x y : Word} (h : x.toNat < y.toNat) : Word.lt x y = 1#256 :=
  (Word.lt_eq_one_iff x y).2 h

theorem lt_zero {x y : Word} (h : y.toNat ≤ x.toNat) : Word.lt x y = 0#256 :=
  (Word.lt_eq_zero_iff x y).2 h

/-- SafeMath `add`'s check `c >= a` passes when the sum fits a word. -/
theorem lt_add_zero {a b : Word} (h : a.toNat + b.toNat < 2 ^ 256) : Word.lt (a + b) a = 0#256 := by
  apply lt_zero
  simp only [BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

/-- SafeMath `add`'s check fails when the sum does not fit a word. -/
theorem lt_add_one {a b : Word} (h : 2 ^ 256 ≤ a.toNat + b.toNat) : Word.lt (a + b) a = 1#256 := by
  apply lt_one
  have hb := b.isLt
  simp only [BitVec.toNat_add]
  rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  omega

/-- SafeMath `mul`'s check passes when the product fits a word. -/
theorem mul_div_eq_one {a b : Word} (ha : a ≠ 0) (h : a.toNat * b.toNat < 2 ^ 256) :
    Word.eq ((a * b).div a) b = 1#256 := by
  apply (Word.eq_eq_one_iff _ _).2
  apply BitVec.eq_of_toNat_eq
  have ha' : 0 < a.toNat := by
    rcases Nat.eq_zero_or_pos a.toNat with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) ha
    · exact h0
  simp only [Word.div, BitVec.toNat_udiv, BitVec.toNat_mul, Nat.mod_eq_of_lt h]
  rw [Nat.mul_div_cancel_left _ ha']

/-- SafeMath `mul`'s check fails when the product does not fit a word. -/
theorem mul_div_eq_zero {a b : Word} (h : 2 ^ 256 ≤ a.toNat * b.toNat) :
    Word.eq ((a * b).div a) b = 0#256 := by
  apply eq_of_ne
  intro he
  have h1 := congrArg BitVec.toNat he
  simp only [Word.div, BitVec.toNat_udiv, BitVec.toNat_mul] at h1
  have hlt := Nat.mod_lt (a.toNat * b.toNat) (show 0 < 2 ^ 256 by decide)
  have hb := b.isLt
  have ha := a.isLt
  -- (a·b mod 2²⁵⁶) / a = b would give a·b mod 2²⁵⁶ ≥ a·b
  have h2 : a.toNat * b.toNat ≤ a.toNat * b.toNat % 2 ^ 256 := by
    rcases Nat.eq_zero_or_pos a.toNat with h0 | h0
    · rw [h0] at h; simp at h
    · have := Nat.div_mul_le_self (a.toNat * b.toNat % 2 ^ 256) a.toNat
      rw [h1] at this
      calc a.toNat * b.toNat = b.toNat * a.toNat := Nat.mul_comm _ _
        _ ≤ _ := this
  omega

end Verified.WeirdERC20.USDT.Spec
