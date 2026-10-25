import EvmLogic.Word

/-!
# `VestingWallet`: word facts of solc's checked arithmetic

The overflow tests solc emits for checked `+`, `-`, `*` decided by the `Nat` value of the
exact result.
-/

namespace Verified.OpenZeppelin.VestingWallet
open EvmLean

theorem toNat_add_of_lt' {x y : Word} (h : x.toNat + y.toNat < 2 ^ 256) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_add_of_ge {x y : Word} (h : 2 ^ 256 ≤ x.toNat + y.toNat) :
    (x + y).toNat = x.toNat + y.toNat - 2 ^ 256 := by
  have hx := x.isLt; have hy := y.isLt
  rw [BitVec.toNat_add, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

theorem ofBool_eq_one {b : Bool} (h : b = true) : Word.ofBool b = 1 := by subst h; rfl
theorem ofBool_eq_zero {b : Bool} (h : b = false) : Word.ofBool b = 0 := by subst h; rfl

/-- solc's checked `x + y` (`if gt(x, add(y, x)) { panic }`), no overflow. -/
theorem checkedAdd_ok {x y : Word} (h : x.toNat + y.toNat < 2 ^ 256) :
    Word.iszero (Word.gt x (y + x)) = 1 := by
  have h1 : (y + x).toNat = y.toNat + x.toNat := toNat_add_of_lt' (by omega)
  have h2 : Word.gt x (y + x) = 0 := by
    unfold Word.gt; apply ofBool_eq_zero; simp only [BitVec.ult, decide_eq_false_iff_not]; omega
  rw [h2]; rfl

/-- solc's checked `x + y`, overflow. -/
theorem checkedAdd_overflow {x y : Word} (h : 2 ^ 256 ≤ x.toNat + y.toNat) :
    Word.iszero (Word.gt x (y + x)) = 0 := by
  have hy := y.isLt
  have h1 : (y + x).toNat = y.toNat + x.toNat - 2 ^ 256 := toNat_add_of_ge (by omega)
  have h2 : Word.gt x (y + x) = 1 := by
    unfold Word.gt; apply ofBool_eq_one; simp only [BitVec.ult, decide_eq_true_eq]; omega
  rw [h2]; rfl

end Verified.OpenZeppelin.VestingWallet

namespace Verified.OpenZeppelin.VestingWallet
open EvmLean

/-- The literal of the 64-bit mask. -/
theorem toNat_mask_and (x : Word) :
    (18446744073709551615#256 &&& x).toNat = x.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_and, Nat.and_comm]
  rw [show (18446744073709551615#256 : Word).toNat = 2 ^ 64 - 1 by decide]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem toNat_and_mask (x : Word) :
    (x &&& 18446744073709551615#256).toNat = x.toNat % 2 ^ 64 := by
  rw [BitVec.and_comm]; exact toNat_mask_and x

theorem iszero_lt_eq_one {x y : Word} (h : y.toNat ≤ x.toNat) : Word.iszero (Word.lt x y) = 1 := by
  rw [(Word.lt_eq_zero_iff x y).2 h]; rfl

theorem iszero_lt_eq_zero {x y : Word} (h : x.toNat < y.toNat) : Word.iszero (Word.lt x y) = 0 := by
  rw [(Word.lt_eq_one_iff x y).2 h]; rfl

theorem lt_eq_zero' {x y : Word} (h : y.toNat ≤ x.toNat) : Word.lt x y = 0 := (Word.lt_eq_zero_iff x y).2 h

theorem lt_eq_one' {x y : Word} (h : x.toNat < y.toNat) : Word.lt x y = 1 := (Word.lt_eq_one_iff x y).2 h

end Verified.OpenZeppelin.VestingWallet

namespace Verified.OpenZeppelin.VestingWallet
open EvmLean

theorem toNat_end (d s : Word) :
    ((18446744073709551615#256 &&& d) + (s &&& 18446744073709551615#256)).toNat =
      d.toNat % 2 ^ 64 + s.toNat % 2 ^ 64 := by
  rw [toNat_add_of_lt' (by rw [toNat_mask_and, toNat_and_mask]; omega), toNat_mask_and,
    toNat_and_mask]

end Verified.OpenZeppelin.VestingWallet

namespace Verified.OpenZeppelin.VestingWallet
open EvmLean

/-- solc's checked `x - y` (`if gt(sub(x, y), x) { panic }`), no underflow. -/
theorem checkedSub_ok {x y : Word} (h : y.toNat ≤ x.toNat) : Word.iszero (Word.gt (x - y) x) = 1 := by
  have h1 : (x - y).toNat = x.toNat - y.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h)]
  have h2 : Word.gt (x - y) x = 0 := by
    unfold Word.gt; apply ofBool_eq_zero; simp only [BitVec.ult, decide_eq_false_iff_not]; omega
  rw [h2]; rfl

/-- solc's checked `x - y`, underflow. -/
theorem checkedSub_underflow {x y : Word} (h : x.toNat < y.toNat) :
    Word.iszero (Word.gt (x - y) x) = 0 := by
  have hx := x.isLt
  have h1 : (x - y).toNat = 2 ^ 256 - y.toNat + x.toNat := by
    rw [BitVec.toNat_sub, Nat.mod_eq_of_lt (by omega)]
  have h2 : Word.gt (x - y) x = 1 := by
    unfold Word.gt; apply ofBool_eq_one; simp only [BitVec.ult, decide_eq_true_eq]; omega
  rw [h2]; rfl

theorem toNat_sub_of_le' {x y : Word} (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat :=
  BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h)

theorem ofNat_add_toNat (x y : Word) (h : x.toNat + y.toNat < 2 ^ 256) :
    BitVec.ofNat 256 (x.toNat + y.toNat) = y + x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, toNat_add_of_lt' (by omega), Nat.add_comm]

end Verified.OpenZeppelin.VestingWallet

namespace Verified.OpenZeppelin.VestingWallet
open EvmLean

theorem toNat_div' (x y : Word) : (Word.div x y).toNat = x.toNat / y.toNat := by
  rw [Word.div, BitVec.toNat_udiv]

/-- solc's checked `x * y` (`if iszero(or(iszero(y), eq(x, div(mul(x, y), y)))) { panic }`),
no overflow. -/
theorem checkedMul_ok {x y : Word} (h : x.toNat * y.toNat < 2 ^ 256) :
    (Word.eq x (Word.div (x * y) y) ||| Word.iszero y) = 1 := by
  by_cases hy : y = 0
  · subst hy
    unfold Word.eq Word.iszero Word.ofBool
    split <;> simp
  · have hy' : y.toNat ≠ 0 := fun h0 => hy (BitVec.eq_of_toNat_eq (by simpa using h0))
    have hd : Word.div (x * y) y = x := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_div', BitVec.toNat_mul, Nat.mod_eq_of_lt h, Nat.mul_div_cancel _ (by omega)]
    have hy0 : ¬ y = 0#256 := hy
    rw [hd]
    unfold Word.eq Word.iszero Word.ofBool
    simp [hy0]

/-- solc's checked `x * y`, overflow. -/
theorem checkedMul_overflow {x y : Word} (h : 2 ^ 256 ≤ x.toNat * y.toNat) :
    (Word.eq x (Word.div (x * y) y) ||| Word.iszero y) = 0 := by
  have hy' : y.toNat ≠ 0 := by intro h0; rw [h0, Nat.mul_zero] at h; omega
  have hy : y ≠ 0 := fun h0 => hy' (by rw [h0]; rfl)
  have hd : Word.div (x * y) y ≠ x := by
    intro hd
    have := congrArg BitVec.toNat hd
    rw [toNat_div', BitVec.toNat_mul] at this
    have hlt := Nat.mod_lt (x.toNat * y.toNat) (show 0 < 2 ^ 256 by decide)
    have hle : x.toNat * y.toNat % 2 ^ 256 / y.toNat * y.toNat ≤ x.toNat * y.toNat % 2 ^ 256 :=
      Nat.div_mul_le_self _ _
    rw [this] at hle
    omega
  have hy0 : ¬ y = 0#256 := hy
  unfold Word.eq Word.iszero Word.ofBool
  simp [hy0, Ne.symm hd]

end Verified.OpenZeppelin.VestingWallet

namespace Verified.OpenZeppelin.VestingWallet
open EvmLean

theorem ofNat_sub_word {v : Nat} {y : Word} (hv : v < 2 ^ 256) (h : y.toNat ≤ v) :
    BitVec.ofNat 256 v - y = BitVec.ofNat 256 (v - y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_sub_of_le' (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]; exact h),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (by omega)]

end Verified.OpenZeppelin.VestingWallet

namespace Verified.OpenZeppelin.VestingWallet
open EvmLean

/-- ABI validation of a `uint64` argument: accepted. -/
theorem eq_and_mask_of_lt {x : Word} (h : x.toNat < 2 ^ 64) :
    Word.eq x (x &&& 18446744073709551615#256) = 1 := by
  have : x &&& 18446744073709551615#256 = x := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_and_mask, Nat.mod_eq_of_lt h]
  rw [this]; unfold Word.eq; simp [Word.ofBool]

/-- ABI validation of a `uint64` argument: rejected. -/
theorem eq_and_mask_of_ge {x : Word} (h : 2 ^ 64 ≤ x.toNat) :
    Word.eq x (x &&& 18446744073709551615#256) = 0 := by
  have : x ≠ x &&& 18446744073709551615#256 := by
    intro he
    have := congrArg BitVec.toNat he
    rw [toNat_and_mask] at this
    have := Nat.mod_lt x.toNat (show 0 < 2 ^ 64 by decide)
    omega
  unfold Word.eq; simp [Word.ofBool, this]

end Verified.OpenZeppelin.VestingWallet

namespace Verified.OpenZeppelin.VestingWallet
open EvmLean

theorem ofNat_sub_add_word {v : Nat} {y : Word} (hv : v < 2 ^ 256) (h : y.toNat ≤ v) :
    BitVec.ofNat 256 (v - y.toNat) + y = BitVec.ofNat 256 v := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_add_of_lt' (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hv]
  omega

end Verified.OpenZeppelin.VestingWallet

namespace Verified.OpenZeppelin.VestingWallet
open EvmLean

/-- Masking to 160 bits does not change the address a word denotes. -/
theorem toAddress_mask_and (x : Word) :
    Word.toAddress (1461501637330902918203684832716283019655932542975#256 &&& x) = Word.toAddress x := by
  apply BitVec.eq_of_toNat_eq
  simp only [Word.toAddress, BitVec.toNat_setWidth, BitVec.toNat_and]
  rw [show (1461501637330902918203684832716283019655932542975#256 : Word).toNat = 2 ^ 160 - 1 by decide,
    Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]

end Verified.OpenZeppelin.VestingWallet
