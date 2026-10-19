import EvmLeanProofs.Solidity.ExtraWord

/-!
# Checked additions of solc 0.8, as symbolic execution shows them

solc compiles a checked `x + y` (`uint256`) as `sum := add(y, x); if gt(x, sum) { panic(0x11) }`
(the conditional jump tests `iszero(gt(x, sum))`), and a checked `x + 1` (`x++`) as
`sum := add(x, 1); if iszero(sum) { panic(0x11) }` (the jump tests `sum` itself). These lemmas
decide the tests from the `Nat` values, in the exact form in which the words appear on the
stack:

* `iszero_gt_add_of_lt` / `iszero_gt_add_of_ge`: the overflow test of `x + y` passes iff
  `x + y < 2²⁵⁶`;
* `add_one_ne_zero_of_lt` / `add_one_eq_zero_of_eq`: the overflow test of `x + 1` passes iff
  `x + 1 < 2²⁵⁶`;
* `toNat_add_of_lt`: a sum that does not overflow is the `Nat` sum.
-/

namespace EvmLean.Solidity

/-- A word sum without overflow is the `Nat` sum. -/
theorem toNat_add_of_lt {x y : Word} (h : x.toNat + y.toNat < 2 ^ 256) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

/-- The overflow test of a checked `x + y` passes (jumps on) without overflow. -/
theorem iszero_gt_add_of_lt {x y : Word} (h : x.toNat + y.toNat < 2 ^ 256) :
    Word.iszero (Word.gt x (y + x)) = 1#256 := by
  rw [gt_eq_ofBool, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega),
    decide_eq_false (by omega)]
  decide

/-- The overflow test of a checked `x + y` fails (panics) on overflow. -/
theorem iszero_gt_add_of_ge {x y : Word} (h : 2 ^ 256 ≤ x.toNat + y.toNat) :
    Word.iszero (Word.gt x (y + x)) = 0#256 := by
  have hx := x.isLt
  have hy := y.isLt
  have hm : (y.toNat + x.toNat) % 2 ^ 256 = y.toNat + x.toNat - 2 ^ 256 := by
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [gt_eq_ofBool, BitVec.toNat_add, hm, decide_eq_true (by omega)]
  decide

/-- The overflow test of a checked `x + 1` passes (jumps on) without overflow. -/
theorem add_one_ne_zero_of_lt {x : Word} (h : x.toNat + 1 < 2 ^ 256) : x + 1#256 ≠ 0#256 := by
  intro he
  have := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simpa using h)] at this
  simp at this

/-- The overflow test of a checked `x + 1` fails (panics) at `type(uint256).max`. -/
theorem add_one_eq_zero_of_eq {x : Word} (h : x.toNat + 1 = 2 ^ 256) : x + 1#256 = 0#256 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  simp [h]

end EvmLean.Solidity
