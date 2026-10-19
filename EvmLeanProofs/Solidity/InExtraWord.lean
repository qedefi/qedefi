import EvmLeanProofs.Solidity.ExtraWord

/-!
# Checked additions of solc 0.8, as symbolic execution shows them

solc compiles a checked `x + 1` (`x++`) as `sum := add(x, 1); if iszero(sum) { panic(0x11) }`
(the conditional jump tests `sum` itself). These lemmas decide the test from the `Nat` value,
in the exact form in which the words appear on the stack:

* (the test of `x + y` is `gt_add_self_of_lt` / `gt_add_self_of_le` of
  `EvmLeanSpecs.Refinement.AssetMint`);
* `add_one_ne_zero_of_lt` / `add_one_eq_zero_of_eq`: the overflow test of `x + 1` passes iff
  `x + 1 < 2²⁵⁶`;
* `toNat_add_of_lt`: a sum that does not overflow is the `Nat` sum.
-/

namespace EvmLean.Solidity

/-- A word sum without overflow is the `Nat` sum. -/
theorem toNat_add_of_lt {x y : Word} (h : x.toNat + y.toNat < 2 ^ 256) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

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
