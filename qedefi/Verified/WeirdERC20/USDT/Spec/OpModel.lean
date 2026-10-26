import Verified.WeirdERC20.USDT.Spec.OpWrite

/-!
# USDT's admin entry points: the model's outcomes

The model's `issue` (a mint to the owner by the owner), `redeem` (a burn by the owner), the
guarded `setPaused`, `setBlacklisted`, `destroyBlackFunds` and `setParams`, in closed form, and
the comparison `lt_add_iff` behind the code's `require(a + v > a)`.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Verified.WeirdERC20.USDT.Contracts
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math QEDefi.ERC4626 Finsupp

theorem op_mint (s : VState Address) (c : Address) (v : ℕ) :
    M.op s (.mint c c v) =
      if c = s.admin ∧ v ≠ 0 ∧ s.supply + v ≤ MAX then
        some { s with supply := s.supply + v, bal := s.bal + single c v }
      else none := by
  simp only [M, QEDefi.ERC20.Spec.USDT.usdtModel_op, QEDefi.ERC20.Spec.USDT.usdtOpGuard,
    Bool.false_eq_true, ↓reduceIte, Variant.stepOp, Variant.mint]
  by_cases h1 : c = s.admin <;> by_cases h2 : v = 0 <;> by_cases h3 : MAX < s.supply + v <;>
    simp [h1, h2, h3, Variant.usdt, Variant.standard, Auth.allows, Variant.units]

theorem op_burn (s : VState Address) (c : Address) (v : ℕ) :
    M.op s (.burn c c v) =
      if c = s.admin ∧ v ≤ s.bal c then
        some { s with supply := s.supply - v, bal := s.bal - single c v }
      else none := by
  simp only [M, QEDefi.ERC20.Spec.USDT.usdtModel_op, QEDefi.ERC20.Spec.USDT.usdtOpGuard,
    Bool.false_eq_true, ↓reduceIte, Variant.stepOp, Variant.burn]
  by_cases h1 : c = s.admin
  · subst h1
    by_cases h3 : s.bal s.admin < v
    · simp [h3, Nat.not_le.2 h3, Variant.usdt, Variant.standard, Auth.allows, Variant.units]
    · simp [h3, Nat.le_of_not_lt h3, Variant.usdt, Variant.standard, Auth.allows, Variant.units]
  · simp [h1, Variant.usdt, Variant.standard, Auth.allows]

theorem op_setBlacklisted (s : VState Address) (c u : Address) (b : Bool) :
    M.op s (.setBlacklisted c u b) =
      if c = s.admin then some { s with blacklisted := Function.update s.blacklisted u b }
      else none := by
  simp only [M, QEDefi.ERC20.Spec.USDT.usdtModel_op, QEDefi.ERC20.Spec.USDT.usdtOpGuard,
    Bool.false_eq_true, ↓reduceIte, Variant.stepOp, Variant.setBlacklisted]
  by_cases h1 : c = s.admin <;> simp [h1, Variant.usdt, Variant.standard]

theorem op_destroy (s : VState Address) (c u : Address) :
    M.op s (.destroyBlackFunds c u) =
      if c = s.admin ∧ s.blacklisted u = true then
        some { s with bal := s.bal - single u (s.bal u), supply := s.supply - s.bal u }
      else none := by
  simp only [M, QEDefi.ERC20.Spec.USDT.usdtModel_op, QEDefi.ERC20.Spec.USDT.usdtOpGuard,
    Bool.false_eq_true, ↓reduceIte, Variant.stepOp, Variant.destroyBlackFunds]
  by_cases h1 : c = s.admin <;> by_cases h2 : s.blacklisted u = true <;>
    simp [h1, h2, Variant.usdt, Variant.standard]

theorem op_setParams (s : VState Address) (c : Address) (b x : ℕ) :
    M.op s (.setParams c b x) =
      if c = s.admin ∧ b < 20 ∧ x < 50 then some { s with feeBps := b, feeMax := x * 10 ^ 6 }
      else none := by
  simp only [M, QEDefi.ERC20.Spec.USDT.usdtModel_op, QEDefi.ERC20.Spec.USDT.usdtOpGuard,
    Bool.false_eq_true, ↓reduceIte, Variant.stepOp, Variant.setParams]
  by_cases h1 : c = s.admin <;> by_cases h2 : b < 20 <;> by_cases h3 : x < 50 <;>
    simp [h1, h2, h3, Variant.usdt, Variant.standard]

theorem op_setPaused (s : VState Address) (c : Address) (b : Bool) :
    M.op s (.setPaused c b) =
      if c = s.admin ∧ s.paused ≠ b then some { s with paused := b } else none :=
  QEDefi.ERC20.Spec.USDT.usdtModel_op_setPaused s c b

/-- `a < a + b` on words: `b ≠ 0` and no overflow. -/
theorem lt_add_iff (a b : Word) :
    a.toNat < (a + b).toNat ↔ 0 < b.toNat ∧ a.toNat + b.toNat < 2 ^ 256 := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.toNat_add]
  by_cases h : a.toNat + b.toNat < 2 ^ 256
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

end Verified.WeirdERC20.USDT.Spec
