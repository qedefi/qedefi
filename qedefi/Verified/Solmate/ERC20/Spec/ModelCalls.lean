import Verified.Solmate.ERC20.Spec.Abs

/-!
# Solmate's model, call by call

The outcome of each call and operation of `solmateModel` in closed form (`call_transfer`,
`call_transferFrom`, `call_approve`, `call_other`, `stepOp_mint`, `stepOp_burn`), and the
finitely supported function facts the bytecode proofs compare against.
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.Solmate
open QEDefi.Math Finsupp

/-- The standard variant over addresses. -/
abbrev V : Variant Address := Variant.standard

variable (s : VState Address) (c : Address)

theorem failKind_standard (x : Call Address) : V.failKind s c x = .revert := by
  unfold Variant.failKind
  cases x <;> simp [Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.standard]

theorem call_transfer (d : Address) (v : ℕ) :
    V.call s c (.transfer d v) =
      if s.bal c < v then .halt .revert
      else .ok { s with bal := s.bal - single c v + single d v } (.word true) := by
  unfold Variant.call
  rw [failKind_standard]
  by_cases h : s.bal c < v
  · simp [Variant.step, Variant.transfer, Variant.moveOk, Variant.move, Variant.units,
      Variant.standard, h, Variant.failWith]
  · simp [Variant.step, Variant.transfer, Variant.moveOk, Variant.move, Variant.units,
      Variant.feeOverflow, Variant.feeOf, Variant.credit, Variant.standard, h, Variant.retData]

theorem call_approve (sp : Address) (v : ℕ) :
    V.call s c (.approve sp v) = .ok (s.setAllowance c sp v) (.word true) := by
  simp [Variant.call, Variant.step, Variant.approve, Variant.approveOk, Variant.standard,
    Variant.retData]

theorem call_other (x : ℕ) : V.call s c (.other x) = .halt .revert := by
  unfold Variant.call
  rw [failKind_standard]
  simp [Variant.step, Variant.fallbackCall, Variant.standard, Variant.failWith]

/-- The allowance step of `transferFrom`, in closed form. -/
def spendState (s : VState Address) (o sp : Address) (v : ℕ) : Option (VState Address) :=
  if s.allowance o sp = MAX then some s
  else if s.allowance o sp < v then none
  else some (s.setAllowance o sp (s.allowance o sp - v))

theorem spend_standard (o sp : Address) (v : ℕ) : V.spend s o sp v = spendState s o sp v := by
  simp [Variant.spend, Variant.standard, Infinite.test, spendState]

theorem call_transferFrom (src d : Address) (v : ℕ) :
    V.call s c (.transferFrom src d v) =
      match spendState s src c v with
      | none => .halt .revert
      | some s₁ =>
        if s₁.bal src < v then .halt .revert
        else .ok { s₁ with bal := s₁.bal - single src v + single d v } (.word true) := by
  unfold Variant.call
  rw [failKind_standard]
  simp only [Variant.step, Variant.transferFrom, Variant.moveOk, spend_standard]
  simp only [Variant.standard, Bool.false_and, Bool.not_false,
    Bool.and_self, ↓reduceIte]
  cases hs : spendState s src c v with
  | none => simp [Variant.failWith]
  | some s₁ =>
    by_cases h : s₁.bal src < v
    · simp [Variant.move, Variant.units, h, Variant.failWith]
    · simp [Variant.move, Variant.units, Variant.feeOverflow, Variant.feeOf, Variant.credit, h,
        Variant.retData]

theorem stepOp_mint (d : Address) (v : ℕ) :
    V.stepOp s (.mint c d v) =
      if MAX < s.supply + v then none
      else some { s with supply := s.supply + v, bal := s.bal + single d v } := by
  simp [Variant.stepOp, Variant.mint, Variant.standard, Auth.allows, Variant.units]

theorem stepOp_burn (src : Address) (v : ℕ) :
    V.stepOp s (.burn c src v) =
      if s.bal src < v then none
      else some { s with supply := s.supply - v, bal := s.bal - single src v } := by
  simp [Variant.stepOp, Variant.burn, Variant.standard, Auth.allows, Variant.units]

/-! ## Finitely supported functions -/

theorem add_le_total {f : Address →₀ ℕ} {a b : Address} (h : a ≠ b) :
    f a + f b ≤ total f := by
  have ht : total f = ∑ x ∈ f.support ∪ {a, b}, f x :=
    Finsupp.sum_of_support_subset f Finset.subset_union_left (fun _ v => v) (fun _ _ => rfl)
  rw [ht, ← Finset.sum_pair h]
  exact Finset.sum_le_sum_of_subset Finset.subset_union_right

/-- A move of `v` from `c` to `d` is two row updates (the second reads the first). -/
theorem move_eq_update (f : Address →₀ ℕ) (c d : Address) (v : ℕ) :
    f - single c v + single d v =
      (f.update c (f c - v)).update d ((f.update c (f c - v)) d + v) := by
  ext a
  simp only [coe_add, coe_tsub, Pi.add_apply, Pi.sub_apply, update_apply, single_apply]
  by_cases had : d = a
  · subst had
    by_cases hac : c = d
    · subst hac; simp
    · simp [hac, Ne.symm hac]
  · by_cases hac : c = a
    · subst hac; simp [had, Ne.symm had]
    · simp [had, hac, Ne.symm had, Ne.symm hac]

end Verified.Solmate.ERC20.Spec
