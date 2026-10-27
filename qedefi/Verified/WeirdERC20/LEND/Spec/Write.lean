import Verified.WeirdERC20.LEND.Spec.Common

/-!
# LEND: writes through the abstraction

What the writes of LEND's ERC-20 calls do to the model state `read`, under `ActorRows` (the
actors' rows are pairwise distinct and avoid the declared slots `0 … 8`): a write to an actor's
balance or allowance row changes that entry only, and leaves the fixed slots (`supply`, the sale
state, the manager, the sold counters).
-/

namespace Verified.WeirdERC20.LEND.Spec
open EvmLean EvmLogic EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec

variable {crypto : Crypto} {Act : Finset Address} {w w' : World} {t : Address}

/-- The fixed slots `read` depends on. -/
def fixedSlots : List Word := [supplySlot, stateSlot, managerSlot, presaleSlot, icoSlot, totalSoldSlot]

theorem fixed_mem {k : Word} (hk : k ∈ fixedSlots) :
    k ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8] : List Word) := by
  simp only [fixedSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `read` from a world agreeing on the fixed slots: only the mappings may differ. -/
theorem read_of_fixed (h : ∀ k ∈ fixedSlots, w'.sload t k = w.sload t k) :
    read crypto Act w' t = { read crypto Act w t with
      bal := readMap crypto Act w' t balancesSlot,
      allowance := readMap2 crypto Act w' t allowedSlot } := by
  simp only [read, readSlot, h supplySlot (by simp [fixedSlots]),
    h stateSlot (by simp [fixedSlots]), h managerSlot (by simp [fixedSlots]),
    h presaleSlot (by simp [fixedSlots]), h icoSlot (by simp [fixedSlots]),
    h totalSoldSlot (by simp [fixedSlots])]

/-- **Writing an actor's balance row** sets that entry of the balances. -/
theorem read_sstore_bal (hS : abs.Sound crypto Act) {a : Address} (ha : a ∈ Act) (x : Word) :
    read crypto Act (w.sstore t (mappingSlot crypto (Word.ofAddress a) balancesSlot) x) t =
      { read crypto Act w t with bal := (read crypto Act w t).bal.update a x.toNat } := by
  rw [read_of_fixed (fun k hk => BNB.Spec.sload_sstore_map hS (fixed_mem hk) (by simp) ha),
    BNB.Spec.readMap_sstore hS (by simp) ha,
    BNB.Spec.readMap2_sstore_map hS (by simp) (by simp) ha]
  rfl

/-- **Writing the allowance row of two actors** sets that entry of the allowances. -/
theorem read_sstore_allow (hS : abs.Sound crypto Act) {o sp : Address} (ho : o ∈ Act)
    (hs : sp ∈ Act) (x : Word) :
    read crypto Act
        (w.sstore t (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) allowedSlot) x) t =
      (read crypto Act w t).setAllowance o sp x.toNat := by
  rw [read_of_fixed (fun k hk => BNB.Spec.sload_sstore_map2 hS (fixed_mem hk) (by simp) ho hs),
    BNB.Spec.readMap_sstore_map2 hS (by simp) (by simp) ho hs,
    BNB.Spec.readMap2_sstore hS (by simp) ho hs]
  rfl

/-- The balances after two writes: `src` lowered by `v` and `dst` raised by `v`, in either
order, when covered and not wrapping. -/
theorem bal_move {f : Address →₀ ℕ} {c d : Address} {v : ℕ} {xc xd : ℕ} (hv : v ≤ f c)
    (hc : xc = f c - v) (hd : xd = (if d = c then f c - v else f d) + v) :
    (f.update c xc).update d xd = f - Finsupp.single c v + Finsupp.single d v := by
  ext a
  simp only [Finsupp.update_apply, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    Finsupp.single_apply]
  by_cases had : a = d
  · subst had
    by_cases hcd : c = a
    · subst hcd; simp [hd]
    · simp [hd, Ne.symm hcd, hcd]
  · by_cases hac : a = c
    · subst hac; simp [had, hc, Ne.symm had]
    · simp [had, hac, Ne.symm had, Ne.symm hac]

end Verified.WeirdERC20.LEND.Spec
