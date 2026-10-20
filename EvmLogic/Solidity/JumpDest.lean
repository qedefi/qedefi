import EvmLean

/-!
# Jump destinations of large bytecode, checked in the kernel

Evaluating `validJumpDests` in the kernel is quadratic (list-backed arrays) and takes minutes
on compiled contracts. `jumpDestList` is the same scan over a `List UInt8`;
`isValidJumpDest_of_mem` lets `decide +kernel` discharge a jump destination in ~0.1 s.
-/

namespace EvmLogic.Solidity
open EvmLean EvmLean.Interpreter

/-- The valid `JUMPDEST` positions of `bytes` (a suffix of the code starting at position
`pos`), scanning at most `fuel` instructions. Mirrors `jumpDestLoop` over a list. -/
def jumpDestList : Nat → List UInt8 → Nat → List Nat
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | f + 1, b :: bs, pos =>
    if b = 0x5b then pos :: jumpDestList f bs (pos + 1)
    else if 0x60 ≤ b ∧ b ≤ 0x7f then
      jumpDestList f (bs.drop (b.toNat - 0x5f)) (pos + 1 + (b.toNat - 0x5f))
    else jumpDestList f bs (pos + 1)

private theorem getElem?_setIfInBounds_of_true {acc : Array Bool} {i j : Nat}
    (h : acc[i]? = some true) : (acc.setIfInBounds j true)[i]? = some true := by
  rw [Array.getElem?_setIfInBounds]
  split
  · subst_vars
    rw [getElem?_eq_some_iff] at h
    simp [h.1]
  · exact h

theorem jumpDestLoop_of_true (code : ByteArray) (fuel pc : Nat) (acc : Array Bool) (i : Nat)
    (h : acc[i]? = some true) : (jumpDestLoop code fuel pc acc)[i]? = some true := by
  induction fuel generalizing pc acc with
  | zero => exact h
  | succ n ih =>
    unfold jumpDestLoop
    split
    · simp only []
      split
      · exact ih _ _ (getElem?_setIfInBounds_of_true h)
      · split <;> exact ih _ _ h
    · exact h

theorem jumpDestLoop_of_mem (code : ByteArray) (fuel pc : Nat) (acc : Array Bool)
    (hacc : acc.size = code.size) (d : Nat)
    (h : d ∈ jumpDestList fuel (code.data.toList.drop pc) pc) :
    (jumpDestLoop code fuel pc acc)[d]? = some true := by
  induction fuel generalizing pc acc with
  | zero => simp [jumpDestList] at h
  | succ n ih =>
    by_cases hpc : pc < code.size
    · have hlen : pc < code.data.toList.length := by simpa using hpc
      rw [List.drop_eq_getElem_cons hlen] at h
      have hb : code.data.toList[pc] = code[pc] := by
        simp [ByteArray.getElem_eq_getElem_data]
      rw [hb] at h
      unfold jumpDestLoop
      simp only [hpc, ↓reduceDIte]
      simp only [jumpDestList] at h
      split
      · rename_i h5b
        simp only [h5b, ↓reduceIte, List.mem_cons] at h
        rcases h with rfl | h
        · apply jumpDestLoop_of_true
          rw [Array.getElem?_setIfInBounds_self_of_lt (by omega)]
        · exact ih _ _ (by simp [hacc]) h
      · rename_i h5b
        simp only [h5b, ↓reduceIte] at h
        split
        · rename_i hpush
          simp only [hpush, and_self, ↓reduceIte, List.drop_drop] at h
          exact ih _ _ hacc h
        · rename_i hpush
          simp only [hpush, ↓reduceIte] at h
          exact ih _ _ hacc h
    · have : code.data.toList.drop pc = [] := by
        apply List.drop_of_length_le
        simp only [Array.length_toList]
        exact Nat.le_of_not_lt hpc
      rw [this] at h
      simp [jumpDestList] at h

/-- **Valid jump destinations from the list scan.** -/
theorem isValidJumpDest_of_mem {code : ByteArray} {d : Nat}
    (h : d ∈ jumpDestList (code.size + 1) code.data.toList 0) :
    isValidJumpDest (validJumpDests code) d = true := by
  unfold isValidJumpDest validJumpDests
  rw [jumpDestLoop_of_mem code (code.size + 1) 0 _ (by simp) d (by simpa using h)]
  rfl

end EvmLogic.Solidity
