import EvmLeanProofs.Decode

/-!
# Jump destinations of large code, in linear time

`validJumpDests code` (`EvmLean.Interpreter.JumpDest`) scans the code with array indexing.
In the kernel a `ByteArray` is a list, so each `code[pc]` costs `O(pc)` and checking one jump
destination of a 16 KB contract by `decide +kernel` takes many minutes. Here the same bitmap
is computed by a single pass over `code.data.toList` (`jdBits`), and
`isValidJumpDest_validJumpDests_eq` shows that the two agree. A jump-destination fact about
concrete code is then a linear-time kernel computation:

```
example : isValidJumpDest (validJumpDests code) 0x4e = true :=
  isValidJumpDest_of_jdCheck (by kernel_decide)
```
-/

namespace EvmLean.Program

open Interpreter

/-- The jump-destination bitmap of a byte list, computed by one pass (`fuel` bounds the number
of instructions; `bs.length + 1` suffices). -/
def jdBits : Nat → List UInt8 → List Bool
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, b :: bs =>
    if b = 0x5b then true :: jdBits fuel bs
    else if 0x60 ≤ b ∧ b ≤ 0x7f then
      false :: (List.replicate (min (b.toNat - 0x5f) bs.length) false ++
        jdBits fuel (bs.drop (b.toNat - 0x5f)))
    else false :: jdBits fuel bs

/-- Is `d` a valid jump destination of `code`? Linear-time in the kernel. -/
def jdCheck (code : ByteArray) (d : Nat) : Bool :=
  (jdBits (code.data.toList.length + 1) code.data.toList)[d]?.getD false

private theorem take_set_succ (l : List Bool) (pc : Nat) (h : pc < l.length) :
    (l.set pc true).take (pc + 1) = l.take pc ++ [true] := by
  rw [List.take_add_one, List.take_set_of_le (Nat.le_refl pc), List.getElem?_set_self h]
  rfl

private theorem drop_eq_replicate (l : List Bool) (pc : Nat)
    (hf : ∀ i, pc ≤ i → l[i]?.getD false = false) :
    l.drop pc = List.replicate (l.length - pc) false := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp, fun b hb => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have := hf (pc + i) (by omega)
  rw [List.getElem_drop] at *
  rw [List.getElem?_eq_getElem (by simp at hi; omega)] at this
  simpa using this

private theorem take_of_false (l : List Bool) (pc k : Nat)
    (hf : ∀ i, pc ≤ i → l[i]?.getD false = false) :
    l.take (pc + 1 + k) = l.take pc ++ List.replicate (min (k + 1) (l.length - pc)) false := by
  rw [show pc + 1 + k = pc + (k + 1) by omega, List.take_add, drop_eq_replicate l pc hf,
    List.take_replicate]

/-- The array scan and the list scan agree. -/
theorem jumpDestLoop_toList (code : ByteArray) :
    ∀ (fuel pc : Nat) (acc : Array Bool), acc.size = code.size →
      (∀ i, pc ≤ i → acc.toList[i]?.getD false = false) → code.size - pc < fuel →
      (jumpDestLoop code fuel pc acc).toList =
        acc.toList.take pc ++ jdBits fuel (code.data.toList.drop pc) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; omega
  | succ fuel ih =>
    intro pc acc hsize hfalse hfuel
    have hlen : code.data.toList.length = code.size := Array.length_toList
    have hacc : acc.toList.length = code.size := by rw [Array.length_toList, hsize]
    unfold jumpDestLoop
    by_cases hpc : pc < code.size
    · simp only [hpc, ↓reduceDIte]
      have hdrop : code.data.toList.drop pc = code[pc] :: code.data.toList.drop (pc + 1) := by
        rw [List.drop_eq_getElem_cons (by omega)]
        rfl
      rw [hdrop]
      generalize code[pc] = b
      simp only [jdBits]
      by_cases hb : b = 0x5b
      · simp only [hb, ↓reduceIte]
        have hs : (acc.setIfInBounds pc true).size = code.size := by
          rw [Array.size_setIfInBounds, hsize]
        rw [ih (pc + 1) _ hs ?_ (by omega)]
        · rw [Array.toList_setIfInBounds, take_set_succ _ _ (by omega), List.append_assoc]
          rfl
        · intro i hi
          rw [Array.toList_setIfInBounds, List.getElem?_set_ne (by omega)]
          exact hfalse i (by omega)
      · simp only [hb, ↓reduceIte]
        by_cases hp : 0x60 ≤ b ∧ b ≤ 0x7f
        · simp only [hp, and_self, ↓reduceIte]
          rw [ih _ _ hsize (fun i hi => hfalse i (by omega)) (by omega)]
          rw [take_of_false _ pc _ (fun i hi => hfalse i hi), List.drop_drop, List.length_drop,
            List.append_assoc]
          have e1 : min (b.toNat - 95 + 1) (acc.toList.length - pc) =
              min (b.toNat - 95) (code.data.toList.length - (pc + 1)) + 1 := by
            rw [hacc, hlen]; omega
          rw [e1, List.replicate_succ, List.cons_append, Nat.add_comm (pc + 1)]
        · simp only [hp, ↓reduceIte]
          rw [ih _ _ hsize (fun i hi => hfalse i (by omega)) (by omega)]
          rw [show pc + 1 = pc + 1 + 0 from rfl, take_of_false _ pc 0 (fun i hi => hfalse i hi)]
          have e1 : min (0 + 1) (acc.toList.length - pc) = 1 := by rw [hacc]; omega
          rw [e1, List.append_assoc]
          rfl
    · simp only [hpc, ↓reduceDIte]
      have hle : code.size ≤ pc := Nat.le_of_not_lt hpc
      rw [List.drop_eq_nil_of_le (by omega), List.take_of_length_le (by omega)]
      cases fuel <;> simp [jdBits]

/-- The bitmap of `validJumpDests`, as a list, is `jdBits`. -/
theorem toList_validJumpDests (code : ByteArray) :
    (validJumpDests code).toList = jdBits (code.data.toList.length + 1) code.data.toList := by
  unfold validJumpDests
  have hlen : code.data.toList.length = code.size := Array.length_toList
  rw [jumpDestLoop_toList code _ 0 _ (by simp) ?_ (by omega)]
  · rw [List.take_zero, List.nil_append, List.drop_zero, hlen]
  · intro i _
    simp only [Array.toList_replicate, List.getElem?_replicate]
    split <;> rfl

/-- `isValidJumpDest` on `validJumpDests` is `jdCheck`. -/
theorem isValidJumpDest_validJumpDests_eq (code : ByteArray) (d : Nat) :
    isValidJumpDest (validJumpDests code) d = jdCheck code d := by
  unfold isValidJumpDest jdCheck
  rw [← toList_validJumpDests, Array.getElem?_toList]

/-- A jump-destination fact from the linear-time check (close the premise with
`kernel_decide`). -/
theorem isValidJumpDest_of_jdCheck {code : ByteArray} {d : Nat} (h : jdCheck code d = true) :
    isValidJumpDest (validJumpDests code) d = true := by
  rw [isValidJumpDest_validJumpDests_eq]; exact h

end EvmLean.Program
