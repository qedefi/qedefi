import EvmLean
import EvmLogic.Solidity.JumpDest
import EvmLogic.Solidity.Abi

/-!
# Compiled contracts: shared definitions

solc compiles an `immutable` into 32-byte `PUSH32` placeholders that the constructor fills.
Generated contract modules (`scripts/build-contracts.sh`) expose `runtimeCodeWith i =
patchWords code ps`, so theorems hold for arbitrary immutables. Symbolic execution only needs
bytes outside the patches (unchanged), the patched words, and the jump table (unchanged, as
`JUMPDEST` scanning skips `PUSH32` immediates: `JumpDestsAgree`).
-/

section

namespace EvmLogic.Solidity
open EvmLean

/-- An immutable variable and the byte offsets of its 32-byte placeholders in the runtime code. -/
structure ImmutableRef where
  name : String
  /-- Offsets of the 32-byte slots holding its value. -/
  offsets : List Nat
  deriving Repr, DecidableEq, Inhabited

/-- Overwrite `l` from position `off` with `src` (truncated at the end of `l`). Structural on
lists, so it reduces in the kernel (`ByteArray.copySlice` does not, usefully). -/
def writeList : List UInt8 → Nat → List UInt8 → List UInt8
  | l, _, [] => l
  | [], _, _ => []
  | _ :: xs, 0, y :: ys => y :: writeList xs 0 ys
  | x :: xs, n + 1, ys => x :: writeList xs n ys

/-- Overwrite the 32 bytes at each offset with the corresponding word (big-endian). -/
def patchWords (code : ByteArray) (ps : List (Nat × Word)) : ByteArray :=
  ⟨⟨ps.foldl (fun l p => writeList l p.1 (Bytes.ofWord p.2).data.toList) code.data.toList⟩⟩

/-- For kernel checks of code equality: compare `.data.toList` (structural), since
`ByteArray`'s `DecidableEq` does not reduce well in the kernel. -/
theorem eq_of_data_toList_eq {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  rcases a with ⟨⟨a⟩⟩
  rcases b with ⟨⟨b⟩⟩
  simp_all

end EvmLogic.Solidity

end

section

/-!
## Code with immutables: reading around the patches

Side conditions are stated over the patch *offsets* (`ps.map Prod.fst = offs`), a literal
list even for symbolic words, so disjointness checks are closed `decide` goals (used by
`EvmLogic.Tactic.Patched`).
-/

namespace EvmLogic.Solidity
open EvmLean

/-! ## `writeList` -/

theorem length_writeList (l : List UInt8) (off : Nat) (ys : List UInt8) :
    (writeList l off ys).length = l.length := by
  induction l generalizing off ys with
  | nil => cases ys <;> simp [writeList]
  | cons x xs ih =>
    cases ys with
    | nil => simp [writeList]
    | cons y ys =>
      cases off with
      | zero => simp [writeList, ih]
      | succ n => simp [writeList, ih]

theorem getElem?_writeList_of_disjoint (l : List UInt8) (off : Nat) (ys : List UInt8) (j : Nat)
    (h : j < off ∨ off + ys.length ≤ j) : (writeList l off ys)[j]? = l[j]? := by
  induction l generalizing off ys j with
  | nil => cases ys <;> simp [writeList]
  | cons x xs ih =>
    cases ys with
    | nil => simp [writeList]
    | cons y ys =>
      cases off with
      | zero =>
        simp only [List.length_cons] at h
        obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        simp only [writeList, List.getElem?_cons_succ]
        exact ih 0 ys j (.inr (by omega))
      | succ n =>
        cases j with
        | zero => simp [writeList]
        | succ j =>
          simp only [writeList, List.getElem?_cons_succ]
          exact ih n (y :: ys) j (by simp only [List.length_cons] at h ⊢; omega)

theorem getElem?_writeList_self (l : List UInt8) (off : Nat) (ys : List UInt8) (j : Nat)
    (hfit : off + ys.length ≤ l.length) (hj : j < ys.length) :
    (writeList l off ys)[off + j]? = ys[j]? := by
  induction l generalizing off ys j with
  | nil => simp only [List.length_nil] at hfit; omega
  | cons x xs ih =>
    cases ys with
    | nil => simp at hj
    | cons y ys =>
      cases off with
      | zero =>
        cases j with
        | zero => simp [writeList]
        | succ j =>
          simp only [writeList, Nat.zero_add, List.getElem?_cons_succ]
          simpa using ih 0 ys j (by simp at hfit ⊢; omega) (by simp at hj; omega)
      | succ n =>
        simp only [writeList, Nat.add_right_comm n 1 j, List.getElem?_cons_succ]
        exact ih n (y :: ys) j (by simp at hfit ⊢; omega) hj

/-! ## `patchWords` -/

/-- The byte list of `patchWords` (the fold over the patches). -/
def patchList (l : List UInt8) (ps : List (Nat × Word)) : List UInt8 :=
  ps.foldl (fun l p => writeList l p.1 (Bytes.ofWord p.2).data.toList) l

theorem length_ofWord_toList (w : Word) : (Bytes.ofWord w).data.toList.length = 32 := by
  simp [Bytes.ofWord, Bytes.ofNatBE]

theorem length_patchList (l : List UInt8) (ps : List (Nat × Word)) :
    (patchList l ps).length = l.length := by
  induction ps generalizing l with
  | nil => rfl
  | cons p ps ih => simp only [patchList, List.foldl_cons] at ih ⊢; rw [ih, length_writeList]

theorem getElem?_patchList_of_disjoint (l : List UInt8) (ps : List (Nat × Word)) (j : Nat)
    (h : ∀ o ∈ ps.map Prod.fst, j < o ∨ o + 32 ≤ j) : (patchList l ps)[j]? = l[j]? := by
  induction ps generalizing l with
  | nil => rfl
  | cons p ps ih =>
    simp only [patchList, List.foldl_cons] at ih ⊢
    rw [ih _ (fun o ho => h o (List.mem_cons_of_mem _ ho)),
      getElem?_writeList_of_disjoint _ _ _ _
        (by rw [length_ofWord_toList]; exact h p.1 (List.mem_cons_self ..))]

theorem getElem?_patchList_last (l : List UInt8) (ps₁ ps₂ : List (Nat × Word)) (o : Nat)
    (w : Word) (hfit : o + 32 ≤ l.length)
    (h₂ : ∀ o' ∈ ps₂.map Prod.fst, o + 32 ≤ o' ∨ o' + 32 ≤ o) (j : Nat) (hj : j < 32) :
    (patchList l (ps₁ ++ (o, w) :: ps₂))[o + j]? = (Bytes.ofWord w).data.toList[j]? := by
  simp only [patchList, List.foldl_append, List.foldl_cons]
  have := getElem?_patchList_of_disjoint
    (writeList (patchList l ps₁) o (Bytes.ofWord w).data.toList) ps₂ (o + j)
    (fun o' ho' => by have := h₂ o' ho'; omega)
  simp only [patchList] at this
  rw [this]
  apply getElem?_writeList_self
  · rw [length_ofWord_toList]
    have := length_patchList l ps₁
    simp only [patchList] at this
    omega
  · rw [length_ofWord_toList]; exact hj

theorem data_patchWords (c : ByteArray) (ps : List (Nat × Word)) :
    (patchWords c ps).data.toList = patchList c.data.toList ps := rfl

theorem getElem?_byteArray (c : ByteArray) (j : Nat) : c[j]? = c.data.toList[j]? := by
  rw [Array.getElem?_toList]
  by_cases h : j < c.size
  · rw [getElem?_pos c j h, getElem?_pos c.data j (by simpa using h),
      ByteArray.getElem_eq_getElem_data]
  · rw [getElem?_neg c j h, getElem?_neg c.data j (by simpa using h)]

theorem size_patchWords (c : ByteArray) (ps : List (Nat × Word)) :
    (patchWords c ps).size = c.size := by
  have h := length_patchList c.data.toList ps
  rw [← data_patchWords] at h
  simpa using h

/-- **Code bytes outside the patches.** -/
theorem getElem?_patchWords_of_offsets (c : ByteArray) (ps : List (Nat × Word)) (j : Nat)
    (offs : List Nat) (hoffs : ps.map Prod.fst = offs)
    (h : ∀ o ∈ offs, j < o ∨ o + 32 ≤ j) : (patchWords c ps)[j]? = c[j]? := by
  rw [getElem?_byteArray, getElem?_byteArray, data_patchWords]
  exact getElem?_patchList_of_disjoint _ _ _ (hoffs ▸ h)

theorem getD_eq_of_getElem? {a b : ByteArray} {i j : Nat} (h : a[i]? = b[j]?) :
    Bytes.getD a i = Bytes.getD b j := by
  unfold Bytes.getD
  by_cases ha : i < a.size <;> by_cases hb : j < b.size
  · rw [getElem?_pos a i ha, getElem?_pos b j hb] at h
    simp only [ha, hb, ↓reduceDIte]
    exact Option.some.inj h
  · rw [getElem?_pos a i ha, getElem?_neg b j hb] at h; cases h
  · rw [getElem?_neg a i ha, getElem?_pos b j hb] at h; cases h
  · simp only [ha, hb, ↓reduceDIte]

/-- **Code reads outside the patches** (`PUSHn` immediates, `CODECOPY`). -/
theorem readBytes_patchWords_of_offsets (c : ByteArray) (ps : List (Nat × Word))
    (off n : Nat) (offs : List Nat) (hoffs : ps.map Prod.fst = offs)
    (h : ∀ o ∈ offs, off + n ≤ o ∨ o + 32 ≤ off) :
    Interpreter.readBytes (patchWords c ps) off n = Interpreter.readBytes c off n := by
  rw [Interpreter.readBytes_eq_readPadded, Interpreter.readBytes_eq_readPadded]
  apply Bytes.ext_getD (by simp [Bytes.size_readPadded])
  intro j hj
  rw [Bytes.size_readPadded] at hj
  rw [Bytes.getD_readPadded, Bytes.getD_readPadded]
  simp only [hj, ↓reduceIte]
  apply getD_eq_of_getElem?
  apply getElem?_patchWords_of_offsets c ps _ offs hoffs
  intro o ho
  have := h o ho
  omega

/-- **The patched word**: a 32-byte read at the last patch's offset (window fits, no later
patch overlaps). -/
theorem readBytes_patchWords_last (c : ByteArray) (ps₁ ps₂ : List (Nat × Word)) (o : Nat)
    (w : Word) (hfit : o + 32 ≤ c.size)
    (h₂ : ∀ o' ∈ ps₂.map Prod.fst, o + 32 ≤ o' ∨ o' + 32 ≤ o) :
    Interpreter.readBytes (patchWords c (ps₁ ++ (o, w) :: ps₂)) o 32 = Bytes.ofWord w := by
  rw [Interpreter.readBytes_eq_readPadded]
  apply Bytes.ext_getD (by rw [Bytes.size_readPadded, Bytes.size_ofWord])
  intro j hj
  rw [Bytes.size_readPadded] at hj
  rw [Bytes.getD_readPadded]
  simp only [hj, ↓reduceIte]
  have hl : (patchWords c (ps₁ ++ (o, w) :: ps₂))[o + j]? = (Bytes.ofWord w)[j]? := by
    rw [getElem?_byteArray, getElem?_byteArray, data_patchWords]
    have hfit' : o + 32 ≤ c.data.toList.length := by rw [Array.length_toList]; exact hfit
    exact getElem?_patchList_last c.data.toList ps₁ ps₂ o w hfit' h₂ j hj
  exact getD_eq_of_getElem? hl

/-! ## Jump destinations -/

/-- `code` has the size and `JUMPDEST` scan of `base` (true of `patchWords base ps` when every
patch lies in a `PUSH32` immediate). Proved per contract by kernel evaluation. -/
def JumpDestsAgree (code base : ByteArray) : Prop :=
  code.size = base.size ∧
    Solidity.jumpDestList (base.size + 1) code.data.toList 0 =
      Solidity.jumpDestList (base.size + 1) base.data.toList 0

theorem isValidJumpDest_of_agree {code base : ByteArray} {d : Nat} (h : JumpDestsAgree code base)
    (hd : d ∈ Solidity.jumpDestList (base.size + 1) base.data.toList 0) :
    Interpreter.isValidJumpDest (Interpreter.validJumpDests code) d = true :=
  Solidity.isValidJumpDest_of_mem (by rw [h.1, h.2]; exact hd)

end EvmLogic.Solidity

end
