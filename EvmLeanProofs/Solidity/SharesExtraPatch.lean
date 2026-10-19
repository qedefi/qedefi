import EvmLeanProofs.Contracts.Basic
import EvmLeanProofs.Solidity.JumpDest
import EvmLeanProofs.Solidity.Abi

/-!
# Code with immutables: reading around the patches

solc compiles a Solidity `immutable` into 32-byte `PUSH32` placeholders that the constructor
fills in; `Contracts.patchWords code ps` is the canonical runtime code with the word `w`
written at offset `o` for each `(o, w) ∈ ps` (`runtimeCodeWith i` of a generated contract
module). Theorems about a deployment with **arbitrary** immutables are about
`patchWords code ps` for symbolic words, which is not a byte literal; but symbolic execution
only ever needs

* the opcode byte at `pc` (`code[pc]? = some b`): outside the patched windows it is the
  canonical byte (`getElem?_patchWords_of_offsets`);
* `PUSHn` immediates and `CODECOPY` sources (`readBytes code off n`): outside the windows
  they are the canonical bytes (`readBytes_patchWords_of_offsets`); inside, they are the
  patched word (`readBytes_patchWords_last`, for a read of the last patch at its offset);
* the jump table: patches only change `PUSH32` immediates, which the `JUMPDEST` scan skips,
  so the scan lists the same destinations. `JumpDestsAgree code base` packages this; for a
  concrete contract it is proved once, for all immutables, by kernel evaluation (the scan
  never inspects the patched bytes).

The side conditions are stated over the list of patch *offsets* (`ps.map Prod.fst = offs`),
which reduces to a literal list for symbolic words, so the disjointness checks are closed
`decide` goals. `EvmLeanProofs.Solidity.SharesExtraTactic` uses these lemmas to run
`sol_step` on patched code.
-/

namespace EvmLean.Contracts

/-! ## `writeList` -/

/-- `writeList` keeps the length. -/
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

/-- `writeList` changes nothing outside the written window. -/
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

/-- `writeList` of `ys` reads back `ys` inside the window, if the window fits. -/
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

/-- A word encodes to 32 bytes. -/
theorem length_ofWord_toList (w : Word) : (Bytes.ofWord w).data.toList.length = 32 := by
  simp [Bytes.ofWord, Bytes.ofNatBE]

/-- Patching keeps the length. -/
theorem length_patchList (l : List UInt8) (ps : List (Nat × Word)) :
    (patchList l ps).length = l.length := by
  induction ps generalizing l with
  | nil => rfl
  | cons p ps ih => simp only [patchList, List.foldl_cons] at ih ⊢; rw [ih, length_writeList]

/-- Patching changes nothing outside the windows. -/
theorem getElem?_patchList_of_disjoint (l : List UInt8) (ps : List (Nat × Word)) (j : Nat)
    (h : ∀ o ∈ ps.map Prod.fst, j < o ∨ o + 32 ≤ j) : (patchList l ps)[j]? = l[j]? := by
  induction ps generalizing l with
  | nil => rfl
  | cons p ps ih =>
    simp only [patchList, List.foldl_cons] at ih ⊢
    rw [ih _ (fun o ho => h o (List.mem_cons_of_mem _ ho)),
      getElem?_writeList_of_disjoint _ _ _ _
        (by rw [length_ofWord_toList]; exact h p.1 (List.mem_cons_self ..))]

/-- The last patch at a window reads back its word, provided no later patch overlaps it and
the window fits. -/
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

/-- `patchWords` is `patchList` on the bytes. -/
theorem data_patchWords (c : ByteArray) (ps : List (Nat × Word)) :
    (patchWords c ps).data.toList = patchList c.data.toList ps := rfl

/-- Byte lookup on a `ByteArray` is lookup on its list of bytes. -/
theorem getElem?_byteArray (c : ByteArray) (j : Nat) : c[j]? = c.data.toList[j]? := by
  rw [Array.getElem?_toList]
  by_cases h : j < c.size
  · rw [getElem?_pos c j h, getElem?_pos c.data j (by simpa using h),
      ByteArray.getElem_eq_getElem_data]
  · rw [getElem?_neg c j h, getElem?_neg c.data j (by simpa using h)]

/-- Patching keeps the size. -/
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

/-- `getD` agrees when lookups agree. -/
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

/-- **The patched word**: a 32-byte read at the offset of the last patch there is the patched
word (the window fits the code, and no later patch overlaps it). -/
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

/-- `code` has the size and the `JUMPDEST` scan of `base` (true of `patchWords base ps` when
every patch lies in a `PUSH32` immediate). Proved per contract by kernel evaluation. -/
def JumpDestsAgree (code base : ByteArray) : Prop :=
  code.size = base.size ∧
    Solidity.jumpDestList (base.size + 1) code.data.toList 0 =
      Solidity.jumpDestList (base.size + 1) base.data.toList 0

/-- A destination listed by the scan of `base` is valid in `code`. -/
theorem isValidJumpDest_of_agree {code base : ByteArray} {d : Nat} (h : JumpDestsAgree code base)
    (hd : d ∈ Solidity.jumpDestList (base.size + 1) base.data.toList 0) :
    Interpreter.isValidJumpDest (Interpreter.validJumpDests code) d = true :=
  Solidity.isValidJumpDest_of_mem (by rw [h.1, h.2]; exact hd)

end EvmLean.Contracts
