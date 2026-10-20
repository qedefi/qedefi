import EvmLogic.Solidity.Strings

/-!
# Words of `extract_byte_array_length` and of the string copy

The getter of a `string` state variable, as solc 0.8.28 compiles it, computes on the slot word
`S` and on the length `L` with word operations. The lemmas here evaluate them in the form
symbolic execution produces (`n#256` literals, `Word.*` operations), to be passed to
`pwp_steps [..]` as rewrite rules:

* the flag `S & 1` (`and_one_of_even`, `and_one_of_odd`) and the length `S >> 1`, masked with
  `0x7f` for short strings (`shr_one_and_127`, `shr_one_of_odd`): `slotLen S`;
* the length checks `lt(L, 32)`, `lt(31, L)`, `iszero(L)` (`lt_32_of_lt`, …);
* the allocation size `div(add(31, L), 32) * 32` and the ABI padding `and(add(L, 31), not(31))`
  (`div_32_mul_32`, `and_notMask31`): both are `⌈L / 32⌉ · 32`;
* the short-string word `div(S, 256) * 256` (the data with the length byte cleared,
  `div_256_mul_256`).
-/

namespace EvmLean.Solidity.Str

/-- `S & 1` is the parity of `S`. -/
theorem toNat_and_one (S : Word) : (S &&& 1#256).toNat = S.toNat % 2 := by
  rw [BitVec.toNat_and]
  simp

/-- The flag of a short (even) slot word is `0`. -/
theorem and_one_of_even {S : Word} (h : S.toNat % 2 = 0) : S &&& 1#256 = 0#256 := by
  apply BitVec.eq_of_toNat_eq; rw [toNat_and_one, h]; rfl

/-- The flag of a long (odd) slot word is `1`. -/
theorem and_one_of_odd {S : Word} (h : S.toNat % 2 = 1) : S &&& 1#256 = 1#256 := by
  apply BitVec.eq_of_toNat_eq; rw [toNat_and_one, h]; rfl

/-- `S >> 1` is `⌊S / 2⌋`. -/
theorem shr_one (S : Word) : Word.shr 1#256 S = BitVec.ofNat 256 (S.toNat / 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Word.shr, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by have := S.isLt; omega)).symm

/-- The length of a short (even) slot word: `(S >> 1) & 0x7f`. -/
theorem shr_one_and_127 {S : Word} (h : S.toNat % 2 = 0) :
    Word.shr 1#256 S &&& 127#256 = BitVec.ofNat 256 (slotLen S) := by
  apply BitVec.eq_of_toNat_eq
  rw [shr_one, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hS := S.isLt
  rw [Nat.mod_eq_of_lt (by omega : S.toNat / 2 < 2 ^ 256)]
  simp only [slotLen, h, ↓reduceIte]
  rw [show (127 : Nat) % 2 ^ 256 = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact (Nat.mod_eq_of_lt (by omega)).symm

/-- The length of a long (odd) slot word: `S >> 1`. -/
theorem shr_one_of_odd {S : Word} (h : S.toNat % 2 = 1) :
    Word.shr 1#256 S = BitVec.ofNat 256 (slotLen S) := by
  rw [shr_one]; simp only [slotLen, h]; rfl

/-- `slotLen` is below `2²⁵⁵`. -/
theorem slotLen_lt (S : Word) : slotLen S < 2 ^ 255 := by
  have := S.isLt
  unfold slotLen; split <;> omega

/-- `toNat` of a small natural number as a word. -/
theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 256) : (BitVec.ofNat 256 n).toNat = n :=
  Nat.mod_eq_of_lt h

/-- `lt(L, 32)` for a short length. -/
theorem lt_32_of_lt {L : Nat} (h : L < 32) : Word.lt (BitVec.ofNat 256 L) 32#256 = 1#256 := by
  simp only [Word.lt, BitVec.ult, toNat_ofNat_of_lt (by omega : L < 2 ^ 256)]
  rw [decide_eq_true (by simp; omega)]; rfl

/-- `lt(L, 32)` for a long length. -/
theorem lt_32_of_ge {L : Nat} (h : 32 ≤ L) (h' : L < 2 ^ 256) :
    Word.lt (BitVec.ofNat 256 L) 32#256 = 0#256 := by
  simp only [Word.lt, BitVec.ult, toNat_ofNat_of_lt h']
  rw [decide_eq_false (by simp; omega)]; rfl

/-- `lt(31, L)` for a short length. -/
theorem lt_31_of_le {L : Nat} (h : L ≤ 31) : Word.lt 31#256 (BitVec.ofNat 256 L) = 0#256 := by
  simp only [Word.lt, BitVec.ult, toNat_ofNat_of_lt (by omega : L < 2 ^ 256)]
  rw [decide_eq_false (by simp; omega)]; rfl

/-- `lt(31, L)` for a long length. -/
theorem lt_31_of_gt {L : Nat} (h : 31 < L) (h' : L < 2 ^ 256) :
    Word.lt 31#256 (BitVec.ofNat 256 L) = 1#256 := by
  simp only [Word.lt, BitVec.ult, toNat_ofNat_of_lt h']
  rw [decide_eq_true (by simp; omega)]; rfl

/-- `iszero(L)` for a non-zero length. -/
theorem iszero_of_ne {L : Nat} (h : L ≠ 0) (h' : L < 2 ^ 256) :
    Word.iszero (BitVec.ofNat 256 L) = 0#256 := by
  have hb : (BitVec.ofNat 256 L == 0) = false := by
    rw [beq_eq_false_iff_ne]; intro he
    have := congrArg BitVec.toNat he
    rw [toNat_ofNat_of_lt h'] at this; exact h this
  simp only [Word.iszero, hb]; rfl

/-- `div(add(31, L), 32) * 32 = ⌈L / 32⌉ · 32` (the allocation of the copy). -/
theorem div_32_mul_32 {L : Nat} (h : L < 2 ^ 255) :
    Word.div (31#256 + BitVec.ofNat 256 L) 32#256 * 32#256 =
      BitVec.ofNat 256 ((L + 31) / 32 * 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Word.div, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : L < 2 ^ 256)]
  simp only [Nat.reducePow, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (by omega : 31 + L < 2 ^ 256 ), Nat.add_comm 31 L]

/-- `not(31)`, as the literal symbolic execution produces. -/
abbrev notMask31 : Word :=
  115792089237316195423570985008687907853269984665640564039457584007913129639904#256

/-- `x & not(31)` rounds down to a multiple of 32. -/
theorem toNat_and_notMask31 (x : Word) : (x &&& notMask31).toNat = x.toNat / 32 * 32 := by
  have hm : notMask31 = BitVec.allOnes 256 <<< 5 := by decide
  rw [hm, ← BitVec.shiftLeft_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  exact Nat.mod_eq_of_lt (by omega)

/-- `and(add(L, 31), not(31)) = ⌈L / 32⌉ · 32` (the ABI padding). -/
theorem and_notMask31 {L : Nat} (h : L < 2 ^ 255) :
    (BitVec.ofNat 256 L + 31#256 &&& notMask31) = BitVec.ofNat 256 ((L + 31) / 32 * 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_notMask31, BitVec.toNat_add, toNat_ofNat_of_lt (by omega),
    toNat_ofNat_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega), toNat_ofNat_of_lt (by omega)]

/-- `div(S, 256) * 256` clears the low byte. -/
theorem div_256_mul_256 (S : Word) :
    Word.div S 256#256 * 256#256 = BitVec.ofNat 256 (S.toNat / 256 * 256) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Word.div, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_ofNat]

/-- `gt(a, b)` when `a > b`. -/
theorem gt_eq_one {a b : Word} (h : b.toNat < a.toNat) : Word.gt a b = 1#256 := by
  simp only [Word.gt, BitVec.ult]
  rw [decide_eq_true (by simpa using h)]; rfl

/-- `gt(a, b)` when `a ≤ b`. -/
theorem gt_eq_zero {a b : Word} (h : a.toNat ≤ b.toNat) : Word.gt a b = 0#256 := by
  simp only [Word.gt, BitVec.ult]
  rw [decide_eq_false (by simp; omega)]; rfl

/-- `toNat` of a sum that does not overflow. -/
theorem toNat_add_of_lt {a b : Word} (h : a.toNat + b.toNat < 2 ^ 256) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

end EvmLean.Solidity.Str
