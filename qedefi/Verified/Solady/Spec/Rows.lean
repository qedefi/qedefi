import Verified.Solady.Spec.Abs
import EvmLogic.Step.Memory
import EvmLogic.Solidity.Steps
import Mathlib.Tactic.IntervalCases

/-!
# Solady's rows in scratch memory

Solady hashes its storage rows from scratch memory that two `mstore`s assemble: the seed word at
`0x0c` and the owner word at `0x00`, so that `[0x0c, 0x2c)` holds `o₂₀ ‖ 0⁸ ‖ seed₄`
(`rowWord o seed`); the allowance row appends the spender's 20 bytes from the word at `0x20`.
`read_row` reads that window back as the row word, from the two half-reads `[0x00, 0x20)`
and `[0x20, 0x2c)` that the normalization of `apwp_norm` computes; `read_storeWord_slice`
computes the second.
-/

namespace Verified.Solady.Spec
open EvmLean EvmLogic EvmLean.Bytes

theorem toUInt8_congr {a b : Nat} (h : a % 256 = b % 256) : a.toUInt8 = b.toUInt8 := by
  apply UInt8.toNat_inj.mp
  simp only [Nat.toUInt8]
  exact h

theorem getD_ofWord (w : Word) (j : Nat) (h : j < 32) :
    getD (ofWord w) j = (w.toNat >>> (8 * (31 - j))).toUInt8 := by
  rw [ofWord, EvmLean.Memory.getD_ofNatBE 32 _ j h]

theorem rowWord_toNat (o : Address) {seed : Word} (hs : seed.toNat < 2 ^ 96) :
    (rowWord o seed).toNat = o.toNat * 2 ^ 96 + seed.toNat := by
  have ho : o.toNat < 2 ^ 160 := o.isLt
  have hlt : o.toNat * 2 ^ 96 < 2 ^ 256 := by
    calc o.toNat * 2 ^ 96 < 2 ^ 160 * 2 ^ 96 := Nat.mul_lt_mul_of_pos_right ho (by positivity)
      _ = 2 ^ 256 := by norm_num
  simp only [rowWord, BitVec.toNat_or, BitVec.toNat_shiftLeft, Word.ofAddress,
    BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (show o.toNat < 2 ^ 256 by omega), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt hlt, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hs,
    Nat.shiftLeft_eq]

/-- Bytes `[k, k + n)` of a stored word. -/
theorem read_storeWord_slice (M : Memory) (off k n : Nat) (w : Word) (hk : k + n ≤ 32) :
    (M.storeWord off w).read (off + k) n = (ofWord w).extract k (k + n) := by
  apply ext_getD (by rw [Memory.read, size_readPadded, ByteArray.size_extract, size_ofWord]; omega)
  intro j hj
  rw [Memory.read, size_readPadded] at hj
  have h1 : off ≤ off + k + j ∧ off + k + j < off + (ofWord w).size := by
    rw [size_ofWord]; omega
  simp only [Memory.read, Memory.storeWord, getD_readPadded, hj, ↓reduceIte,
    Memory.getD_bytes_write, h1, and_self, getD_extract, show k + j < k + n by omega]
  congr 1
  omega

theorem read_storeWord_slice' (M : Memory) (off k n p : Nat) (w : Word) (hk : k + n ≤ 32)
    (hp : off + k = p) : (M.storeWord off w).read p n = (ofWord w).extract k (k + n) := by
  subst hp; exact read_storeWord_slice M off k n w hk

/-- **The row window** `[0x0c, 0x2c)`, read back as `rowWord`. -/
theorem read_row (M : Memory) (o : Address) (seed : Word) (hs : seed.toNat < 2 ^ 96)
    (h1 : M.read 0 32 = ofWord (Word.ofAddress o))
    (h2 : M.read 32 12 = (ofWord seed).extract 20 32) :
    M.read 12 32 = ofWord (rowWord o seed) := by
  apply ext_getD (by rw [Memory.read, size_readPadded, size_ofWord])
  intro j hj
  rw [Memory.read, size_readPadded] at hj
  have ho : o.toNat < 2 ^ 160 := o.isLt
  have hoa : (Word.ofAddress o).toNat = o.toNat := by
    simp only [Word.ofAddress, BitVec.toNat_setWidth]; omega
  rw [getD_ofWord _ _ hj, rowWord_toNat o hs]
  simp only [Memory.read, getD_readPadded, hj, ↓reduceIte]
  by_cases hj20 : j < 20
  · have e := congrArg (fun b => getD b (12 + j)) h1
    simp only [Memory.read, getD_readPadded, show 12 + j < 32 by omega, ↓reduceIte,
      Nat.zero_add] at e
    rw [e, getD_ofWord _ _ (by omega), hoa]
    apply toUInt8_congr
    simp only [Nat.shiftRight_eq_div_pow]
    interval_cases j <;> omega
  · have e := congrArg (fun b => getD b (j - 20)) h2
    simp only [Memory.read, getD_readPadded, show j - 20 < 12 by omega, ↓reduceIte,
      getD_extract, show 20 + (j - 20) < 32 by omega] at e
    rw [show 12 + j = 32 + (j - 20) by omega, e, getD_ofWord _ _ (by omega),
      show 20 + (j - 20) = j by omega]
    apply toUInt8_congr
    simp only [Nat.shiftRight_eq_div_pow]
    interval_cases j <;> omega

theorem ofWord_ofAddress_extract (a : Address) :
    (ofWord (Word.ofAddress a)).extract 12 32 = ofAddress a := by
  apply ext_getD (by simp [ByteArray.size_extract, size_ofWord, size_ofAddress])
  intro j hj
  rw [ByteArray.size_extract, size_ofWord] at hj
  have ho : a.toNat < 2 ^ 160 := a.isLt
  have hoa : (Word.ofAddress a).toNat = a.toNat := by
    simp only [Word.ofAddress, BitVec.toNat_setWidth]; omega
  rw [getD_extract, ite_eq_left_iff.mpr (fun h => absurd (by omega) h), getD_ofWord _ _ (by omega), ofAddress,
    EvmLean.Memory.getD_ofNatBE 20 _ j (by omega), hoa]
  congr 2
  omega

/-- **The allowance window** `[0x0c, 0x40)`: the row word, then the spender's 20 bytes. -/
theorem read_allowRow (M : Memory) (o sp : Address) (seed : Word) (hs : seed.toNat < 2 ^ 96)
    (h1 : M.read 0 32 = ofWord (Word.ofAddress o))
    (h2 : M.read 32 12 = (ofWord seed).extract 20 32)
    (h3 : M.read 44 20 = (ofWord (Word.ofAddress sp)).extract 12 32) :
    M.read 12 52 = ofWord (rowWord o seed) ++ ofAddress sp := by
  rw [show (52 : Nat) = 32 + 20 from rfl, Memory.read_add, read_row M o seed hs h1 h2,
    show 12 + 32 = 44 from rfl, h3, ofWord_ofAddress_extract]

/-- Solady's Permit2 test `(sp & mask) + ~(PERMIT2 − 1) = 0`, normalized. -/
theorem permit2_test (sp : Address) :
    Word.ofAddress sp +
      115792089237316195423570985008687907853269803818564352520799939062701070251101#256 = 0 ↔
      sp = PERMIT2 := by
  have ho : sp.toNat < 2 ^ 160 := sp.isLt
  have hoa : (Word.ofAddress sp).toNat = sp.toNat := by
    simp only [Word.ofAddress, BitVec.toNat_setWidth]; omega
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, hoa] at h'
    have e1 : (115792089237316195423570985008687907853269803818564352520799939062701070251101#256
      : Word).toNat = 115792089237316195423570985008687907853269803818564352520799939062701070251101
      := rfl
    have e2 : (0 : Word).toNat = 0 := rfl
    have e3 : PERMIT2.toNat = 180847076211518657644945212059388835 := rfl
    rw [e1, e2] at h'
    apply BitVec.eq_of_toNat_eq
    rw [e3]
    omega
  · rintro rfl
    decide

/-- `shr(96, mload(0x2c))` after `mstore(0x20, sp)`: the spender, whatever follows in memory. -/
theorem shr_loadWord_addr (M : Memory) (sp : Address) :
    Word.shr 96#256 ((M.storeWord 32 (Word.ofAddress sp)).loadWord 44) = Word.ofAddress sp := by
  have hs : sp.toNat < 2 ^ 160 := sp.isLt
  have hoa : (Word.ofAddress sp).toNat = sp.toNat := by
    simp only [Word.ofAddress, BitVec.toNat_setWidth]; omega
  have h1 : (M.storeWord 32 (Word.ofAddress sp)).read 44 20 = ofAddress sp := by
    rw [read_storeWord_slice' _ 32 12 20 44 _ (by omega) rfl, ofWord_ofAddress_extract]
  have hB := toNat_lt ((M.storeWord 32 (Word.ofAddress sp)).read 64 12)
  rw [Memory.read, size_readPadded] at hB
  apply BitVec.eq_of_toNat_eq
  rw [Memory.loadWord, show (M.storeWord 32 (Word.ofAddress sp)).read 44 32 =
    (M.storeWord 32 (Word.ofAddress sp)).read 44 20 ++
      (M.storeWord 32 (Word.ofAddress sp)).read 64 12 from Memory.read_add _ 44 20 12, h1]
  simp only [Word.shr, toWord, toNat_append, toNat_ofAddress, hoa, Memory.read, size_readPadded]
  change (BitVec.ofNat 256 _ >>> (96 : Nat)).toNat = _
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- Solady `approve`'s Permit2 test `or(xor(sp, PERMIT2), iszero(not(v)))`, normalized: zero
exactly when the spender is Permit2 and the amount is not `MAX`. -/
theorem approve_test (sp : Address) (v : Word) :
    (~~~v).iszero ||| 180847076211518657644945212059388835#256 ^^^ Word.ofAddress sp = 0 ↔
      sp = PERMIT2 ∧ v ≠ ~~~0 := by
  have hx : 180847076211518657644945212059388835#256 ^^^ Word.ofAddress sp = 0 ↔ sp = PERMIT2 := by
    rw [show (0 : Word) = 0#256 from rfl, BitVec.xor_eq_zero_iff]
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h
      simp only [Word.ofAddress, BitVec.toNat_setWidth] at this
      have hs : sp.toNat < 2 ^ 160 := sp.isLt
      rw [show PERMIT2.toNat = 180847076211518657644945212059388835 from rfl]
      rw [show (180847076211518657644945212059388835#256 : Word).toNat =
        180847076211518657644945212059388835 from rfl] at this
      omega
    · rintro rfl; decide
  have hA : (~~~v).iszero = 0 ↔ ~~~v ≠ 0 := by
    by_cases hx : ~~~v = 0 <;> simp [Word.iszero, Word.ofBool, hx]
  have hB : ~~~v ≠ 0 ↔ v ≠ ~~~0 := by
    constructor
    · intro h hv; exact h (by rw [hv, BitVec.not_not])
    · intro h hv; exact h (by rw [← hv, BitVec.not_not])
  rw [show (0 : Word) = 0#256 from rfl, BitVec.or_eq_zero_iff, ← show (0 : Word) = 0#256 from rfl,
    hA, hB, hx, and_comm]

theorem read_seed_tail (M : Memory) (s : Word) :
    (M.storeWord 12 s).read 32 12 = (ofWord s).extract 20 32 :=
  read_storeWord_slice' M 12 20 12 32 s (by omega) rfl

/-- The row window after `mstore(0x00, o)`, given the seed tail at `[0x20, 0x2c)`. -/
theorem read_row_of (M : Memory) (o : Address) (seed : Word) (hs : seed.toNat < 2 ^ 96)
    (h2 : M.read 32 12 = (ofWord seed).extract 20 32) :
    (M.storeWord 0 (Word.ofAddress o)).read 12 32 = ofWord (rowWord o seed) :=
  read_row _ o seed hs (Memory.read_storeWord _ _ _)
    (by rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), h2])

/-- `read_row_of` for the balance seed (a `simp` lemma with its hypothesis discharged). -/
theorem read_balRow (M : Memory) (o : Address)
    (h2 : M.read 32 12 = (ofWord 2275545506#256).extract 20 32) :
    (M.storeWord 0 (Word.ofAddress o)).read 12 32 = ofWord (rowWord o balSeed) :=
  read_row_of M o balSeed (by decide) h2

/-- `shr(96, mload(off))` when `[off, off + 20)` holds an address. -/
theorem shr_loadWord_of (M : Memory) (off : Nat) (a : Address)
    (h : M.read off 20 = ofAddress a) :
    Word.shr 96#256 (M.loadWord off) = Word.ofAddress a := by
  have hs : a.toNat < 2 ^ 160 := a.isLt
  have hB := toNat_lt (M.read (off + 20) 12)
  rw [Memory.read, size_readPadded] at hB
  apply BitVec.eq_of_toNat_eq
  rw [Memory.loadWord, show M.read off 32 = M.read off 20 ++ M.read (off + 20) 12 from
    Memory.read_add _ off 20 12, h]
  simp only [Word.shr, toWord, toNat_append, toNat_ofAddress, Memory.read, size_readPadded]
  change (BitVec.ofNat 256 _ >>> (96 : Nat)).toNat = _
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hoa : (Word.ofAddress a).toNat = a.toNat := by
    simp only [Word.ofAddress, BitVec.toNat_setWidth]; omega
  rw [hoa]
  omega

/-- The address in a stored address word: bytes `[off + 12, off + 32)`. -/
theorem read_addr_of_store (M : Memory) (off : Nat) (a : Address) :
    (M.storeWord off (Word.ofAddress a)).read (off + 12) 20 = ofAddress a := by
  rw [read_storeWord_slice' _ off 12 20 (off + 12) _ (by omega) rfl, ofWord_ofAddress_extract]

theorem read_addr0 (M : Memory) (a : Address) :
    (M.storeWord 0 (Word.ofAddress a)).read 12 20 = ofAddress a :=
  read_addr_of_store M 0 a

theorem le_of_iszero_gt {v b : Word} (h : Word.iszero (Word.gt v b) ≠ 0) : v.toNat ≤ b.toNat := by
  by_contra hlt
  have hu : BitVec.ult b v = true := by simp [BitVec.ult]; omega
  simp [Word.iszero, Word.gt, Word.ofBool, hu] at h

theorem lt_of_iszero_gt_eq {v b : Word} (h : Word.iszero (Word.gt v b) = 0) : b.toNat < v.toNat := by
  by_contra hle
  have hu : BitVec.ult b v = false := by simp [BitVec.ult]; omega
  simp [Word.iszero, Word.gt, Word.ofBool, hu] at h

end Verified.Solady.Spec
