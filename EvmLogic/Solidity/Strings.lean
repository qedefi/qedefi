import EvmLogic.Solidity.Abi
import EvmLogic.Solidity.Layout
import EvmLogic.Solidity.Word

/-!
# `string` / `bytes` in storage and in ABI return data

Solidity stores a `string` (or `bytes`) state variable at slot `p` in one of two forms
(Solidity docs, "Layout of State Variables in Storage", *bytes and string*):

* **short** (at most 31 bytes): the data, left-aligned, in the high bytes of the slot word,
  and `2 · length` in its lowest byte (so the word is even);
* **long** (32 bytes or more): `2 · length + 1` in the slot (odd), and the data in the
  consecutive slots `keccak256(p) + j` (`Layout.arrayDataSlot`), 32 bytes each, the last one
  zero-padded.

solc reads it back with `extract_byte_array_length`: `len := word >> 1`, masked with `0x7f`
when the word is even, and a `Panic(0x22)` when the two forms are inconsistent (an even word
with `len ≥ 32`, or an odd one with `len < 32`). This file follows the compiled code:

* `Str.slotLen`, `Str.slotOk`: the length and the consistency check;
* `Str.decode crypto sload p`: the bytes the getter of a `string` at slot `p` returns, or
  `none` if the slot panics; `stringAt crypto w a p` is it for account `a` of world `w`;
* `Abi.encodeString s`: the ABI encoding of a single `string` return value: the offset
  `0x20`, the length, the data zero-padded to a multiple of 32 bytes.

Encoding lemmas: `Str.decode_shortWord` (a short string stored as `Str.shortWord s` decodes
to `s`) and `Str.decode_of_storesLong` (a long string stored as `Str.StoresLong` describes
decodes to it). Reading needs no hypothesis on Keccak: the data slots are whatever
`arrayDataSlot` is for the given `Crypto`.

The word lemmas at the end evaluate the operations of `extract_byte_array_length` and of the
copy loop on the words symbolic execution produces (`Str.and_one_of_even`, `Str.shr_one`,
`Str.and_notMask31`, …).
-/

section

namespace EvmLean.Solidity

open Bytes

/-! ## Bytes of words -/

/-- Byte `j` of the big-endian encoding of `n` in `len` bytes. -/
theorem getD_ofNatBE (len n j : Nat) (h : j < len) :
    getD (ofNatBE len n) j = (n >>> (8 * (len - 1 - j))).toUInt8 := by
  have h' : j < (ofNatBE len n).size := by rw [size_ofNatBE]; exact h
  simp only [getD, h', ↓reduceDIte]
  simp [ofNatBE, ByteArray.getElem_eq_getElem_data]

/-- Byte `j` of a word. -/
theorem getD_ofWord (w : Word) (j : Nat) (h : j < 32) :
    getD (ofWord w) j = (w.toNat >>> (8 * (31 - j))).toUInt8 :=
  getD_ofNatBE 32 w.toNat j h

/-- A prefix of the zero word is zeros. -/
theorem extract_ofWord_zero {n : Nat} (h : n ≤ 32) : (ofWord 0#256).extract 0 n = zeros n := by
  apply ext_getD (by rw [ByteArray.size_extract, size_ofWord, size_zeros]; omega)
  intro j hj
  rw [ByteArray.size_extract, size_ofWord] at hj
  rw [getD_extract, getD_zeros, ite_eq_left (by omega), getD_ofWord _ _ (by omega)]
  simp

/-- Clearing the low byte of a word (`div(S, 256) * 256`) keeps its first 31 bytes. -/
theorem extract_ofWord_div256 (S : Word) {n : Nat} (h : n ≤ 31) :
    (ofWord (BitVec.ofNat 256 (S.toNat / 256 * 256))).extract 0 n = (ofWord S).extract 0 n := by
  apply ext_getD (by simp only [ByteArray.size_extract, size_ofWord])
  intro j hj
  rw [ByteArray.size_extract, size_ofWord] at hj
  rw [getD_extract, getD_extract]
  split
  · rename_i hj'
    rw [getD_ofWord _ _ (by omega), getD_ofWord _ _ (by omega)]
    congr 1
    have hS := S.isLt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow]
    obtain ⟨k, hk⟩ : ∃ k, 8 * (31 - (0 + j)) = 8 + 8 * k := ⟨30 - j, by omega⟩
    rw [hk, Nat.pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel _ (by decide)]
  · rfl

namespace Str

/-! ## Decoding the slot -/

/-- The length a string slot word encodes: `word >> 1`, masked with `0x7f` for the short
(even) form, as `extract_byte_array_length` computes it. -/
def slotLen (S : Word) : Nat := if S.toNat % 2 = 0 then S.toNat / 2 % 128 else S.toNat / 2

/-- The consistency check of `extract_byte_array_length`: a short (even) word encodes fewer
than 32 bytes, a long (odd) one at least 32. -/
def slotOk (S : Word) : Bool := if S.toNat % 2 = 0 then decide (slotLen S < 32) else
  decide (32 ≤ slotLen S)

/-- The words at slots `d, d + 1, …, d + k - 1` of a storage, concatenated. -/
def wordsFrom (sload : Word → Word) (d : Word) (k : Nat) : ByteArray :=
  (List.range k).foldl (fun acc j => acc ++ ofWord (sload (d + BitVec.ofNat 256 j)))
    ByteArray.empty

/-- The data of a long string of `len` bytes whose first data slot is `d`: the words at
`d, d + 1, …` (`⌈len / 32⌉` of them), concatenated and cut to `len` bytes. -/
def longData (sload : Word → Word) (d : Word) (len : Nat) : ByteArray :=
  (wordsFrom sload d ((len + 31) / 32)).extract 0 len

/-- One more word. -/
theorem wordsFrom_succ (sload : Word → Word) (d : Word) (k : Nat) :
    wordsFrom sload d (k + 1) = wordsFrom sload d k ++ ofWord (sload (d + BitVec.ofNat 256 k)) := by
  simp only [wordsFrom, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `k` words are `32 k` bytes. -/
theorem size_wordsFrom (sload : Word → Word) (d : Word) (k : Nat) :
    (wordsFrom sload d k).size = 32 * k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [wordsFrom_succ, ByteArray.size_append, ih, size_ofWord]; omega

/-- The bytes of the `string` at slot `p` of a storage `sload`, or `none` if its getter
panics (inconsistent slot word). -/
def decode (crypto : Crypto) (sload : Word → Word) (p : Word) : Option ByteArray :=
  let S := sload p
  if slotOk S then
    if S.toNat % 2 = 0 then some ((ofWord S).extract 0 (slotLen S))
    else some (longData sload (arrayDataSlot crypto p) (slotLen S))
  else none

/-! ## Encoding -/

/-- The slot word of a short string `s` (`s.size ≤ 31`): the data in the high bytes, zeros,
and `2 · length` in the lowest byte. -/
def shortWord (s : ByteArray) : Word :=
  toWord (s ++ zeros (31 - s.size) ++ ⟨#[(2 * s.size).toUInt8]⟩)

/-- Word `j` of the data of a long string: bytes `32 j … 32 j + 31`, zero-padded. -/
def chunk (s : ByteArray) (j : Nat) : Word := toWord (readPadded s (32 * j) 32)

/-- `sload` holds the long string `s` (32 bytes or more) at slot `p`: `2 · length + 1` in
the slot and the data words at `keccak256(p) + j`. -/
structure StoresLong (crypto : Crypto) (sload : Word → Word) (p : Word) (s : ByteArray) :
    Prop where
  /-- At least 32 bytes. -/
  long : 32 ≤ s.size
  /-- The length fits the slot word. -/
  fits : 2 * s.size + 1 < 2 ^ 256
  /-- The slot word. -/
  head : sload p = BitVec.ofNat 256 (2 * s.size + 1)
  /-- The data words. -/
  data : ∀ j < (s.size + 31) / 32,
    sload (arrayDataSlot crypto p + BitVec.ofNat 256 j) = chunk s j

/-- Gas that suffices for a call of the compiled getter of a `string` whose slot encodes
length `L` (solc 0.8.28, Solmate `ERC20`): the dispatcher and two `SLOAD`s of the slot, one
cold `SLOAD` (2100) and the loop overhead per data word, and the memory of the copy and of the
return buffer (`256 + 64 ⌈L / 32⌉` bytes). -/
def getterGas (L : Nat) : Nat :=
  8000 + 2400 * ((L + 31) / 32) + Gas.memoryCost (256 + 64 * ((L + 31) / 32))

end Str

/-- The `string` (as bytes) that the getter of a `string` state variable at slot `p` of
account `a` returns in world `w`, or `none` if the getter panics. -/
def stringAt (crypto : Crypto) (w : World) (a : Address) (p : Word) : Option ByteArray :=
  Str.decode crypto (w.sload a) p

namespace Abi

/-- The ABI encoding of one `string`/`bytes` return value: offset `0x20`, the length, and the
data zero-padded to a multiple of 32 bytes. -/
def encodeString (s : ByteArray) : ByteArray :=
  ofWord 32#256 ++ ofWord (BitVec.ofNat 256 s.size) ++ s ++
    zeros ((s.size + 31) / 32 * 32 - s.size)

/-- The size of `encodeString s`: two words and the padded data. -/
theorem size_encodeString (s : ByteArray) :
    (encodeString s).size = 64 + (s.size + 31) / 32 * 32 := by
  simp only [encodeString, ByteArray.size_append, size_ofWord, size_zeros]
  omega

/-- The encoding of the empty string: the offset and a zero length. -/
theorem encodeString_of_size_zero {s : ByteArray} (h : s.size = 0) :
    encodeString s = ofWord 32#256 ++ ofWord 0#256 := by
  have hs : s = ByteArray.empty := ByteArray.ext (Array.eq_empty_of_size_eq_zero h)
  subst hs
  simp only [encodeString, ByteArray.size_empty, ByteArray.append_empty]
  rfl

end Abi

end EvmLean.Solidity

end

section

/-!
## Words of `extract_byte_array_length` and of the string copy

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

end

section

/-!
## Storage encoding of strings decodes back

The two storage forms of a `string` (`EvmLeanProofs.Solidity.Strings`) decode to the stored
string:

* `Str.decode_shortWord`: a string of at most 31 bytes stored as `Str.shortWord s` (the form
  Solidity writes: data left-aligned, `2 · length` in the low byte);
* `Str.decode_of_storesLong`: a string of at least 32 bytes stored as `Str.StoresLong`
  describes (`2 · length + 1` in the slot, the zero-padded 32-byte chunks at
  `keccak256(slot) + j`).

Both hold for every `Crypto` and need no hypothesis on Keccak.

The byte-level facts behind them: `Bytes.toNat_div_mod` (byte `j` of a big-endian number) and
`Bytes.ofWord_toWord` (a 32-byte array is the encoding of its word).
-/

namespace EvmLean.Bytes

/-- A one-byte array has the byte's value. -/
theorem toNat_single (c : UInt8) : toNat ⟨#[c]⟩ = c.toNat := by
  rw [toNat_eq_foldl]; simp

/-- Splitting a byte array at `k`. -/
theorem extract_append_extract' (b : ByteArray) {k : Nat} (hk : k ≤ b.size) :
    b.extract 0 k ++ b.extract k b.size = b := by
  apply ext_getD (by simp only [ByteArray.size_append, ByteArray.size_extract]; omega)
  intro j hj
  simp only [ByteArray.size_append, ByteArray.size_extract] at hj
  rw [getD_append, ByteArray.size_extract, getD_extract, getD_extract]
  by_cases h : j < min k b.size - 0
  · simp only [h, ↓reduceIte, Nat.zero_add, show j < k by omega]
  · simp only [h, ↓reduceIte, show k + (j - (min k b.size - 0)) = j by omega,
      show j < b.size by omega]

/-- The first `j + 1` bytes are the first `j` and byte `j`. -/
theorem extract_succ (b : ByteArray) {j : Nat} (hj : j < b.size) :
    b.extract 0 (j + 1) = b.extract 0 j ++ ⟨#[getD b j]⟩ := by
  apply ext_getD (by
    rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      show ByteArray.size ⟨#[getD b j]⟩ = 1 from rfl]; omega)
  intro i hi
  simp only [ByteArray.size_extract] at hi
  rw [getD_append, ByteArray.size_extract, getD_extract, getD_extract]
  by_cases h : i < min j b.size - 0
  · simp only [h, ↓reduceIte, Nat.zero_add, show i < j + 1 by omega, show i < j by omega]
  · have hi' : i = j := by omega
    subst hi'
    simp only [h, ↓reduceIte, Nat.zero_add, show i < i + 1 by omega,
      show i - (min i b.size - 0) = 0 by omega]
    rfl

/-- Byte `j` of a big-endian number: `⌊toNat b / 256 ^ (size - 1 - j)⌋ mod 256`. -/
theorem toNat_div_mod (b : ByteArray) {j : Nat} (hj : j < b.size) :
    toNat b / 256 ^ (b.size - 1 - j) % 256 = (getD b j).toNat := by
  have hsplit := extract_append_extract' b (show j + 1 ≤ b.size by omega)
  have hB : (b.extract (j + 1) b.size).size = b.size - 1 - j := by
    rw [ByteArray.size_extract]; omega
  have hlt := toNat_lt (b.extract (j + 1) b.size)
  rw [hB] at hlt
  have e1 : toNat b = toNat (b.extract 0 (j + 1)) * 256 ^ (b.size - 1 - j) +
      toNat (b.extract (j + 1) b.size) := by
    conv => lhs; rw [← hsplit]
    rw [toNat_append, hB]
  have e2 : toNat (b.extract 0 (j + 1)) = toNat (b.extract 0 j) * 256 + (getD b j).toNat := by
    rw [extract_succ b hj, toNat_append, toNat_single]; rfl
  have hpos : 0 < 256 ^ (b.size - 1 - j) := Nat.pow_pos (by decide)
  rw [e1, e2, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]
  have := (getD b j).toNat_lt
  omega

/-- A 32-byte array is the encoding of its word. -/
theorem ofWord_toWord {b : ByteArray} (h : b.size = 32) : ofWord (toWord b) = b := by
  apply ext_getD (by rw [size_ofWord, h])
  intro j hj
  rw [size_ofWord] at hj
  rw [Solidity.getD_ofWord _ _ hj]
  apply UInt8.toNat_inj.mp
  have hlt := toNat_lt b
  rw [h] at hlt
  rw [Nat.toUInt8_eq, UInt8.toNat_ofNat', toWord, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := toNat b) (b := 2 ^ 256) (by simpa using hlt), Nat.shiftRight_eq_div_pow,
    show 2 ^ (8 * (31 - j)) = 256 ^ (b.size - 1 - j) by rw [h, Nat.pow_mul]]
  exact toNat_div_mod b (by omega)

end EvmLean.Bytes

namespace EvmLean.Solidity.Str

open Bytes

/-- The value of `shortWord s`: the bytes of `s` and the padding, shifted by one byte, plus
`2 · length`. -/
theorem toNat_shortWord {s : ByteArray} (hs : s.size ≤ 31) :
    (shortWord s).toNat = toNat (s ++ zeros (31 - s.size)) * 256 + 2 * s.size := by
  obtain ⟨B, hB⟩ : ∃ B, B = s ++ zeros (31 - s.size) ++ ⟨#[(2 * s.size).toUInt8]⟩ := ⟨_, rfl⟩
  have hBs : B.size = 32 := by
    rw [hB, ByteArray.size_append, ByteArray.size_append, size_zeros,
      show ByteArray.size ⟨#[(2 * s.size).toUInt8]⟩ = 1 from rfl]; omega
  have hlt := toNat_lt B
  rw [hBs] at hlt
  rw [shortWord, toWord, BitVec.toNat_ofNat, ← hB,
    Nat.mod_eq_of_lt (a := toNat B) (b := 2 ^ 256) (by simpa using hlt), hB,
    toNat_append, toNat_single]
  simp only [show ByteArray.size ⟨#[(2 * s.size).toUInt8]⟩ = 1 from rfl, Nat.pow_one,
    Nat.toUInt8_eq, UInt8.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega)]

/-- `shortWord s` is a short (even) slot word. -/
theorem shortWord_even {s : ByteArray} (hs : s.size ≤ 31) : (shortWord s).toNat % 2 = 0 := by
  rw [toNat_shortWord hs]; omega

/-- The length `shortWord s` encodes is the length of `s`. -/
theorem slotLen_shortWord {s : ByteArray} (hs : s.size ≤ 31) : slotLen (shortWord s) = s.size := by
  rw [slotLen, ite_eq_left (shortWord_even hs), toNat_shortWord hs]; omega

/-- **A short string stored as `shortWord s` decodes to `s`.** -/
theorem decode_shortWord (crypto : Crypto) {sload : Word → Word} {p : Word} {s : ByteArray}
    (hs : s.size ≤ 31) (h : sload p = shortWord s) : decode crypto sload p = some s := by
  obtain ⟨B, hB⟩ : ∃ B, B = s ++ zeros (31 - s.size) ++ ⟨#[(2 * s.size).toUInt8]⟩ := ⟨_, rfl⟩
  have hBs : B.size = 32 := by
    rw [hB, ByteArray.size_append, ByteArray.size_append, size_zeros,
      show ByteArray.size ⟨#[(2 * s.size).toUInt8]⟩ = 1 from rfl]; omega
  simp only [decode, h, slotOk, shortWord_even hs, ↓reduceIte, slotLen_shortWord hs,
    show s.size < 32 by omega, decide_true]
  rw [shortWord, ← hB, ofWord_toWord hBs]
  congr 1
  apply ext_getD (by simp only [ByteArray.size_extract, hBs]; omega)
  intro j hj
  simp only [ByteArray.size_extract, hBs] at hj
  rw [getD_extract, ite_eq_left (by omega), Nat.zero_add, hB, getD_append, getD_append,
    ite_eq_left (by rw [ByteArray.size_append]; omega), ite_eq_left (by omega)]

/-- `k` stored chunks of `s` are the first `32 k` bytes of `s`, zero-padded. -/
theorem wordsFrom_chunks {sload : Word → Word} {d : Word} {s : ByteArray} :
    ∀ k, (∀ j < k, sload (d + BitVec.ofNat 256 j) = chunk s j) →
      wordsFrom sload d k = readPadded s 0 (32 * k)
  | 0, _ => by
    simp only [wordsFrom, List.range_zero, List.foldl_nil, Nat.mul_zero]
    apply ext_getD (by simp [size_readPadded]); intro j hj; simp at hj
  | k + 1, h => by
    rw [wordsFrom_succ, wordsFrom_chunks k (fun j hj => h j (by omega)), h k (by omega), chunk,
      ofWord_toWord (size_readPadded _ _ _), show 32 * (k + 1) = 32 * k + 32 by omega,
      Solidity.readPadded_add, Nat.zero_add]

/-- **A long string stored as `StoresLong` describes decodes to it.** -/
theorem decode_of_storesLong {crypto : Crypto} {sload : Word → Word} {p : Word} {s : ByteArray}
    (h : StoresLong crypto sload p s) : decode crypto sload p = some s := by
  obtain ⟨hlong, hfits, hhead, hdata⟩ := h
  have hval : (BitVec.ofNat 256 (2 * s.size + 1)).toNat = 2 * s.size + 1 :=
    Nat.mod_eq_of_lt hfits
  have hodd : (BitVec.ofNat 256 (2 * s.size + 1)).toNat % 2 = 1 := by rw [hval]; omega
  have hlen : slotLen (BitVec.ofNat 256 (2 * s.size + 1)) = s.size := by
    rw [slotLen, ite_eq_right (by omega), hval]; omega
  simp only [decode, hhead, slotOk, hodd, hlen, Nat.one_ne_zero, ↓reduceIte, hlong, decide_true]
  congr 1
  rw [longData, wordsFrom_chunks _ hdata]
  apply ext_getD (by simp only [ByteArray.size_extract, size_readPadded]; omega)
  intro j hj
  simp only [ByteArray.size_extract, size_readPadded] at hj
  rw [getD_extract, ite_eq_left (by omega), getD_readPadded, ite_eq_left (by omega), Nat.zero_add,
    Nat.zero_add]

end EvmLean.Solidity.Str

end
