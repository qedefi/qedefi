import EvmLeanProofs.Solidity.Abi
import EvmLeanProofs.Solidity.Layout
import EvmLeanProofs.Solidity.ExtraWord

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

/-- The data of a long string of `len` bytes whose first data slot is `d`: the words at
`d, d + 1, …` (`⌈len / 32⌉` of them), concatenated and cut to `len` bytes. -/
def longData (sload : Word → Word) (d : Word) (len : Nat) : ByteArray :=
  ((List.range ((len + 31) / 32)).foldl
    (fun acc j => acc ++ ofWord (sload (d + BitVec.ofNat 256 j))) ByteArray.empty).extract 0 len

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
