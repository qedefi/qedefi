import EvmLeanProofs.Solidity.Strings

/-!
# Storage encoding of strings decodes back

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
