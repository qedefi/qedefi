import EvmLean

/-!
# Byte-level lemmas

Big-endian decoding (`Bytes.toNat_eq_foldl`, `toWord_ofWord`), `MSTORE`/`MLOAD` read-over-write
and calldata slicing, for all inputs. Everything is reduced to `Bytes.getD` (zero past the end)
plus a size equation and closed by `Bytes.ext_getD`, avoiding dependent array indices.
`bv_decide` is not used: it adds an axiom.
-/

namespace EvmLean.Bytes

/-! ## `ByteArray.foldl` as a list fold -/

private theorem foldlM_loop_eq {β : Type _} (f : β → UInt8 → β) (as : ByteArray)
    (h : as.size ≤ as.size) :
    ∀ (i j : Nat) (acc : β),
      ByteArray.foldlM.loop (m := Id) (fun b a => pure (f b a)) as as.size h i j acc =
        ((as.data.toList.drop j).take i).foldl f acc := by
  intro i
  induction i with
  | zero =>
    intro j acc
    unfold ByteArray.foldlM.loop
    split <;> rfl
  | succ i ih =>
    intro j acc
    unfold ByteArray.foldlM.loop
    split
    · rename_i hj
      have hj' : j < as.data.toList.length := by simpa using hj
      rw [List.drop_eq_getElem_cons hj', List.take_succ_cons, List.foldl_cons, ← ih]
      simp only [Array.getElem_toList, ByteArray.getElem_eq_getElem_data]
      rfl
    · rename_i hj
      have hj' : as.data.toList.length ≤ j := by simpa using hj
      rw [List.drop_eq_nil_of_le hj']
      rfl

theorem foldl_eq_foldl_data_toList {β : Type _} (f : β → UInt8 → β) (init : β)
    (as : ByteArray) : as.foldl f init = as.data.toList.foldl f init := by
  unfold ByteArray.foldl ByteArray.foldlM
  simp only [Nat.le_refl, ↓reduceDIte, Nat.sub_zero]
  rw [foldlM_loop_eq]
  have hs : as.size = as.data.toList.length := by simp
  rw [List.drop_zero, hs, List.take_length]
  rfl

/-! ## `chunk64` is the big-endian value of eight bytes -/

private theorem shiftLeft_eight_or (a : Nat) (x : UInt8) :
    a <<< 8 ||| x.toNat = a * 256 + x.toNat := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt (UInt8.toNat_lt x), Nat.shiftLeft_eq]

private theorem shiftLeft_or_shiftLeft (a b k : Nat) :
    a <<< (k + 8) ||| b <<< k = (a <<< 8 ||| b) <<< k := by
  rw [Nat.shiftLeft_or_distrib, Nat.add_comm k 8, Nat.shiftLeft_add]

private theorem toNat_shiftLeft_lt (x : UInt8) (k : Nat) (hk : k ≤ 56) :
    x.toNat <<< k < 2 ^ 64 := by
  rw [Nat.shiftLeft_eq]
  have h1 := UInt8.toNat_lt x
  have h2 : 2 ^ k ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) hk
  have h3 : x.toNat * 2 ^ k < 2 ^ 8 * 2 ^ 56 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos k))
      (Nat.mul_le_mul_left _ h2)
  simpa using h3

private theorem toNat_or_shiftLeft (x0 x1 x2 x3 x4 x5 x6 x7 : UInt8) :
    (x0.toUInt64 <<< 56 ||| x1.toUInt64 <<< 48 ||| x2.toUInt64 <<< 40 |||
      x3.toUInt64 <<< 32 ||| x4.toUInt64 <<< 24 ||| x5.toUInt64 <<< 16 |||
      x6.toUInt64 <<< 8 ||| x7.toUInt64).toNat =
    [x0, x1, x2, x3, x4, x5, x6, x7].foldl (fun acc x => acc * 256 + x.toNat) 0 := by
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64,
    UInt64.reduceToNat, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (toNat_shiftLeft_lt x0 56 (by decide)),
    Nat.mod_eq_of_lt (toNat_shiftLeft_lt x1 48 (by decide)),
    Nat.mod_eq_of_lt (toNat_shiftLeft_lt x2 40 (by decide)),
    Nat.mod_eq_of_lt (toNat_shiftLeft_lt x3 32 (by decide)),
    Nat.mod_eq_of_lt (toNat_shiftLeft_lt x4 24 (by decide)),
    Nat.mod_eq_of_lt (toNat_shiftLeft_lt x5 16 (by decide)),
    Nat.mod_eq_of_lt (toNat_shiftLeft_lt x6 8 (by decide))]
  rw [shiftLeft_or_shiftLeft _ _ 48, shiftLeft_or_shiftLeft _ _ 40,
    shiftLeft_or_shiftLeft _ _ 32, shiftLeft_or_shiftLeft _ _ 24,
    shiftLeft_or_shiftLeft _ _ 16, shiftLeft_or_shiftLeft _ _ 8]
  simp only [shiftLeft_eight_or, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add]

theorem toNat_chunk64 (b : ByteArray) (i : Nat) :
    (chunk64 b i).toNat =
      [getD b i, getD b (i + 1), getD b (i + 2), getD b (i + 3), getD b (i + 4),
        getD b (i + 5), getD b (i + 6), getD b (i + 7)].foldl
        (fun acc x => acc * 256 + x.toNat) 0 :=
  toNat_or_shiftLeft _ _ _ _ _ _ _ _

/-! ## `toNat` is the big-endian fold -/

private theorem foldl_take_add_one (b : ByteArray) (i : Nat) (h : i < b.size) (a : Nat) :
    (b.data.toList.take (i + 1)).foldl (fun acc x => acc * 256 + x.toNat) a =
      (b.data.toList.take i).foldl (fun acc x => acc * 256 + x.toNat) a * 256 +
        (getD b i).toNat := by
  have h' : i < b.data.toList.length := by simpa using h
  rw [List.take_add_one, List.getElem?_eq_getElem h', List.foldl_append]
  simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, getD, h, ↓reduceDIte,
    Array.getElem_toList, ByteArray.getElem_eq_getElem_data]

private theorem foldl_take_add_eight (b : ByteArray) (i : Nat) (h : i + 8 ≤ b.size) :
    (b.data.toList.take (i + 8)).foldl (fun acc x => acc * 256 + x.toNat) 0 =
      ((b.data.toList.take i).foldl (fun acc x => acc * 256 + x.toNat) 0 <<< 64) |||
        (chunk64 b i).toNat := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt (UInt64.toNat_lt _), Nat.shiftLeft_eq, toNat_chunk64]
  rw [show i + 8 = i + 7 + 1 from rfl, foldl_take_add_one _ _ (by omega),
    foldl_take_add_one _ (i + 6) (by omega), foldl_take_add_one _ (i + 5) (by omega),
    foldl_take_add_one _ (i + 4) (by omega), foldl_take_add_one _ (i + 3) (by omega),
    foldl_take_add_one _ (i + 2) (by omega), foldl_take_add_one _ (i + 1) (by omega),
    foldl_take_add_one _ i (by omega)]
  simp only [List.foldl_cons, List.foldl_nil, Nat.reducePow]
  omega

private theorem toNatChunks_foldl_take (b : ByteArray) :
    ∀ (k i : Nat), i + 8 * k ≤ b.size →
      toNatChunks b ((b.data.toList.take i).foldl (fun acc x => acc * 256 + x.toNat) 0) i k =
        (b.data.toList.take (i + 8 * k)).foldl (fun acc x => acc * 256 + x.toNat) 0 := by
  intro k
  induction k with
  | zero => intro i _; rfl
  | succ k ih =>
    intro i h
    rw [toNatChunks, ← foldl_take_add_eight b i (by omega), ih (i + 8) (by omega)]
    congr 2
    omega

/-- The chunked `toNat` is the big-endian value of the bytes, as its docstring claims. -/
theorem toNat_eq_foldl (b : ByteArray) :
    Bytes.toNat b = b.data.foldl (fun acc x => acc * 256 + x.toNat) 0 := by
  rw [toNat, foldl_eq_foldl_data_toList, ByteArray.data_extract, Array.toList_extract,
    List.extract, List.drop_zero, Nat.sub_zero, toNatChunks_foldl_take b _ _ (by omega),
    ← Array.foldl_toList]
  have hs : b.size % 8 + 8 * (b.size / 8) = b.data.toList.length := by simp; omega
  rw [hs, List.take_length]

/-! ## Encoding then decoding -/

private theorem foldl_ofFn_shiftRight (len n : Nat) :
    (List.ofFn (n := len) fun i => (n >>> (8 * (len - 1 - i.val))).toUInt8).foldl
      (fun acc x => acc * 256 + x.toNat) 0 = n % 2 ^ (8 * len) := by
  induction len generalizing n with
  | zero =>
    simp only [List.ofFn_zero, List.foldl_nil, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | succ len ih =>
    rw [List.ofFn_succ_last, List.foldl_append]
    have hpre :
        (fun i : Fin len => (n >>> (8 * (len + 1 - 1 - (Fin.castSucc i).val))).toUInt8) =
          fun i : Fin len => ((n >>> 8) >>> (8 * (len - 1 - i.val))).toUInt8 := by
      funext i
      rw [← Nat.shiftRight_add]
      congr 2
      have := i.isLt
      simp only [Fin.val_castSucc]
      omega
    rw [hpre, ih]
    simp only [Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, Nat.mul_zero, List.foldl_cons,
      List.foldl_nil, Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
    rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm (2 ^ (8 * len)), Nat.mod_mul]
    simp only [Nat.mul_one, Nat.reducePow]
    omega

/-- Decoding `len` big-endian bytes of `n` gives `n` modulo `2^(8 * len)`. -/
theorem toNat_ofNatBE (len n : Nat) :
    Bytes.toNat (Bytes.ofNatBE len n) = n % 2 ^ (8 * len) := by
  rw [toNat_eq_foldl, ← Array.foldl_toList]
  simp only [ofNatBE, Array.toList_ofFn]
  exact foldl_ofFn_shiftRight len n

theorem size_ofNatBE (len n : Nat) : (ofNatBE len n).size = len := by
  simp only [ofNatBE, ByteArray.size, Array.size_ofFn]

theorem size_ofWord (w : Word) : (ofWord w).size = 32 := size_ofNatBE 32 w.toNat

theorem size_ofAddress (a : Address) : (ofAddress a).size = 20 := size_ofNatBE 20 a.toNat

theorem toNat_ofWord (w : Word) : toNat (ofWord w) = w.toNat := by
  rw [ofWord, toNat_ofNatBE]
  exact Nat.mod_eq_of_lt w.isLt

theorem toWord_ofWord (w : Word) : toWord (ofWord w) = w := by
  apply BitVec.eq_of_toNat_eq
  rw [toWord, toNat_ofWord, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt w.isLt

theorem toNat_ofAddress (a : Address) : toNat (ofAddress a) = a.toNat := by
  rw [ofAddress, toNat_ofNatBE]
  exact Nat.mod_eq_of_lt a.isLt

theorem toWord_ofAddress (a : Address) : toWord (ofAddress a) = Word.ofAddress a := by
  apply BitVec.eq_of_toNat_eq
  rw [toWord, toNat_ofAddress, BitVec.toNat_ofNat, Word.ofAddress, BitVec.toNat_setWidth]

/-! ## Byte access via `getD` -/

theorem size_zeros (n : Nat) : (zeros n).size = n := by
  simp only [zeros, ByteArray.size, Array.size_replicate]

theorem getD_zeros (n j : Nat) : getD (zeros n) j = 0 := by
  unfold getD
  split
  · simp only [zeros, ByteArray.getElem_eq_getElem_data, Array.getElem_replicate]
  · rfl

theorem getD_of_size_le {b : ByteArray} {j : Nat} (h : b.size ≤ j) : getD b j = 0 := by
  simp only [getD, Nat.not_lt.mpr h, ↓reduceDIte]

theorem getD_append (x y : ByteArray) (j : Nat) :
    getD (x ++ y) j = if j < x.size then getD x j else getD y (j - x.size) := by
  split
  · rename_i h
    simp only [getD, ByteArray.size_append, h, ↓reduceDIte, Nat.lt_add_right,
      ByteArray.getElem_append_left h]
  · rename_i h
    unfold getD
    by_cases h' : j < (x ++ y).size
    · have h'' : j - x.size < y.size := by rw [ByteArray.size_append] at h'; omega
      simp only [h', h'', ↓reduceDIte, ByteArray.getElem_append_right (Nat.not_lt.mp h)]
    · have h'' : ¬ j - x.size < y.size := by rw [ByteArray.size_append] at h'; omega
      simp only [h', h'', ↓reduceDIte]

theorem getD_extract (b : ByteArray) (s e j : Nat) :
    getD (b.extract s e) j = if s + j < e then getD b (s + j) else 0 := by
  unfold getD
  by_cases h : j < (b.extract s e).size
  · have h1 : s + j < e := by rw [ByteArray.size_extract] at h; omega
    have h2 : s + j < b.size := by rw [ByteArray.size_extract] at h; omega
    simp only [h, h1, h2, ↓reduceDIte, ↓reduceIte, ByteArray.getElem_extract]
  · simp only [h, ↓reduceDIte]
    split
    · have h2 : ¬ s + j < b.size := by rw [ByteArray.size_extract] at h; omega
      simp only [h2, ↓reduceDIte]
    · rfl

/-- Byte arrays of equal size with equal bytes are equal. -/
theorem ext_getD {a b : ByteArray} (h : a.size = b.size)
    (h' : ∀ j, j < a.size → getD a j = getD b j) : a = b := by
  apply ByteArray.ext_getElem h
  intro j hj hj'
  have := h' j hj
  simp only [getD, hj, hj', ↓reduceDIte] at this
  exact this

/-! ## `readPadded` and `write` -/

theorem size_readPadded (b : ByteArray) (off len : Nat) :
    (readPadded b off len).size = len := by
  unfold readPadded
  split
  · simp only [ByteArray.size_append, size_zeros, ByteArray.size_extract]
    omega
  · exact size_zeros len

theorem getD_readPadded (b : ByteArray) (off len j : Nat) :
    getD (readPadded b off len) j = if j < len then getD b (off + j) else 0 := by
  unfold readPadded
  split
  · simp only [getD_append, getD_extract, getD_zeros, ByteArray.size_extract]
    by_cases h1 : j < min (min (off + len) b.size) b.size - off
    · have h2 : off + j < min (off + len) b.size := by omega
      have h3 : j < len := by omega
      simp only [h1, h2, h3, ↓reduceIte]
    · simp only [h1, ↓reduceIte]
      by_cases h3 : j < len
      · simp only [h3, ↓reduceIte]
        exact (getD_of_size_le (by omega)).symm
      · simp only [h3, ↓reduceIte]
  · rw [getD_zeros]
    split
    · exact (getD_of_size_le (by omega)).symm
    · rfl

theorem size_write {dst src : ByteArray} {off : Nat}
    (h : off + src.size ≤ dst.size ∨ src.size = 0) :
    (write dst off src).size = dst.size := by
  simp only [write, ByteArray.copySlice_eq_append, ByteArray.size_append,
    ByteArray.size_extract]
  simp only [ByteArray.size] at *
  omega

/-- Byte `j` after a `write` that starts in bounds (or is empty): from `src` inside
`[off, off + src.size)`, from `dst` elsewhere. -/
theorem getD_write {dst src : ByteArray} {off : Nat} (h : off ≤ dst.size ∨ src.size = 0)
    (j : Nat) :
    getD (write dst off src) j =
      if off ≤ j ∧ j < off + src.size then getD src (j - off) else getD dst j := by
  have hs : ∀ a : ByteArray, a.data.size = a.size := fun _ => rfl
  simp only [write, ByteArray.copySlice_eq_append, hs, getD_append, getD_extract,
    ByteArray.size_append, ByteArray.size_extract, Nat.zero_add, Nat.sub_zero,
    Nat.min_eq_left (Nat.le_refl _)]
  repeat' split
  all_goals first
    | rfl
    | (exfalso; omega)
    | (congr 1; omega)
    | exact (getD_of_size_le (by omega)).symm
    | exact getD_of_size_le (by omega)

theorem readPadded_append_left (x y : ByteArray) : readPadded (x ++ y) 0 x.size = x := by
  apply ext_getD (size_readPadded _ _ _)
  intro j hj
  rw [size_readPadded] at hj
  simp only [getD_readPadded, hj, ↓reduceIte, Nat.zero_add, getD_append]

theorem readPadded_append_right (x y : ByteArray) :
    readPadded (x ++ y) x.size y.size = y := by
  apply ext_getD (size_readPadded _ _ _)
  intro j hj
  rw [size_readPadded] at hj
  have h : ¬ x.size + j < x.size := by omega
  simp only [getD_readPadded, hj, ↓reduceIte, getD_append, h, Nat.add_sub_cancel_left]

theorem readPadded_zero_size (x : ByteArray) : readPadded x 0 x.size = x := by
  have h := readPadded_append_left x ByteArray.empty
  rwa [ByteArray.append_empty] at h

end EvmLean.Bytes

namespace EvmLean.Memory

open EvmLean.Bytes

theorem size_expand (m : Memory) (off len : Nat) :
    (m.expand off len).size = max m.size (32 * wordsAfter m.words off len) := by
  simp only [expand]
  split
  · omega
  · simp only [size, ByteArray.size_append, size_zeros]
    omega

theorem getD_bytes_expand (m : Memory) (off len j : Nat) :
    getD (m.expand off len).bytes j = getD m.bytes j := by
  simp only [expand]
  split
  · rfl
  · rw [getD_append]
    split
    · rfl
    · rw [getD_zeros]
      exact (getD_of_size_le (by omega)).symm

theorem add_le_size_expand (m : Memory) (off len : Nat) (h : len ≠ 0) :
    off + len ≤ (m.expand off len).size := by
  rw [size_expand, wordsAfter, ite_eq_right h]
  omega

private theorem add_le_size_expand_or (m : Memory) (off len : Nat) :
    off + len ≤ (m.expand off len).size ∨ len = 0 := by
  by_cases h : len = 0
  · exact Or.inr h
  · exact Or.inl (add_le_size_expand m off len h)

theorem size_write (m : Memory) (off : Nat) (data : ByteArray) :
    (m.write off data).size = (m.expand off data.size).size :=
  Bytes.size_write (add_le_size_expand_or m off data.size)

/-- Byte `j` after `write`: from `data` inside `[off, off + data.size)`, unchanged
elsewhere (bytes added by expansion read as zero, as before). -/
theorem getD_bytes_write (m : Memory) (off : Nat) (data : ByteArray) (j : Nat) :
    getD (m.write off data).bytes j =
      if off ≤ j ∧ j < off + data.size then getD data (j - off) else getD m.bytes j := by
  simp only [write]
  have h : off ≤ (m.expand off data.size).bytes.size ∨ data.size = 0 := by
    have := add_le_size_expand_or m off data.size
    simp only [size] at this
    omega
  rw [Bytes.getD_write h, getD_bytes_expand]

theorem read_write (m : Memory) (off : Nat) (data : ByteArray) :
    (m.write off data).read off data.size = data := by
  apply ext_getD (by rw [read, size_readPadded])
  intro j hj
  rw [read, size_readPadded] at hj
  have h : off ≤ off + j ∧ off + j < off + data.size := by omega
  simp only [read, getD_readPadded, hj, ↓reduceIte, getD_bytes_write, h, and_self,
    Nat.add_sub_cancel_left]

theorem read_write_of_disjoint (m : Memory) (off off' len : Nat) (data : ByteArray)
    (h : off' + len ≤ off ∨ off + data.size ≤ off') :
    (m.write off data).read off' len = m.read off' len := by
  apply ext_getD (by rw [read, read, size_readPadded, size_readPadded])
  intro j hj
  rw [read, size_readPadded] at hj
  have h' : ¬ (off ≤ off' + j ∧ off' + j < off + data.size) := by omega
  simp only [read, getD_readPadded, hj, ↓reduceIte, getD_bytes_write, h']

theorem size_storeWord (m : Memory) (off : Nat) (w : Word) :
    (m.storeWord off w).size = max m.size (32 * ((off + 32 + 31) / 32)) := by
  rw [storeWord, size_write, size_expand, size_ofWord, wordsAfter, ite_eq_right (by decide), words]
  omega

theorem read_storeWord (m : Memory) (off : Nat) (w : Word) :
    (m.storeWord off w).read off 32 = ofWord w := by
  have h := read_write m off (ofWord w)
  rwa [size_ofWord] at h

theorem loadWord_storeWord (m : Memory) (off : Nat) (w : Word) :
    (m.storeWord off w).loadWord off = w := by
  rw [loadWord, read_storeWord, toWord_ofWord]

theorem read_storeWord_of_disjoint (m : Memory) (off off' len : Nat) (w : Word)
    (h : off' + len ≤ off ∨ off + 32 ≤ off') :
    (m.storeWord off w).read off' len = m.read off' len :=
  read_write_of_disjoint m off off' len (ofWord w) (by rw [size_ofWord]; exact h)

theorem loadWord_storeWord_of_disjoint (m : Memory) (off off' : Nat) (w : Word)
    (h : off' + 32 ≤ off ∨ off + 32 ≤ off') :
    (m.storeWord off w).loadWord off' = m.loadWord off' := by
  rw [loadWord, loadWord, read_storeWord_of_disjoint m off off' 32 w h]

end EvmLean.Memory

namespace EvmLean.Interpreter

open EvmLean.Bytes

theorem readBytes_eq_readPadded (b : ByteArray) (off len : Nat) :
    readBytes b off len = readPadded b off len := by
  unfold readBytes readPadded
  split
  · rw [ite_eq_right (by omega)]
  · rfl

theorem readBytes_append_left (x y : ByteArray) : readBytes (x ++ y) 0 x.size = x := by
  rw [readBytes_eq_readPadded, readPadded_append_left]

theorem readBytes_append_right (x y : ByteArray) :
    readBytes (x ++ y) x.size y.size = y := by
  rw [readBytes_eq_readPadded, readPadded_append_right]

theorem readBytes_zero_size (x : ByteArray) : readBytes x 0 x.size = x := by
  rw [readBytes_eq_readPadded, readPadded_zero_size]

theorem readBytes_ofWord_append_left (a b : Word) :
    readBytes (ofWord a ++ ofWord b) 0 32 = ofWord a := by
  have h := readBytes_append_left (ofWord a) (ofWord b)
  rwa [size_ofWord] at h

theorem readBytes_ofWord_append_right (a b : Word) :
    readBytes (ofWord a ++ ofWord b) 32 32 = ofWord b := by
  have h := readBytes_append_right (ofWord a) (ofWord b)
  rwa [size_ofWord, size_ofWord] at h

theorem toWord_readBytes_ofWord_append_left (a b : Word) :
    toWord (readBytes (ofWord a ++ ofWord b) 0 32) = a := by
  rw [readBytes_ofWord_append_left, toWord_ofWord]

theorem toWord_readBytes_ofWord_append_right (a b : Word) :
    toWord (readBytes (ofWord a ++ ofWord b) 32 32) = b := by
  rw [readBytes_ofWord_append_right, toWord_ofWord]

end EvmLean.Interpreter
