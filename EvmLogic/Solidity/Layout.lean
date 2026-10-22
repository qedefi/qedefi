import EvmLogic.State
import EvmLogic.Bytes

/-!
# Solidity storage layout

Where solc 0.8 puts state variables: packed value types (`Field`, with `get`/`set` as solc's
mask-and-shift), mappings (`mappingSlot`: `keccak256(pad32(k) ‖ pad32(p))`, nested
`mappingSlot2`) and dynamic arrays (`arraySlot`). Slots use the context's `Crypto.keccak256`;
distinctness of slots is a hypothesis (`EvmLogic.Solidity.Keccak`). Field lemmas are proved
bitwise, without `bv_decide`.
-/

namespace EvmLogic.Solidity
open EvmLean EvmLean.Bytes

/-! ## Mappings and arrays -/

/-- The slot of `m[key]` for a mapping `m` at slot `base`, with a value-type key already
padded to a word: `keccak256(key ‖ base)`. -/
def mappingSlot (crypto : Crypto) (key base : Word) : Word :=
  crypto.keccak256 (ofWord key ++ ofWord base)

/-- The slot of `m[k₁][k₂]` for a nested mapping at slot `base`. -/
def mappingSlot2 (crypto : Crypto) (k₁ k₂ base : Word) : Word :=
  mappingSlot crypto k₂ (mappingSlot crypto k₁ base)

/-- The first data slot of a dynamic array (or long `bytes`/`string`) at slot `base`:
`keccak256(base)`. -/
def arrayDataSlot (crypto : Crypto) (base : Word) : Word := crypto.keccak256 (ofWord base)

/-- The slot of element `i` of a dynamic array of 32-byte elements at slot `base`. -/
def arraySlot (crypto : Crypto) (base i : Word) : Word := arrayDataSlot crypto base + i

/-! ## Packed value types -/

/-- A value-type state variable: `size` bytes at byte `offset` from the least significant end
of slot `slot` (as in `--storage-layout`). -/
structure Field where
  slot : Word
  offset : Nat
  size : Nat

namespace Field
open EvmLean

/-- A field is well formed if it fits in its slot. -/
def Valid (f : Field) : Prop := 0 < f.size ∧ f.offset + f.size ≤ 32

/-- Two fields of the same slot do not overlap. -/
def Disjoint (f g : Field) : Prop := f.offset + f.size ≤ g.offset ∨ g.offset + g.size ≤ f.offset

/-- The low `size` bytes set: the mask of the field's value. -/
def mask (f : Field) : Word := BitVec.allOnes 256 >>> (256 - 8 * f.size)

/-- The field's value within the slot word `v` (`(v >> 8·offset) & mask`). -/
def get (f : Field) (v : Word) : Word := (v >>> (8 * f.offset)) &&& f.mask

/-- The slot word `v` with the field replaced by `x` (truncated to the field's width), as
solc writes packed variables: `(v & ~(mask << 8·offset)) | ((x & mask) << 8·offset)`. -/
def set (f : Field) (v x : Word) : Word :=
  (v &&& ~~~(f.mask <<< (8 * f.offset))) ||| ((x &&& f.mask) <<< (8 * f.offset))

/-- Read the field from a storage. -/
def read (f : Field) (s : Storage) : Word := f.get (s.get f.slot)

/-- Write the field into a storage (read-modify-write of its slot). -/
def write (f : Field) (s : Storage) (x : Word) : Storage := s.set f.slot (f.set (s.get f.slot) x)

theorem getLsbD_mask (f : Field) (hf : f.Valid) (i : Nat) :
    f.mask.getLsbD i = decide (i < 8 * f.size) := by
  simp only [mask, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]
  have := hf.2
  by_cases h : i < 8 * f.size
  · simp [h]; omega
  · simp [h]; omega

theorem getLsbD_get (f : Field) (hf : f.Valid) (v : Word) (i : Nat) :
    (f.get v).getLsbD i = (decide (i < 8 * f.size) && v.getLsbD (8 * f.offset + i)) := by
  simp only [get, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, getLsbD_mask f hf]
  cases decide (i < 8 * f.size) <;> simp

theorem getLsbD_set (f : Field) (hf : f.Valid) (v x : Word) (i : Nat) (hi : i < 256) :
    (f.set v x).getLsbD i =
      if 8 * f.offset ≤ i ∧ i < 8 * (f.offset + f.size) then x.getLsbD (i - 8 * f.offset)
      else v.getLsbD i := by
  simp only [set, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, getLsbD_mask f hf, hi, decide_true, Bool.true_and]
  by_cases h1 : i < 8 * f.offset
  · have : ¬ (8 * f.offset ≤ i ∧ i < 8 * (f.offset + f.size)) := by omega
    simp [h1, this]
  · by_cases h2 : i < 8 * (f.offset + f.size)
    · have h3 : i - 8 * f.offset < 8 * f.size := by omega
      have : 8 * f.offset ≤ i ∧ i < 8 * (f.offset + f.size) := by omega
      simp [h1, h3, this]
    · have h3 : ¬ i - 8 * f.offset < 8 * f.size := by omega
      have : ¬ (8 * f.offset ≤ i ∧ i < 8 * (f.offset + f.size)) := by omega
      simp [h1, h3, this]

/-- **Read after write, same field**: the written value, truncated to the field's width. -/
theorem get_set_self (f : Field) (hf : f.Valid) (v x : Word) : f.get (f.set v x) = x &&& f.mask := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_get f hf, BitVec.getLsbD_and, getLsbD_mask f hf]
  by_cases h : i < 8 * f.size
  · have hf2 := hf.2
    rw [getLsbD_set f hf v x _ (by omega)]
    have : 8 * f.offset ≤ 8 * f.offset + i ∧ 8 * f.offset + i < 8 * (f.offset + f.size) := by
      omega
    simp [h, this]
  · simp [h]

/-- **Packed neighbours are not disturbed**: writing field `f` leaves a disjoint field `g`
of the same slot unchanged. -/
theorem get_set_of_disjoint (f g : Field) (hf : f.Valid) (hg : g.Valid) (hd : Disjoint f g)
    (v x : Word) : g.get (f.set v x) = g.get v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_get g hg, getLsbD_get g hg]
  by_cases h : i < 8 * g.size
  · have hg2 := hg.2
    rw [getLsbD_set f hf v x _ (by omega)]
    have : ¬ (8 * f.offset ≤ 8 * g.offset + i ∧ 8 * g.offset + i < 8 * (f.offset + f.size)) := by
      unfold Disjoint at hd; omega
    simp [this]
  · simp [h]

theorem get_and_mask (f : Field) (v : Word) : f.get v &&& f.mask = f.get v := by
  simp only [get, BitVec.and_assoc, BitVec.and_self]

theorem read_write_self (f : Field) (hf : f.Valid) (s : Storage) (x : Word) :
    f.read (f.write s x) = x &&& f.mask := by
  simp only [read, write, Storage.get_set_self, get_set_self f hf]

theorem read_write_of_disjoint (f g : Field) (hf : f.Valid) (hg : g.Valid) (hd : Disjoint f g)
    (hslot : g.slot = f.slot) (s : Storage) (x : Word) : g.read (f.write s x) = g.read s := by
  simp only [read, write, hslot, Storage.get_set_self, get_set_of_disjoint f g hf hg hd]

theorem read_write_of_slot_ne (f g : Field) (hslot : g.slot ≠ f.slot) (s : Storage) (x : Word) :
    g.read (f.write s x) = g.read s := by
  simp only [read, write, Storage.get_set_ne _ _ hslot]

theorem get_of_full (f : Field) (h0 : f.offset = 0) (h32 : f.size = 32) (v : Word) :
    f.get v = v := by
  simp only [get, mask, h0, h32, Nat.mul_zero, BitVec.ushiftRight_zero, Nat.reduceMul,
    Nat.sub_self, BitVec.and_allOnes]

end Field

/-! ## Bit fields

`Field` is byte-granular. Solidity packs narrower values too: `uint120`/`uint128` halves of a
word (Aave's `_userState`), bit ranges of a configuration word (Aave's `ReserveConfiguration`:
16-bit percentages, 36-bit caps, 1-bit flags), and bits at a **runtime index**
(`UserConfiguration`: two bits per reserve at `2 * reserveIndex`). A `BitField` is `width` bits
at bit `offset` of a word; neither needs to be a numeral, so a field at a symbolic index is just
a `BitField` with a symbolic offset. `get`/`set` are solc's shift-and-mask; the lemmas give the
value as a number (`toNat_get`), bit by bit (`getLsbD_get`, `getLsbD_set`), and the
read-after-write laws (`get_set_self`, `get_set_of_disjoint`), all proved bitwise. -/

/-- `width` bits at bit `offset` (from the least significant end) of a word. -/
structure BitField where
  offset : Nat
  width : Nat

namespace BitField
open EvmLean

/-- The field fits in a word. -/
def Valid (f : BitField) : Prop := f.offset + f.width ≤ 256

/-- Two fields do not overlap. -/
def Disjoint (f g : BitField) : Prop :=
  f.offset + f.width ≤ g.offset ∨ g.offset + g.width ≤ f.offset

instance (f : BitField) : Decidable f.Valid := inferInstanceAs (Decidable (_ ≤ _))

instance (f g : BitField) : Decidable (f.Disjoint g) := inferInstanceAs (Decidable (_ ∨ _))

/-- The low `width` bits set. -/
def mask (f : BitField) : Word := BitVec.ofNat 256 (2 ^ f.width - 1)

/-- The field's value in the word `v`: `(v >> offset) & mask`. -/
def get (f : BitField) (v : Word) : Word := (v >>> f.offset) &&& f.mask

/-- The word `v` with the field replaced by `x` (truncated to the width):
`(v & ~(mask << offset)) | ((x & mask) << offset)`. -/
def set (f : BitField) (v x : Word) : Word :=
  (v &&& ~~~(f.mask <<< f.offset)) ||| ((x &&& f.mask) <<< f.offset)

/-- The single bit `i` (a `bool` flag; `UserConfiguration`'s bits at a runtime index). -/
def bit (i : Nat) : BitField := ⟨i, 1⟩

theorem getLsbD_mask (f : BitField) (i : Nat) :
    f.mask.getLsbD i = (decide (i < 256) && decide (i < f.width)) := by
  simp only [mask, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]

theorem toNat_mask (f : BitField) (hw : f.width ≤ 256) : f.mask.toNat = 2 ^ f.width - 1 := by
  simp only [mask, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) hw
  have := Nat.one_le_two_pow (n := f.width)
  omega

/-- The field as a number: `⌊v / 2^offset⌋ mod 2^width`. -/
theorem toNat_get (f : BitField) (hf : f.width ≤ 256) (v : Word) :
    (f.get v).toNat = v.toNat / 2 ^ f.offset % 2 ^ f.width := by
  rw [get, BitVec.toNat_and, toNat_mask f hf, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem get_eq_ofNat (f : BitField) (hf : f.width ≤ 256) (v : Word) :
    f.get v = BitVec.ofNat 256 (v.toNat / 2 ^ f.offset % 2 ^ f.width) := by
  apply BitVec.eq_of_toNat_eq
  have h : v.toNat / 2 ^ f.offset % 2 ^ f.width < 2 ^ 256 :=
    calc v.toNat / 2 ^ f.offset % 2 ^ f.width ≤ v.toNat / 2 ^ f.offset := Nat.mod_le _ _
      _ ≤ v.toNat := Nat.div_le_self _ _
      _ < 2 ^ 256 := v.isLt
  rw [toNat_get f hf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem getLsbD_get (f : BitField) (v : Word) (i : Nat) :
    (f.get v).getLsbD i = (decide (i < f.width) && v.getLsbD (f.offset + i)) := by
  simp only [get, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, getLsbD_mask]
  by_cases h1 : i < 256
  · simp only [h1, decide_true, Bool.true_and]
    cases decide (i < f.width) <;> simp
  · simp only [h1, decide_false, Bool.false_and, Bool.and_false]
    by_cases h2 : i < f.width
    · simp only [h2, decide_true, Bool.true_and]
      exact (BitVec.getLsbD_of_ge v _ (by omega)).symm
    · simp [h2]

theorem getLsbD_set (f : BitField) (v x : Word) (i : Nat) (hi : i < 256) :
    (f.set v x).getLsbD i =
      if f.offset ≤ i ∧ i < f.offset + f.width then x.getLsbD (i - f.offset)
      else v.getLsbD i := by
  simp only [set, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, getLsbD_mask, hi, decide_true, Bool.true_and]
  by_cases h1 : i < f.offset
  · have : ¬ (f.offset ≤ i ∧ i < f.offset + f.width) := by omega
    simp [h1, this]
  · by_cases h2 : i < f.offset + f.width
    · have h3 : i - f.offset < f.width := by omega
      have h4 : i - f.offset < 256 := by omega
      have : f.offset ≤ i ∧ i < f.offset + f.width := by omega
      simp [h1, h3, h4, this]
    · have h3 : ¬ i - f.offset < f.width := by omega
      have : ¬ (f.offset ≤ i ∧ i < f.offset + f.width) := by omega
      simp [h1, h3, this]

/-- **Read after write, same field**: the written value, truncated to the width. -/
theorem get_set_self (f : BitField) (hf : f.Valid) (v x : Word) :
    f.get (f.set v x) = x &&& f.mask := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_get, BitVec.getLsbD_and, getLsbD_mask]
  by_cases h : i < f.width
  · have hf2 : f.offset + f.width ≤ 256 := hf
    rw [getLsbD_set f v x _ (by omega)]
    have : f.offset ≤ f.offset + i ∧ f.offset + i < f.offset + f.width := by omega
    simp [h, this, hi]
  · simp [h]

/-- The written value as a number: `x mod 2^width`. -/
theorem toNat_get_set_self (f : BitField) (hf : f.Valid) (v x : Word) :
    (f.get (f.set v x)).toNat = x.toNat % 2 ^ f.width := by
  have hw : f.width ≤ 256 := by have : f.offset + f.width ≤ 256 := hf; omega
  rw [get_set_self f hf, BitVec.toNat_and, toNat_mask f hw, Nat.and_two_pow_sub_one_eq_mod]

/-- **Neighbours are not disturbed**: writing `f` leaves a disjoint field `g` unchanged. -/
theorem get_set_of_disjoint (f g : BitField) (hd : Disjoint f g) (v x : Word) :
    g.get (f.set v x) = g.get v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_get, getLsbD_get]
  by_cases h : i < g.width
  · by_cases h2 : g.offset + i < 256
    · rw [getLsbD_set f v x _ h2]
      have : ¬ (f.offset ≤ g.offset + i ∧ g.offset + i < f.offset + f.width) := by
        unfold Disjoint at hd; omega
      simp [this]
    · simp [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt h2)]
  · simp [h]

/-- The value of a disjoint field as a number, after a write. -/
theorem toNat_get_set_of_disjoint (f g : BitField) (hg : g.width ≤ 256) (hd : Disjoint f g)
    (v x : Word) : (g.get (f.set v x)).toNat = v.toNat / 2 ^ g.offset % 2 ^ g.width := by
  rw [get_set_of_disjoint f g hd, toNat_get g hg]

/-- Bit `i` of a word is `get (bit i)`: `1` if set, `0` otherwise (solc's
`(v >> i) & 1`). -/
theorem get_bit (v : Word) (i : Nat) :
    (bit i).get v = if v.getLsbD i then 1#256 else 0#256 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_get]
  simp only [bit]
  by_cases h : j = 0
  · subst h
    cases v.getLsbD i <;> simp
  · have : ¬ j < 1 := by omega
    have h1 : Nat.testBit 1 j = false := Nat.testBit_lt_two_pow (Nat.one_lt_two_pow h)
    cases v.getLsbD i <;> simp [this, BitVec.getLsbD_ofNat, h1]

/-- Bit `i` after writing bit `j ≠ i`. -/
theorem getLsbD_set_bit_of_ne (v x : Word) {i j : Nat} (h : i ≠ j) :
    (BitField.set (bit j) v x).getLsbD i = v.getLsbD i := by
  by_cases hi : i < 256
  · rw [getLsbD_set _ v x i hi]
    simp only [bit]
    have : ¬ (j ≤ i ∧ i < j + 1) := by omega
    simp [this]
  · simp [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt hi)]

/-- Bit `i` after writing bit `i` with `x`: the low bit of `x` (for `i < 256`). -/
theorem getLsbD_set_bit_self (v x : Word) {i : Nat} (hi : i < 256) :
    (BitField.set (bit i) v x).getLsbD i = x.getLsbD 0 := by
  rw [getLsbD_set _ v x i hi]
  simp [bit]

end BitField

end EvmLogic.Solidity

/-! ## Storage layouts in compiler output -/

namespace EvmLogic.Solidity
open EvmLean

/-- A Solidity storage type, as described by solc's `storageLayout.types` table. -/
inductive StorageType where
  /-- A value stored in place (elementary types), with its solc label and its size in bytes. -/
  | inplace (label : String) (numberOfBytes : Nat)
  /-- A `string` or `bytes` value (short strings in place, long ones at `keccak(slot)`). -/
  | bytes (label : String)
  /-- `mapping(key => value)`: the value of `k` lives at `keccak(k ‖ slot)`. -/
  | mapping (key value : StorageType)
  /-- A dynamic array of elements, stored from `keccak(slot)`. -/
  | dynamicArray (elem : StorageType)
  deriving Repr, DecidableEq, Inhabited

/-- A state variable: its slot, byte offset within the slot and type. -/
structure StorageVar where
  label : String
  slot : Nat
  offset : Nat
  type : StorageType
  deriving Repr, DecidableEq, Inhabited

/-- The slot of the state variable `label`, if any. -/
def slotOf? (layout : List StorageVar) (label : String) : Option Nat :=
  (layout.find? (·.label == label)).map (·.slot)

end EvmLogic.Solidity
