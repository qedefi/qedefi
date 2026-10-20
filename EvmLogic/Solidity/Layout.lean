import EvmLogic.State
import EvmLogic.Bytes

/-!
# Solidity storage layout

Where solc 0.8 puts state variables (the `--storage-layout` output gives, for each
variable, a `slot` and a byte `offset`; see "Layout of State Variables in Storage" in the
Solidity documentation):

* **Value types** occupy `size` bytes at byte `offset` (counted from the *least*
  significant end) of slot `slot`; consecutive small variables are *packed* into one slot.
  `Field` models such a variable; `Field.get`/`Field.set` extract and replace it within the
  slot's word (`SLOAD`/`SHR`/`AND`, resp. `AND NOT`/`OR`), and `Field.read`/`Field.write`
  do so in a `Storage`.
* **Mappings** `mapping(K => V)` at slot `p`: the value for key `k` is at
  `keccak256(pad32(k) ‖ pad32(p))` (`mappingSlot`), for value-type keys (addresses and
  integers are left-padded to 32 bytes: `Word.ofAddress`). Nested mappings apply this twice
  (`mappingSlot2`: `allowance[o][s]` is at `keccak256(pad32(s) ‖ keccak256(pad32(o) ‖ p))`).
* **Dynamic arrays** at slot `p`: the length is at `p`, element `i` (of a 32-byte element
  type) at `keccak256(pad32(p)) + i` (`arraySlot`).

Slots are computed with `Crypto.keccak256` of the context, so everything here holds for
every `Crypto`; that distinct variables get distinct slots is a hypothesis
(`EvmLeanProofs.Solidity.Keccak`).

## Read/write lemmas

* `Storage.get_set_ne` (core): writing one slot leaves every other slot alone; with slot
  disequalities from `Keccak` this separates variables in different slots.
* `Field.get_set_self`: reading a field after writing it gives the written value (masked to
  the field's width); `Field.get_set_of_disjoint`: writing a field does not disturb a
  *packed neighbour* in the same slot. Both are proved bitwise (`BitVec.getLsbD`), for every
  word, without `bv_decide`.
-/

namespace EvmLean.Solidity

open Bytes

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

/-- A value-type state variable: `size` bytes (`1 ≤ size ≤ 32`) at byte `offset` from the
least significant end of slot `slot` (the `slot`/`offset` of `--storage-layout`, with the
size of the type). -/
structure Field where
  /-- The storage slot. -/
  slot : Word
  /-- Byte offset from the least significant end. -/
  offset : Nat
  /-- Size in bytes. -/
  size : Nat

namespace Field

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

/-- Bit `i` of the mask. -/
theorem getLsbD_mask (f : Field) (hf : f.Valid) (i : Nat) :
    f.mask.getLsbD i = decide (i < 8 * f.size) := by
  simp only [mask, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]
  have := hf.2
  by_cases h : i < 8 * f.size
  · simp [h]; omega
  · simp [h]; omega

/-- Bit `i` of `get`. -/
theorem getLsbD_get (f : Field) (hf : f.Valid) (v : Word) (i : Nat) :
    (f.get v).getLsbD i = (decide (i < 8 * f.size) && v.getLsbD (8 * f.offset + i)) := by
  simp only [get, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, getLsbD_mask f hf]
  cases decide (i < 8 * f.size) <;> simp

/-- Bit `i` of `set`. -/
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

/-- The value of a field fits its width. -/
theorem get_and_mask (f : Field) (v : Word) : f.get v &&& f.mask = f.get v := by
  simp only [get, BitVec.and_assoc, BitVec.and_self]

/-- `read` after `write` of the same field. -/
theorem read_write_self (f : Field) (hf : f.Valid) (s : Storage) (x : Word) :
    f.read (f.write s x) = x &&& f.mask := by
  simp only [read, write, Storage.get_set_self, get_set_self f hf]

/-- `read` after `write` of a disjoint field of the same slot. -/
theorem read_write_of_disjoint (f g : Field) (hf : f.Valid) (hg : g.Valid) (hd : Disjoint f g)
    (hslot : g.slot = f.slot) (s : Storage) (x : Word) : g.read (f.write s x) = g.read s := by
  simp only [read, write, hslot, Storage.get_set_self, get_set_of_disjoint f g hf hg hd]

/-- `read` after `write` of a field in another slot. -/
theorem read_write_of_slot_ne (f g : Field) (hslot : g.slot ≠ f.slot) (s : Storage) (x : Word) :
    g.read (f.write s x) = g.read s := by
  simp only [read, write, Storage.get_set_ne _ _ hslot]

/-- A full-slot field (`uint256`, `bytes32`, …) is the slot itself. -/
theorem get_of_full (f : Field) (h0 : f.offset = 0) (h32 : f.size = 32) (v : Word) :
    f.get v = v := by
  simp only [get, mask, h0, h32, Nat.mul_zero, BitVec.ushiftRight_zero, Nat.reduceMul,
    Nat.sub_self, BitVec.and_allOnes]

end Field

end EvmLean.Solidity
