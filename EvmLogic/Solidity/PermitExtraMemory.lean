import EvmLogic.Solidity.Memory
import EvmLogic.Step.Memory
import EvmLogic.Solidity.PermitExtraAttr
import EvmLogic.Tactic.EvmStep

/-!
# Multi-word memory reads

The EIP-712 code of Solmate's `permit` and `DOMAIN_SEPARATOR` hashes several consecutive words
of memory (`abi.encode` of 5 or 6 words) and a packed `"\x19\x01" ‖ separator ‖ structHash`
(66 bytes, at unaligned offsets), and passes four words to `ECRECOVER`. These lemmas split
such reads into the word reads that the read-over-write lemmas evaluate
(`Memory.read_storeWord`, `Memory.read_storeWord_of_disjoint`, `Memory.read_storeWord_prefix`).
They are not `simp` lemmas by default: they are passed to the symbolic executor where needed.
-/

namespace EvmLean.Memory

open Bytes

/-- A read of `32 + n` bytes is a word read followed by the rest. -/
theorem read_word_add (m : Memory) (off n : Nat) :
    m.read off (32 + n) = m.read off 32 ++ m.read (off + 32) n :=
  read_add m off 32 n

/-- A 96-byte read is three word reads. -/
theorem read_96 (m : Memory) (off : Nat) :
    m.read off 96 = m.read off 32 ++ (m.read (off + 32) 32 ++ m.read (off + 64) 32) := by
  rw [show (96 : Nat) = 32 + 64 from rfl, read_word_add, read_64, Nat.add_assoc]

/-- A 128-byte read is four word reads. -/
theorem read_128 (m : Memory) (off : Nat) :
    m.read off 128 = m.read off 32 ++ (m.read (off + 32) 32 ++ (m.read (off + 64) 32 ++
      m.read (off + 96) 32)) := by
  rw [show (128 : Nat) = 32 + 96 from rfl, read_word_add, read_96, Nat.add_assoc, Nat.add_assoc]

/-- A 160-byte read is five word reads. -/
theorem read_160 (m : Memory) (off : Nat) :
    m.read off 160 = m.read off 32 ++ (m.read (off + 32) 32 ++ (m.read (off + 64) 32 ++
      (m.read (off + 96) 32 ++ m.read (off + 128) 32))) := by
  rw [show (160 : Nat) = 32 + 128 from rfl, read_word_add, read_128, Nat.add_assoc, Nat.add_assoc,
    Nat.add_assoc]

/-- A 192-byte read is six word reads. -/
theorem read_192 (m : Memory) (off : Nat) :
    m.read off 192 = m.read off 32 ++ (m.read (off + 32) 32 ++ (m.read (off + 64) 32 ++
      (m.read (off + 96) 32 ++ (m.read (off + 128) 32 ++ m.read (off + 160) 32)))) := by
  rw [show (192 : Nat) = 32 + 160 from rfl, read_word_add, read_160, Nat.add_assoc, Nat.add_assoc,
    Nat.add_assoc, Nat.add_assoc]

/-- The 66-byte read of `"\x19\x01" ‖ word ‖ word`: two bytes and two (unaligned) words. -/
theorem read_66 (m : Memory) (off : Nat) :
    m.read off 66 = m.read off 2 ++ (m.read (off + 2) 32 ++ m.read (off + 34) 32) := by
  rw [show (66 : Nat) = 2 + 64 from rfl, read_add, read_64, Nat.add_assoc]

end EvmLean.Memory

namespace EvmLean.Memory

/-- The first two bytes of a stored word (the `"\x19\x01"` prefix of an EIP-712 digest,
stored as `shl(240, 0x1901)`). -/
theorem read_storeWord_two (m : Memory) (off : Nat) (w : Word) :
    (m.storeWord off w).read off 2 = (Bytes.ofWord w).extract 0 2 :=
  read_storeWord_prefix m off 2 w (by decide)

end EvmLean.Memory

attribute [permit_norm] EvmLean.Interpreter.memoryCost EvmLean.Gas.extendMemory List.foldl
  EvmLean.Gas.ceil32 EvmLean.Gas.memoryCost EvmLean.Gas.words EvmLean.Gas.memoryPerWord
  EvmLean.Memory.size_storeWord EvmLean.Memory.size_expand
  EvmLean.Memory.wordsAfter EvmLean.Memory.words EvmLean.Gas.keccak256Cost
  EvmLean.Gas.keccak256Base EvmLean.Gas.keccak256PerWord Nat.max_def

attribute [permit_norm] Nat.reduceEqDiff Nat.reduceLeDiff Nat.reduceAdd Nat.reduceMul Nat.reduceDiv
  Nat.reduceSub reduceIte

namespace EvmLean.Memory

/-- An access inside a word-aligned memory does not expand it (also for a symbolic length). -/
theorem expand_eq_self_of_le {m : Memory} {off len : Nat} (h : off + len ≤ m.size) (h32 : m.size % 32 = 0) :
    m.expand off len = m := by
  unfold expand
  have : 32 * wordsAfter m.words off len ≤ m.size := by
    unfold wordsAfter words
    split
    · omega
    · rw [Nat.max_def]; split <;> omega
  simp only [this, ↓reduceIte]

end EvmLean.Memory

namespace EvmLean.Gas

/-- An access inside a word-aligned memory costs no expansion gas (also for a symbolic
length). -/
theorem extendMemory_one_of_le {size off len : Nat} (h : off + len ≤ size) (h32 : size % 32 = 0) :
    extendMemory size [(off, len)] = { cost := 0, newSize := size } := by
  unfold extendMemory
  simp only [List.foldl_cons, List.foldl_nil]
  split
  · rfl
  · have : ceil32 (off + len) ≤ ceil32 size := by unfold ceil32; omega
    simp only [this, ↓reduceIte]

end EvmLean.Gas
