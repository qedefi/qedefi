import EvmLogic.Step.Memory
import EvmLogic.Solidity.Abi
import EvmLogic.Solidity.SimpAttr
import EvmLogic.Bytes
import EvmLogic.Tactic.EvmStep

/-!
# Memory as solc uses it

During symbolic execution memory is a term of `expand`s and `storeWord`s. The `@[sol_norm]`
lemmas here evaluate reads of such terms by pushing them through non-overlapping stores
(side conditions decided on numerals) to the store that wrote them; `initMemory` is the
memory after solc's prologue `PUSH1 0x80 PUSH1 0x40 MSTORE`.
-/

section

namespace EvmLean.Memory
open EvmLogic EvmLean.Bytes

attribute [sol_norm] read_expand

theorem read_add (m : Memory) (off a b : Nat) :
    m.read off (a + b) = m.read off a ++ m.read (off + a) b := by
  simp only [read, Solidity.readPadded_add]

@[sol_norm] theorem read_64 (m : Memory) (off : Nat) :
    m.read off 64 = m.read off 32 ++ m.read (off + 32) 32 :=
  read_add m off 32 32

@[sol_norm] theorem write_ofWord (m : Memory) (off : Nat) (w : Word) :
    m.write off (Bytes.ofWord w) = m.storeWord off w := rfl

@[sol_norm] theorem loadWord_eq (m : Memory) (off : Nat) :
    m.loadWord off = Bytes.toWord (m.read off 32) := rfl

attribute [sol_norm] read_storeWord read_storeWord_of_disjoint Bytes.toWord_ofWord

end EvmLean.Memory

namespace EvmLogic.Solidity
open EvmLean EvmLogic.Tactic

/-- The memory after solc's prologue `PUSH1 0x80 PUSH1 0x40 MSTORE` (free-memory pointer
`0x80` at `0x40`), in the form symbolic execution produces it. -/
def initMemory : Memory := (({} : Memory).expand 64 32).storeWord 64 0x80

attribute [sol_norm] initMemory

theorem loadWord_initMemory : initMemory.loadWord 64 = 0x80 :=
  Memory.loadWord_storeWord _ _ _

theorem size_initMemory : initMemory.size = 96 := by
  simp [initMemory, Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words]

end EvmLogic.Solidity

end

section

/-! ## Calldata assembled in memory (the calldata of a child call is a memory window) -/

namespace EvmLean.Memory
open EvmLogic EvmLean.Bytes EvmLean.Interpreter

/-- A read within a read is a read (the callee decoding calldata from the caller's memory). -/
theorem readBytes_read (mem : Memory) (off len i n : Nat) (h : i + n ≤ len) :
    readBytes (mem.read off len) i n = mem.read (off + i) n := by
  rw [readBytes_eq_readPadded]
  apply ext_getD (by rw [size_readPadded, read, size_readPadded])
  intro j hj
  rw [size_readPadded] at hj
  simp only [read, getD_readPadded, hj, ↓reduceIte, show i + j < len by omega, Nat.add_assoc]

end EvmLean.Memory

end

section

/-!
## Multi-word memory reads

Split multi-word reads (EIP-712 hashing in `permit`) into word reads. Not `simp` lemmas by
default: passed to the symbolic executor where needed.
-/

namespace EvmLean.Memory
open EvmLogic EvmLean.Bytes

theorem read_word_add (m : Memory) (off n : Nat) :
    m.read off (32 + n) = m.read off 32 ++ m.read (off + 32) n :=
  read_add m off 32 n

theorem read_96 (m : Memory) (off : Nat) :
    m.read off 96 = m.read off 32 ++ (m.read (off + 32) 32 ++ m.read (off + 64) 32) := by
  rw [show (96 : Nat) = 32 + 64 from rfl, read_word_add, read_64, Nat.add_assoc]

theorem read_128 (m : Memory) (off : Nat) :
    m.read off 128 = m.read off 32 ++ (m.read (off + 32) 32 ++ (m.read (off + 64) 32 ++
      m.read (off + 96) 32)) := by
  rw [show (128 : Nat) = 32 + 96 from rfl, read_word_add, read_96, Nat.add_assoc, Nat.add_assoc]

theorem read_160 (m : Memory) (off : Nat) :
    m.read off 160 = m.read off 32 ++ (m.read (off + 32) 32 ++ (m.read (off + 64) 32 ++
      (m.read (off + 96) 32 ++ m.read (off + 128) 32))) := by
  rw [show (160 : Nat) = 32 + 128 from rfl, read_word_add, read_128, Nat.add_assoc, Nat.add_assoc,
    Nat.add_assoc]

theorem read_192 (m : Memory) (off : Nat) :
    m.read off 192 = m.read off 32 ++ (m.read (off + 32) 32 ++ (m.read (off + 64) 32 ++
      (m.read (off + 96) 32 ++ (m.read (off + 128) 32 ++ m.read (off + 160) 32)))) := by
  rw [show (192 : Nat) = 32 + 160 from rfl, read_word_add, read_160, Nat.add_assoc, Nat.add_assoc,
    Nat.add_assoc, Nat.add_assoc]

theorem read_66 (m : Memory) (off : Nat) :
    m.read off 66 = m.read off 2 ++ (m.read (off + 2) 32 ++ m.read (off + 34) 32) := by
  rw [show (66 : Nat) = 2 + 64 from rfl, read_add, read_64, Nat.add_assoc]

end EvmLean.Memory

namespace EvmLean.Memory
open EvmLogic

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
open EvmLogic

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
open EvmLogic

theorem extendMemory_one_of_le {size off len : Nat} (h : off + len ≤ size) (h32 : size % 32 = 0) :
    extendMemory size [(off, len)] = { cost := 0, newSize := size } := by
  unfold extendMemory
  simp only [List.foldl_cons, List.foldl_nil]
  split
  · rfl
  · have : ceil32 (off + len) ≤ ceil32 size := by unfold ceil32; omega
    simp only [this, ↓reduceIte]

end EvmLean.Gas

end
