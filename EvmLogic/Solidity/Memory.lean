import EvmLogic.Step.StepMemory
import EvmLogic.Solidity.Abi
import EvmLogic.Solidity.SimpAttr

/-!
# Memory as solc uses it

solc's memory discipline: the free-memory pointer at `0x40` is initialised to `0x80` by the
first three instructions of every contract (`PUSH1 0x80 PUSH1 0x40 MSTORE`); the scratch
space `[0x00, 0x40)` holds the two words hashed by mapping lookups (`key ‖ slot`, then
`KECCAK256(0x00, 0x40)`); event data and return values are written at the free pointer.

During symbolic execution memory is a growing term of `expand`s and `storeWord`s. The lemmas
here evaluate *reads* of such terms, by pushing a read through every store it does not
overlap (`Memory.read_storeWord_of_disjoint`, whose side condition simp decides on numerals)
until it hits the store that wrote it (`Memory.read_storeWord`):

* `Memory.read_expand`: expansion appends zeros, which reads already return;
* `Memory.read_64`: a 64-byte read (the mapping-slot preimage) is two word reads;
* `Memory.write_ofWord`: a 32-byte `CODECOPY` of a word constant is an `MSTORE`;
* `Memory.loadWord_eq`: `MLOAD` is a read.

They are tagged `@[sol_norm]`, together with the core read-over-write lemmas.
-/

namespace EvmLean.Memory

open Bytes

/-- Expansion does not change what a read returns. -/
@[sol_norm] theorem read_expand (m : Memory) (o l off len : Nat) :
    (m.expand o l).read off len = m.read off len := by
  apply ext_getD (by simp [read, size_readPadded])
  intro j hj
  simp only [read, getD_readPadded, getD_bytes_expand]

/-- Reads split at any point. -/
theorem read_add (m : Memory) (off a b : Nat) :
    m.read off (a + b) = m.read off a ++ m.read (off + a) b := by
  simp only [read, Solidity.readPadded_add]

/-- A 64-byte read is two word reads. -/
@[sol_norm] theorem read_64 (m : Memory) (off : Nat) :
    m.read off 64 = m.read off 32 ++ m.read (off + 32) 32 :=
  read_add m off 32 32

/-- Writing the encoding of a word is `MSTORE`. -/
@[sol_norm] theorem write_ofWord (m : Memory) (off : Nat) (w : Word) :
    m.write off (Bytes.ofWord w) = m.storeWord off w := rfl

/-- `MLOAD` is the word of a 32-byte read. -/
@[sol_norm] theorem loadWord_eq (m : Memory) (off : Nat) :
    m.loadWord off = Bytes.toWord (m.read off 32) := rfl

attribute [sol_norm] read_storeWord read_storeWord_of_disjoint Bytes.toWord_ofWord

end EvmLean.Memory

namespace EvmLean.Solidity

/-- The memory after solc's prologue `PUSH1 0x80 PUSH1 0x40 MSTORE` (free-memory pointer
`0x80` at `0x40`), in the form symbolic execution produces it. -/
def initMemory : Memory := (({} : Memory).expand 64 32).storeWord 64 0x80

attribute [sol_norm] initMemory

/-- The free-memory pointer of `initMemory`. -/
theorem loadWord_initMemory : initMemory.loadWord 64 = 0x80 :=
  Memory.loadWord_storeWord _ _ _

/-- `initMemory` has three words. -/
theorem size_initMemory : initMemory.size = 96 := by
  simp [initMemory, Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words]

end EvmLean.Solidity
