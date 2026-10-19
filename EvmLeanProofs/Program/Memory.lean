import EvmLeanProofs.StepMemory

/-!
# Memory lemmas for symbolic execution

Reads are unaffected by expansion (`Memory.read_expand`, `Memory.loadWord_expand`); together
with `Memory.loadWord_storeWord(_of_disjoint)` these evaluate the `MLOAD`s of solc's free
memory pointer and of returned words. `memNorm` lists them for `wp_step [..]`.
-/

namespace EvmLean.Memory

open Bytes

/-- Expansion does not change what is read. -/
@[simp] theorem read_expand (m : Memory) (off len off' len' : Nat) :
    (m.expand off len).read off' len' = m.read off' len' := by
  apply ext_getD (by rw [read, read, size_readPadded, size_readPadded])
  intro j _
  simp only [read, getD_readPadded, getD_bytes_expand]

/-- Expansion does not change what `MLOAD` reads. -/
@[simp] theorem loadWord_expand (m : Memory) (off len off' : Nat) :
    (m.expand off len).loadWord off' = m.loadWord off' := by
  rw [loadWord, loadWord, read_expand]

/-- The empty memory reads as zero words. -/
theorem loadWord_empty (off : Nat) : ({} : Memory).loadWord off = 0 := by
  simp only [loadWord, read]
  unfold readPadded
  simp only [show ¬ off < ({} : Memory).bytes.size by simp [ByteArray.size], ↓reduceIte]
  rfl

end EvmLean.Memory
