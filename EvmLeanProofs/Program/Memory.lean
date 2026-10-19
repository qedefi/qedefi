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

/-- Reading a prefix of a stored word gives a prefix of its encoding (e.g. the 4-byte selector
solc stores with `mstore(p, shl(224, sel))` and passes as calldata). -/
theorem read_storeWord_prefix (m : Memory) (off n : Nat) (w : Word) (hn : n ≤ 32) :
    (m.storeWord off w).read off n = (ofWord w).extract 0 n := by
  apply ext_getD (by rw [read, size_readPadded, ByteArray.size_extract, size_ofWord]; omega)
  intro j hj
  rw [read, size_readPadded] at hj
  have h : off ≤ off + j ∧ off + j < off + (ofWord w).size := by rw [size_ofWord]; omega
  simp only [read, getD_readPadded, hj, ↓reduceIte, storeWord, getD_bytes_write, h, and_self,
    Nat.add_sub_cancel_left, getD_extract, Nat.zero_add]

/-- `read` returns exactly `len` bytes. -/
@[simp] theorem size_read (m : Memory) (off len : Nat) : (m.read off len).size = len := by
  rw [read, size_readPadded]

/-- The empty memory reads as zero words. -/
theorem loadWord_empty (off : Nat) : ({} : Memory).loadWord off = 0 := by
  simp only [loadWord, read]
  unfold readPadded
  simp only [show ¬ off < ({} : Memory).bytes.size by simp [ByteArray.size], ↓reduceIte]
  rfl

end EvmLean.Memory

namespace EvmLean.Interpreter

/-- `readBytes` returns exactly `len` bytes. -/
@[simp] theorem size_readBytes (b : ByteArray) (off len : Nat) : (readBytes b off len).size = len := by
  rw [readBytes_eq_readPadded, Bytes.size_readPadded]

end EvmLean.Interpreter
