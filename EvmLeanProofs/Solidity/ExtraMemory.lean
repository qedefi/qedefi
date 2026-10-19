import EvmLeanProofs.Bytes
import EvmLeanProofs.StepMemory
import EvmLeanProofs.Program.Memory

/-!
# Calldata assembled in memory

When a compiled contract calls another one, the callee's calldata is a window of the caller's
memory (`Memory.read off len`, as `childMsg` builds it), and the callee's ABI decoder reads
sub-windows of it (`readBytes data i n`). `readBytes_read` collapses the two reads, so that the
callee's view of its calldata is computed by the usual read-over-write memory lemmas.
-/

namespace EvmLean.Memory

open Bytes Interpreter

/-- A read within a read is a read: `readBytes (mem.read off len) i n = mem.read (off + i) n`
when the inner window lies inside the outer one. -/
theorem readBytes_read (mem : Memory) (off len i n : Nat) (h : i + n ≤ len) :
    readBytes (mem.read off len) i n = mem.read (off + i) n := by
  rw [readBytes_eq_readPadded]
  apply ext_getD (by rw [size_readPadded, read, size_readPadded])
  intro j hj
  rw [size_readPadded] at hj
  simp only [read, getD_readPadded, hj, ↓reduceIte, show i + j < len by omega, Nat.add_assoc]

end EvmLean.Memory
