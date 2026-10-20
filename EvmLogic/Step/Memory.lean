import EvmLogic.Step.Basic
import EvmLogic.Bytes

/-!
# Step lemmas: memory

`MLOAD`, `MSTORE`, `MSTORE8`. The gas is `3 + expansion`, where the expansion cost is
`memoryCost m x n = (Gas.extendMemory m.frame.memory.size [(x.toNat, n)]).cost`; memory is
first expanded to cover the access (`Memory.expand`), then read or written. The
read-after-write facts about the resulting memory are in `EvmLogic.Bytes`
(`Memory.loadWord_storeWord`, `Memory.size_storeWord`, …).
-/

section

namespace EvmLean.Interpreter

variable {m : Machine} {x y : Word} {rest : List Word}

/-- The empty memory has size zero. -/
@[simp] theorem Memory.size_empty : ({} : Memory).size = 0 := rfl

/-- Expanding memory to a range it already covers does nothing. -/
theorem Memory.expand_of_le (mem : Memory) (off len : Nat)
    (h : 32 * Memory.wordsAfter mem.words off len ≤ mem.size) : mem.expand off len = mem := by
  simp only [Memory.expand, h, ite_true]

/-- After `MSTORE` at `off`, memory covers `[off, off + 32)`. -/
@[simp] theorem Memory.expand_storeWord_self (mem : Memory) (off : Nat) (w : Word) :
    (mem.storeWord off w).expand off 32 = mem.storeWord off w := by
  apply Memory.expand_of_le
  rw [Memory.size_storeWord]
  simp only [Memory.wordsAfter, Memory.words, Memory.size_storeWord]
  simp only [Nat.reduceEqDiff, ite_false]
  omega

/-- Reading memory bytes with `readBytes` is `Memory.read`. -/
@[simp] theorem readBytes_bytes (mem : Memory) (off len : Nat) :
    readBytes mem.bytes off len = mem.read off len := by
  rw [readBytes_eq_readPadded]
  rfl

/-- Memory expansion cost of an `n`-byte access at offset `x` in machine `m`. -/
def memoryCost (m : Machine) (x : Word) (n : Nat) : Nat :=
  (Gas.extendMemory m.frame.memory.size [(x.toNat, n)]).cost

/-- `MLOAD` at offset `x`. -/
theorem step_mload (hcode : m.frame.code[m.frame.pc]? = some 0x51)
    (hstk : m.frame.stack = x :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow + memoryCost m x 32 ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (m.frame.memory.expand x.toNat 32).loadWord x.toNat :: rest,
      memory := m.frame.memory.expand x.toNat 32,
      gasLeft := m.frame.gasLeft - (Gas.veryLow + memoryCost m x 32),
      pc := m.frame.pc + 1 } } := by
  have hg := Nat.not_lt.mpr hgas
  have hl : ¬ Gas.stackLimit ≤ rest.length := Nat.not_le.mpr hlen
  simp only [memoryCost] at hg
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x51 = .mload by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popNat, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
    hstk, hg, hl, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false,
    memoryExpansion, expandMemory, List.foldl]
  rfl

/-- `MSTORE` of `y` at offset `x`. -/
theorem step_mstore (hcode : m.frame.code[m.frame.pc]? = some 0x52)
    (hstk : m.frame.stack = x :: y :: rest)
    (hgas : Gas.veryLow + memoryCost m x 32 ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := (m.frame.memory.expand x.toNat 32).storeWord x.toNat y,
      gasLeft := m.frame.gasLeft - (Gas.veryLow + memoryCost m x 32),
      pc := m.frame.pc + 1 } } := by
  have hg := Nat.not_lt.mpr hgas
  simp only [memoryCost] at hg
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x52 = .mstore by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame, StateT.run_bind,
    hstk, hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false,
    memoryExpansion, expandMemory, List.foldl]
  rfl

/-- `MSTORE8` of the low byte of `y` at offset `x`. -/
theorem step_mstore8 (hcode : m.frame.code[m.frame.pc]? = some 0x53)
    (hstk : m.frame.stack = x :: y :: rest)
    (hgas : Gas.veryLow + memoryCost m x 1 ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := (m.frame.memory.expand x.toNat 1).storeByte x.toNat y,
      gasLeft := m.frame.gasLeft - (Gas.veryLow + memoryCost m x 1),
      pc := m.frame.pc + 1 } } := by
  have hg := Nat.not_lt.mpr hgas
  simp only [memoryCost] at hg
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x53 = .mstore8 by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame, StateT.run_bind,
    hstk, hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false,
    memoryExpansion, expandMemory, List.foldl]
  rfl

/-- `KECCAK256` of memory `[x, x + y)`: the result is `ctx.crypto.keccak256` of the bytes,
for whatever `Crypto` the context carries. -/
theorem step_keccak256 (hcode : m.frame.code[m.frame.pc]? = some 0x20)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.keccak256Cost y.toNat + (Gas.extendMemory m.frame.memory.size
      [(x.toNat, y.toNat)]).cost ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := m.ctx.crypto.keccak256
        (readBytes (m.frame.memory.expand x.toNat y.toNat).bytes x.toNat y.toNat) :: rest,
      memory := m.frame.memory.expand x.toNat y.toNat,
      gasLeft := m.frame.gasLeft - (Gas.keccak256Cost y.toNat +
        (Gas.extendMemory m.frame.memory.size [(x.toNat, y.toNat)]).cost),
      pc := m.frame.pc + 1 } } := by
  have hg := Nat.not_lt.mpr hgas
  have hl : ¬ Gas.stackLimit ≤ rest.length := Nat.not_le.mpr hlen
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x20 = .keccak256 by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popNat, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
    hstk, hg, hl, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false,
    memoryExpansion, expandMemory, List.foldl, readMemory]
  rfl

end EvmLean.Interpreter

end

section

/-!
## Memory lemmas for symbolic execution

Reads are unaffected by expansion (`Memory.read_expand`, `Memory.loadWord_expand`); together
with `Memory.loadWord_storeWord(_of_disjoint)` these evaluate the `MLOAD`s of solc's free
memory pointer and of returned words. `memNorm` lists them for `wp_step [..]`.
-/

namespace EvmLean.Memory

open EvmLean.Bytes

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

end
