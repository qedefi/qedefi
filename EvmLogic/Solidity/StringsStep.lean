import EvmLogic.Step.StepMemory
import EvmLogic.Step.Memory
import EvmLogic.Solidity.Steps

/-!
# Step lemma: `MCOPY` (EIP-5656)

solc 0.8.24+ (`evmVersion = cancun`) copies a `bytes`/`string` memory value into the ABI
return buffer with `MCOPY`. The step lemma follows `exec .mcopy`
(`EvmLean/Interpreter/Instructions.lean`, mirroring `memory.py:mcopy`): pop
`(dst, src, len)`, charge `3 + 3 · ⌈len / 32⌉ + expansion` (the expansion covers both
`[src, src + len)` and `[dst, dst + len)`), expand memory, read `len` bytes at `src` and
write them at `dst`.

* `step_mcopy`: a non-empty copy (`len ≠ 0`); the copied bytes are read from the expanded
  memory (`Memory.read`), so read-over-write lemmas apply to them.
* `step_mcopy_zero`: an empty copy costs `3` and changes nothing but pc, stack and gas
  (zero-length accesses never expand memory).
* `mcopyCost m dst src len`: the expansion part of the cost, as `memoryCost` is for
  `MLOAD`/`MSTORE`.

Decoding of `0x5e` is fork-independent in `Opcode.decode` (the byte decodes to `MCOPY` in
every fork the semantics knows), so, like the other step lemmas, these hold for every fork and
every `Crypto`.
-/

namespace EvmLean.Interpreter

open Bytes

variable {m : Machine} {x y z : Word} {rest : List Word}

/-- Memory expansion cost of `MCOPY` from `src` to `dst` of `len` bytes in machine `m`: both
ranges are covered (source first, as in the reference). -/
def mcopyCost (m : Machine) (dst src : Word) (len : Nat) : Nat :=
  (Gas.extendMemory m.frame.memory.size [(src.toNat, len), (dst.toNat, len)]).cost

/-- Memory after an `MCOPY` of `len` bytes from `src` to `dst`: expanded over both ranges,
then the source bytes (read after the expansion) written at `dst`. -/
def _root_.EvmLean.Memory.mcopy (mem : Memory) (dst src len : Nat) : Memory :=
  let mem' := (mem.expand src len).expand dst len
  mem'.write dst (mem'.read src len)

/-- `MCOPY` of `z ≠ 0` bytes from memory offset `y` to memory offset `x` (stack
`x :: y :: z :: rest`, top first). -/
theorem step_mcopy (hcode : m.frame.code[m.frame.pc]? = some 0x5e)
    (hstk : m.frame.stack = x :: y :: z :: rest) (hz : z.toNat ≠ 0)
    (hgas : 3 + 3 * ((z.toNat + 31) / 32) + mcopyCost m x y z.toNat ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := m.frame.memory.mcopy x.toNat y.toNat z.toNat,
      gasLeft := m.frame.gasLeft - (3 + 3 * ((z.toNat + 31) / 32) + mcopyCost m x y z.toNat),
      pc := m.frame.pc + 1 } } := by
  have hc : Gas.veryLow + Gas.copyCost z.toNat = 3 + 3 * ((z.toNat + 31) / 32) := rfl
  have hg := Nat.not_lt.mpr hgas
  rw [← hc] at hg ⊢
  simp only [mcopyCost] at hg
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x5e = .mcopy by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame,
    StateT.run_bind, hstk, hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
    ite_false, memoryExpansion, expandMemory, List.foldl, writeMemory, readMemory,
    readBytes_bytes, mcopyCost, Memory.mcopy, Memory.size_read, hz]
  rfl

/-- `MCOPY` of zero bytes: only pc, stack and gas change (`3` gas). -/
theorem step_mcopy_zero (hcode : m.frame.code[m.frame.pc]? = some 0x5e)
    (hstk : m.frame.stack = x :: y :: z :: rest) (hz : z.toNat = 0)
    (hgas : 3 ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - 3, pc := m.frame.pc + 1 } } := by
  have hc : Gas.veryLow + Gas.copyCost z.toNat +
      (Gas.extendMemory m.frame.memory.size [(y.toNat, z.toNat), (x.toNat, z.toNat)]).cost = 3 := by
    simp [hz, Gas.veryLow, Gas.copyCost, Gas.words, Gas.ceil32, Gas.copyPerWord,
      Gas.extendMemory]
  have hc0 : Gas.veryLow + Gas.copyCost 0 +
      (Gas.extendMemory m.frame.memory.size [(y.toNat, 0), (x.toNat, 0)]).cost = 3 := by
    rw [← hz, hc]
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x5e = .mcopy by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame,
    StateT.run_bind, hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
    memoryExpansion, expandMemory, List.foldl, writeMemory, readMemory, ↓reduceIte, hz, Memory.expand_zero, size_readBytes, hc0, Nat.not_lt.mpr hgas]
  rfl

end EvmLean.Interpreter
