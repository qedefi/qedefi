import EvmLogic.Step.Memory
import EvmLogic.Step.Stack
import EvmLogic.Solidity.Abi

/-!
# Step lemmas used by compiled Solidity

Two instructions that solc 0.8.28 output needs and the core step library does not state in
a form suited to large bytecode:

* `step_pushN`: `PUSH1`–`PUSH32` with the width as a plain `Nat` (no `Fin` arithmetic in
  the result), leaving the pushed value as `Bytes.toWord (readBytes code (pc + 1) n)`; the
  `reduceCodeImm` simproc of `EvmLeanProofs.Solidity.Tactic` evaluates it for literal code.
* `step_codecopy`: `CODECOPY` of a non-empty range (solc loads 32-byte event topics and
  other large constants from the end of the code this way).
-/

section

namespace EvmLean.Interpreter

open Bytes

variable {m : Machine} {x y z : Word} {rest : List Word}

/-- `PUSHn` for `1 ≤ n ≤ 32`: push the `n` immediate bytes as a big-endian word. -/
theorem step_pushN (n : Nat) (hn : 0 < n ∧ n < 33)
    (hcode : m.frame.code[m.frame.pc]? = some (0x5f + n).toUInt8)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := Bytes.toWord (readBytes m.frame.code (m.frame.pc + 1) n) :: m.frame.stack,
      gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + (1 + n) } } := by
  have hne : ¬ n = 0 := by omega
  have h := step_push ⟨n, hn.2⟩ hcode hlen (by simpa [hne] using hgas)
  simpa [hne] using h

/-- `CODECOPY` of `z ≠ 0` bytes from code offset `y` to memory offset `x`. The cost
`3 + 3 · ⌈z / 32⌉ + expansion` is spelled out (`Gas.veryLow + Gas.copyCost z`), so that
`evm_gas` can bound it. -/
theorem step_codecopy (hcode : m.frame.code[m.frame.pc]? = some 0x39)
    (hstk : m.frame.stack = x :: y :: z :: rest) (hz : z.toNat ≠ 0)
    (hgas : 3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := (m.frame.memory.expand x.toNat z.toNat).write x.toNat
        (readBytes m.frame.code y.toNat z.toNat),
      gasLeft := m.frame.gasLeft - (3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat),
      pc := m.frame.pc + 1 } } := by
  have hc : Gas.veryLow + Gas.copyCost z.toNat = 3 + 3 * ((z.toNat + 31) / 32) := rfl
  have hg := Nat.not_lt.mpr hgas
  rw [← hc] at hg ⊢
  simp only [memoryCost] at hg
  have hs : ¬ (readBytes m.frame.code y.toNat z.toNat).size = 0 := by
    rw [size_readBytes]; exact hz
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x39 = .codecopy by
    cases m.ctx.fork <;> rfl]
  simp only [exec, copyToMemory, popNat, pop, charge, advance, getFrame, modifyFrame,
    StateT.run_bind, hstk, hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
    ite_false, memoryExpansion, expandMemory, List.foldl, writeMemory, hs]
  rfl

end EvmLean.Interpreter

end

section

/-!
## Step lemma: `MCOPY` (EIP-5656)

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

end
