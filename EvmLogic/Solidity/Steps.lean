import EvmLogic.Step.StepMemory
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
