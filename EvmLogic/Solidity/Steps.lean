import EvmLogic.Step.Memory
import EvmLogic.Step.Stack
import EvmLogic.Solidity.Abi

/-!
# Step lemmas used by compiled Solidity

`PUSHn`, `CODECOPY` and `MCOPY` in forms suited to large bytecode: `step_pushN` takes the
width as a plain `Nat` (no `Fin` arithmetic) and leaves the immediate as a `readBytes` of the
code, evaluated by the `reduceCodeImm` simproc of `sol_step`.
-/

section

namespace EvmLean.Interpreter
open EvmLogic EvmLean.Bytes

variable {m : Machine} {x y z : Word} {rest : List Word}

theorem step_pushN (n : Nat) (hn : 0 < n ∧ n < 33)
    (hcode : m.frame.code[m.frame.pc]? = some (0x5f + n).toUInt8)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := Bytes.toWord (readBytes m.frame.code (m.frame.pc + 1) n) :: m.frame.stack,
      gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + (1 + n) } } := by
  have hne : ¬ n = 0 := by omega
  have h := step_push ⟨n, hn.2⟩ hcode hlen (by simpa [hne] using hgas)
  simpa [hne] using h

/-- `CODECOPY` of `z ≠ 0` bytes. The cost is spelled out as `3 + 3 · ⌈z / 32⌉ + expansion`
so that `evm_gas` can bound it. -/
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

/-! ## `MCOPY` (EIP-5656) -/

namespace EvmLean.Interpreter
open EvmLogic EvmLean.Bytes

variable {m : Machine} {x y z : Word} {rest : List Word}

/-- Memory expansion cost of `MCOPY`: both ranges, source first (as in the reference). -/
def mcopyCost (m : Machine) (dst src : Word) (len : Nat) : Nat :=
  (Gas.extendMemory m.frame.memory.size [(src.toNat, len), (dst.toNat, len)]).cost

/-- Memory after an `MCOPY`: expanded over both ranges, then the source bytes (read after
the expansion) written at `dst`. -/
def _root_.EvmLean.Memory.mcopy (mem : Memory) (dst src len : Nat) : Memory :=
  let mem' := (mem.expand src len).expand dst len
  mem'.write dst (mem'.read src len)

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
