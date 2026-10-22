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

/-- `CALLDATACOPY` of `z ≠ 0` bytes (zero-padded past the end of the calldata). -/
theorem step_calldatacopy (hcode : m.frame.code[m.frame.pc]? = some 0x37)
    (hstk : m.frame.stack = x :: y :: z :: rest) (hz : z.toNat ≠ 0)
    (hgas : 3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := (m.frame.memory.expand x.toNat z.toNat).write x.toNat
        (readBytes m.frame.msg.data y.toNat z.toNat),
      gasLeft := m.frame.gasLeft - (3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat),
      pc := m.frame.pc + 1 } } := by
  have hc : Gas.veryLow + Gas.copyCost z.toNat = 3 + 3 * ((z.toNat + 31) / 32) := rfl
  have hg := Nat.not_lt.mpr hgas
  rw [← hc] at hg ⊢
  simp only [memoryCost] at hg
  have hs : ¬ (readBytes m.frame.msg.data y.toNat z.toNat).size = 0 := by
    rw [size_readBytes]; exact hz
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x37 = .calldatacopy by
    cases m.ctx.fork <;> rfl]
  simp only [exec, copyToMemory, popNat, pop, charge, advance, getFrame, modifyFrame,
    StateT.run_bind, hstk, hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
    ite_false, memoryExpansion, expandMemory, List.foldl, writeMemory, hs]
  rfl

/-- `CALLDATACOPY` of no bytes: only the 3 gas and the pops. -/
theorem step_calldatacopy_zero (hcode : m.frame.code[m.frame.pc]? = some 0x37)
    (hstk : m.frame.stack = x :: y :: z :: rest) (hz : z.toNat = 0)
    (hgas : 3 ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - 3, pc := m.frame.pc + 1 } } := by
  have hc : Gas.veryLow + Gas.copyCost z.toNat +
      (Gas.extendMemory m.frame.memory.size [(x.toNat, z.toNat)]).cost = 3 := by
    simp [hz, Gas.extendMemory, Gas.copyCost, Gas.words, Gas.veryLow]
  have hg3 : ¬ m.frame.gasLeft < 3 := by omega
  have hs : (readBytes m.frame.msg.data y.toNat z.toNat).size = 0 := by
    rw [size_readBytes]; exact hz
  have he : m.frame.memory.expand x.toNat z.toNat = m.frame.memory :=
    Memory.expand_of_le _ _ _ (by
      simp only [Memory.wordsAfter, hz, ↓reduceIte, Memory.words]; exact Nat.mul_div_le _ _)
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x37 = .calldatacopy by
    cases m.ctx.fork <;> rfl]
  simp only [exec, copyToMemory, popNat, pop, charge, advance, getFrame, modifyFrame,
    StateT.run_bind, hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
    ite_false, memoryExpansion, expandMemory, List.foldl, writeMemory, hs, ite_true, he, hc, hg3]
  rfl

/-- **`RETURNDATACOPY`** of a non-empty window inside the return data. -/
theorem step_returndatacopy (hcode : m.frame.code[m.frame.pc]? = some 0x3e)
    (hstk : m.frame.stack = x :: y :: z :: rest) (hz : z.toNat ≠ 0)
    (hrd : y.toNat + z.toNat ≤ m.frame.returnData.size)
    (hgas : 3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := (m.frame.memory.expand x.toNat z.toNat).write x.toNat
        (m.frame.returnData.extract y.toNat (y.toNat + z.toNat)),
      gasLeft := m.frame.gasLeft - (3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat),
      pc := m.frame.pc + 1 } } := by
  have hc : Gas.veryLow + Gas.copyCost z.toNat = 3 + 3 * ((z.toNat + 31) / 32) := rfl
  have hg := Nat.not_lt.mpr hgas
  rw [← hc] at hg ⊢
  simp only [memoryCost] at hg
  have hr : ¬ y.toNat + z.toNat > m.frame.returnData.size := Nat.not_lt.mpr hrd
  have hs : ¬ (m.frame.returnData.extract y.toNat (y.toNat + z.toNat)).size = 0 := by
    rw [ByteArray.size_extract]; omega
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x3e = .returndatacopy by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame,
    StateT.run_bind, hstk, hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
    ite_false, memoryExpansion, expandMemory, List.foldl, writeMemory, hs, hr]
  rfl

/-- `RETURNDATACOPY` of no bytes at an offset inside the return data: only the 3 gas. -/
theorem step_returndatacopy_zero (hcode : m.frame.code[m.frame.pc]? = some 0x3e)
    (hstk : m.frame.stack = x :: y :: z :: rest) (hz : z.toNat = 0)
    (hrd : y.toNat ≤ m.frame.returnData.size) (hgas : 3 ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - 3, pc := m.frame.pc + 1 } } := by
  have hc : Gas.veryLow + Gas.copyCost z.toNat +
      (Gas.extendMemory m.frame.memory.size [(x.toNat, z.toNat)]).cost = 3 := by
    simp [hz, Gas.extendMemory, Gas.copyCost, Gas.words, Gas.veryLow]
  have hg3 : ¬ m.frame.gasLeft < 3 := by omega
  have hr : ¬ y.toNat + z.toNat > m.frame.returnData.size := by omega
  have hs : (m.frame.returnData.extract y.toNat (y.toNat + z.toNat)).size = 0 := by
    rw [ByteArray.size_extract]; omega
  have he : m.frame.memory.expand x.toNat z.toNat = m.frame.memory :=
    Memory.expand_of_le _ _ _ (by
      simp only [Memory.wordsAfter, hz, ↓reduceIte, Memory.words]; exact Nat.mul_div_le _ _)
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x3e = .returndatacopy by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame,
    StateT.run_bind, hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
    ite_false, memoryExpansion, expandMemory, List.foldl, writeMemory, hs, hr, ite_true, he, hc,
    hg3]
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

section

/-!
## Copies of possibly empty data (`CALLDATACOPY`, `RETURNDATACOPY`)

`copyMemory mem off data` is the memory after copying `data` to `off` (expansion, then the write;
nothing for empty data). `step_calldatacopy_any`/`step_returndatacopy_any` cover both the empty
and the non-empty copy with one gas charge, so a copy of symbolic size needs no case split; the
`copyMemory_*` facts and the expansion-cost bounds serve symbolic-size memory.
-/

namespace EvmLean.Interpreter
open EvmLogic EvmLean.Bytes

variable {m : Machine} {x y z : Word} {rest : List Word}

/-- Memory after copying `data` to `off`: expanded and written, unchanged for empty data. -/
def copyMemory (mem : Memory) (off : Nat) (data : ByteArray) : Memory :=
  if data.size = 0 then mem else (mem.expand off data.size).write off data

theorem memoryCost_zero_len (m : Machine) (x : Word) : memoryCost m x 0 = 0 := by
  simp [memoryCost, Gas.extendMemory]

/-- **`CALLDATACOPY`** of any size. -/
theorem step_calldatacopy_any (hcode : m.frame.code[m.frame.pc]? = some 0x37)
    (hstk : m.frame.stack = x :: y :: z :: rest)
    (hgas : 3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := copyMemory m.frame.memory x.toNat (readBytes m.frame.msg.data y.toNat z.toNat),
      gasLeft := m.frame.gasLeft - (3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat),
      pc := m.frame.pc + 1 } } := by
  by_cases hz : z.toNat = 0
  · rw [hz, memoryCost_zero_len] at hgas ⊢
    rw [step_calldatacopy_zero hcode hstk hz (by omega)]
    simp [copyMemory]
  · rw [step_calldatacopy hcode hstk hz hgas]
    simp [copyMemory, hz]

/-- **`RETURNDATACOPY`** of any size inside the return data. -/
theorem step_returndatacopy_any (hcode : m.frame.code[m.frame.pc]? = some 0x3e)
    (hstk : m.frame.stack = x :: y :: z :: rest)
    (hrd : y.toNat + z.toNat ≤ m.frame.returnData.size)
    (hgas : 3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := copyMemory m.frame.memory x.toNat
        (m.frame.returnData.extract y.toNat (y.toNat + z.toNat)),
      gasLeft := m.frame.gasLeft - (3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat),
      pc := m.frame.pc + 1 } } := by
  have hsz : (m.frame.returnData.extract y.toNat (y.toNat + z.toNat)).size = z.toNat := by
    rw [ByteArray.size_extract]; omega
  by_cases hz : z.toNat = 0
  · rw [hz, memoryCost_zero_len] at hgas ⊢
    rw [step_returndatacopy_zero hcode hstk hz (by omega) (by omega)]
    simp [copyMemory]
  · rw [step_returndatacopy hcode hstk hz hrd hgas]
    simp [copyMemory, hsz, hz]

theorem read_copyMemory (mem : Memory) (off : Nat) (data : ByteArray) :
    (copyMemory mem off data).read off data.size = data := by
  unfold copyMemory
  split
  · rename_i h
    have h1 : mem.read off data.size = .empty := ByteArray.size_eq_zero_iff.mp (by simp [h])
    rw [h1, ByteArray.size_eq_zero_iff.mp h]
  · exact Memory.read_write _ _ _

theorem size_copyMemory (mem : Memory) (data : ByteArray) :
    mem.size ≤ (copyMemory mem 0 data).size ∧ data.size ≤ (copyMemory mem 0 data).size := by
  unfold copyMemory
  split
  · rename_i h; omega
  · rw [Memory.size_write, Memory.size_expand, Memory.size_expand]
    simp only [Memory.wordsAfter, Memory.words, Nat.zero_add]
    split
    · omega
    · constructor
      · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
      · have : data.size ≤ 32 * ((data.size + 31) / 32) := by omega
        omega

theorem memoryCost_mono {a b : Nat} (h : a ≤ b) : Gas.memoryCost a ≤ Gas.memoryCost b := by
  unfold Gas.memoryCost Gas.words Gas.memoryPerWord
  dsimp only
  have h1 : (a + 31) / 32 ≤ (b + 31) / 32 := Nat.div_le_div_right (by omega)
  have h2 := Nat.mul_le_mul h1 h1
  have h3 := Nat.div_le_div_right (c := 512) h2
  omega

theorem memoryCost_ceil32 (n : Nat) : Gas.memoryCost (Gas.ceil32 n) = Gas.memoryCost n := by
  unfold Gas.memoryCost Gas.ceil32 Gas.words
  have : ((n + 31) / 32 * 32 + 31) / 32 = (n + 31) / 32 := by omega
  rw [this]

/-- The expansion cost of an access `[0, n)` is at most the cost of `n` bytes from scratch. -/
theorem extendMemory_cost_le (s n : Nat) :
    (Gas.extendMemory s [(0, n)]).cost ≤ Gas.memoryCost n := by
  simp only [Gas.extendMemory, List.foldl, Nat.zero_add]
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · simp only [memoryCost_ceil32]; omega

/-- An access `[0, n)` inside memory of size `s ≥ n` costs nothing. -/
theorem extendMemory_cost_eq_zero {s n : Nat} (h : n ≤ s) :
    (Gas.extendMemory s [(0, n)]).cost = 0 := by
  simp only [Gas.extendMemory, List.foldl, Nat.zero_add]
  split
  · rfl
  · rw [ite_eq_left_iff.mpr fun h' => absurd ?_ h']
    unfold Gas.ceil32
    exact Nat.mul_le_mul_right _ (Nat.div_le_div_right (by omega))

/-- A call's windows `[0, n)` and `[0, 0)` inside memory of size `s ≥ n` cost nothing. -/
theorem extendMemory_cost_eq_zero₂ {s n : Nat} (h : n ≤ s) :
    (Gas.extendMemory s [(0, n), (0, 0)]).cost = 0 := by
  have h1 := extendMemory_cost_eq_zero h
  unfold Gas.extendMemory at h1 ⊢
  simp only [List.foldl_cons, List.foldl_nil] at h1 ⊢
  simpa using h1

end EvmLean.Interpreter

end
