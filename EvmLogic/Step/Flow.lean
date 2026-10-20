import EvmLogic.Step.Basic

/-!
# Step lemmas: control flow and halting

Jumps, `STOP`, `RETURN`, `REVERT`, `INVALID`. Halting instructions are stated as
`step m = finishFrame m' outcome`; for a top-level call frame the `*_top` lemmas turn that into
`.done (topLevelResult …)`, whose fields the `topLevelResult_*` simp lemmas read off.
-/

namespace EvmLean.Interpreter

variable {m : Machine} {x y : Word} {rest : List Word}

/-! ## Jumps -/

theorem step_jumpdest (hcode : m.frame.code[m.frame.pc]? = some 0x5b)
    (hgas : Gas.jumpdest ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      gasLeft := m.frame.gasLeft - Gas.jumpdest, pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < Gas.jumpdest := Nat.not_lt.mpr hgas
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x5b = .jumpdest by
    cases m.ctx.fork <;> rfl]
  simp only [exec, charge, advance, getFrame, modifyFrame, StateT.run_bind, hg,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false]
  rfl

theorem step_jump (hcode : m.frame.code[m.frame.pc]? = some 0x56)
    (hstk : m.frame.stack = x :: rest) (hdest : isValidJumpDest m.frame.jumpDests x.toNat = true)
    (hgas : Gas.mid ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - Gas.mid, pc := x.toNat } } := by
  have hg : ¬ m.frame.gasLeft < Gas.mid := Nat.not_lt.mpr hgas
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x56 = .jump by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popNat, pop, charge, getFrame, modifyFrame, StateT.run_bind, hg, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false, hdest,
    Bool.not_true, Bool.false_eq_true]
  rfl

theorem step_jumpi_of_ne_zero (hcode : m.frame.code[m.frame.pc]? = some 0x57)
    (hstk : m.frame.stack = x :: y :: rest) (hcond : y ≠ 0)
    (hdest : isValidJumpDest m.frame.jumpDests x.toNat = true)
    (hgas : Gas.high ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - Gas.high, pc := x.toNat } } := by
  have hg : ¬ m.frame.gasLeft < Gas.high := Nat.not_lt.mpr hgas
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x57 = .jumpi by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popNat, pop, charge, getFrame, modifyFrame, StateT.run_bind, hg, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false, hdest, hcond,
    Bool.not_true, Bool.false_eq_true]
  rfl

theorem step_jumpi_of_eq_zero (hcode : m.frame.code[m.frame.pc]? = some 0x57)
    (hstk : m.frame.stack = x :: 0 :: rest) (hgas : Gas.high ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - Gas.high, pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < Gas.high := Nat.not_lt.mpr hgas
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x57 = .jumpi by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame, StateT.run_bind, hg, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false, ite_true]
  rfl

/-- `JUMPI` (either way): the new pc is `x` if `y ≠ 0` and the next instruction otherwise. -/
theorem step_jumpi (hcode : m.frame.code[m.frame.pc]? = some 0x57)
    (hstk : m.frame.stack = x :: y :: rest)
    (hdest : y ≠ 0 → isValidJumpDest m.frame.jumpDests x.toNat = true)
    (hgas : Gas.high ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - Gas.high,
      pc := if y = 0 then m.frame.pc + 1 else x.toNat } } := by
  by_cases hy : y = 0
  · subst hy
    rw [step_jumpi_of_eq_zero hcode hstk hgas, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  · rw [step_jumpi_of_ne_zero hcode hstk hy (hdest hy) hgas, ite_eq_right_of_eq_false _ _ (eq_false hy)]

/-! ## Halting -/

theorem step_stop (hcode : m.frame.code[m.frame.pc]? = some 0x00) :
    step m = finishFrame m (.success .empty) := by
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x00 = .stop by
    cases m.ctx.fork <;> rfl]
  rfl

theorem step_invalid (hcode : m.frame.code[m.frame.pc]? = some 0xfe) :
    step m = finishFrame m (.halt .invalidOpcode) := by
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0xfe = .invalid by
    cases m.ctx.fork <;> rfl]
  rfl

/-- The memory expansion cost of `RETURN`/`REVERT` reading `[off, off + size)`. -/
def outputCost (m : Machine) (off size : Word) : Nat :=
  (Gas.extendMemory m.frame.memory.size [(off.toNat, size.toNat)]).cost

/-- The machine after `RETURN`/`REVERT` popped `[off, size]` and expanded memory. -/
def outputMachine (m : Machine) (off size : Word) (rest : List Word) : Machine :=
  { m with frame := { m.frame with
    stack := rest, gasLeft := m.frame.gasLeft - outputCost m off size,
    memory := m.frame.memory.expand off.toNat size.toNat } }

/-- The output of `RETURN`/`REVERT` reading `[off, off + size)`. -/
def outputData (m : Machine) (off size : Word) : ByteArray :=
  readBytes (m.frame.memory.expand off.toNat size.toNat).bytes off.toNat size.toNat

theorem run_readOutput (hstk : m.frame.stack = x :: y :: rest)
    (hgas : outputCost m x y ≤ m.frame.gasLeft) :
    readOutput.run m = .ok (outputData m x y, outputMachine m x y rest) := by
  have hg : ¬ m.frame.gasLeft < outputCost m x y := Nat.not_lt.mpr hgas
  simp only [outputCost] at hg
  simp only [readOutput, popNat, pop, charge, getFrame, modifyFrame, StateT.run_bind, hg, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false,
    memoryExpansion, expandMemory, readMemory, List.foldl]
  rfl

theorem step_return (hcode : m.frame.code[m.frame.pc]? = some 0xf3)
    (hstk : m.frame.stack = x :: y :: rest) (hgas : outputCost m x y ≤ m.frame.gasLeft) :
    step m = finishFrame (outputMachine m x y rest) (.success (outputData m x y)) := by
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0xf3 = .«return» by
    cases m.ctx.fork <;> rfl]
  simp only [exec, StateT.run_bind, run_readOutput hstk hgas]
  rfl

theorem step_revert (hcode : m.frame.code[m.frame.pc]? = some 0xfd)
    (hstk : m.frame.stack = x :: y :: rest) (hgas : outputCost m x y ≤ m.frame.gasLeft) :
    step m = finishFrame (outputMachine m x y rest) (.revert (outputData m x y)) := by
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0xfd = .revert by
    cases m.ctx.fork <;> rfl]
  simp only [exec, StateT.run_bind, run_readOutput hstk hgas]
  rfl

theorem outputCost_zero (m : Machine) (off : Word) : outputCost m off 0 = 0 := by
  simp [outputCost, Gas.extendMemory]

theorem outputMachine_zero (m : Machine) (off : Word) (rest : List Word) :
    outputMachine m off 0 rest = { m with frame := { m.frame with stack := rest } } := by
  simp only [outputMachine, outputCost_zero, Nat.sub_zero]
  rw [show (0 : Word).toNat = 0 from rfl, Memory.expand_zero]

theorem outputData_zero (m : Machine) (off : Word) : outputData m off 0 = .empty := by
  simp only [outputData]
  rw [show (0 : Word).toNat = 0 from rfl, readBytes_zero]

/-! ## Finishing the top-level frame -/

theorem finishFrame_success_top {out : ByteArray} {o s : Nat} (hp : m.parents = [])
    (hk : m.frame.kind = .call o s) :
    finishFrame m (.success out) = .done (topLevelResult m.frame.msg.target m.world m.transient
      { gasLeft := m.frame.gasLeft, error := none, reverted := false, output := out,
        sub := m.frame.sub, target := m.frame.msg.currentTarget, kind := m.frame.kind }) := by
  simp only [finishFrame, hk, hp]

theorem finishFrame_revert_top {out : ByteArray} (hp : m.parents = []) :
    finishFrame m (.revert out) = .done (topLevelResult m.frame.msg.target m.frame.snapshot.1
      m.frame.snapshot.2
      { gasLeft := m.frame.gasLeft, error := none, reverted := true, output := out,
        sub := m.frame.sub, target := m.frame.msg.currentTarget, kind := m.frame.kind }) := by
  simp only [finishFrame, hp]

theorem finishFrame_halt_top {e : ExceptionalHalt} (hp : m.parents = []) :
    finishFrame m (.halt e) = .done (topLevelResult m.frame.msg.target m.frame.snapshot.1
      m.frame.snapshot.2
      { gasLeft := 0, error := some e, reverted := false, output := .empty,
        sub := m.frame.sub, target := m.frame.msg.currentTarget, kind := m.frame.kind }) := by
  simp only [finishFrame, hp]

theorem step_stop_top {o s : Nat} (hcode : m.frame.code[m.frame.pc]? = some 0x00)
    (hp : m.parents = []) (hk : m.frame.kind = .call o s) :
    step m = .done (topLevelResult m.frame.msg.target m.world m.transient
      { gasLeft := m.frame.gasLeft, error := none, reverted := false, output := .empty,
        sub := m.frame.sub, target := m.frame.msg.currentTarget, kind := m.frame.kind }) := by
  rw [step_stop hcode, finishFrame_success_top hp hk]

theorem step_return_top {o s : Nat} (hcode : m.frame.code[m.frame.pc]? = some 0xf3)
    (hstk : m.frame.stack = x :: y :: rest) (hgas : outputCost m x y ≤ m.frame.gasLeft)
    (hp : m.parents = []) (hk : m.frame.kind = .call o s) :
    step m = .done (topLevelResult m.frame.msg.target m.world m.transient
      { gasLeft := m.frame.gasLeft - outputCost m x y, error := none, reverted := false,
        output := outputData m x y, sub := m.frame.sub, target := m.frame.msg.currentTarget,
        kind := m.frame.kind }) := by
  rw [step_return hcode hstk hgas, finishFrame_success_top (m := outputMachine m x y rest) hp hk]
  rfl

theorem step_revert_top (hcode : m.frame.code[m.frame.pc]? = some 0xfd)
    (hstk : m.frame.stack = x :: y :: rest) (hgas : outputCost m x y ≤ m.frame.gasLeft)
    (hp : m.parents = []) :
    step m = .done (topLevelResult m.frame.msg.target m.frame.snapshot.1 m.frame.snapshot.2
      { gasLeft := m.frame.gasLeft - outputCost m x y, error := none, reverted := true,
        output := outputData m x y, sub := m.frame.sub, target := m.frame.msg.currentTarget,
        kind := m.frame.kind }) := by
  rw [step_revert hcode hstk hgas, finishFrame_revert_top (m := outputMachine m x y rest) hp]
  rfl

@[simp] theorem topLevelResult_world (t : Option Address) (w : World) (tr : TransientStorage)
    (r : ChildResult) : (topLevelResult t w tr r).world = w := by
  unfold topLevelResult; split <;> rfl

@[simp] theorem topLevelResult_success (t : Option Address) (w : World) (tr : TransientStorage)
    (r : ChildResult) : (topLevelResult t w tr r).success = r.success := by
  unfold topLevelResult; split <;> simp_all [MessageResult.success, ChildResult.success]

@[simp] theorem topLevelResult_reverted (t : Option Address) (w : World) (tr : TransientStorage)
    (r : ChildResult) : (topLevelResult t w tr r).reverted = r.reverted := by
  unfold topLevelResult; split
  · simp_all [ChildResult.success]
  · rfl

@[simp] theorem topLevelResult_gasLeft (t : Option Address) (w : World) (tr : TransientStorage)
    (r : ChildResult) : (topLevelResult t w tr r).gasLeft = r.gasLeft := by
  unfold topLevelResult; split <;> rfl

@[simp] theorem topLevelResult_output (t : Option Address) (w : World) (tr : TransientStorage)
    (r : ChildResult) : (topLevelResult t w tr r).output = r.output := by
  unfold topLevelResult; split <;> rfl

@[simp] theorem topLevelResult_error (t : Option Address) (w : World) (tr : TransientStorage)
    (r : ChildResult) : (topLevelResult t w tr r).error = r.error := by
  unfold topLevelResult; split
  · simp_all [ChildResult.success]
  · rfl

end EvmLean.Interpreter
