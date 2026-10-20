import EvmLean

/-!
# Step lemmas: generic infrastructure

Per-opcode step lemmas take the byte at `pc` (`hcode`), the stack shape (`hstk`, its variables
found by unification), and sufficient gas, and conclude `step m = .running { m with … }` with
the exact cost; they hold for every fork and `Crypto` (decoding is fork-independent except
`0x1e`, `CLZ`). This file has the shared reductions: `step_eq_of_code`, the instruction shapes
`binOp`/`unOp`/`ternOp`/`pushValue`, and the `run` equations used by symbolic execution.
-/

section

namespace EvmLean.Interpreter

/-! ## `run` -/

/-- One step of `run` when `step` continues. -/
theorem run_succ_of_running {m m' : Machine} {n : Nat} (h : step m = .running m') :
    run (n + 1) m = run n m' := by
  simp only [run, h]

/-- One step of `run` when `step` finishes the top-level frame. -/
theorem run_succ_of_done {m : Machine} {r : MessageResult} {n : Nat} (h : step m = .done r) :
    run (n + 1) m = .ok r := by
  simp only [run, h]

theorem run_add_of_ok {m : Machine} {r : MessageResult} {n : Nat} (h : run n m = .ok r)
    (k : Nat) : run (n + k) m = .ok r := by
  induction n generalizing m with
  | zero => simp [run] at h
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [run] at h ⊢
    split at h
    · exact h
    · exact ih h

/-! ## `step` for a known byte -/

/-- `step` when the byte at `pc` is known: decode it and run `exec`. -/
theorem step_eq_of_code {m : Machine} {b : UInt8} (hcode : m.frame.code[m.frame.pc]? = some b) :
    step m = match (exec (Opcode.decode m.ctx.fork b)).run m with
      | .error e => finishFrame m (.halt e)
      | .ok (.next, m') => .running m'
      | .ok (.stop out, m') => finishFrame m' (.success out)
      | .ok (.revert out, m') => finishFrame m' (.revert out)
      | .ok (.call req, m') => .running (launchCall m' req)
      | .ok (.create msg, m') => .running (launchCreate m' msg) := by
  rw [getElem?_eq_some_iff] at hcode
  obtain ⟨hlt, hb⟩ := hcode
  simp only [step, hlt, dite_true, hb]
  rfl

theorem step_of_exec_next {m m' : Machine} {b : UInt8}
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (hexec : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m')) :
    step m = .running m' := by
  rw [step_eq_of_code hcode, hexec]

theorem step_of_exec_stop {m m' : Machine} {b : UInt8} {out : ByteArray}
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (hexec : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.stop out, m')) :
    step m = finishFrame m' (.success out) := by
  rw [step_eq_of_code hcode, hexec]

theorem step_of_exec_revert {m m' : Machine} {b : UInt8} {out : ByteArray}
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (hexec : (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.revert out, m')) :
    step m = finishFrame m' (.revert out) := by
  rw [step_eq_of_code hcode, hexec]

theorem step_of_exec_error {m : Machine} {b : UInt8} {e : ExceptionalHalt}
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (hexec : (exec (Opcode.decode m.ctx.fork b)).run m = .error e) :
    step m = finishFrame m (.halt e) := by
  rw [step_eq_of_code hcode, hexec]

theorem step_of_pc_ge {m : Machine} (h : m.frame.code.size ≤ m.frame.pc) :
    step m = finishFrame m (.success .empty) := by
  simp only [step, Nat.not_lt.mpr h, dite_false]

/-! ## Zero-length reads -/

theorem readBytes_zero (b : ByteArray) (off : Nat) : readBytes b off 0 = .empty := by
  apply ByteArray.size_eq_zero_iff.mp
  unfold readBytes Bytes.readPadded Bytes.zeros
  split
  · rfl
  · split
    · rw [ByteArray.size_append, ByteArray.size_extract]
      simp only [ByteArray.size, Array.size_replicate]
      omega
    · rfl

theorem Memory.expand_zero (mem : Memory) (off : Nat) : mem.expand off 0 = mem := by
  simp only [Memory.expand, Memory.wordsAfter, ite_true, Memory.words, Memory.size]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (Nat.mul_div_le _ _))]

/-! ## Instruction shapes -/

/-- Generic step lemmas for the instruction shapes `binOp`, `unOp`, `ternOp`, `pushValue`. -/
theorem step_of_binOp {m : Machine} {b : UInt8} {cost : Nat} {f : Word → Word → Word}
    {x y : Word} {rest : List Word}
    (hop : ∀ fk, exec (Opcode.decode fk b) = binOp cost f)
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : cost ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := f x y :: rest, gasLeft := m.frame.gasLeft - cost, pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < cost := Nat.not_lt.mpr hgas
  have hl : ¬ Gas.stackLimit ≤ rest.length := Nat.not_le.mpr hlen
  rw [step_eq_of_code hcode, hop]
  simp only [binOp, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk, hg,
    hl, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false]
  rfl

theorem step_of_unOp {m : Machine} {b : UInt8} {cost : Nat} {f : Word → Word}
    {x : Word} {rest : List Word}
    (hop : ∀ fk, exec (Opcode.decode fk b) = unOp cost f)
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (hstk : m.frame.stack = x :: rest) (hlen : rest.length < 1024)
    (hgas : cost ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := f x :: rest, gasLeft := m.frame.gasLeft - cost, pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < cost := Nat.not_lt.mpr hgas
  have hl : ¬ Gas.stackLimit ≤ rest.length := Nat.not_le.mpr hlen
  rw [step_eq_of_code hcode, hop]
  simp only [unOp, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk, hg,
    hl, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false]
  rfl

theorem step_of_ternOp {m : Machine} {b : UInt8} {cost : Nat} {f : Word → Word → Word → Word}
    {x y z : Word} {rest : List Word}
    (hop : ∀ fk, exec (Opcode.decode fk b) = ternOp cost f)
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (hstk : m.frame.stack = x :: y :: z :: rest) (hlen : rest.length < 1024)
    (hgas : cost ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := f x y z :: rest, gasLeft := m.frame.gasLeft - cost, pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < cost := Nat.not_lt.mpr hgas
  have hl : ¬ Gas.stackLimit ≤ rest.length := Nat.not_le.mpr hlen
  rw [step_eq_of_code hcode, hop]
  simp only [ternOp, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk, hg,
    hl, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false]
  rfl

/-- The value is computed from the machine after the gas charge (only `GAS` observes it). -/
theorem step_of_pushValue {m : Machine} {b : UInt8} {cost : Nat} {v : Machine → Word}
    (hop : ∀ fk, exec (Opcode.decode fk b) = pushValue cost v)
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (hlen : m.frame.stack.length < 1024) (hgas : cost ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := v { m with frame := { m.frame with gasLeft := m.frame.gasLeft - cost } }
        :: m.frame.stack,
      gasLeft := m.frame.gasLeft - cost, pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < cost := Nat.not_lt.mpr hgas
  have hl : ¬ Gas.stackLimit ≤ m.frame.stack.length := Nat.not_le.mpr hlen
  rw [step_eq_of_code hcode, hop]
  simp only [pushValue, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hg,
    hl, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false]
  rfl

end EvmLean.Interpreter

end

section

/-! ## From `processMessageCall` to `run` -/

namespace EvmLean.Interpreter

theorem applyTopLevelDelegation_eq {ctx : Context} {isPre : Address → Bool} {w : World}
    {msg : Message} (h : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? msg.code = none) :
    applyTopLevelDelegation ctx isPre w msg = (w, msg, 0) := by
  unfold applyTopLevelDelegation
  split
  · rfl
  · rename_i hf
    have hauth : ctx.tx.authorizations = [] := h.resolve_left hf
    split
    · rfl
    · rfl
    · simp only [hauth, List.isEmpty_nil, ite_true, hdel]

/-- `processMessageCall` is `run` from the machine `initMachine` sets up, when EIP-7702
delegation does nothing. -/
theorem processMessageCall_eq_run {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {m : Machine} (h : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? msg.code = none)
    (hinit : initMachine (PrecompileImpl.standard ctx) ctx w tr msg = .inr m) (fuel : Nat) :
    processMessageCall fuel ctx w tr msg = run fuel m := by
  simp only [processMessageCall, processMessageCallWith, applyTopLevelDelegation_eq h hdel,
    hinit, Int.add_zero]
  cases run fuel m <;> rfl

/-- `initMachine` for a call to a non-precompile, with no value moving, at depth zero. -/
theorem initMachine_call {pre : PrecompileImpl} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {a : Address} (htarget : msg.target = some a)
    (hcode : msg.codeAddress = some a) (hpre : pre.isPrecompile a = false)
    (hvalue : msg.value = 0) (hdepth : msg.depth = 0) :
    initMachine pre ctx w tr msg = .inr
      { ctx, precompiles := pre, world := w, transient := tr, originalWorld := w,
        createdAccounts := ∅, frame := Frame.init msg (.call 0 0) (w, tr), parents := [] } := by
  simp only [initMachine, hdepth, htarget, hvalue, transferValue, precompileOf, hcode, hpre,
    Gas.stackDepthLimit]
  simp
end EvmLean.Interpreter

end
