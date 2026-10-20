import EvmLogic.GasMono.Interface
import EvmLogic.Tactic.WpStep
import EvmLogic.Tactic.Patched

/-!
# Gas monotonicity: failure paths, for any gas, memory and stack below

`Fails code pc s`: every machine running `code` at `pc` with stack `s` ends its frame without
success. Each rule (`Fails.unOp`, `Fails.mstore`, …) reduces it to the next pc and absorbs every
exceptional halt of the instruction, so out-of-gas branches are proved once per instruction
shape, not once per step. A `FailureReverts` proof is `failureReverts_of_fails` followed by
`fails_steps`, which drives the rules over (possibly patched) code.
-/

section

namespace EvmLogic.GasMono
open EvmLean EvmLogic.Program EvmLean.Interpreter

/-! ## Not succeeding -/

/-- The frame of `m` ends, and not successfully (a revert or an exceptional halt). -/
def NoSuccess (m : Machine) : Prop := Halts m fun _ o => ∀ out, o ≠ .success out

namespace NoSuccess

variable {m m' : Machine}

theorem of_halt {e : ExceptionalHalt} (h : step m = finishFrame m (.halt e)) : NoSuccess m :=
  Halts.of_step h (.refl m) (fun _ h => Outcome.noConfusion h)

theorem of_error {b : UInt8} {e : ExceptionalHalt} (hcode : m.frame.code[m.frame.pc]? = some b)
    (h : (exec (Opcode.decode m.ctx.fork b)).run m = .error e) : NoSuccess m :=
  of_halt (step_of_exec_error hcode h)

theorem of_running (h : step m = .running m') (hs : SameFrame m m') (k : NoSuccess m') :
    NoSuccess m :=
  Halts.of_steps (Steps.of_step h hs) k

theorem of_exec_next {b : UInt8} (hcode : m.frame.code[m.frame.pc]? = some b)
    (h : ∀ r, (exec (Opcode.decode m.ctx.fork b)).run m = .ok r →
      r.1 = .next ∧ SameFrame m r.2 ∧ NoSuccess r.2) : NoSuccess m := by
  cases hr : (exec (Opcode.decode m.ctx.fork b)).run m with
  | error e => exact of_error hcode hr
  | ok r =>
    obtain ⟨h1, hs, hn⟩ := h r hr
    obtain ⟨a, m'⟩ := r
    simp only at h1
    subst h1
    exact of_running (step_of_exec_next hcode hr) hs hn

end NoSuccess

/-! ## The judgement -/

/-- Every machine running `code` at `pc` with stack `s` ends its frame without success, whatever
its gas, memory, return data, world, jump table and context. -/
def Fails (code : ByteArray) (pc : Nat) (s : List Word) : Prop :=
  ∀ m : Machine, m.frame.code = code → m.frame.pc = pc → m.frame.stack = s → NoSuccess m

/-- **`FailureReverts` from `Fails`.** -/
theorem failureReverts_of_fails {code : ByteArray} {p : Nat}
    (h : ∀ rest, Fails code p (0 :: rest)) : FailureReverts code p := by
  intro m hc hpc hhd
  cases hs : m.frame.stack with
  | nil => simp [hs] at hhd
  | cons top rest =>
    rw [hs] at hhd
    simp only [List.head?_cons, Option.some.injEq] at hhd
    subst hhd
    exact h rest m hc hpc hs

namespace Fails

variable {code : ByteArray} {pc : Nat} {b : UInt8} {x y z : Word} {rest s : List Word}

private theorem hcode_of {m : Machine} (hc : m.frame.code = code) (hpc : m.frame.pc = pc)
    (hb : code[pc]? = some b) : m.frame.code[m.frame.pc]? = some b := by
  rw [hc, hpc]; exact hb

theorem unOp {cost : Nat} {f : Word → Word}
    (hop : ∀ fk, exec (Opcode.decode fk b) = Interpreter.unOp cost f) (hb : code[pc]? = some b)
    (h : Fails code (pc + 1) (f x :: rest)) : Fails code pc (x :: rest) := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  by_cases hg : cost ≤ m.frame.gasLeft
  · by_cases hl : rest.length < 1024
    · exact .of_running (step_of_unOp hop hcode hs hl hg) (by same_frame)
        (h _ hc (by simp [hpc]) rfl)
    · apply NoSuccess.of_error (e := .stackOverflow) hcode
      have hg' : ¬ m.frame.gasLeft < cost := Nat.not_lt.mpr hg
      have hl' : Gas.stackLimit ≤ rest.length := Nat.le_of_not_lt hl
      rw [hop]
      simp only [Interpreter.unOp, Interpreter.pop, Interpreter.push, charge, advance, getFrame, modifyFrame,
        StateT.run_bind, hs, hg', hl', StateT.run_get, StateT.run_pure, StateT.run_modify,
        pure_bind, ite_true, ite_false]
      rfl
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < cost := Nat.lt_of_not_le hg
    rw [hop]
    simp only [Interpreter.unOp, Interpreter.pop, Interpreter.push, charge, advance, getFrame, modifyFrame,
      StateT.run_bind, hs, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      ite_true]
    rfl

theorem binOp {cost : Nat} {f : Word → Word → Word}
    (hop : ∀ fk, exec (Opcode.decode fk b) = Interpreter.binOp cost f) (hb : code[pc]? = some b)
    (h : Fails code (pc + 1) (f x y :: rest)) : Fails code pc (x :: y :: rest) := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  by_cases hg : cost ≤ m.frame.gasLeft
  · by_cases hl : rest.length < 1024
    · exact .of_running (step_of_binOp hop hcode hs hl hg) (by same_frame)
        (h _ hc (by simp [hpc]) rfl)
    · apply NoSuccess.of_error (e := .stackOverflow) hcode
      have hg' : ¬ m.frame.gasLeft < cost := Nat.not_lt.mpr hg
      have hl' : Gas.stackLimit ≤ rest.length := Nat.le_of_not_lt hl
      rw [hop]
      simp only [Interpreter.binOp, Interpreter.pop, Interpreter.push, charge, advance, getFrame, modifyFrame,
        StateT.run_bind, hs, hg', hl', StateT.run_get, StateT.run_pure, StateT.run_modify,
        pure_bind, ite_true, ite_false]
      rfl
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < cost := Nat.lt_of_not_le hg
    rw [hop]
    simp only [Interpreter.binOp, Interpreter.pop, Interpreter.push, charge, advance, getFrame, modifyFrame,
      StateT.run_bind, hs, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      ite_true]
    rfl

theorem pushValue {cost : Nat} {v : Machine → Word}
    (hop : ∀ fk, exec (Opcode.decode fk b) = Interpreter.pushValue cost v)
    (hb : code[pc]? = some b) (h : ∀ w, Fails code (pc + 1) (w :: s)) : Fails code pc s := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  by_cases hg : cost ≤ m.frame.gasLeft
  · by_cases hl : m.frame.stack.length < 1024
    · exact .of_running (step_of_pushValue hop hcode hl hg) (by same_frame)
        (h (v { m with frame := { m.frame with gasLeft := m.frame.gasLeft - cost } }) _ hc
          (by simp [hpc]) (by simp [hs]))
    · apply NoSuccess.of_error (e := .stackOverflow) hcode
      have hg' : ¬ m.frame.gasLeft < cost := Nat.not_lt.mpr hg
      have hl' : Gas.stackLimit ≤ m.frame.stack.length := Nat.le_of_not_lt hl
      rw [hop]
      simp only [Interpreter.pushValue, Interpreter.push, charge, advance, getFrame, modifyFrame,
        StateT.run_bind, hg', hl', StateT.run_get, StateT.run_pure, StateT.run_modify,
        pure_bind, ite_true, ite_false]
      rfl
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < cost := Nat.lt_of_not_le hg
    rw [hop]
    simp only [Interpreter.pushValue, Interpreter.push, charge, advance, getFrame, modifyFrame,
      StateT.run_bind, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      ite_true]
    rfl

theorem push {v : Word} (n : Nat) (hn : n < 33) (hb : code[pc]? = some (0x5f + n).toUInt8)
    (hval : Bytes.toWord (readBytes code (pc + 1) n) = v)
    (h : Fails code (pc + (1 + n)) (v :: s)) : Fails code pc s := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  have hval' : Bytes.toWord (readBytes m.frame.code (m.frame.pc + 1) n) = v := by
    rw [hc, hpc]; exact hval
  by_cases hg : (if n = 0 then Gas.base else Gas.veryLow) ≤ m.frame.gasLeft
  · by_cases hl : m.frame.stack.length < 1024
    · exact .of_running (step_push_val n hn hcode hval' hl hg) (by same_frame)
        (h _ hc (by simp [hpc]) (by simp [hs]))
    · apply NoSuccess.of_error (e := .stackOverflow) hcode
      have hg' : ¬ m.frame.gasLeft < (if n = 0 then Gas.base else Gas.veryLow) :=
        Nat.not_lt.mpr hg
      have hl' : Gas.stackLimit ≤ m.frame.stack.length := Nat.le_of_not_lt hl
      rw [show (0x5f + n).toUInt8 = (0x5f + (⟨n, hn⟩ : Fin 33).val).toUInt8 from rfl,
        decode_push]
      simp only [exec, Interpreter.push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hg', hl',
        StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true, ite_false]
      rfl
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < (if n = 0 then Gas.base else Gas.veryLow) := Nat.lt_of_not_le hg
    rw [show (0x5f + n).toUInt8 = (0x5f + (⟨n, hn⟩ : Fin 33).val).toUInt8 from rfl, decode_push]
    simp only [exec, Interpreter.push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hg',
      StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

theorem dup (n : Fin 16) (hb : code[pc]? = some (0x80 + n.val).toUInt8)
    (hget : s[n.val]? = some x) (h : Fails code (pc + 1) (x :: s)) : Fails code pc s := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  have hget' : m.frame.stack[n.val]? = some x := by rw [hs]; exact hget
  by_cases hg : Gas.veryLow ≤ m.frame.gasLeft
  · by_cases hl : m.frame.stack.length < 1024
    · exact .of_running (step_dup n hcode hget' hl hg) (by same_frame)
        (h _ hc (by simp [hpc]) (by simp [hs]))
    · apply NoSuccess.of_error (e := .stackOverflow) hcode
      have hg' : ¬ m.frame.gasLeft < Gas.veryLow := Nat.not_lt.mpr hg
      have hl' : Gas.stackLimit ≤ m.frame.stack.length := Nat.le_of_not_lt hl
      rw [decode_dup]
      simp only [exec, Interpreter.push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hg', hl',
        hget', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true,
        ite_false]
      rfl
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < Gas.veryLow := Nat.lt_of_not_le hg
    rw [decode_dup]
    simp only [exec, Interpreter.push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hg',
      StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

theorem swap (n : Fin 16) (hb : code[pc]? = some (0x90 + n.val).toUInt8)
    (hget : (y :: rest)[n.val + 1]? = some x)
    (h : Fails code (pc + 1) (((y :: rest).set 0 x).set (n.val + 1) y)) :
    Fails code pc (y :: rest) := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  have hget' : m.frame.stack[n.val + 1]? = some x := by rw [hs]; exact hget
  by_cases hg : Gas.veryLow ≤ m.frame.gasLeft
  · exact .of_running (step_swap n hcode hs hget' hg) (by same_frame)
      (h _ hc (by simp [hpc]) rfl)
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < Gas.veryLow := Nat.lt_of_not_le hg
    rw [decode_swap]
    simp only [exec, charge, advance, getFrame, modifyFrame, StateT.run_bind, hg',
      StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

/-- `SWAP(n+1)` on a stack that is too short: a stack underflow (or out of gas). -/
theorem swap_underflow (n : Fin 16) (hb : code[pc]? = some (0x90 + n.val).toUInt8)
    (hget : s[n.val + 1]? = none) : Fails code pc s := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  have hget' : m.frame.stack[n.val + 1]? = none := by rw [hs]; exact hget
  by_cases hg : Gas.veryLow ≤ m.frame.gasLeft
  · apply NoSuccess.of_error (e := .stackUnderflow) hcode
    have hg' : ¬ m.frame.gasLeft < Gas.veryLow := Nat.not_lt.mpr hg
    rw [decode_swap]
    simp only [exec, charge, advance, getFrame, modifyFrame, StateT.run_bind, hg', hget',
      StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false]
    split <;> first | rfl | simp_all
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < Gas.veryLow := Nat.lt_of_not_le hg
    rw [decode_swap]
    simp only [exec, charge, advance, getFrame, modifyFrame, StateT.run_bind, hg',
      StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

theorem pop (hb : code[pc]? = some 0x50) (h : Fails code (pc + 1) rest) :
    Fails code pc (x :: rest) := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  by_cases hg : Gas.base ≤ m.frame.gasLeft
  · exact .of_running (step_pop hcode hs hg) (by same_frame) (h _ hc (by simp [hpc]) rfl)
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < Gas.base := Nat.lt_of_not_le hg
    rw [show Opcode.decode m.ctx.fork 0x50 = .pop by cases m.ctx.fork <;> rfl]
    simp only [exec, Interpreter.pop, charge, advance, getFrame, modifyFrame, StateT.run_bind,
      hs, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

theorem jumpdest (hb : code[pc]? = some 0x5b) (h : Fails code (pc + 1) s) : Fails code pc s := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  by_cases hg : Gas.jumpdest ≤ m.frame.gasLeft
  · exact .of_running (step_jumpdest hcode hg) (by same_frame) (h _ hc (by simp [hpc]) hs)
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < Gas.jumpdest := Nat.lt_of_not_le hg
    rw [show Opcode.decode m.ctx.fork 0x5b = .jumpdest by cases m.ctx.fork <;> rfl]
    simp only [exec, charge, advance, getFrame, modifyFrame, StateT.run_bind, hg',
      StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

/-- `JUMP` to `x` (an invalid destination halts exceptionally, which is fine). -/
theorem jump (hb : code[pc]? = some 0x56) (h : Fails code x.toNat rest) :
    Fails code pc (x :: rest) := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  have hdec : Opcode.decode m.ctx.fork 0x56 = .jump := by cases m.ctx.fork <;> rfl
  by_cases hg : Gas.mid ≤ m.frame.gasLeft
  · by_cases hd : isValidJumpDest m.frame.jumpDests x.toNat = true
    · exact .of_running (step_jump hcode hs hd hg) (by same_frame) (h _ hc rfl rfl)
    · apply NoSuccess.of_error (e := .invalidJumpDestination) hcode
      have hg' : ¬ m.frame.gasLeft < Gas.mid := Nat.not_lt.mpr hg
      rw [hdec]
      simp only [exec, popNat, Interpreter.pop, charge, getFrame, modifyFrame, StateT.run_bind,
        hg', hs, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false]
      simp only [Bool.not_eq_true] at hd
      simp only [hd, Bool.not_false, ite_true]
      rfl
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < Gas.mid := Nat.lt_of_not_le hg
    rw [hdec]
    simp only [exec, popNat, Interpreter.pop, charge, getFrame, modifyFrame, StateT.run_bind,
      hg', hs, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

theorem jumpi_zero (hb : code[pc]? = some 0x57) (hy : y = 0) (h : Fails code (pc + 1) rest) :
    Fails code pc (x :: y :: rest) := by
  subst hy
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  by_cases hg : Gas.high ≤ m.frame.gasLeft
  · exact .of_running (step_jumpi_of_eq_zero hcode hs hg) (by same_frame)
      (h _ hc (by simp [hpc]) rfl)
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < Gas.high := Nat.lt_of_not_le hg
    rw [show Opcode.decode m.ctx.fork 0x57 = .jumpi by cases m.ctx.fork <;> rfl]
    simp only [exec, popNat, Interpreter.pop, charge, getFrame, modifyFrame, StateT.run_bind,
      hg', hs, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

theorem jumpi_ne_zero (hb : code[pc]? = some 0x57) (hy : y ≠ 0) (h : Fails code x.toNat rest) :
    Fails code pc (x :: y :: rest) := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  have hdec : Opcode.decode m.ctx.fork 0x57 = .jumpi := by cases m.ctx.fork <;> rfl
  by_cases hg : Gas.high ≤ m.frame.gasLeft
  · by_cases hd : isValidJumpDest m.frame.jumpDests x.toNat = true
    · exact .of_running (step_jumpi_of_ne_zero hcode hs hy hd hg) (by same_frame)
        (h _ hc rfl rfl)
    · apply NoSuccess.of_error (e := .invalidJumpDestination) hcode
      have hg' : ¬ m.frame.gasLeft < Gas.high := Nat.not_lt.mpr hg
      rw [hdec]
      simp only [exec, popNat, Interpreter.pop, charge, getFrame, modifyFrame, StateT.run_bind,
        hg', hs, hy, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false]
      simp only [Bool.not_eq_true] at hd
      simp only [hd, Bool.not_false, ite_true]
      rfl
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < Gas.high := Nat.lt_of_not_le hg
    rw [hdec]
    simp only [exec, popNat, Interpreter.pop, charge, getFrame, modifyFrame, StateT.run_bind,
      hg', hs, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

theorem mload (hb : code[pc]? = some 0x51) (h : ∀ w, Fails code (pc + 1) (w :: rest)) :
    Fails code pc (x :: rest) := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  have hdec : Opcode.decode m.ctx.fork 0x51 = .mload := by cases m.ctx.fork <;> rfl
  by_cases hg : Gas.veryLow + memoryCost m x 32 ≤ m.frame.gasLeft
  · by_cases hl : rest.length < 1024
    · exact .of_running (step_mload hcode hs hl hg) (by same_frame)
        (h _ _ hc (by simp [hpc]) rfl)
    · apply NoSuccess.of_error (e := .stackOverflow) hcode
      have hg' : ¬ m.frame.gasLeft < Gas.veryLow + memoryCost m x 32 := Nat.not_lt.mpr hg
      have hl' : Gas.stackLimit ≤ rest.length := Nat.le_of_not_lt hl
      simp only [memoryCost] at hg'
      rw [hdec]
      simp only [exec, popNat, Interpreter.pop, Interpreter.push, charge, advance, getFrame,
        modifyFrame, StateT.run_bind, hs, hg', hl', StateT.run_get, StateT.run_pure,
        StateT.run_modify, pure_bind, ite_true, ite_false, memoryExpansion, expandMemory,
        List.foldl]
      rfl
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < Gas.veryLow + memoryCost m x 32 := Nat.lt_of_not_le hg
    simp only [memoryCost] at hg'
    rw [hdec]
    simp only [exec, popNat, Interpreter.pop, Interpreter.push, charge, advance, getFrame,
      modifyFrame, StateT.run_bind, hs, hg', StateT.run_get, StateT.run_pure, StateT.run_modify,
      pure_bind, ite_true, memoryExpansion, expandMemory, List.foldl]
    rfl

theorem mstore (hb : code[pc]? = some 0x52) (h : Fails code (pc + 1) rest) :
    Fails code pc (x :: y :: rest) := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  by_cases hg : Gas.veryLow + memoryCost m x 32 ≤ m.frame.gasLeft
  · exact .of_running (step_mstore hcode hs hg) (by same_frame) (h _ hc (by simp [hpc]) rfl)
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < Gas.veryLow + memoryCost m x 32 := Nat.lt_of_not_le hg
    simp only [memoryCost] at hg'
    rw [show Opcode.decode m.ctx.fork 0x52 = .mstore by cases m.ctx.fork <;> rfl]
    simp only [exec, popNat, Interpreter.pop, charge, advance, getFrame, modifyFrame,
      StateT.run_bind, hs, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      ite_true, memoryExpansion, expandMemory, List.foldl]
    rfl

theorem returndatacopy (hb : code[pc]? = some 0x3e) (h : Fails code (pc + 1) rest) :
    Fails code pc (x :: y :: z :: rest) := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  have hdec : Opcode.decode m.ctx.fork 0x3e = .returndatacopy := by cases m.ctx.fork <;> rfl
  by_cases hg : Gas.veryLow + Gas.copyCost z.toNat +
      (Gas.extendMemory m.frame.memory.size [(x.toNat, z.toNat)]).cost ≤ m.frame.gasLeft
  · have hg' := Nat.not_lt.mpr hg
    by_cases hbd : y.toNat + z.toNat > m.frame.returnData.size
    · apply NoSuccess.of_error (e := .returnDataOutOfBounds) hcode
      rw [hdec]
      simp only [exec, popNat, Interpreter.pop, charge, advance, getFrame, modifyFrame,
        StateT.run_bind, hs, hg', hbd, StateT.run_get, StateT.run_pure, StateT.run_modify,
        pure_bind, ite_true, ite_false, memoryExpansion, expandMemory, List.foldl]
      rfl
    · apply NoSuccess.of_exec_next hcode
      intro r hr
      rw [hdec] at hr
      simp only [exec, popNat, Interpreter.pop, charge, advance, getFrame, modifyFrame,
        StateT.run_bind, hs, hg', hbd, StateT.run_get, StateT.run_pure, StateT.run_modify,
        pure_bind, ite_false, memoryExpansion, expandMemory, writeMemory,
        List.foldl] at hr
      split at hr <;> cases hr <;> exact ⟨rfl, by same_frame, h _ hc (by simp [hpc]) rfl⟩
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' := Nat.lt_of_not_le hg
    rw [hdec]
    simp only [exec, popNat, Interpreter.pop, charge, advance, getFrame, modifyFrame,
      StateT.run_bind, hs, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      ite_true, memoryExpansion, expandMemory, List.foldl]
    rfl

/-- `REVERT`: a revert, or an exceptional halt while expanding memory. -/
theorem revert (hb : code[pc]? = some 0xfd) : Fails code pc (x :: y :: rest) := by
  intro m hc hpc hs
  have hcode := hcode_of hc hpc hb
  by_cases hg : outputCost m x y ≤ m.frame.gasLeft
  · exact Halts.of_step (step_revert hcode hs hg) (by same_frame) (fun _ h => Outcome.noConfusion h)
  · apply NoSuccess.of_error (e := .outOfGas) hcode
    have hg' : m.frame.gasLeft < outputCost m x y := Nat.lt_of_not_le hg
    simp only [outputCost] at hg'
    rw [show Opcode.decode m.ctx.fork 0xfd = .revert by cases m.ctx.fork <;> rfl]
    simp only [exec, readOutput, popNat, Interpreter.pop, charge, getFrame, modifyFrame,
      StateT.run_bind, hg', hs, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      ite_true, memoryExpansion, expandMemory, readMemory, List.foldl]
    rfl

theorem invalid (hb : code[pc]? = some 0xfe) : Fails code pc s := by
  intro m hc hpc _
  exact .of_halt (step_invalid (hcode_of hc hpc hb))

end Fails

end EvmLogic.GasMono

end

section

/-!
## `fails_step`: driving the `Fails` rules over compiled code

The opcode byte at `pc` is read at the meta level and justified by a kernel-checked `pcode_fact`
(`EvmLogic.Tactic.Patched`), so the code may carry symbolic immutables; `PUSHn` immediates come
from `ppushFact?`, and `JUMPI` conditions are decided by `fails_cond`.
-/

namespace EvmLogic.GasMono
open EvmLean EvmLogic.Program EvmLean.Interpreter

/-! ## Instruction shapes: `unOp`, `binOp`, `pushValue` -/

theorem hop_add : ∀ fk, exec (Opcode.decode fk 0x01) = binOp Gas.veryLow (· + ·) := by
  intro fk; cases fk <;> rfl
theorem hop_mul : ∀ fk, exec (Opcode.decode fk 0x02) = binOp Gas.low (· * ·) := by
  intro fk; cases fk <;> rfl
theorem hop_sub : ∀ fk, exec (Opcode.decode fk 0x03) = binOp Gas.veryLow (· - ·) := by
  intro fk; cases fk <;> rfl
theorem hop_div : ∀ fk, exec (Opcode.decode fk 0x04) = binOp Gas.low Word.div := by
  intro fk; cases fk <;> rfl
theorem hop_lt : ∀ fk, exec (Opcode.decode fk 0x10) = binOp Gas.veryLow Word.lt := by
  intro fk; cases fk <;> rfl
theorem hop_gt : ∀ fk, exec (Opcode.decode fk 0x11) = binOp Gas.veryLow Word.gt := by
  intro fk; cases fk <;> rfl
theorem hop_eq : ∀ fk, exec (Opcode.decode fk 0x14) = binOp Gas.veryLow Word.eq := by
  intro fk; cases fk <;> rfl
theorem hop_and : ∀ fk, exec (Opcode.decode fk 0x16) = binOp Gas.veryLow (· &&& ·) := by
  intro fk; cases fk <;> rfl
theorem hop_or : ∀ fk, exec (Opcode.decode fk 0x17) = binOp Gas.veryLow (· ||| ·) := by
  intro fk; cases fk <;> rfl
theorem hop_xor : ∀ fk, exec (Opcode.decode fk 0x18) = binOp Gas.veryLow (· ^^^ ·) := by
  intro fk; cases fk <;> rfl
theorem hop_shl : ∀ fk, exec (Opcode.decode fk 0x1b) = binOp Gas.veryLow Word.shl := by
  intro fk; cases fk <;> rfl
theorem hop_shr : ∀ fk, exec (Opcode.decode fk 0x1c) = binOp Gas.veryLow Word.shr := by
  intro fk; cases fk <;> rfl
theorem hop_iszero : ∀ fk, exec (Opcode.decode fk 0x15) = unOp Gas.veryLow Word.iszero := by
  intro fk; cases fk <;> rfl
theorem hop_not : ∀ fk, exec (Opcode.decode fk 0x19) = unOp Gas.veryLow (~~~ ·) := by
  intro fk; cases fk <;> rfl
theorem hop_returndatasize : ∀ fk, exec (Opcode.decode fk 0x3d) =
    pushValue Gas.base fun m => ofNat m.frame.returnData.size := by
  intro fk; cases fk <;> rfl
theorem hop_caller : ∀ fk, exec (Opcode.decode fk 0x33) =
    pushValue Gas.base fun m => Word.ofAddress m.frame.msg.caller := by
  intro fk; cases fk <;> rfl
theorem hop_address : ∀ fk, exec (Opcode.decode fk 0x30) =
    pushValue Gas.base fun m => Word.ofAddress m.frame.msg.currentTarget := by
  intro fk; cases fk <;> rfl

/-! ## The tactic -/

open Lean Elab Tactic EvmLogic.Tactic Meta

/-- The `Fails` rule and shape lemma for an opcode of shape `unOp`/`binOp`/`pushValue`. -/
def shapeRule (b : Nat) : Option (Name × Name) :=
  let bin : List (Nat × Name) := [(0x01, ``hop_add), (0x02, ``hop_mul), (0x03, ``hop_sub),
    (0x04, ``hop_div), (0x10, ``hop_lt), (0x11, ``hop_gt), (0x14, ``hop_eq), (0x16, ``hop_and),
    (0x17, ``hop_or), (0x18, ``hop_xor), (0x1b, ``hop_shl), (0x1c, ``hop_shr)]
  let un : List (Nat × Name) := [(0x15, ``hop_iszero), (0x19, ``hop_not)]
  let pv : List (Nat × Name) := [(0x3d, ``hop_returndatasize), (0x33, ``hop_caller),
    (0x30, ``hop_address)]
  match bin.lookup b, un.lookup b, pv.lookup b with
  | some h, _, _ => some (``Fails.binOp, h)
  | _, some h, _ => some (``Fails.unOp, h)
  | _, _, some h => some (``Fails.pushValue, h)
  | _, _, _ => none

/-- `x AND 0 = 0` (a failed call's flag masks any other condition). -/
theorem word_and_zero (x : Word) : x &&& 0 = 0 := BitVec.and_zero

theorem word_zero_and (x : Word) : 0 &&& x = 0 := BitVec.zero_and

/-- Decide a `JUMPI` condition `y = 0` or `y ≠ 0`, simplifying `x &&& 0` first. -/
macro "fails_cond" : tactic =>
  `(tactic| first
    | rfl
    | decide
    | (simp only [word_and_zero, word_zero_and, BitVec.and_zero, BitVec.zero_and]
       first | rfl | decide))

/-- Normalize a `Fails` goal: pc arithmetic, jump targets, stack updates. -/
macro "fails_norm" : tactic =>
  `(tactic| try simp only [Nat.reduceAdd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    List.set_cons_zero, List.set_cons_succ])

/-- Advance a goal `Fails code pc s` by one instruction. Returns `false` (goal unchanged) if no
rule applies. -/
def failsStep : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let_expr Fails code pcE _ := t | return false
  let some pc ← (evalNat pcE).run | return false
  let some (bytes, pinfo) ← codeInfo? code | return false
  let some b := bytes[pc]? | return false
  let hb ← Term.exprToSyntax (← pcodeFact code pinfo pc b)
  let bn := b.toNat
  let saved ← saveState
  let attempt (t : TSyntax `tactic) : TacticM Bool := do
    tryCatchRuntimeEx
      (do withoutRecover (evalTactic t); return true)
      (fun _ => do saved.restore; return false)
  let tacs : List (TSyntax `tactic) ←
    if bn = 0xfd then pure [← `(tactic| exact Fails.revert $hb)]
    else if bn = 0xfe then pure [← `(tactic| exact Fails.invalid $hb)]
    else if bn = 0x50 then pure [← `(tactic| refine Fails.pop $hb ?_)]
    else if bn = 0x56 then pure [← `(tactic| refine Fails.jump $hb ?_)]
    else if bn = 0x57 then pure [← `(tactic| refine Fails.jumpi_zero $hb (by fails_cond) ?_),
      ← `(tactic| refine Fails.jumpi_ne_zero $hb (by fails_cond) ?_)]
    else if bn = 0x5b then pure [← `(tactic| refine Fails.jumpdest $hb ?_)]
    else if bn = 0x51 then pure [← `(tactic| (refine Fails.mload $hb ?_; intro))]
    else if bn = 0x52 then pure [← `(tactic| refine Fails.mstore $hb ?_)]
    else if bn = 0x3e then pure [← `(tactic| refine Fails.returndatacopy $hb ?_)]
    else if 0x5f ≤ bn ∧ bn ≤ 0x7f then do
      let n := bn - 0x5f
      let some hv ← ppushFact? code pinfo bytes pc n | pure []
      let hv ← Term.exprToSyntax hv
      let nS := Syntax.mkNumLit (toString n)
      pure [← `(tactic| refine Fails.push $nS (by decide) $hb $hv ?_)]
    else if 0x80 ≤ bn ∧ bn < 0x90 then do
      let kS := Syntax.mkNumLit (toString (bn - 0x80))
      pure [← `(tactic| refine Fails.dup ⟨$kS, by decide⟩ $hb rfl ?_)]
    else if 0x90 ≤ bn ∧ bn < 0xa0 then do
      let kS := Syntax.mkNumLit (toString (bn - 0x90))
      pure [← `(tactic| refine Fails.swap ⟨$kS, by decide⟩ $hb rfl ?_)]
    else match shapeRule bn with
      | some (rule, hop) =>
        let ruleI := mkIdent rule
        let hopI := mkIdent hop
        if rule == ``Fails.pushValue then
          pure [← `(tactic| (refine $ruleI $hopI $hb ?_; intro))]
        else pure [← `(tactic| refine $ruleI $hopI $hb ?_)]
      | none => pure []
  for tac in tacs do
    if ← attempt tac then
      if (← getGoals).isEmpty then return true
      evalTactic (← `(tactic| fails_norm))
      return true
  return false

/-- Advance a goal `Fails code pc s` by one instruction. -/
elab "fails_step" : tactic => do
  unless ← failsStep do throwError "fails_step: no rule applies to the next instruction"

/-- Repeat `fails_step` until the goal is closed or no rule applies. -/
elab "fails_steps" : tactic => do
  for _ in [0:100000] do
    if (← getGoals).isEmpty then return
    unless ← failsStep do return

end EvmLogic.GasMono

end
