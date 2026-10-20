import EvmLogic.GasMono.Interface
import EvmLogic.Tactic.WpStep

/-!
# Gas monotonicity: failure paths, for any gas, memory and stack below

`FailureReverts code p` (`GasMono.Interface`) asks that *every* machine at `pc = p` with `0` on
top of the stack (a failed call's success flag) ends its frame without success: for symbolic
gas, memory, return data, world, jump table and stack below the top. Splitting every step of
the general calculus on "enough gas or not" is slow, because the out-of-gas branch is computed
from scratch each time.

Here the out-of-gas branches are proved **once per instruction shape**. The judgement is

`Fails code pc s`: every machine running `code` at `pc` with stack exactly `s` ends its frame
without success (`NoSuccess`).

It mentions neither gas nor memory: each rule (`Fails.unOp`, `Fails.mstore`, …) reduces `Fails`
at `pc` to `Fails` at the next pc with the next stack, and absorbs inside its proof every way
the instruction can halt exceptionally (out of gas, stack overflow, invalid jump destination,
return data out of bounds): those are not successes either. Values that depend on the parts of
the machine we do not track (`MLOAD`, `RETURNDATASIZE`, …) become universally quantified words.
`REVERT` and `INVALID` close the goal (`Fails.revert`, `Fails.invalid`).

`fails_step` applies the rule for the opcode at `pc` (reading the byte, and `PUSHn` immediates,
with the kernel-checked facts of `EvmLeanProofs.Solidity.ExtraPatchedWP`, so the code may carry
symbolic immutables), and `fails_steps` repeats it. A `FailureReverts` proof is then
`failureReverts_of_fails` followed by `fails_steps`.
-/

namespace EvmLean.Program.GasMono

open Interpreter

/-! ## Not succeeding -/

/-- The frame of `m` ends, and not successfully (a revert or an exceptional halt). -/
def NoSuccess (m : Machine) : Prop := Halts m fun _ o => ∀ out, o ≠ .success out

namespace NoSuccess

variable {m m' : Machine}

/-- An exceptional halt is not a success. -/
theorem of_halt {e : ExceptionalHalt} (h : step m = finishFrame m (.halt e)) : NoSuccess m :=
  Halts.of_step h (.refl m) (fun _ h => Outcome.noConfusion h)

/-- An instruction that halts exceptionally. -/
theorem of_error {b : UInt8} {e : ExceptionalHalt} (hcode : m.frame.code[m.frame.pc]? = some b)
    (h : (exec (Opcode.decode m.ctx.fork b)).run m = .error e) : NoSuccess m :=
  of_halt (step_of_exec_error hcode h)

/-- A step in the frame. -/
theorem of_running (h : step m = .running m') (hs : SameFrame m m') (k : NoSuccess m') :
    NoSuccess m :=
  Halts.of_steps (Steps.of_step h hs) k

/-- An instruction that either halts exceptionally or continues (`.next`) to a machine in the
same frame that does not succeed. -/
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

/-- The byte at the machine's pc. -/
private theorem hcode_of {m : Machine} (hc : m.frame.code = code) (hpc : m.frame.pc = pc)
    (hb : code[pc]? = some b) : m.frame.code[m.frame.pc]? = some b := by
  rw [hc, hpc]; exact hb

/-- Instructions of shape `unOp cost f`. -/
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

/-- Instructions of shape `binOp cost f`. -/
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

/-- Instructions of shape `pushValue cost v`: the pushed value is arbitrary. -/
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

/-- `PUSHn` (`n ≤ 32`) of the value `v` read from the code. -/
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

/-- `DUP(n+1)`. -/
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

/-- `SWAP(n+1)`. -/
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

/-- `POP`. -/
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

/-- `JUMPDEST`. -/
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

/-- `JUMPI` with a zero condition: fall through. -/
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

/-- `JUMPI` with a non-zero condition: jump to `x` (or halt on an invalid destination). -/
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

/-- `MLOAD`: the loaded word is arbitrary. -/
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

/-- `MSTORE`. -/
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

/-- `RETURNDATACOPY`. -/
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

/-- `INVALID`. -/
theorem invalid (hb : code[pc]? = some 0xfe) : Fails code pc s := by
  intro m hc hpc _
  exact .of_halt (step_invalid (hcode_of hc hpc hb))

end Fails

end EvmLean.Program.GasMono
