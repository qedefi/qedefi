import EvmLogic.Step.Basic

/-!
# Step lemmas: stack instructions

`PUSH0`–`PUSH32`, `DUP1`–`DUP16`, `SWAP1`–`SWAP16`, `POP`.

`PUSHn` pushes `Bytes.toWord (readBytes code (pc + 1) n)` (immediate bytes past the end of
the code read as zero); `EvmLeanProofs.StepPush` evaluates it for `PUSH1` and `PUSH2`.
`DUPn` and `SWAPn` are stated with the accessed stack element given by a `getElem?`
hypothesis, so they apply to stacks of any shape.
-/

namespace EvmLean.Interpreter

variable {m : Machine} {x y : Word} {rest : List Word}

/-- Decoding of `PUSH0`–`PUSH32` (fork-independent). -/
theorem decode_push (fk : Fork) (n : Fin 33) :
    Opcode.decode fk (0x5f + n.val).toUInt8 = .push n := by
  revert n; cases fk <;> decide

/-- Decoding of `DUP1`–`DUP16` (fork-independent). -/
theorem decode_dup (fk : Fork) (n : Fin 16) :
    Opcode.decode fk (0x80 + n.val).toUInt8 = .dup n := by
  revert n; cases fk <;> decide

/-- Decoding of `SWAP1`–`SWAP16` (fork-independent). -/
theorem decode_swap (fk : Fork) (n : Fin 16) :
    Opcode.decode fk (0x90 + n.val).toUInt8 = .swap n := by
  revert n; cases fk <;> decide

/-- Decoding of `LOG0`–`LOG4` (fork-independent). -/
theorem decode_log (fk : Fork) (n : Fin 5) :
    Opcode.decode fk (0xa0 + n.val).toUInt8 = .log n := by
  revert n; cases fk <;> decide

/-- `PUSHn` (`n = 0` is `PUSH0`, costing 2; otherwise 3): push the `n` immediate bytes. -/
theorem step_push (n : Fin 33) (hcode : m.frame.code[m.frame.pc]? = some (0x5f + n.val).toUInt8)
    (hlen : m.frame.stack.length < 1024)
    (hgas : (if n.val = 0 then Gas.base else Gas.veryLow) ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := Bytes.toWord (readBytes m.frame.code (m.frame.pc + 1) n.val) :: m.frame.stack,
      gasLeft := m.frame.gasLeft - (if n.val = 0 then Gas.base else Gas.veryLow),
      pc := m.frame.pc + (1 + n.val) } } := by
  have hg : ¬ m.frame.gasLeft < (if n.val = 0 then Gas.base else Gas.veryLow) :=
    Nat.not_lt.mpr hgas
  have hl : ¬ Gas.stackLimit ≤ m.frame.stack.length := Nat.not_le.mpr hlen
  rw [step_eq_of_code hcode, decode_push]
  simp only [exec, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hg,
    hl, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false]
  rfl

/-- The value pushed by `PUSH0`. -/
theorem toWord_readBytes_zero (b : ByteArray) (off : Nat) :
    Bytes.toWord (readBytes b off 0) = 0 := by
  rw [readBytes_zero]
  rfl

/-- `PUSH0`: push zero. -/
theorem step_push0 (hcode : m.frame.code[m.frame.pc]? = some 0x5f)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := 0 :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } := by
  rw [step_push 0 hcode hlen hgas]
  simp only [Fin.val_zero, toWord_readBytes_zero, ite_true, Nat.add_zero]

/-- `POP`. -/
theorem step_pop (hcode : m.frame.code[m.frame.pc]? = some 0x50)
    (hstk : m.frame.stack = x :: rest) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - Gas.base, pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < Gas.base := Nat.not_lt.mpr hgas
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x50 = .pop by cases m.ctx.fork <;> rfl]
  simp only [exec, pop, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk, hg,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false]
  rfl

/-- `DUP(n+1)`: push a copy of the `n`-th stack item (0 = top). -/
theorem step_dup (n : Fin 16) (hcode : m.frame.code[m.frame.pc]? = some (0x80 + n.val).toUInt8)
    (hget : m.frame.stack[n.val]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < Gas.veryLow := Nat.not_lt.mpr hgas
  have hl : ¬ Gas.stackLimit ≤ m.frame.stack.length := Nat.not_le.mpr hlen
  rw [step_eq_of_code hcode, decode_dup]
  simp only [exec, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hg, hget,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false, hl]
  rfl

/-- `SWAP(n+1)`: exchange the top with the `(n+1)`-th stack item. -/
theorem step_swap (n : Fin 16) (hcode : m.frame.code[m.frame.pc]? = some (0x90 + n.val).toUInt8)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[n.val + 1]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := ((y :: rest).set 0 x).set (n.val + 1) y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < Gas.veryLow := Nat.not_lt.mpr hgas
  rw [hstk] at hget
  rw [step_eq_of_code hcode, decode_swap]
  simp only [exec, charge, advance, getFrame, modifyFrame, StateT.run_bind, hg, hget, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false]
  rfl

/-- `DUP1`. -/
theorem step_dup1 (hcode : m.frame.code[m.frame.pc]? = some 0x80)
    (hget : m.frame.stack[0]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 0 hcode hget hlen hgas

/-- `DUP2`. -/
theorem step_dup2 (hcode : m.frame.code[m.frame.pc]? = some 0x81)
    (hget : m.frame.stack[1]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 1 hcode hget hlen hgas

/-- `DUP3`. -/
theorem step_dup3 (hcode : m.frame.code[m.frame.pc]? = some 0x82)
    (hget : m.frame.stack[2]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 2 hcode hget hlen hgas

/-- `DUP4`. -/
theorem step_dup4 (hcode : m.frame.code[m.frame.pc]? = some 0x83)
    (hget : m.frame.stack[3]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 3 hcode hget hlen hgas

/-- `DUP5`. -/
theorem step_dup5 (hcode : m.frame.code[m.frame.pc]? = some 0x84)
    (hget : m.frame.stack[4]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 4 hcode hget hlen hgas

/-- `DUP6`. -/
theorem step_dup6 (hcode : m.frame.code[m.frame.pc]? = some 0x85)
    (hget : m.frame.stack[5]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 5 hcode hget hlen hgas

/-- `DUP7`. -/
theorem step_dup7 (hcode : m.frame.code[m.frame.pc]? = some 0x86)
    (hget : m.frame.stack[6]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 6 hcode hget hlen hgas

/-- `DUP8`. -/
theorem step_dup8 (hcode : m.frame.code[m.frame.pc]? = some 0x87)
    (hget : m.frame.stack[7]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 7 hcode hget hlen hgas

/-- `DUP9`. -/
theorem step_dup9 (hcode : m.frame.code[m.frame.pc]? = some 0x88)
    (hget : m.frame.stack[8]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 8 hcode hget hlen hgas

/-- `DUP10`. -/
theorem step_dup10 (hcode : m.frame.code[m.frame.pc]? = some 0x89)
    (hget : m.frame.stack[9]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 9 hcode hget hlen hgas

/-- `DUP11`. -/
theorem step_dup11 (hcode : m.frame.code[m.frame.pc]? = some 0x8a)
    (hget : m.frame.stack[10]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 10 hcode hget hlen hgas

/-- `DUP12`. -/
theorem step_dup12 (hcode : m.frame.code[m.frame.pc]? = some 0x8b)
    (hget : m.frame.stack[11]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 11 hcode hget hlen hgas

/-- `DUP13`. -/
theorem step_dup13 (hcode : m.frame.code[m.frame.pc]? = some 0x8c)
    (hget : m.frame.stack[12]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 12 hcode hget hlen hgas

/-- `DUP14`. -/
theorem step_dup14 (hcode : m.frame.code[m.frame.pc]? = some 0x8d)
    (hget : m.frame.stack[13]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 13 hcode hget hlen hgas

/-- `DUP15`. -/
theorem step_dup15 (hcode : m.frame.code[m.frame.pc]? = some 0x8e)
    (hget : m.frame.stack[14]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 14 hcode hget hlen hgas

/-- `DUP16`. -/
theorem step_dup16 (hcode : m.frame.code[m.frame.pc]? = some 0x8f)
    (hget : m.frame.stack[15]? = some x) (hlen : m.frame.stack.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_dup 15 hcode hget hlen hgas

/-- `SWAP1`. -/
theorem step_swap1 (hcode : m.frame.code[m.frame.pc]? = some 0x90)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[1]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 0 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 0 hcode hstk hget hgas

/-- `SWAP2`. -/
theorem step_swap2 (hcode : m.frame.code[m.frame.pc]? = some 0x91)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[2]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 1 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 1 hcode hstk hget hgas

/-- `SWAP3`. -/
theorem step_swap3 (hcode : m.frame.code[m.frame.pc]? = some 0x92)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[3]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 2 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 2 hcode hstk hget hgas

/-- `SWAP4`. -/
theorem step_swap4 (hcode : m.frame.code[m.frame.pc]? = some 0x93)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[4]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 3 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 3 hcode hstk hget hgas

/-- `SWAP5`. -/
theorem step_swap5 (hcode : m.frame.code[m.frame.pc]? = some 0x94)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[5]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 4 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 4 hcode hstk hget hgas

/-- `SWAP6`. -/
theorem step_swap6 (hcode : m.frame.code[m.frame.pc]? = some 0x95)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[6]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 5 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 5 hcode hstk hget hgas

/-- `SWAP7`. -/
theorem step_swap7 (hcode : m.frame.code[m.frame.pc]? = some 0x96)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[7]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 6 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 6 hcode hstk hget hgas

/-- `SWAP8`. -/
theorem step_swap8 (hcode : m.frame.code[m.frame.pc]? = some 0x97)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[8]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 7 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 7 hcode hstk hget hgas

/-- `SWAP9`. -/
theorem step_swap9 (hcode : m.frame.code[m.frame.pc]? = some 0x98)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[9]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 8 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 8 hcode hstk hget hgas

/-- `SWAP10`. -/
theorem step_swap10 (hcode : m.frame.code[m.frame.pc]? = some 0x99)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[10]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 9 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 9 hcode hstk hget hgas

/-- `SWAP11`. -/
theorem step_swap11 (hcode : m.frame.code[m.frame.pc]? = some 0x9a)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[11]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 10 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 10 hcode hstk hget hgas

/-- `SWAP12`. -/
theorem step_swap12 (hcode : m.frame.code[m.frame.pc]? = some 0x9b)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[12]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 11 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 11 hcode hstk hget hgas

/-- `SWAP13`. -/
theorem step_swap13 (hcode : m.frame.code[m.frame.pc]? = some 0x9c)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[13]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 12 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 12 hcode hstk hget hgas

/-- `SWAP14`. -/
theorem step_swap14 (hcode : m.frame.code[m.frame.pc]? = some 0x9d)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[14]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 13 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 13 hcode hstk hget hgas

/-- `SWAP15`. -/
theorem step_swap15 (hcode : m.frame.code[m.frame.pc]? = some 0x9e)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[15]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 14 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 14 hcode hstk hget hgas

/-- `SWAP16`. -/
theorem step_swap16 (hcode : m.frame.code[m.frame.pc]? = some 0x9f)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[16]? = some x)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := x :: rest.set 15 y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } :=
  step_swap 15 hcode hstk hget hgas

end EvmLean.Interpreter
