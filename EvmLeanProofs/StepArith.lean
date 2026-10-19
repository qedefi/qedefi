import EvmLeanProofs.StepBasic

/-!
# Step lemmas: arithmetic, comparison and bitwise instructions

One lemma per opcode, each an instance of `step_of_binOp`, `step_of_unOp` or
`step_of_ternOp`. The top of the stack is the first operand (`x`), as in the reference:
`SUB` computes `x - y`, `LT` computes `x < y`, `SHL` shifts `y` by `x`.

All lemmas hold for every fork and every `Crypto`; see `EvmLeanProofs.StepBasic` for the
shape of the hypotheses.
-/

namespace EvmLean.Interpreter

variable {m : Machine} {x y z : Word} {rest : List Word}

/-- `ADD`: wrapping addition. -/
theorem step_add (hcode : m.frame.code[m.frame.pc]? = some 0x01)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (x + y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `MUL`: wrapping multiplication. -/
theorem step_mul (hcode : m.frame.code[m.frame.pc]? = some 0x02)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.low ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (x * y) :: rest, gasLeft := m.frame.gasLeft - Gas.low, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `SUB`: wrapping subtraction (top minus second). -/
theorem step_sub (hcode : m.frame.code[m.frame.pc]? = some 0x03)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (x - y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `DIV`: unsigned division (zero divisor gives zero). -/
theorem step_div (hcode : m.frame.code[m.frame.pc]? = some 0x04)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.low ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.div x y) :: rest, gasLeft := m.frame.gasLeft - Gas.low, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `SDIV`: signed division. -/
theorem step_sdiv (hcode : m.frame.code[m.frame.pc]? = some 0x05)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.low ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.sdiv x y) :: rest, gasLeft := m.frame.gasLeft - Gas.low, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `MOD`: unsigned remainder (zero modulus gives zero). -/
theorem step_mod (hcode : m.frame.code[m.frame.pc]? = some 0x06)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.low ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.mod x y) :: rest, gasLeft := m.frame.gasLeft - Gas.low, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `SMOD`: signed remainder. -/
theorem step_smod (hcode : m.frame.code[m.frame.pc]? = some 0x07)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.low ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.smod x y) :: rest, gasLeft := m.frame.gasLeft - Gas.low, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `SIGNEXTEND`. -/
theorem step_signextend (hcode : m.frame.code[m.frame.pc]? = some 0x0b)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.low ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.signextend x y) :: rest, gasLeft := m.frame.gasLeft - Gas.low, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `LT`: unsigned `x < y`. -/
theorem step_lt (hcode : m.frame.code[m.frame.pc]? = some 0x10)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.lt x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `GT`: unsigned `x > y`. -/
theorem step_gt (hcode : m.frame.code[m.frame.pc]? = some 0x11)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.gt x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `SLT`: signed `x < y`. -/
theorem step_slt (hcode : m.frame.code[m.frame.pc]? = some 0x12)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.slt x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `SGT`: signed `x > y`. -/
theorem step_sgt (hcode : m.frame.code[m.frame.pc]? = some 0x13)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.sgt x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `EQ`. -/
theorem step_eq (hcode : m.frame.code[m.frame.pc]? = some 0x14)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.eq x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `AND`. -/
theorem step_and (hcode : m.frame.code[m.frame.pc]? = some 0x16)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (x &&& y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `OR`. -/
theorem step_or (hcode : m.frame.code[m.frame.pc]? = some 0x17)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (x ||| y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `XOR`. -/
theorem step_xor (hcode : m.frame.code[m.frame.pc]? = some 0x18)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (x ^^^ y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `BYTE`: byte `x` of `y`. -/
theorem step_byte (hcode : m.frame.code[m.frame.pc]? = some 0x1a)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.byte x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `SHL`: `y` shifted left by `x`. -/
theorem step_shl (hcode : m.frame.code[m.frame.pc]? = some 0x1b)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.shl x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `SHR`: `y` shifted right by `x`. -/
theorem step_shr (hcode : m.frame.code[m.frame.pc]? = some 0x1c)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.shr x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `SAR`: `y` arithmetically shifted right by `x`. -/
theorem step_sar (hcode : m.frame.code[m.frame.pc]? = some 0x1d)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.sar x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_binOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `ISZERO`. -/
theorem step_iszero (hcode : m.frame.code[m.frame.pc]? = some 0x15)
    (hstk : m.frame.stack = x :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.iszero x) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_unOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `NOT`. -/
theorem step_not (hcode : m.frame.code[m.frame.pc]? = some 0x19)
    (hstk : m.frame.stack = x :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (~~~x) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } :=
  step_of_unOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `ADDMOD`: `(x + y) mod z` without wrap-around. -/
theorem step_addmod (hcode : m.frame.code[m.frame.pc]? = some 0x08)
    (hstk : m.frame.stack = x :: y :: z :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.mid ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.addmod x y z) :: rest, gasLeft := m.frame.gasLeft - Gas.mid, pc := m.frame.pc + 1 } } :=
  step_of_ternOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `MULMOD`: `(x * y) mod z` without wrap-around. -/
theorem step_mulmod (hcode : m.frame.code[m.frame.pc]? = some 0x09)
    (hstk : m.frame.stack = x :: y :: z :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.mid ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := (Word.mulmod x y z) :: rest, gasLeft := m.frame.gasLeft - Gas.mid, pc := m.frame.pc + 1 } } :=
  step_of_ternOp (fun fk => by cases fk <;> rfl) hcode hstk hlen hgas

/-- `EXP`: `x ^ y` modulo `2²⁵⁶`, costing `10 + 50 · bytes(y)`. -/
theorem step_exp (hcode : m.frame.code[m.frame.pc]? = some 0x0a)
    (hstk : m.frame.stack = x :: y :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.expCost y.toNat ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := Word.exp x y :: rest, gasLeft := m.frame.gasLeft - Gas.expCost y.toNat,
      pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < Gas.expCost y.toNat := Nat.not_lt.mpr hgas
  have hl : ¬ Gas.stackLimit ≤ rest.length := Nat.not_le.mpr hlen
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x0a = .exp by cases m.ctx.fork <;> rfl]
  simp only [exec, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk, hg,
    hl, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false]
  rfl

end EvmLean.Interpreter
