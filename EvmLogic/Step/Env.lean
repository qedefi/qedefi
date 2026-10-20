import EvmLogic.Step.Basic

/-!
# Step lemmas: environment instructions

Instructions that push a value read from the message, the context, the world or the frame
(instances of `step_of_pushValue`), and `CALLDATALOAD`.
-/

namespace EvmLean.Interpreter

variable {m : Machine} {x : Word} {rest : List Word}

/-- `ADDRESS`: the executing account. -/
theorem step_address (hcode : m.frame.code[m.frame.pc]? = some 0x30)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := Word.ofAddress m.frame.msg.currentTarget :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `ORIGIN`: the transaction sender. -/
theorem step_origin (hcode : m.frame.code[m.frame.pc]? = some 0x32)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := Word.ofAddress m.ctx.tx.origin :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `CALLER`: the message sender. -/
theorem step_caller (hcode : m.frame.code[m.frame.pc]? = some 0x33)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := Word.ofAddress m.frame.msg.caller :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `CALLVALUE`. -/
theorem step_callvalue (hcode : m.frame.code[m.frame.pc]? = some 0x34)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := m.frame.msg.value :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `CALLDATASIZE`. -/
theorem step_calldatasize (hcode : m.frame.code[m.frame.pc]? = some 0x36)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := ofNat m.frame.msg.data.size :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `CODESIZE`. -/
theorem step_codesize (hcode : m.frame.code[m.frame.pc]? = some 0x38)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := ofNat m.frame.code.size :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `GASPRICE`. -/
theorem step_gasprice (hcode : m.frame.code[m.frame.pc]? = some 0x3a)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := ofNat m.ctx.tx.gasPrice :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `RETURNDATASIZE`. -/
theorem step_returndatasize (hcode : m.frame.code[m.frame.pc]? = some 0x3d)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := ofNat m.frame.returnData.size :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `COINBASE`. -/
theorem step_coinbase (hcode : m.frame.code[m.frame.pc]? = some 0x41)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := Word.ofAddress m.ctx.block.coinbase :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `TIMESTAMP`. -/
theorem step_timestamp (hcode : m.frame.code[m.frame.pc]? = some 0x42)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := ofNat m.ctx.block.timestamp :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `NUMBER`. -/
theorem step_number (hcode : m.frame.code[m.frame.pc]? = some 0x43)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := ofNat m.ctx.block.number :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `PREVRANDAO`. -/
theorem step_prevrandao (hcode : m.frame.code[m.frame.pc]? = some 0x44)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := m.ctx.block.prevRandao :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `GASLIMIT`. -/
theorem step_gaslimit (hcode : m.frame.code[m.frame.pc]? = some 0x45)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := ofNat m.ctx.block.gasLimit :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `CHAINID`. -/
theorem step_chainid (hcode : m.frame.code[m.frame.pc]? = some 0x46)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := ofNat m.ctx.block.chainId :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `SELFBALANCE`. -/
theorem step_selfbalance (hcode : m.frame.code[m.frame.pc]? = some 0x47)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.fastStep ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := m.world.balance m.frame.msg.currentTarget :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.fastStep,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `BASEFEE`. -/
theorem step_basefee (hcode : m.frame.code[m.frame.pc]? = some 0x48)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := ofNat m.ctx.block.baseFee :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `PC`: the address of this instruction. -/
theorem step_pc (hcode : m.frame.code[m.frame.pc]? = some 0x58)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := ofNat m.frame.pc :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `MSIZE`. -/
theorem step_msize (hcode : m.frame.code[m.frame.pc]? = some 0x59)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := ofNat m.frame.memory.size :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `GAS`: gas left after this instruction's charge. -/
theorem step_gas (hcode : m.frame.code[m.frame.pc]? = some 0x5a)
    (hlen : m.frame.stack.length < 1024) (hgas : Gas.base ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := ofNat (m.frame.gasLeft - Gas.base) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } :=
  step_of_pushValue (fun fk => by cases fk <;> rfl) hcode hlen hgas

/-- `CALLDATALOAD`: the 32 calldata bytes at offset `x`, zero-padded. -/
theorem step_calldataload (hcode : m.frame.code[m.frame.pc]? = some 0x35)
    (hstk : m.frame.stack = x :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.veryLow ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := Bytes.toWord (readBytes m.frame.msg.data x.toNat 32) :: rest,
      gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < Gas.veryLow := Nat.not_lt.mpr hgas
  have hl : ¬ Gas.stackLimit ≤ rest.length := Nat.not_le.mpr hlen
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x35 = .calldataload by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popNat, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
    hstk, hg, hl, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false]
  rfl

end EvmLean.Interpreter
