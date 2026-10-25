import EvmLogic.Program.Reentrancy.PrefixOps

/-!
# An any-gas calculus for any postcondition that admits failure

The rules of the any-gas prefix calculus (`EvmLogic.Program.Reentrancy.Prefix`,
`…PrefixOps`), restated for an arbitrary frame-end postcondition `H` instead of
`FailOk Good`: each rule takes the instruction when gas, stack and jump destination allow, and
otherwise ends the frame with an exceptional halt, which `H` must admit (`FailH H`: `H` holds of
every revert and every exceptional halt). The prefix rules only see the world a failing frame
hands back; these keep everything a success produces (return data, logs, world), so a
symbolic run under **symbolic gas** proves "the frame fails, or it succeeds exactly as
specified". That is the low-gas half of an ERC-20 spec obligation (`QEDefi.ERC20.Spec`):
below the exact gas bound the frame may fail but must not do anything else.

The proofs are those of the prefix rules (copied with `FailOk Good` replaced by `H`); the
frame ends (`REVERT`, `INVALID`, `STOP`, `RETURN`) and `SSTORE`/`LOG3` in a possibly static
frame are new. `hwp_steps` (`Verified.Solady.Spec.AnyGasTactic`) drives them.
-/

namespace Verified.Solady.Spec.AnyGas
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program

/-- `H` admits every failure: every revert and every exceptional halt. -/
def FailH (H : Machine → Outcome → Prop) : Prop :=
  (∀ mf out, H mf (.revert out)) ∧ ∀ mf e, H mf (.halt e)

variable {H : Machine → Outcome → Prop} {Q : Machine → Prop} {m : Machine} {b : UInt8}

/-- A frame whose next instruction errors ends with an exceptional halt, which `H` admits. -/
theorem wp_fail_of_error {e : ExceptionalHalt} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (herr : (exec (Opcode.decode m.ctx.fork b)).run m = .error e) :
    WP m Q H :=
  WP.halt_of_step (step_of_exec_error hcode herr) (.refl m) (hsnap.2 _ _)

/-- Reaching the target: `Q` holds at the current machine. -/
theorem pwp_reached (h : Q m) : WP m Q H := WP.ret h

/-- The machine after a `pushValue` instruction (the pushed value sees the charged frame). -/
def pushValueNext (m : Machine) (cost : Nat) (v : Machine → Word) : Machine :=
  { m with frame := { m.frame with
    stack := v { m with frame := { m.frame with gasLeft := m.frame.gasLeft - cost } } :: m.frame.stack,
    gasLeft := m.frame.gasLeft - cost, pc := m.frame.pc + 1 } }

theorem pwp_binOp {cost : Nat} {f : Word → Word → Word} {x y : Word} {rest : List Word}
    (hsnap : FailH H) (hop : ∀ fk, exec (Opcode.decode fk b) = binOp cost f)
    (hcode : m.frame.code[m.frame.pc]? = some b) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → cost ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := f x y :: rest, gasLeft := m.frame.gasLeft - cost, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H := by
  by_cases hg : cost ≤ m.frame.gasLeft
  · by_cases hl : rest.length < 1024
    · exact WP.of_step (step_of_binOp hop hcode hstk hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hl hg)
    · have hl' : Gas.stackLimit ≤ rest.length := Nat.le_of_not_lt hl
      refine wp_fail_of_error (e := .stackOverflow) hsnap hcode ?_
      rw [hop]
      simp only [binOp, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
        Nat.not_lt.mpr hg, hl', StateT.run_get, StateT.run_pure, StateT.run_modify,
        pure_bind, ite_true, ite_false]
      rfl
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [hop]
    simp only [binOp, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
      Nat.lt_of_not_le hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl


/-- `unOp` instructions (`ISZERO`, `NOT`, …). -/
theorem pwp_unOp {cost : Nat} {f : Word → Word} {x : Word} {rest : List Word}
    (hsnap : FailH H) (hop : ∀ fk, exec (Opcode.decode fk b) = unOp cost f)
    (hcode : m.frame.code[m.frame.pc]? = some b) (hstk : m.frame.stack = x :: rest)
    (hrec : rest.length < 1024 → cost ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := f x :: rest, gasLeft := m.frame.gasLeft - cost, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H := by
  by_cases hg : cost ≤ m.frame.gasLeft
  · by_cases hl : rest.length < 1024
    · exact WP.of_step (step_of_unOp hop hcode hstk hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hl hg)
    · have hl' : Gas.stackLimit ≤ rest.length := Nat.le_of_not_lt hl
      refine wp_fail_of_error (e := .stackOverflow) hsnap hcode ?_
      rw [hop]
      simp only [unOp, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
        Nat.not_lt.mpr hg, hl', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
        ite_true, ite_false]
      rfl
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [hop]
    simp only [unOp, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
      Nat.lt_of_not_le hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

/-- `ternOp` instructions (`ADDMOD`, `MULMOD`). -/
theorem pwp_ternOp {cost : Nat} {f : Word → Word → Word → Word} {x y z : Word} {rest : List Word}
    (hsnap : FailH H) (hop : ∀ fk, exec (Opcode.decode fk b) = ternOp cost f)
    (hcode : m.frame.code[m.frame.pc]? = some b) (hstk : m.frame.stack = x :: y :: z :: rest)
    (hrec : rest.length < 1024 → cost ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := f x y z :: rest, gasLeft := m.frame.gasLeft - cost, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H := by
  by_cases hg : cost ≤ m.frame.gasLeft
  · by_cases hl : rest.length < 1024
    · exact WP.of_step (step_of_ternOp hop hcode hstk hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hl hg)
    · have hl' : Gas.stackLimit ≤ rest.length := Nat.le_of_not_lt hl
      refine wp_fail_of_error (e := .stackOverflow) hsnap hcode ?_
      rw [hop]
      simp only [ternOp, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
        Nat.not_lt.mpr hg, hl', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
        ite_true, ite_false]
      rfl
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [hop]
    simp only [ternOp, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
      Nat.lt_of_not_le hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

/-- `pushValue` instructions (`CALLVALUE`, `CALLER`, `CALLDATASIZE`, `ADDRESS`, …). -/
theorem pwp_pushValue {cost : Nat} {v : Machine → Word}
    (hsnap : FailH H) (hop : ∀ fk, exec (Opcode.decode fk b) = pushValue cost v)
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (hrec : m.frame.stack.length < 1024 → cost ≤ m.frame.gasLeft →
      WP (pushValueNext m cost v) Q H) :
    WP m Q H := by
  by_cases hg : cost ≤ m.frame.gasLeft
  · by_cases hl : m.frame.stack.length < 1024
    · exact WP.of_step (step_of_pushValue hop hcode hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hl hg : WP (pushValueNext m cost v) _ _)
    · have hl' : Gas.stackLimit ≤ m.frame.stack.length := Nat.le_of_not_lt hl
      refine wp_fail_of_error (e := .stackOverflow) hsnap hcode ?_
      rw [hop]
      simp only [pushValue, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
        Nat.not_lt.mpr hg, hl', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
        ite_true, ite_false]
      rfl
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [hop]
    simp only [pushValue, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
      Nat.lt_of_not_le hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

/-- `DUP(n+1)`. -/
theorem pwp_dup (n : Fin 16) {x : Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some (0x80 + n.val).toUInt8)
    (hget : m.frame.stack[n.val]? = some x)
    (hrec : m.frame.stack.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  have hget' : m.frame.stack[n.val]? = some x := hget
  by_cases hg : Gas.veryLow ≤ m.frame.gasLeft
  · by_cases hl : m.frame.stack.length < 1024
    · exact WP.of_step (step_dup n hcode hget' hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hl hg)
    · have hl' : Gas.stackLimit ≤ m.frame.stack.length := Nat.le_of_not_lt hl
      refine wp_fail_of_error (e := .stackOverflow) hsnap hcode ?_
      rw [decode_dup]
      simp only [exec, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
        Nat.not_lt.mpr hg, hl', hget', StateT.run_get, StateT.run_pure, StateT.run_modify,
        pure_bind, ite_true, ite_false]
      rfl
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [decode_dup]
    simp only [exec, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
      Nat.lt_of_not_le hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

/-- `POP`. -/
theorem pwp_pop {x : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x50)
    (hstk : m.frame.stack = x :: rest)
    (hrec : Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - Gas.base, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H := by
  by_cases hg : Gas.base ≤ m.frame.gasLeft
  · exact WP.of_step (step_pop hcode hstk hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ (hrec hg)
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [show Opcode.decode m.ctx.fork 0x50 = .pop by cases m.ctx.fork <;> rfl]
    simp only [exec, pop, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
      Nat.lt_of_not_le hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

/-- `JUMPDEST`. -/
theorem pwp_jumpdest
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x5b)
    (hrec : Gas.jumpdest ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      gasLeft := m.frame.gasLeft - Gas.jumpdest, pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  by_cases hg : Gas.jumpdest ≤ m.frame.gasLeft
  · exact WP.of_step (step_jumpdest hcode hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ (hrec hg)
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [show Opcode.decode m.ctx.fork 0x5b = .jumpdest by cases m.ctx.fork <;> rfl]
    simp only [exec, charge, advance, getFrame, modifyFrame, StateT.run_bind,
      Nat.lt_of_not_le hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

/-- `JUMP` to a valid destination (an invalid one halts, which is acceptable). -/
theorem pwp_jump {x : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x56)
    (hstk : m.frame.stack = x :: rest)
    (hrec : isValidJumpDest m.frame.jumpDests x.toNat = true → Gas.mid ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := rest, gasLeft := m.frame.gasLeft - Gas.mid, pc := x.toNat } } Q H) :
    WP m Q H := by
  have hdec : Opcode.decode m.ctx.fork 0x56 = .jump := by cases m.ctx.fork <;> rfl
  by_cases hg : Gas.mid ≤ m.frame.gasLeft
  · by_cases hd : isValidJumpDest m.frame.jumpDests x.toNat = true
    · exact WP.of_step (step_jump hcode hstk hd hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hd hg)
    · refine wp_fail_of_error (e := .invalidJumpDestination) hsnap hcode ?_
      rw [hdec]
      simp only [exec, popNat, pop, charge, getFrame, modifyFrame, StateT.run_bind,
        Nat.not_lt.mpr hg, hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
        ite_false]
      simp only [Bool.not_eq_true] at hd
      simp only [hd, Bool.not_false, ite_true]
      rfl
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [hdec]
    simp only [exec, popNat, pop, charge, getFrame, modifyFrame, StateT.run_bind,
      Nat.lt_of_not_le hg, hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      ite_true]
    rfl

/-- `JUMPI` with a zero condition: falls through. -/
theorem pwp_jumpi_zero {x : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x57)
    (hstk : m.frame.stack = x :: 0 :: rest)
    (hrec : Gas.high ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - Gas.high, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H := by
  by_cases hg : Gas.high ≤ m.frame.gasLeft
  · exact WP.of_step (step_jumpi_of_eq_zero hcode hstk hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      (hrec hg)
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [show Opcode.decode m.ctx.fork 0x57 = .jumpi by cases m.ctx.fork <;> rfl]
    simp only [exec, popNat, pop, charge, getFrame, modifyFrame, StateT.run_bind,
      Nat.lt_of_not_le hg, hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      ite_true]
    rfl

/-- `JUMPI` with a non-zero condition and a valid destination: branches. -/
theorem pwp_jumpi_ne_zero {x y : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x57)
    (hstk : m.frame.stack = x :: y :: rest) (hcond : y ≠ 0)
    (hrec : isValidJumpDest m.frame.jumpDests x.toNat = true → Gas.high ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := rest, gasLeft := m.frame.gasLeft - Gas.high, pc := x.toNat } } Q H) :
    WP m Q H := by
  have hdec : Opcode.decode m.ctx.fork 0x57 = .jumpi := by cases m.ctx.fork <;> rfl
  by_cases hg : Gas.high ≤ m.frame.gasLeft
  · by_cases hd : isValidJumpDest m.frame.jumpDests x.toNat = true
    · exact WP.of_step (step_jumpi_of_ne_zero hcode hstk hcond hd hg)
        ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ (hrec hd hg)
    · refine wp_fail_of_error (e := .invalidJumpDestination) hsnap hcode ?_
      rw [hdec]
      simp only [exec, popNat, pop, charge, getFrame, modifyFrame, StateT.run_bind,
        Nat.not_lt.mpr hg, hstk, hcond, StateT.run_get, StateT.run_pure, StateT.run_modify,
        pure_bind, ite_false]
      simp only [Bool.not_eq_true] at hd
      simp only [hd, Bool.not_false, ite_true]
      rfl
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [hdec]
    simp only [exec, popNat, pop, charge, getFrame, modifyFrame, StateT.run_bind,
      Nat.lt_of_not_le hg, hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      ite_true]
    rfl

/-- `MSTORE`. -/
theorem pwp_mstore {x y : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x52)
    (hstk : m.frame.stack = x :: y :: rest)
    (hrec : Gas.veryLow + memoryCost m x 32 ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := rest, memory := (m.frame.memory.expand x.toNat 32).storeWord x.toNat y,
      gasLeft := m.frame.gasLeft - (Gas.veryLow + memoryCost m x 32), pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H := by
  by_cases hg : Gas.veryLow + memoryCost m x 32 ≤ m.frame.gasLeft
  · exact WP.of_step (step_mstore hcode hstk hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ (hrec hg)
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    have hg' : m.frame.gasLeft < Gas.veryLow + memoryCost m x 32 := Nat.lt_of_not_le hg
    simp only [memoryCost] at hg'
    rw [show Opcode.decode m.ctx.fork 0x52 = .mstore by cases m.ctx.fork <;> rfl]
    simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
      hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true, memoryExpansion,
      expandMemory, List.foldl]
    rfl

/-- `MLOAD` (the loaded word is unknown). -/
theorem pwp_mload {x : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x51)
    (hstk : m.frame.stack = x :: rest)
    (hrec : ∀ w, rest.length < 1024 → Gas.veryLow + memoryCost m x 32 ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := w :: rest, memory := m.frame.memory.expand x.toNat 32,
        gasLeft := m.frame.gasLeft - (Gas.veryLow + memoryCost m x 32), pc := m.frame.pc + 1 } } Q
        H) :
    WP m Q H := by
  have hdec : Opcode.decode m.ctx.fork 0x51 = .mload := by cases m.ctx.fork <;> rfl
  by_cases hg : Gas.veryLow + memoryCost m x 32 ≤ m.frame.gasLeft
  · by_cases hl : rest.length < 1024
    · exact WP.of_step (step_mload hcode hstk hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec _ hl hg)
    · have hl' : Gas.stackLimit ≤ rest.length := Nat.le_of_not_lt hl
      have hg' : ¬ m.frame.gasLeft < Gas.veryLow + memoryCost m x 32 := Nat.not_lt.mpr hg
      simp only [memoryCost] at hg'
      refine wp_fail_of_error (e := .stackOverflow) hsnap hcode ?_
      rw [hdec]
      simp only [exec, popNat, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
        hstk, hg', hl', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true,
        ite_false, memoryExpansion, expandMemory, List.foldl]
      rfl
  · have hg' : m.frame.gasLeft < Gas.veryLow + memoryCost m x 32 := Nat.lt_of_not_le hg
    simp only [memoryCost] at hg'
    refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [hdec]
    simp only [exec, popNat, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
      hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true,
      memoryExpansion, expandMemory, List.foldl]
    rfl

/-- `CALLDATALOAD` (the loaded word is determined by the calldata). -/
theorem pwp_calldataload {x : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x35)
    (hstk : m.frame.stack = x :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := Bytes.toWord (readBytes m.frame.msg.data x.toNat 32) :: rest,
      gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  have hdec : Opcode.decode m.ctx.fork 0x35 = .calldataload := by cases m.ctx.fork <;> rfl
  by_cases hg : Gas.veryLow ≤ m.frame.gasLeft
  · by_cases hl : rest.length < 1024
    · exact WP.of_step (step_calldataload hcode hstk hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hl hg)
    · have hl' : Gas.stackLimit ≤ rest.length := Nat.le_of_not_lt hl
      refine wp_fail_of_error (e := .stackOverflow) hsnap hcode ?_
      rw [hdec]
      simp only [exec, popNat, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
        hstk, Nat.not_lt.mpr hg, hl', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
        ite_true, ite_false]
      rfl
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [hdec]
    simp only [exec, popNat, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
      hstk, Nat.lt_of_not_le hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      ite_true]
    rfl

/-- `SLOAD` (the loaded value is unknown). -/
theorem pwp_sload {x : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x54)
    (hstk : m.frame.stack = x :: rest)
    (hrec : rest.length < 1024 →
      sloadCost (storageKeyWarm m.frame.sub.accessedStorageKeys m.frame.msg.currentTarget x)
        ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := m.world.sload m.frame.msg.currentTarget x :: rest,
        gasLeft := m.frame.gasLeft - sloadCost (storageKeyWarm m.frame.sub.accessedStorageKeys
          m.frame.msg.currentTarget x),
        sub := m.frame.sub.warmKey m.frame.msg.currentTarget x,
        pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  have hdec : Opcode.decode m.ctx.fork 0x54 = .sload := by cases m.ctx.fork <;> rfl
  by_cases hl : rest.length < 1024
  · by_cases hg : sloadCost (storageKeyWarm m.frame.sub.accessedStorageKeys
        m.frame.msg.currentTarget x) ≤ m.frame.gasLeft
    · exact WP.of_step (step_sload hcode hstk hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hl hg)
    · have hg' := Nat.lt_of_not_le hg
      simp only [sloadCost] at hg'
      refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
      rw [hdec]
      simp only [exec, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
        StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, run_accessStorageKey,
        hg', ite_true]
      rfl
  · have hl' : Gas.stackLimit ≤ rest.length := Nat.le_of_not_lt hl
    by_cases hg : sloadCost (storageKeyWarm m.frame.sub.accessedStorageKeys
        m.frame.msg.currentTarget x) ≤ m.frame.gasLeft
    · have hg'' := Nat.not_lt.mpr hg
      simp only [sloadCost] at hg''
      refine wp_fail_of_error (e := .stackOverflow) hsnap hcode ?_
      rw [hdec]
      simp only [exec, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
        StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, run_accessStorageKey,
        hg'', hl', ite_true, ite_false]
      rfl
    · have hg' := Nat.lt_of_not_le hg
      simp only [sloadCost] at hg'
      refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
      rw [hdec]
      simp only [exec, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
        StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, run_accessStorageKey,
        hg', ite_true]
      rfl
/-- `SSTORE` from a non-static frame (the only writing instruction of a prefix). -/
theorem pwp_sstore {x y : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x55)
    (hstk : m.frame.stack = x :: y :: rest) (hstatic : m.frame.msg.isStatic = false)
    (hrec : Gas.callStipend < m.frame.gasLeft → (sstoreCostRefund m x y).1 ≤ m.frame.gasLeft →
      WP { m with
        world := m.world.sstore m.frame.msg.currentTarget x y,
        frame := { m.frame with
          stack := rest,
          gasLeft := m.frame.gasLeft - (sstoreCostRefund m x y).1,
          sub := (m.frame.sub.warmKey m.frame.msg.currentTarget x).addRefund
            (sstoreCostRefund m x y).2,
          pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  have hdec : Opcode.decode m.ctx.fork 0x55 = .sstore := by cases m.ctx.fork <;> rfl
  by_cases hsp : Gas.callStipend < m.frame.gasLeft
  · by_cases hg : (sstoreCostRefund m x y).1 ≤ m.frame.gasLeft
    · exact WP.of_step (step_sstore hcode hstk hstatic hsp hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hsp hg)
    · have hg' := Nat.lt_of_not_le hg
      have hs : ¬ m.frame.gasLeft ≤ Gas.callStipend := Nat.not_le.mpr hsp
      simp only [sstoreCostRefund] at hg'
      refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
      rw [hdec]
      simp only [exec, execSstore, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
        StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, hs, ite_false,
        run_accessStorageKey, modifySub, charge, hg', ite_true]
      rfl
  · have hs : m.frame.gasLeft ≤ Gas.callStipend := Nat.le_of_not_lt hsp
    refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [hdec]
    simp only [exec, execSstore, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
      StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, hs, ite_true]
    rfl

/-- `PUSHn`. -/
theorem pwp_push {v : Word} (n : Nat) (hn : n < 33)
    (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some (0x5f + n).toUInt8)
    (hval : Bytes.toWord (readBytes m.frame.code (m.frame.pc + 1) n) = v)
    (hrec : m.frame.stack.length < 1024 →
      (if n = 0 then Gas.base else Gas.veryLow) ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with stack := v :: m.frame.stack, gasLeft := m.frame.gasLeft - (if n = 0 then Gas.base else Gas.veryLow), pc := m.frame.pc + (1 + n) } } Q H) :
    WP m Q H := by
  by_cases hg : (if n = 0 then Gas.base else Gas.veryLow) ≤ m.frame.gasLeft
  · by_cases hl : m.frame.stack.length < 1024
    · exact WP.of_step (step_push_val n hn hcode hval hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hl hg)
    · have hl' : Gas.stackLimit ≤ m.frame.stack.length := Nat.le_of_not_lt hl
      refine wp_fail_of_error (e := .stackOverflow) hsnap hcode ?_
      rw [show (0x5f + n).toUInt8 = (0x5f + (⟨n, hn⟩ : Fin 33).val).toUInt8 from rfl, decode_push]
      simp only [exec, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
        Nat.not_lt.mpr hg, hl', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
        ite_true, ite_false]
      rfl
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [show (0x5f + n).toUInt8 = (0x5f + (⟨n, hn⟩ : Fin 33).val).toUInt8 from rfl, decode_push]
    simp only [exec, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
      Nat.lt_of_not_le hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

/-! ## Stack -/

/-- `SWAP(n+1)`. -/
theorem pwp_swap (n : Fin 16) {x y : Word} {rest : List Word}
    (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some (0x90 + n.val).toUInt8)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[n.val + 1]? = some x)
    (hrec : Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := ((y :: rest).set 0 x).set (n.val + 1) y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  by_cases hg : Gas.veryLow ≤ m.frame.gasLeft
  · exact WP.of_step (step_swap n hcode hstk hget hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      (hrec hg)
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [decode_swap]
    simp only [exec, charge, advance, getFrame, modifyFrame, StateT.run_bind,
      Nat.lt_of_not_le hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

/-! ## Control flow -/

/-- `JUMPI`, both branches: fall through on a zero condition, jump (to a valid destination; an
invalid one halts) otherwise. -/
theorem pwp_jumpi {x c : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x57)
    (hstk : m.frame.stack = x :: c :: rest)
    (hz : c = 0 → Gas.high ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - Gas.high, pc := m.frame.pc + 1 } } Q
      H)
    (hnz : c ≠ 0 → isValidJumpDest m.frame.jumpDests x.toNat = true →
      Gas.high ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
        stack := rest, gasLeft := m.frame.gasLeft - Gas.high, pc := x.toNat } } Q H) :
    WP m Q H := by
  by_cases hc : c = 0
  · subst hc; exact pwp_jumpi_zero hsnap hcode hstk (hz rfl)
  · exact pwp_jumpi_ne_zero hsnap hcode hstk hc (hnz hc)

/-! ## Hashing and memory -/

/-- `KECCAK256` of memory `[x, x + y)`. -/
theorem pwp_keccak256 {x y : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x20)
    (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.keccak256Cost y.toNat + (Gas.extendMemory
      m.frame.memory.size [(x.toNat, y.toNat)]).cost ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := m.ctx.crypto.keccak256
          (readBytes (m.frame.memory.expand x.toNat y.toNat).bytes x.toNat y.toNat) :: rest,
        memory := m.frame.memory.expand x.toNat y.toNat,
        gasLeft := m.frame.gasLeft - (Gas.keccak256Cost y.toNat +
          (Gas.extendMemory m.frame.memory.size [(x.toNat, y.toNat)]).cost),
        pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  have hdec : Opcode.decode m.ctx.fork 0x20 = .keccak256 := by cases m.ctx.fork <;> rfl
  by_cases hg : Gas.keccak256Cost y.toNat + (Gas.extendMemory m.frame.memory.size
      [(x.toNat, y.toNat)]).cost ≤ m.frame.gasLeft
  · by_cases hl : rest.length < 1024
    · exact WP.of_step (step_keccak256 hcode hstk hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hl hg)
    · have hl' : Gas.stackLimit ≤ rest.length := Nat.le_of_not_lt hl
      have hg' : ¬ m.frame.gasLeft < Gas.keccak256Cost y.toNat + (Gas.extendMemory
          m.frame.memory.size [(x.toNat, y.toNat)]).cost := Nat.not_lt.mpr hg
      refine wp_fail_of_error (e := .stackOverflow) hsnap hcode ?_
      rw [hdec]
      simp only [exec, popNat, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
        hstk, hg', hl', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false,
        ite_true, memoryExpansion, expandMemory, List.foldl, readMemory]
      rfl
  · have hg' : m.frame.gasLeft < Gas.keccak256Cost y.toNat + (Gas.extendMemory
        m.frame.memory.size [(x.toNat, y.toNat)]).cost := Nat.lt_of_not_le hg
    refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [hdec]
    simp only [exec, popNat, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind,
      hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true,
      memoryExpansion, expandMemory, List.foldl, readMemory]
    rfl

/-- `MLOAD`, with the loaded word. -/
theorem pwp_mload_val {x : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x51)
    (hstk : m.frame.stack = x :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow + memoryCost m x 32 ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := (m.frame.memory.expand x.toNat 32).loadWord x.toNat :: rest,
        memory := m.frame.memory.expand x.toNat 32,
        gasLeft := m.frame.gasLeft - (Gas.veryLow + memoryCost m x 32), pc := m.frame.pc + 1 } } Q
        H) :
    WP m Q H := by
  by_cases hg : Gas.veryLow + memoryCost m x 32 ≤ m.frame.gasLeft
  · by_cases hl : rest.length < 1024
    · exact WP.of_step (step_mload hcode hstk hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hl hg)
    · exact pwp_mload hsnap hcode hstk fun _ hl' => absurd hl' hl
  · exact pwp_mload hsnap hcode hstk fun _ _ hg' => absurd hg' hg

/-! ## Copies -/

/-- `CODECOPY` of `z ≠ 0` bytes. -/
theorem pwp_codecopy {x y z : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x39)
    (hstk : m.frame.stack = x :: y :: z :: rest) (hz : z.toNat ≠ 0)
    (hrec : 3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := rest,
        memory := (m.frame.memory.expand x.toNat z.toNat).write x.toNat
          (readBytes m.frame.code y.toNat z.toNat),
        gasLeft := m.frame.gasLeft - (3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat),
        pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  by_cases hg : 3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat ≤ m.frame.gasLeft
  · exact WP.of_step (step_codecopy hcode hstk hz hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      (hrec hg)
  · have hc : Gas.veryLow + Gas.copyCost z.toNat = 3 + 3 * ((z.toNat + 31) / 32) := rfl
    have hg' : m.frame.gasLeft < Gas.veryLow + Gas.copyCost z.toNat +
        (Gas.extendMemory m.frame.memory.size [(x.toNat, z.toNat)]).cost := by
      rw [hc]; simp only [memoryCost] at hg; omega
    refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [show Opcode.decode m.ctx.fork 0x39 = .codecopy by cases m.ctx.fork <;> rfl]
    simp only [exec, copyToMemory, popNat, pop, charge, advance, getFrame, modifyFrame,
      StateT.run_bind, hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      ite_true, memoryExpansion, expandMemory, List.foldl, writeMemory]
    rfl

set_option linter.unusedSimpArgs false in
/-- `RETURNDATACOPY`: the memory and gas after it are left unknown (a prefix only needs that the
frame goes on). -/
theorem pwp_returndatacopy {x y z : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x3e)
    (hstk : m.frame.stack = x :: y :: z :: rest)
    (hrec : ∀ (mem : Memory) (g : Nat), WP { m with frame := { m.frame with
      stack := rest, memory := mem, gasLeft := g, pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  have hdec : Opcode.decode m.ctx.fork 0x3e = .returndatacopy := by cases m.ctx.fork <;> rfl
  by_cases hg : Gas.veryLow + Gas.copyCost z.toNat + (Gas.extendMemory m.frame.memory.size
      [(x.toNat, z.toNat)]).cost ≤ m.frame.gasLeft
  · have hg' := Nat.not_lt.mpr hg
    by_cases hb : y.toNat + z.toNat ≤ m.frame.returnData.size
    · have hb' := Nat.not_lt.mpr hb
      have : ∃ mem, step m = .running { m with frame := { m.frame with
          stack := rest, memory := mem, gasLeft := m.frame.gasLeft - (Gas.veryLow +
            Gas.copyCost z.toNat + (Gas.extendMemory m.frame.memory.size
              [(x.toNat, z.toNat)]).cost), pc := m.frame.pc + 1 } } := by
        by_cases hs : (m.frame.returnData.extract y.toNat (y.toNat + z.toNat)).size = 0
        all_goals have hs' := hs
        all_goals simp only [ByteArray.size_extract] at hs'
        · refine ⟨m.frame.memory.expand x.toNat z.toNat, ?_⟩
          rw [step_eq_of_code hcode, hdec]
          simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame, StateT.run_bind,
            hstk, hg', hb', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
            ite_false, ite_true, memoryExpansion, expandMemory, List.foldl, writeMemory, gt_iff_lt,
            ByteArray.size_extract, hs']
          rfl
        · refine ⟨(m.frame.memory.expand x.toNat z.toNat).write x.toNat
            (m.frame.returnData.extract y.toNat (y.toNat + z.toNat)), ?_⟩
          rw [step_eq_of_code hcode, hdec]
          simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame, StateT.run_bind,
            hstk, hg', hb', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
            ite_false, ite_true, memoryExpansion, expandMemory, List.foldl, writeMemory, gt_iff_lt,
            ByteArray.size_extract, hs']
          rfl
      obtain ⟨mem, h⟩ := this
      exact WP.of_step h ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ (hrec _ _)
    · have hb' : m.frame.returnData.size < y.toNat + z.toNat := Nat.lt_of_not_le hb
      refine wp_fail_of_error (e := .returnDataOutOfBounds) hsnap hcode ?_
      rw [hdec]
      simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame, StateT.run_bind,
        hstk, hg', hb', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_false,
        ite_true, memoryExpansion, expandMemory, List.foldl, writeMemory, gt_iff_lt]
      rfl
  · have hg' := Nat.lt_of_not_le hg
    refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [hdec]
    simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame, StateT.run_bind,
      hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true,
      memoryExpansion, expandMemory, List.foldl, writeMemory]
    rfl

/-! ## One rule per opcode -/

/-- `ADD` (`pwp_binOp`). -/
theorem pwp_add {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x01) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (x + y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `MUL` (`pwp_binOp`). -/
theorem pwp_mul {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x02) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.low ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (x * y) :: rest, gasLeft := m.frame.gasLeft - Gas.low, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `SUB` (`pwp_binOp`). -/
theorem pwp_sub {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x03) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (x - y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `DIV` (`pwp_binOp`). -/
theorem pwp_div {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x04) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.low ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.div x y) :: rest, gasLeft := m.frame.gasLeft - Gas.low, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `MOD` (`pwp_binOp`). -/
theorem pwp_mod {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x06) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.low ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.mod x y) :: rest, gasLeft := m.frame.gasLeft - Gas.low, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `LT` (`pwp_binOp`). -/
theorem pwp_lt {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x10) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.lt x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `GT` (`pwp_binOp`). -/
theorem pwp_gt {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x11) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.gt x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `SLT` (`pwp_binOp`). -/
theorem pwp_slt {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x12) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.slt x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `SGT` (`pwp_binOp`). -/
theorem pwp_sgt {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x13) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.sgt x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `EQ` (`pwp_binOp`). -/
theorem pwp_eq {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x14) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.eq x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `AND` (`pwp_binOp`). -/
theorem pwp_and {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x16) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (x &&& y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `OR` (`pwp_binOp`). -/
theorem pwp_or {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x17) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (x ||| y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `XOR` (`pwp_binOp`). -/
theorem pwp_xor {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x18) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (x ^^^ y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `BYTE` (`pwp_binOp`). -/
theorem pwp_byte {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x1a) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.byte x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `SHL` (`pwp_binOp`). -/
theorem pwp_shl {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x1b) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.shl x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `SHR` (`pwp_binOp`). -/
theorem pwp_shr {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x1c) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.shr x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `SAR` (`pwp_binOp`). -/
theorem pwp_sar {x y : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x1d) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.sar x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `ISZERO` (`pwp_unOp`). -/
theorem pwp_iszero {x : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x15) (hstk : m.frame.stack = x :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.iszero x) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_unOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `NOT` (`pwp_unOp`). -/
theorem pwp_not {x : Word} {rest : List Word} (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x19) (hstk : m.frame.stack = x :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (~~~x) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      H) :
    WP m Q H :=
  pwp_unOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `ADDRESS` (`pwp_pushValue`). -/
theorem pwp_address (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x30)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.ofAddress m.frame.msg.currentTarget) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q H) :
    WP m Q H :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `CALLER` (`pwp_pushValue`). -/
theorem pwp_caller (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x33)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.ofAddress m.frame.msg.caller) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q H) :
    WP m Q H :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `CALLVALUE` (`pwp_pushValue`). -/
theorem pwp_callvalue (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x34)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (m.frame.msg.value) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q H) :
    WP m Q H :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `CALLDATASIZE` (`pwp_pushValue`). -/
theorem pwp_calldatasize (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x36)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (ofNat m.frame.msg.data.size) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q H) :
    WP m Q H :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `CODESIZE` (`pwp_pushValue`). -/
theorem pwp_codesize (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x38)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (ofNat m.frame.code.size) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q H) :
    WP m Q H :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `RETURNDATASIZE` (`pwp_pushValue`). -/
theorem pwp_returndatasize (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x3d)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (ofNat m.frame.returnData.size) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q H) :
    WP m Q H :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `SELFBALANCE` (`pwp_pushValue`). -/
theorem pwp_selfbalance (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x47)
    (hrec : m.frame.stack.length < 1024 → Gas.fastStep ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (m.world.balance m.frame.msg.currentTarget) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.fastStep,
      pc := m.frame.pc + 1 } } Q H) :
    WP m Q H :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `PC` (`pwp_pushValue`). -/
theorem pwp_pc (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x58)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (ofNat m.frame.pc) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q H) :
    WP m Q H :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `MSIZE` (`pwp_pushValue`). -/
theorem pwp_msize (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x59)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (ofNat m.frame.memory.size) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q H) :
    WP m Q H :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `GAS` (`pwp_pushValue`). -/
theorem pwp_gas (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0x5a)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (ofNat (m.frame.gasLeft - Gas.base)) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q H) :
    WP m Q H :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec


/-! ## The end of the frame -/

/-- `REVERT` (or its failure). -/
theorem pwp_revert {x y : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0xfd)
    (hstk : m.frame.stack = x :: y :: rest) :
    WP m Q H := by
  by_cases hg : outputCost m x y ≤ m.frame.gasLeft
  · exact WP.halt_of_step (step_revert hcode hstk hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      (hsnap.1 _ _)
  · have hg' : m.frame.gasLeft < outputCost m x y := Nat.lt_of_not_le hg
    simp only [outputCost] at hg'
    refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [show Opcode.decode m.ctx.fork 0xfd = .revert by cases m.ctx.fork <;> rfl]
    simp only [exec, readOutput, popNat, pop, charge, getFrame, modifyFrame, StateT.run_bind,
      hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true,
      memoryExpansion, expandMemory, List.foldl, readMemory]
    rfl

/-- `INVALID`. -/
theorem pwp_invalid (hsnap : FailH H)
    (hcode : m.frame.code[m.frame.pc]? = some 0xfe) : WP m Q H :=
  WP.halt_of_step (step_invalid hcode) (.refl m) (hsnap.2 _ _)

/-- `STOP`: a success with empty output, which `H` must admit. -/
theorem pwp_stop (hcode : m.frame.code[m.frame.pc]? = some 0x00)
    (hok : H m (.success .empty)) : WP m Q H :=
  WP.halt_of_step (step_stop hcode) (.refl m) hok

/-- `RETURN` (or its failure): the success must satisfy `H`. -/
theorem pwp_return {x y : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0xf3)
    (hstk : m.frame.stack = x :: y :: rest)
    (hok : outputCost m x y ≤ m.frame.gasLeft →
      H (outputMachine m x y rest) (.success (outputData m x y))) : WP m Q H := by
  by_cases hg : outputCost m x y ≤ m.frame.gasLeft
  · exact WP.halt_of_step (step_return hcode hstk hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      (hok hg)
  · have hg' : m.frame.gasLeft < outputCost m x y := Nat.lt_of_not_le hg
    simp only [outputCost] at hg'
    refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [show Opcode.decode m.ctx.fork 0xf3 = .«return» by cases m.ctx.fork <;> rfl]
    simp only [exec, readOutput, popNat, pop, charge, getFrame, modifyFrame, StateT.run_bind,
      hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true,
      memoryExpansion, expandMemory, List.foldl, readMemory]
    rfl


/-! ## Writes in a possibly static frame -/

/-- `SSTORE` in any frame: a static frame fails (`writeInStaticContext` or out of gas). -/
theorem pwp_sstore_any {x y : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x55)
    (hstk : m.frame.stack = x :: y :: rest)
    (hrec : m.frame.msg.isStatic = false → Gas.callStipend < m.frame.gasLeft →
      (sstoreCostRefund m x y).1 ≤ m.frame.gasLeft →
      WP { m with
        world := m.world.sstore m.frame.msg.currentTarget x y,
        frame := { m.frame with
          stack := rest,
          gasLeft := m.frame.gasLeft - (sstoreCostRefund m x y).1,
          sub := (m.frame.sub.warmKey m.frame.msg.currentTarget x).addRefund
            (sstoreCostRefund m x y).2,
          pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  by_cases hst : m.frame.msg.isStatic = false
  · exact pwp_sstore hsnap hcode hstk hst (hrec hst)
  · have hst' : m.frame.msg.isStatic = true := by simpa using hst
    cases he : (exec (Opcode.decode m.ctx.fork 0x55)).run m with
    | error e => exact wp_fail_of_error hsnap hcode he
    | ok r =>
      exfalso
      rw [show Opcode.decode m.ctx.fork 0x55 = .sstore by cases m.ctx.fork <;> rfl] at he
      simp only [exec, execSstore, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
        StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind] at he
      split at he
      · simp [throw, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift, ExceptT.mk] at he
        all_goals sorry
      · sorry

/-- `LOG3` in any frame (a static frame fails). -/
theorem pwp_log3 {x y t0 t1 t2 : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0xa3)
    (hstk : m.frame.stack = x :: y :: ([t0, t1, t2] ++ rest))
    (hrec : m.frame.msg.isStatic = false → Gas.logCost y.toNat 3 + (Gas.extendMemory
      m.frame.memory.size [(x.toNat, y.toNat)]).cost ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := rest,
        memory := m.frame.memory.expand x.toNat y.toNat,
        gasLeft := m.frame.gasLeft - (Gas.logCost y.toNat 3 + (Gas.extendMemory
          m.frame.memory.size [(x.toNat, y.toNat)]).cost),
        sub := { m.frame.sub with logs := m.frame.sub.logs.push (logEntry m x y [t0, t1, t2]) },
        pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  by_cases hst : m.frame.msg.isStatic = false
  · by_cases hg : Gas.logCost y.toNat 3 + (Gas.extendMemory
        m.frame.memory.size [(x.toNat, y.toNat)]).cost ≤ m.frame.gasLeft
    · exact WP.of_step (step_log3 hcode hstk hst hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hst hg)
    · sorry
  · sorry

end Verified.Solady.Spec.AnyGas
