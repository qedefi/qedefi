import EvmLogic.Program.Logic
import EvmLogic.Step.Basic
import EvmLogic.Step.Arith
import EvmLogic.Step.Stack
import EvmLogic.Step.Push
import EvmLogic.Step.Flow
import EvmLogic.Step.Memory
import EvmLogic.Step.Storage
import EvmLogic.Step.Env
import EvmLogic.Program.Summary

/-!
# An any-gas prefix calculus

A protected function's body, from its dispatcher entry up to its single untrusted call, is a
*prefix*: a straight run in which data-dependent branches that `require`/revert are fine (a revert
restores the snapshot). These rules run such a prefix under a **symbolic gas** amount: each one
either takes the instruction (enough gas and stack) and continues, or the instruction fails (out
of gas, stack underflow/overflow, a bad jump, or an explicit `REVERT`), which is acceptable
because the frame's rollback snapshot is `Good` (`FailOk`). They mirror the failure rules of
`EvmLogic.GasMono.CodeFails` but keep a forward goal, so a prefix composes with `WP.call_havoc`
at the call site with no gas lower bound.
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program

/-- The frame-end postcondition of a prefix: whatever outcome, the world it hands back is `Good`.
On a revert or halt that is the (unchanged) snapshot; on a success it is the current world. -/
abbrev FailOk (Good : World → Prop) (mf : Machine) (o : Outcome) : Prop :=
  Good (frameResult mf o).2.1

variable {Good : World → Prop} {Q : Machine → Prop} {m : Machine} {b : UInt8}

/-- A frame whose next instruction errors (OOG, underflow, overflow, bad jump) ends unsuccessfully,
so `FailOk` holds from a `Good` snapshot. -/
theorem wp_fail_of_error {e : ExceptionalHalt} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (herr : (exec (Opcode.decode m.ctx.fork b)).run m = .error e) :
    WP m Q (FailOk Good) :=
  WP.halt_of_step (step_of_exec_error hcode herr) (.refl m)
    (by show Good (frameResult m (.halt e)).2.1; rw [frameResult_halt]; exact hsnap)

/-- `FailOk` holds on a `REVERT` from a `Good` snapshot. -/
theorem wp_fail_of_revert {out : ByteArray} (hsnap : Good m.frame.snapshot.1)
    (hstep : step m = finishFrame m (.revert out)) : WP m Q (FailOk Good) :=
  WP.halt_of_step hstep (.refl m)
    (by show Good (frameResult m (.revert out)).2.1; rw [frameResult_revert]; exact hsnap)
/-- Reaching the target: `Q` holds at the current machine. -/
theorem pwp_reached (h : Q m) : WP m Q (FailOk Good) := WP.ret h

/-- The machine after a `pushValue` instruction (the pushed value sees the charged frame). -/
def pushValueNext (m : Machine) (cost : Nat) (v : Machine → Word) : Machine :=
  { m with frame := { m.frame with
    stack := v { m with frame := { m.frame with gasLeft := m.frame.gasLeft - cost } } :: m.frame.stack,
    gasLeft := m.frame.gasLeft - cost, pc := m.frame.pc + 1 } }

theorem pwp_binOp {cost : Nat} {f : Word → Word → Word} {x y : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hop : ∀ fk, exec (Opcode.decode fk b) = binOp cost f)
    (hcode : m.frame.code[m.frame.pc]? = some b) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → cost ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := f x y :: rest, gasLeft := m.frame.gasLeft - cost, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hop : ∀ fk, exec (Opcode.decode fk b) = unOp cost f)
    (hcode : m.frame.code[m.frame.pc]? = some b) (hstk : m.frame.stack = x :: rest)
    (hrec : rest.length < 1024 → cost ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := f x :: rest, gasLeft := m.frame.gasLeft - cost, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hop : ∀ fk, exec (Opcode.decode fk b) = ternOp cost f)
    (hcode : m.frame.code[m.frame.pc]? = some b) (hstk : m.frame.stack = x :: y :: z :: rest)
    (hrec : rest.length < 1024 → cost ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := f x y z :: rest, gasLeft := m.frame.gasLeft - cost, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hop : ∀ fk, exec (Opcode.decode fk b) = pushValue cost v)
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (hrec : m.frame.stack.length < 1024 → cost ≤ m.frame.gasLeft →
      WP (pushValueNext m cost v) Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some (0x80 + n.val).toUInt8)
    (hget : m.frame.stack[n.val]? = some x)
    (hrec : m.frame.stack.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with stack := x :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x50)
    (hstk : m.frame.stack = x :: rest)
    (hrec : Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - Gas.base, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) := by
  by_cases hg : Gas.base ≤ m.frame.gasLeft
  · exact WP.of_step (step_pop hcode hstk hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ (hrec hg)
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [show Opcode.decode m.ctx.fork 0x50 = .pop by cases m.ctx.fork <;> rfl]
    simp only [exec, pop, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
      Nat.lt_of_not_le hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

/-- `JUMPDEST`. -/
theorem pwp_jumpdest
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x5b)
    (hrec : Gas.jumpdest ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      gasLeft := m.frame.gasLeft - Gas.jumpdest, pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  by_cases hg : Gas.jumpdest ≤ m.frame.gasLeft
  · exact WP.of_step (step_jumpdest hcode hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ (hrec hg)
  · refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [show Opcode.decode m.ctx.fork 0x5b = .jumpdest by cases m.ctx.fork <;> rfl]
    simp only [exec, charge, advance, getFrame, modifyFrame, StateT.run_bind,
      Nat.lt_of_not_le hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true]
    rfl

/-- `JUMP` to a valid destination (an invalid one halts, which is acceptable). -/
theorem pwp_jump {x : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x56)
    (hstk : m.frame.stack = x :: rest)
    (hrec : isValidJumpDest m.frame.jumpDests x.toNat = true → Gas.mid ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := rest, gasLeft := m.frame.gasLeft - Gas.mid, pc := x.toNat } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x57)
    (hstk : m.frame.stack = x :: 0 :: rest)
    (hrec : Gas.high ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - Gas.high, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x57)
    (hstk : m.frame.stack = x :: y :: rest) (hcond : y ≠ 0)
    (hrec : isValidJumpDest m.frame.jumpDests x.toNat = true → Gas.high ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := rest, gasLeft := m.frame.gasLeft - Gas.high, pc := x.toNat } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x52)
    (hstk : m.frame.stack = x :: y :: rest)
    (hrec : Gas.veryLow + memoryCost m x 32 ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := rest, memory := (m.frame.memory.expand x.toNat 32).storeWord x.toNat y,
      gasLeft := m.frame.gasLeft - (Gas.veryLow + memoryCost m x 32), pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x51)
    (hstk : m.frame.stack = x :: rest)
    (hrec : ∀ w, rest.length < 1024 → Gas.veryLow + memoryCost m x 32 ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := w :: rest, memory := m.frame.memory.expand x.toNat 32,
        gasLeft := m.frame.gasLeft - (Gas.veryLow + memoryCost m x 32), pc := m.frame.pc + 1 } } Q
        (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x35)
    (hstk : m.frame.stack = x :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := Bytes.toWord (readBytes m.frame.msg.data x.toNat 32) :: rest,
      gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x54)
    (hstk : m.frame.stack = x :: rest)
    (hrec : rest.length < 1024 →
      sloadCost (storageKeyWarm m.frame.sub.accessedStorageKeys m.frame.msg.currentTarget x)
        ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := m.world.sload m.frame.msg.currentTarget x :: rest,
        gasLeft := m.frame.gasLeft - sloadCost (storageKeyWarm m.frame.sub.accessedStorageKeys
          m.frame.msg.currentTarget x),
        sub := m.frame.sub.warmKey m.frame.msg.currentTarget x,
        pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x55)
    (hstk : m.frame.stack = x :: y :: rest) (hstatic : m.frame.msg.isStatic = false)
    (hrec : Gas.callStipend < m.frame.gasLeft → (sstoreCostRefund m x y).1 ≤ m.frame.gasLeft →
      WP { m with
        world := m.world.sstore m.frame.msg.currentTarget x y,
        frame := { m.frame with
          stack := rest,
          gasLeft := m.frame.gasLeft - (sstoreCostRefund m x y).1,
          sub := (m.frame.sub.warmKey m.frame.msg.currentTarget x).addRefund
            (sstoreCostRefund m x y).2,
          pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
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

end EvmLogic.Program.Reentrancy
