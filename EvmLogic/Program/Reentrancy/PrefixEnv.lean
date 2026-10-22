import EvmLogic.Program.Reentrancy.PrefixOps
import EvmLogic.Program.Call
import EvmLogic.Program.Nested.Frame

/-!
# Prefix rules for the environment and copy instructions

More rules of the any-gas prefix calculus (`EvmLogic.Program.Reentrancy.Prefix`), for the
instructions of Aave's AToken and the proxies that the first rules lack:

* `EXTCODESIZE` (`pwp_extcodesize`, the pushed size exact: solc's check before a call to a
  function without return value, `isConstructor()`), `CHAINID` (`pwp_chainid`), `TIMESTAMP`
  (`pwp_timestamp`);
* `CALLDATACOPY` (`pwp_calldatacopy`) and `MCOPY` (`pwp_mcopy`): the memory and gas after them are
  left unknown (as `pwp_returndatacopy`), which is all a prefix needs when the copied bytes are
  only passed on (the proxy's calldata, the `bytes` of an event);
* `pwp_next`: any instruction that, when it succeeds, continues the frame without touching the
  world (the generic shape the two copy rules are instances of).

Each rule takes the instruction when gas and stack allow and otherwise absorbs the failure
(`FailOk`), like the rules of `Prefix.lean`.
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program EvmLogic.Program.Nested

variable {Good : World → Prop} {Q : Machine → Prop} {m : Machine}

/-! ## A generic rule -/

/-- **Any instruction that only continues.** If every successful run of the instruction at `pc`
continues the frame (`.next`), then it suffices that the frame goes on from every machine such a
run produces (same frame, by `exec_frame`); an error hands back the `Good` snapshot. -/
theorem pwp_next {b : UInt8} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some b)
    (hnext : ∀ a m', (exec (Opcode.decode m.ctx.fork b)).run m = .ok (a, m') → a = .next)
    (hrec : ∀ m', (exec (Opcode.decode m.ctx.fork b)).run m = .ok (.next, m') →
      SameFrame m m' → WP m' Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  cases he : (exec (Opcode.decode m.ctx.fork b)).run m with
  | error e => exact wp_fail_of_error hsnap hcode he
  | ok p =>
    obtain ⟨a, m'⟩ := p
    have ha := hnext a m' he
    subst ha
    have hf := ((exec_frame (Opcode.decode m.ctx.fork b) m).of_run he).1
    exact WP.of_step (step_of_exec_next hcode he) hf.same (hrec m' he hf.same)

/-! ## Environment -/

/-- `EXTCODESIZE`, with the size of the code at the address. -/
theorem pwp_extcodesize {x : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x3b)
    (hstk : m.frame.stack = x :: rest)
    (hrec : rest.length < 1024 →
      Gas.accessCost (m.frame.sub.accessedAddresses.contains (Word.toAddress x)) ≤
        m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := ofNat (m.world.code (Word.toAddress x)).size :: rest,
        gasLeft := m.frame.gasLeft -
          Gas.accessCost (m.frame.sub.accessedAddresses.contains (Word.toAddress x)),
        sub := m.frame.sub.warmAddr (Word.toAddress x),
        pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  have hdec : Opcode.decode m.ctx.fork 0x3b = .extcodesize := by cases m.ctx.fork <;> rfl
  by_cases hl : rest.length < 1024
  · by_cases hg : Gas.accessCost (m.frame.sub.accessedAddresses.contains (Word.toAddress x)) ≤
        m.frame.gasLeft
    · exact WP.of_step (step_extcodesize hcode hstk hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hl hg)
    · have hg' := Nat.lt_of_not_le hg
      refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
      rw [hdec]
      simp only [exec, popAddress, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
        StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind]
      rw [run_accessAddress]
      simp only [pure_bind, charge, getFrame, StateT.run_bind, StateT.run_get, StateT.run_pure,
        hg', ite_true]
      rfl
  · have hl' : Gas.stackLimit ≤ rest.length := Nat.le_of_not_lt hl
    by_cases hg : Gas.accessCost (m.frame.sub.accessedAddresses.contains (Word.toAddress x)) ≤
        m.frame.gasLeft
    · have hg' := Nat.not_lt.mpr hg
      refine wp_fail_of_error (e := .stackOverflow) hsnap hcode ?_
      rw [hdec]
      simp only [exec, popAddress, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
        StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind]
      rw [run_accessAddress]
      simp only [pure_bind, charge, push, getFrame, modifyFrame, StateT.run_bind, StateT.run_get,
        StateT.run_pure, StateT.run_modify, hg', hl', ite_true, ite_false]
      rfl
    · have hg' := Nat.lt_of_not_le hg
      refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
      rw [hdec]
      simp only [exec, popAddress, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
        StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind]
      rw [run_accessAddress]
      simp only [pure_bind, charge, getFrame, StateT.run_bind, StateT.run_get, StateT.run_pure,
        hg', ite_true]
      rfl

/-- `CHAINID` (`pwp_pushValue`). -/
theorem pwp_chainid (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x46)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (ofNat m.ctx.block.chainId) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `TIMESTAMP` (`pwp_pushValue`). -/
theorem pwp_timestamp (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x42)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (ofNat m.ctx.block.timestamp) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-! ## Copies with the memory left unknown -/

/-- The machine after an instruction that popped down to `rest` and changed only memory and
gas. -/
abbrev memGasNext (m : Machine) (rest : List Word) (mem : Memory) (g : Nat) : Machine :=
  { m with frame := { m.frame with
    stack := rest, memory := mem, gasLeft := g, pc := m.frame.pc + 1 } }

set_option linter.unusedSimpArgs false in
/-- `CALLDATACOPY`: the memory and gas after it are left unknown. -/
theorem pwp_calldatacopy {x y z : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x37)
    (hstk : m.frame.stack = x :: y :: z :: rest)
    (hrec : ∀ (mem : Memory) (g : Nat), g ≤ m.frame.gasLeft →
      WP (memGasNext m rest mem g) Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  have hdec : Opcode.decode m.ctx.fork 0x37 = .calldatacopy := by cases m.ctx.fork <;> rfl
  by_cases hg : Gas.veryLow + Gas.copyCost z.toNat + (Gas.extendMemory m.frame.memory.size
      [(x.toNat, z.toNat)]).cost ≤ m.frame.gasLeft
  · have hg' := Nat.not_lt.mpr hg
    have : ∃ mem, step m = .running (memGasNext m rest mem (m.frame.gasLeft - (Gas.veryLow +
        Gas.copyCost z.toNat + (Gas.extendMemory m.frame.memory.size [(x.toNat, z.toNat)]).cost))) := by
      by_cases hs : z.toNat = 0
      · refine ⟨m.frame.memory.expand x.toNat z.toNat, ?_⟩
        rw [step_eq_of_code hcode, hdec]
        simp only [exec, copyToMemory, popNat, pop, charge, advance, getFrame, modifyFrame,
          StateT.run_bind, hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify,
          pure_bind, ite_false, ite_true, memoryExpansion, expandMemory, List.foldl, writeMemory,
          size_readBytes]
        rw [ite_eq_left hs]
        rfl
      · refine ⟨(m.frame.memory.expand x.toNat z.toNat).write x.toNat
          (readBytes m.frame.msg.data y.toNat z.toNat), ?_⟩
        rw [step_eq_of_code hcode, hdec]
        simp only [exec, copyToMemory, popNat, pop, charge, advance, getFrame, modifyFrame,
          StateT.run_bind, hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify,
          pure_bind, ite_false, ite_true, memoryExpansion, expandMemory, List.foldl, writeMemory,
          size_readBytes, hs]
        rfl
    obtain ⟨mem, h⟩ := this
    exact WP.of_step h ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ (hrec _ _ (Nat.sub_le _ _))
  · have hg' := Nat.lt_of_not_le hg
    refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [hdec]
    simp only [exec, copyToMemory, popNat, pop, charge, advance, getFrame, modifyFrame,
      StateT.run_bind, hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      ite_true, memoryExpansion, expandMemory, List.foldl, writeMemory]
    rfl

set_option linter.unusedSimpArgs false in
/-- `MCOPY`: the memory and gas after it are left unknown. -/
theorem pwp_mcopy {x y z : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x5e)
    (hstk : m.frame.stack = x :: y :: z :: rest)
    (hrec : ∀ (mem : Memory) (g : Nat), g ≤ m.frame.gasLeft →
      WP (memGasNext m rest mem g) Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  have hdec : Opcode.decode m.ctx.fork 0x5e = .mcopy := by cases m.ctx.fork <;> rfl
  by_cases hg : Gas.veryLow + Gas.copyCost z.toNat + (Gas.extendMemory m.frame.memory.size
      [(y.toNat, z.toNat), (x.toNat, z.toNat)]).cost ≤ m.frame.gasLeft
  · have hg' := Nat.not_lt.mpr hg
    have : ∃ mem, step m = .running (memGasNext m rest mem (m.frame.gasLeft - (Gas.veryLow +
        Gas.copyCost z.toNat + (Gas.extendMemory m.frame.memory.size
          [(y.toNat, z.toNat), (x.toNat, z.toNat)]).cost))) := by
      by_cases hs : z.toNat = 0
      · refine ⟨(m.frame.memory.expand y.toNat z.toNat).expand x.toNat z.toNat, ?_⟩
        rw [step_eq_of_code hcode, hdec]
        simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame,
          StateT.run_bind, hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify,
          pure_bind, ite_false, ite_true, memoryExpansion, expandMemory, List.foldl, writeMemory,
          readMemory, size_readBytes]
        rw [ite_eq_left hs]
        rfl
      · refine ⟨((m.frame.memory.expand y.toNat z.toNat).expand x.toNat z.toNat).write x.toNat
          (readBytes ((m.frame.memory.expand y.toNat z.toNat).expand x.toNat z.toNat).bytes
            y.toNat z.toNat), ?_⟩
        rw [step_eq_of_code hcode, hdec]
        simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame,
          StateT.run_bind, hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify,
          pure_bind, ite_false, ite_true, memoryExpansion, expandMemory, List.foldl, writeMemory,
          readMemory, size_readBytes, hs]
        rfl
    obtain ⟨mem, h⟩ := this
    exact WP.of_step h ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ (hrec _ _ (Nat.sub_le _ _))
  · have hg' := Nat.lt_of_not_le hg
    refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [hdec]
    simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame,
      StateT.run_bind, hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      ite_true, memoryExpansion, expandMemory, List.foldl, writeMemory, readMemory]
    rfl

set_option linter.unusedSimpArgs false in
/-- `RETURNDATACOPY` (as `pwp_returndatacopy`), keeping that the gas after it is at most the gas
before (the bound a later call rule needs). -/
theorem pwp_returndatacopy_le {x y z : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x3e)
    (hstk : m.frame.stack = x :: y :: z :: rest)
    (hrec : ∀ (mem : Memory) (g : Nat), g ≤ m.frame.gasLeft →
      WP (memGasNext m rest mem g) Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  have hdec : Opcode.decode m.ctx.fork 0x3e = .returndatacopy := by cases m.ctx.fork <;> rfl
  by_cases hg : Gas.veryLow + Gas.copyCost z.toNat + (Gas.extendMemory m.frame.memory.size
      [(x.toNat, z.toNat)]).cost ≤ m.frame.gasLeft
  · have hg' := Nat.not_lt.mpr hg
    by_cases hb : y.toNat + z.toNat ≤ m.frame.returnData.size
    · have hb' := Nat.not_lt.mpr hb
      have : ∃ mem, step m = .running (memGasNext m rest mem (m.frame.gasLeft - (Gas.veryLow +
          Gas.copyCost z.toNat + (Gas.extendMemory m.frame.memory.size
            [(x.toNat, z.toNat)]).cost))) := by
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
      exact WP.of_step h ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ (hrec _ _ (Nat.sub_le _ _))
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

end EvmLogic.Program.Reentrancy
