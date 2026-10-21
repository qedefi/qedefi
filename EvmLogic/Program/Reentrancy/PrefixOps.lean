import EvmLogic.Program.Reentrancy.Prefix
import EvmLogic.Solidity.Steps

/-!
# More rules of the any-gas prefix calculus

The rules of `EvmLogic.Program.Reentrancy.Prefix` for the remaining instructions of a Solidity
function body up to its external call: one rule per arithmetic, comparison and environment
opcode (`pwp_add`, `pwp_eq`, `pwp_caller`, …, instances of `pwp_binOp`/`pwp_unOp`/
`pwp_pushValue`), `SWAPn` (`pwp_swap`), both branches of `JUMPI` at once (`pwp_jumpi`),
`KECCAK256`, `MLOAD` with its value (`pwp_mload_val`), `CODECOPY` (solc's 32-byte constants),
`RETURNDATACOPY` (the memory after it is left unknown), and the frame ends: `REVERT` and
`INVALID` are always acceptable (the snapshot is `Good`), `STOP` and `RETURN` hand back the
current world, which must then be `Good`. Each rule takes the instruction when gas and stack
allow and otherwise absorbs the failure (`FailOk`). The tactic `apwp_steps`
(`EvmLogic.Tactic.PrefixStep`) drives them.
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program

variable {Good : World → Prop} {Q : Machine → Prop} {m : Machine}

/-! ## Stack -/

/-- `SWAP(n+1)`. -/
theorem pwp_swap (n : Fin 16) {x y : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some (0x90 + n.val).toUInt8)
    (hstk : m.frame.stack = y :: rest) (hget : m.frame.stack[n.val + 1]? = some x)
    (hrec : Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := ((y :: rest).set 0 x).set (n.val + 1) y, gasLeft := m.frame.gasLeft - Gas.veryLow,
      pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x57)
    (hstk : m.frame.stack = x :: c :: rest)
    (hz : c = 0 → Gas.high ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := rest, gasLeft := m.frame.gasLeft - Gas.high, pc := m.frame.pc + 1 } } Q
      (FailOk Good))
    (hnz : c ≠ 0 → isValidJumpDest m.frame.jumpDests x.toNat = true →
      Gas.high ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
        stack := rest, gasLeft := m.frame.gasLeft - Gas.high, pc := x.toNat } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  by_cases hc : c = 0
  · subst hc; exact pwp_jumpi_zero hsnap hcode hstk (hz rfl)
  · exact pwp_jumpi_ne_zero hsnap hcode hstk hc (hnz hc)

/-! ## Hashing and memory -/

/-- `KECCAK256` of memory `[x, x + y)`. -/
theorem pwp_keccak256 {x y : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x20)
    (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.keccak256Cost y.toNat + (Gas.extendMemory
      m.frame.memory.size [(x.toNat, y.toNat)]).cost ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := m.ctx.crypto.keccak256
          (readBytes (m.frame.memory.expand x.toNat y.toNat).bytes x.toNat y.toNat) :: rest,
        memory := m.frame.memory.expand x.toNat y.toNat,
        gasLeft := m.frame.gasLeft - (Gas.keccak256Cost y.toNat +
          (Gas.extendMemory m.frame.memory.size [(x.toNat, y.toNat)]).cost),
        pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x51)
    (hstk : m.frame.stack = x :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow + memoryCost m x 32 ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := (m.frame.memory.expand x.toNat 32).loadWord x.toNat :: rest,
        memory := m.frame.memory.expand x.toNat 32,
        gasLeft := m.frame.gasLeft - (Gas.veryLow + memoryCost m x 32), pc := m.frame.pc + 1 } } Q
        (FailOk Good)) :
    WP m Q (FailOk Good) := by
  by_cases hg : Gas.veryLow + memoryCost m x 32 ≤ m.frame.gasLeft
  · by_cases hl : rest.length < 1024
    · exact WP.of_step (step_mload hcode hstk hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hl hg)
    · exact pwp_mload hsnap hcode hstk fun _ hl' => absurd hl' hl
  · exact pwp_mload hsnap hcode hstk fun _ _ hg' => absurd hg' hg

/-! ## The end of the frame -/

/-- `REVERT` (or its failure): the snapshot is handed back. -/
theorem pwp_revert {x y : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0xfd)
    (hstk : m.frame.stack = x :: y :: rest) :
    WP m Q (FailOk Good) := by
  by_cases hg : outputCost m x y ≤ m.frame.gasLeft
  · exact WP.halt_of_step (step_revert hcode hstk hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      (by show Good (frameResult _ (.revert _)).2.1; rw [frameResult_revert]; exact hsnap)
  · have hg' : m.frame.gasLeft < outputCost m x y := Nat.lt_of_not_le hg
    simp only [outputCost] at hg'
    refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [show Opcode.decode m.ctx.fork 0xfd = .revert by cases m.ctx.fork <;> rfl]
    simp only [exec, readOutput, popNat, pop, charge, getFrame, modifyFrame, StateT.run_bind,
      hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true,
      memoryExpansion, expandMemory, List.foldl, readMemory]
    rfl

/-- `INVALID`: an exceptional halt hands back the snapshot. -/
theorem pwp_invalid (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0xfe) : WP m Q (FailOk Good) :=
  WP.halt_of_step (step_invalid hcode) (.refl m)
    (by show Good (frameResult m (.halt _)).2.1; rw [frameResult_halt]; exact hsnap)

/-- `STOP` in a message-call frame: the current world, which must be `Good`. -/
theorem pwp_stop {ko ks : Nat} (hcode : m.frame.code[m.frame.pc]? = some 0x00)
    (hkind : m.frame.kind = .call ko ks) (hw : Good m.world) : WP m Q (FailOk Good) :=
  WP.halt_of_step (step_stop hcode) (.refl m)
    (by show Good (frameResult m (.success _)).2.1; rw [frameResult_success_call hkind]; exact hw)

/-- `RETURN` in a message-call frame (or its failure): the current world, which must be `Good`. -/
theorem pwp_return {ko ks : Nat} {x y : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0xf3)
    (hstk : m.frame.stack = x :: y :: rest) (hkind : m.frame.kind = .call ko ks)
    (hw : Good m.world) : WP m Q (FailOk Good) := by
  by_cases hg : outputCost m x y ≤ m.frame.gasLeft
  · exact WP.halt_of_step (step_return hcode hstk hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      (by
        show Good (frameResult (outputMachine m x y rest) (.success _)).2.1
        rw [frameResult_success_call (mf := outputMachine m x y rest) (o := ko) (s := ks) hkind]
        exact hw)
  · have hg' : m.frame.gasLeft < outputCost m x y := Nat.lt_of_not_le hg
    simp only [outputCost] at hg'
    refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [show Opcode.decode m.ctx.fork 0xf3 = .«return» by cases m.ctx.fork <;> rfl]
    simp only [exec, readOutput, popNat, pop, charge, getFrame, modifyFrame, StateT.run_bind,
      hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, ite_true,
      memoryExpansion, expandMemory, List.foldl, readMemory]
    rfl

/-! ## Copies -/

/-- `CODECOPY` of `z ≠ 0` bytes. -/
theorem pwp_codecopy {x y z : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x39)
    (hstk : m.frame.stack = x :: y :: z :: rest) (hz : z.toNat ≠ 0)
    (hrec : 3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := rest,
        memory := (m.frame.memory.expand x.toNat z.toNat).write x.toNat
          (readBytes m.frame.code y.toNat z.toNat),
        gasLeft := m.frame.gasLeft - (3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat),
        pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x3e)
    (hstk : m.frame.stack = x :: y :: z :: rest)
    (hrec : ∀ (mem : Memory) (g : Nat), WP { m with frame := { m.frame with
      stack := rest, memory := mem, gasLeft := g, pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
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
theorem pwp_add {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x01) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (x + y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `MUL` (`pwp_binOp`). -/
theorem pwp_mul {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x02) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.low ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (x * y) :: rest, gasLeft := m.frame.gasLeft - Gas.low, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `SUB` (`pwp_binOp`). -/
theorem pwp_sub {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x03) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (x - y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `DIV` (`pwp_binOp`). -/
theorem pwp_div {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x04) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.low ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.div x y) :: rest, gasLeft := m.frame.gasLeft - Gas.low, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `MOD` (`pwp_binOp`). -/
theorem pwp_mod {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x06) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.low ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.mod x y) :: rest, gasLeft := m.frame.gasLeft - Gas.low, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `LT` (`pwp_binOp`). -/
theorem pwp_lt {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x10) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.lt x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `GT` (`pwp_binOp`). -/
theorem pwp_gt {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x11) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.gt x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `SLT` (`pwp_binOp`). -/
theorem pwp_slt {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x12) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.slt x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `SGT` (`pwp_binOp`). -/
theorem pwp_sgt {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x13) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.sgt x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `EQ` (`pwp_binOp`). -/
theorem pwp_eq {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x14) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.eq x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `AND` (`pwp_binOp`). -/
theorem pwp_and {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x16) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (x &&& y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `OR` (`pwp_binOp`). -/
theorem pwp_or {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x17) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (x ||| y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `XOR` (`pwp_binOp`). -/
theorem pwp_xor {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x18) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (x ^^^ y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `BYTE` (`pwp_binOp`). -/
theorem pwp_byte {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x1a) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.byte x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `SHL` (`pwp_binOp`). -/
theorem pwp_shl {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x1b) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.shl x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `SHR` (`pwp_binOp`). -/
theorem pwp_shr {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x1c) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.shr x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `SAR` (`pwp_binOp`). -/
theorem pwp_sar {x y : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x1d) (hstk : m.frame.stack = x :: y :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.sar x y) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_binOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `ISZERO` (`pwp_unOp`). -/
theorem pwp_iszero {x : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x15) (hstk : m.frame.stack = x :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.iszero x) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_unOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `NOT` (`pwp_unOp`). -/
theorem pwp_not {x : Word} {rest : List Word} (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x19) (hstk : m.frame.stack = x :: rest)
    (hrec : rest.length < 1024 → Gas.veryLow ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (~~~x) :: rest, gasLeft := m.frame.gasLeft - Gas.veryLow, pc := m.frame.pc + 1 } } Q
      (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_unOp hsnap (fun fk => by cases fk <;> rfl) hcode hstk hrec

/-- `ADDRESS` (`pwp_pushValue`). -/
theorem pwp_address (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x30)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.ofAddress m.frame.msg.currentTarget) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `CALLER` (`pwp_pushValue`). -/
theorem pwp_caller (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x33)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (Word.ofAddress m.frame.msg.caller) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `CALLVALUE` (`pwp_pushValue`). -/
theorem pwp_callvalue (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x34)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (m.frame.msg.value) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `CALLDATASIZE` (`pwp_pushValue`). -/
theorem pwp_calldatasize (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x36)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (ofNat m.frame.msg.data.size) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `CODESIZE` (`pwp_pushValue`). -/
theorem pwp_codesize (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x38)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (ofNat m.frame.code.size) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `RETURNDATASIZE` (`pwp_pushValue`). -/
theorem pwp_returndatasize (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x3d)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (ofNat m.frame.returnData.size) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `SELFBALANCE` (`pwp_pushValue`). -/
theorem pwp_selfbalance (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x47)
    (hrec : m.frame.stack.length < 1024 → Gas.fastStep ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (m.world.balance m.frame.msg.currentTarget) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.fastStep,
      pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `PC` (`pwp_pushValue`). -/
theorem pwp_pc (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x58)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (ofNat m.frame.pc) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `MSIZE` (`pwp_pushValue`). -/
theorem pwp_msize (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x59)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (ofNat m.frame.memory.size) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `GAS` (`pwp_pushValue`). -/
theorem pwp_gas (hsnap : Good m.frame.snapshot.1)
    (hcode : m.frame.code[m.frame.pc]? = some 0x5a)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft → WP { m with frame := { m.frame with
      stack := (ofNat (m.frame.gasLeft - Gas.base)) :: m.frame.stack, gasLeft := m.frame.gasLeft - Gas.base,
      pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

end EvmLogic.Program.Reentrancy
