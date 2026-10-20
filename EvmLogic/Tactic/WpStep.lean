import Lean
import EvmLogic.Tactic.EvmStep
import EvmLogic.Program.Logic
import EvmLogic.Program.Code
import EvmLogic.Word
import EvmLogic.Step.Memory

/-!
# Symbolic execution in the frame-local logic

The tactics of `EvmLeanProofs.Tactic` advance goals of the form `run (n + 1) m = …`. Here the
same step lemmas advance goals `WP m Q H` (`EvmLeanProofs.Program.Logic`), where `m` is a
machine whose code, pc and stack shape are literal (values may be symbolic):

* `wp_step [h₁, …]` applies `WP.of_step` with the step lemma for the next instruction (found
  by `evm_step_core`, side conditions by `evm_disch`), proves `SameFrame` by `rfl`, and
  normalizes the new machine with `evm_norm [h₁, …]`. On a halting instruction (`STOP`,
  `RETURN`, `REVERT`, `INVALID`) it applies `WP.halt_of_step` with the frame-generic step lemma
  instead (any parents, not only top level), leaving the goal `H mf o`.
* `wp_steps [h₁, …]` repeats `wp_step`; `wp_steps n [h₁, …]` does at most `n` steps.
* `wp_run_to pc₁, pc₂, … [h₁, …]` steps until the pc of the machine is one of the given
  values (the starting pc does not count, so it can run around a loop back to its head), or
  until `wp_step` fails (e.g. at a `JUMPI` with a symbolic condition).
* `wp_intro m` destructures a machine variable `m` into its fields and substitutes the
  equations about them (code, pc, stack, …) from the context, so that the step lemmas apply.
* `same_frame` proves `SameFrame m m'` when `m'` is `m` with only mutable fields changed.

Jump destinations are checked by `decide` (as in `evm_step`) unless a hypothesis
`isValidJumpDest jd d = true` is in the context: `evm_disch` is extended here to try
`assumption` first, so precomputed facts about large code are used before evaluation.
-/

section

namespace EvmLean.Program

open Lean Elab Tactic Meta
open Interpreter

/-- Prove `SameFrame m m'` when `m'` only changes mutable fields of `m`. Each field is closed
by `dsimp only` (projections of structure instances), which unlike `rfl` never asks the
unifier to compare whole machines (that can unfold the code and the jump table). -/
macro "same_frame" : tactic =>
  `(tactic| (constructor <;> first | (dsimp only [outputMachine]; done) | exact rfl))

initialize registerTraceClass `EvmLean.wp

/-- The step lemmas to try for an opcode byte, and whether the instruction halts the frame.
`PUSHn` is handled separately (`step_push_val` with a `pushFact`). -/
def stepLemmasFor (b : Nat) : List Name × Bool :=
  let arith : List (Nat × Name) := [
    (0x01, ``step_add), (0x02, ``step_mul), (0x03, ``step_sub), (0x04, ``step_div),
    (0x05, ``step_sdiv), (0x06, ``step_mod), (0x07, ``step_smod), (0x08, ``step_addmod),
    (0x09, ``step_mulmod), (0x0a, ``step_exp), (0x0b, ``step_signextend),
    (0x10, ``step_lt), (0x11, ``step_gt), (0x12, ``step_slt), (0x13, ``step_sgt),
    (0x14, ``step_eq), (0x15, ``step_iszero), (0x16, ``step_and), (0x17, ``step_or),
    (0x18, ``step_xor), (0x19, ``step_not), (0x1a, ``step_byte), (0x1b, ``step_shl),
    (0x1c, ``step_shr), (0x1d, ``step_sar), (0x20, ``step_keccak256),
    (0x30, ``step_address), (0x32, ``step_origin), (0x33, ``step_caller),
    (0x34, ``step_callvalue), (0x35, ``step_calldataload), (0x36, ``step_calldatasize),
    (0x38, ``step_codesize), (0x3a, ``step_gasprice), (0x3d, ``step_returndatasize),
    (0x41, ``step_coinbase), (0x42, ``step_timestamp), (0x43, ``step_number),
    (0x44, ``step_prevrandao), (0x45, ``step_gaslimit), (0x46, ``step_chainid),
    (0x47, ``step_selfbalance), (0x48, ``step_basefee),
    (0x50, ``step_pop), (0x51, ``step_mload), (0x52, ``step_mstore), (0x53, ``step_mstore8),
    (0x54, ``step_sload), (0x55, ``step_sstore), (0x56, ``step_jump),
    (0x58, ``step_pc), (0x59, ``step_msize), (0x5a, ``step_gas), (0x5b, ``step_jumpdest),
    (0xa0, ``step_log0), (0xa1, ``step_log1), (0xa2, ``step_log2), (0xa3, ``step_log3),
    (0xa4, ``step_log4)]
  let dups : List Name := [``step_dup1, ``step_dup2, ``step_dup3, ``step_dup4, ``step_dup5,
    ``step_dup6, ``step_dup7, ``step_dup8, ``step_dup9, ``step_dup10, ``step_dup11,
    ``step_dup12, ``step_dup13, ``step_dup14, ``step_dup15, ``step_dup16]
  let swaps : List Name := [``step_swap1, ``step_swap2, ``step_swap3, ``step_swap4,
    ``step_swap5, ``step_swap6, ``step_swap7, ``step_swap8, ``step_swap9, ``step_swap10,
    ``step_swap11, ``step_swap12, ``step_swap13, ``step_swap14, ``step_swap15, ``step_swap16]
  if b = 0x00 then ([``step_stop], true)
  else if b = 0xf3 then ([``step_return], true)
  else if b = 0xfd then ([``step_revert], true)
  else if b = 0xfe then ([``step_invalid], true)
  else if b = 0x57 then ([``step_jumpi_of_eq_zero, ``step_jumpi_of_ne_zero], false)
  else if 0x80 ≤ b ∧ b < 0x90 then ((dups[b - 0x80]?).toList, false)
  else if 0x90 ≤ b ∧ b < 0xa0 then ((swaps[b - 0x90]?).toList, false)
  else ((arith.lookup b).toList ++ (extraStepLemmas.lookup b).toList, false)
where
  /-- Step lemmas of `EvmLeanProofs.Program` for opcodes the base library does not cover. -/
  extraStepLemmas : List (Nat × Name) := []

/-- Run `tac`, turning any failure (including runtime exceptions such as the recursion limit)
into `false` with the state restored. -/
def tryTac (tac : TacticM Unit) : TacticM Bool := do
  let saved ← saveState
  tryCatchRuntimeEx (do withoutRecover tac; return true)
    (fun _ => do saved.restore; return false)

/-- Discharge a side condition of a step lemma. Order matters for speed and robustness:
inequalities (gas, stack bounds) go to `evm_gas` (`omega`) before `decide`; equalities
(stack shapes, opcode immediates) to `exact rfl`; jump destinations to `jumpdest_disch`;
`assumption` last. -/
def wpDisch : TacticM Unit := withMainContext do
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  let isIneq := t.isAppOf ``LE.le || t.isAppOf ``LT.lt
  let isJd := match t.eq? with
    | some (_, lhs, _) => lhs.isAppOf ``isValidJumpDest
    | none => false
  let alts : List (TSyntax `tactic) ←
    if isJd then pure [← `(tactic| jumpdest_disch), ← `(tactic| assumption)]
    else if isIneq then
      pure [← `(tactic| evm_gas), ← `(tactic| decide), ← `(tactic| assumption)]
    else pure [← `(tactic| exact rfl), ← `(tactic| decide), ← `(tactic| assumption)]
  for a in alts do
    if ← tryTac (evalTactic a) then return
  throwError "wp_disch: cannot discharge side condition"

/-- `wp_disch`: see `wpDisch`. -/
elab "wp_disch" : tactic => wpDisch

/-- Close a goal `code[pc]? = some b` for literal code (behind projections of a literal
machine) and a numeral `pc`, by a kernel-checked fact (`codeFact`). -/
elab "code_fact" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let_expr Eq _ lhs rhs := t | throwError "code_fact: not an equation"
  let_expr GetElem?.getElem? _ _ _ _ _ coll i := lhs | throwError "code_fact: not `code[pc]?`"
  let code ← whnfR coll
  let some pc ← (evalNat (← whnfR i)).run | throwError "code_fact: pc is not a numeral"
  let some bytes ← codeBytes? code | throwError "code_fact: code is not a literal"
  let some b := bytes[pc]? | throwError "code_fact: pc out of range"
  let_expr Option.some _ v := rhs | throwError "code_fact: right side is not `some b`"
  let some v ← uint8Lit? v | throwError "code_fact: right side is not a literal"
  unless v = b.toNat do throwError "code_fact: the byte at {pc} is {b}, not {v}"
  g.assign (← codeFact code pc b)
  replaceMainGoal []

/-- The machine of a goal `WP m Q H`. -/
def wpGoalMachine? (g : MVarId) : MetaM (Option Expr) := do
  let t ← instantiateMVars (← g.getType)
  let_expr WP m _ _ := t | return none
  return some m

/-- Advance a goal `WP m Q H` by one instruction. Returns `false` (leaving the goal unchanged)
if no step lemma applies. -/
def wpStep (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Bool :=
  withMainContext do
  let g ← getMainGoal
  let some m ← wpGoalMachine? g | return false
  let code ← whnfR (mkApp (mkConst ``Frame.code) (← whnfR (mkApp (mkConst ``Machine.frame) m)))
  let pcE ← whnfR (mkApp (mkConst ``Frame.pc) (← whnfR (mkApp (mkConst ``Machine.frame) m)))
  let some pc ← (evalNat (← instantiateMVars pcE)).run | return false
  let some bytes ← codeBytes? code | return false
  let some b := bytes[pc]? | return false
  let hb ← Term.exprToSyntax (← codeFact code pc b)
  let saved ← saveState
  let attempt (t : TSyntax `tactic) : TacticM Bool := do
    tryCatchRuntimeEx
      (do withoutRecover (evalTactic t); return true)
      (fun e => do
        trace[EvmLean.wp] "pc {pc}, byte {b}: {e.toMessageData}"
        saved.restore
        return false)
  let norm : TacticM Unit := do
    try evalTactic (← `(tactic| evm_norm [List.set_cons_zero, List.set_cons_succ, Nat.sub_sub,
      Memory.loadWord_expand, Memory.read_expand, Memory.loadWord_storeWord, Memory.read_storeWord,
      Memory.loadWord_storeWord_of_disjoint, Memory.read_storeWord_of_disjoint, true_or, or_true,
      reduceClosedWord, Bytes.size_ofWord,
      $extra,*]))
    catch _ => pure ()
  if 0x5f ≤ b.toNat ∧ b.toNat ≤ 0x7f then
    let n := b.toNat - 0x5f
    let hv ← Term.exprToSyntax (← pushFact code bytes pc n)
    let nS := Syntax.mkNumLit (toString n)
    if ← attempt (← `(tactic| (
        apply WP.of_step
        case h =>
          apply step_push_val $nS (by decide)
          case hcode => exact $hb
          case hval => exact $hv
          all_goals wp_disch
        case hs => same_frame))) then
      norm
      return true
    return false
  let (lemmas, halts) := stepLemmasFor b.toNat
  for l in lemmas do
    let lS := mkIdent l
    let t ← if halts then
      `(tactic| (
        apply WP.halt_of_step
        case h =>
          apply $lS
          case hcode => exact $hb
          all_goals wp_disch
        case hs => same_frame))
    else
      `(tactic| (
        apply WP.of_step
        case h =>
          apply $lS
          case hcode => exact $hb
          all_goals wp_disch
        case hs => same_frame))
    if ← attempt t then
      norm
      return true
  return false

/-- Advance a goal `WP m Q H` by one instruction (see the module docstring). -/
syntax "wp_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| wp_step $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    unless ← wpStep extra do
      throwError "wp_step: no step lemma applies to the next instruction"

/-- Repeat `wp_step` while it succeeds (at most `n` times if a bound is given). -/
syntax "wp_steps" (ppSpace num)? (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| wp_steps $[$n]? $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let limit := (n.map (·.getNat)).getD 1000000
    for _ in [0:limit] do
      unless ← wpStep extra do return

/-- The program counter of the machine in a goal `WP m Q H`, if it is a numeral. -/
def wpGoalPc? (g : MVarId) : MetaM (Option Nat) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let_expr WP m _ _ := t | return none
  let pc ← whnfD (mkApp (mkConst ``Frame.pc) (mkApp (mkConst ``Machine.frame) m))
  (evalNat (← instantiateMVars pc)).run

/-- Step a `WP` goal until its pc is one of `pcs` (after at least one step), or no step
lemma applies, or `limit` steps were taken. -/
def wpRunTo (pcs : List Nat) (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma))
    (limit : Nat := 1000000) : TacticM Unit := do
  for i in [0:limit] do
    let g ← getMainGoal
    if i > 0 then
      if let some pc ← wpGoalPc? g then
        if pcs.contains pc then return
    unless ← wpStep extra do return

/-- `wp_run_to pc₁, … [h₁, …]`: step until the pc is one of the `pcᵢ` (see the module
docstring). -/
syntax "wp_run_to " num,+ (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| wp_run_to $pcs,* $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    wpRunTo (pcs.getElems.toList.map (·.getNat)) extra

/-- Destructure the machine variable `m` into its fields `m_ctx`, `m_world`, `m_msg`,
`m_gasLeft`, `m_sub`, … and substitute equations about them from the context (except the
jump table, kept as a `JumpTable` hypothesis). -/
syntax "wp_intro " ident : tactic

/-- Turn every hypothesis `x = validJumpDests c` into `JumpTable x c` (so that `subst` keeps
it; see `JumpTable`). -/
elab "wp_hide_jump_tables" : tactic => withMainContext do
  let mut g ← getMainGoal
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let some (_, lhs, rhs) := ty.eq? | continue
    let some code := rhs.app1? ``validJumpDests | continue
    unless lhs.isFVar do continue
    g ← g.replaceLocalDeclDefEq decl.fvarId (mkApp2 (mkConst ``JumpTable) lhs code)
  replaceMainGoal [g]

macro_rules
  | `(tactic| wp_intro $m) => do
    let n (f : String) : TSyntax `ident := mkIdent (Name.mkSimple (m.getId.toString ++ "_" ++ f))
    `(tactic| (
      obtain ⟨$(n "ctx"), $(n "pre"), $(n "world"), $(n "transient"), $(n "originalWorld"),
        $(n "created"), ⟨$(n "msg"), $(n "code"), $(n "jumpDests"), $(n "pc"), $(n "stack"),
          $(n "memory"), $(n "gasLeft"), $(n "returnData"), $(n "sub"), $(n "snapshot"),
          $(n "kind")⟩, $(n "parents")⟩ := $m
      dsimp only at *
      wp_hide_jump_tables
      subst_vars))

end EvmLean.Program

end

section

/-!
## Gas side conditions over symbolic memory

`evm_gas` normalizes the memory-expansion cost of an access and calls `omega`. When the
memory of the machine is a variable `M` (as in summaries of internal functions that are called
at different memory states), the cost is an `if` on `M.size`, which `omega` cannot see
through, even with a hypothesis `M.size = n` in context.

* `wp_generalize_gas g h` replaces the gas expression of a `WP` goal's machine by a variable.
* `rw_mem_sizes` rewrites the goal and hypotheses with every hypothesis of the form `Memory.size M = n`.
* An alternative expansion of `evm_gas` (tried before the original one) normalizes, runs
  `rw_mem_sizes` (sizes of `storeWord`/`expand` terms over `M` only appear after the first
  normalization) and normalizes again, so that the expansion cost evaluates. When it fails,
  the original `evm_gas` runs.
-/

namespace EvmLean.Program

open Lean Elab Tactic Meta
open EvmLean.Interpreter

/-- Rewrite the goal, and every other hypothesis mentioning `Memory.size`, with each hypothesis
`Memory.size M = n` (no-op if there is none). -/
elab "rw_mem_sizes" : tactic => withMainContext do
  let lctx ← getLCtx
  let mut sizeHyps : Array LocalDecl := #[]
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let some (_, lhs, _) := ty.eq? | continue
    if lhs.isAppOfArity ``Memory.size 1 then sizeHyps := sizeHyps.push decl
  for h in sizeHyps do
    let hS ← Term.exprToSyntax h.toExpr
    try evalTactic (← `(tactic| simp only [$hS:term])) catch _ => pure ()
    for decl in lctx do
      if decl.isImplementationDetail || decl.fvarId == h.fvarId then continue
      if decl.userName.hasMacroScopes then continue
      let ty ← instantiateMVars decl.type
      unless (ty.find? (·.isConstOf ``Memory.size)).isSome do continue
      if sizeHyps.any (·.fvarId == decl.fvarId) then continue
      let n := mkIdent decl.userName
      try evalTactic (← `(tactic| simp only [$hS:term] at $n:ident)) catch _ => pure ()

/-- `wp_generalize_gas g h`: in a goal `WP m Q H` whose machine is a structure literal,
replace the frame's gas expression by a new variable `g` (with `h : expr = g`). After a call
the gas left is a large expression (EIP-150 forwarding, the callee's refund); proving a bound
on `g` once and generalizing keeps the gas side conditions of the following steps cheap. -/
elab "wp_generalize_gas " g:ident h:ident : tactic => withMainContext do
  let some m ← wpGoalMachine? (← getMainGoal) | throwError "wp_generalize_gas: not a WP goal"
  let fr ← whnfR (mkApp (mkConst ``Machine.frame) m)
  let gas ← whnfR (mkApp (mkConst ``Frame.gasLeft) fr)
  let gasS ← Term.exprToSyntax gas
  evalTactic (← `(tactic| generalize $h : $gasS = $g))

/-- The normalization `evm_gas` applies to memory-expansion and other costs. -/
macro "evm_gas_norm" : tactic => `(tactic|
  try simp only [memoryCost, outputCost, Gas.extendMemory, List.foldl, Gas.ceil32,
    Gas.memoryCost, Gas.words, Gas.memoryPerWord, Memory.size_storeWord, Memory.size_expand,
    Memory.size_empty, Memory.wordsAfter, Memory.words, Gas.logCost, Gas.logBase,
    Gas.logDataPerByte, Gas.logTopic, Gas.keccak256Cost, Gas.keccak256Base,
    Gas.keccak256PerWord, BitVec.reduceToNat, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
    Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.max_def, ↓reduceIte] at *)

macro_rules
  | `(tactic| evm_gas) => `(tactic| (
    rw_mem_sizes
    evm_gas_bounds
    try dsimp only at *
    evm_gas_norm
    rw_mem_sizes
    evm_gas_norm
    try simp only [Gas.base, Gas.veryLow, Gas.low, Gas.mid, Gas.high, Gas.jumpdest,
      Gas.fastStep, Gas.callStipend, Gas.warmAccess, Gas.coldStorageAccess, List.length_cons,
      List.length_nil] at *
    omega))

end EvmLean.Program

end
