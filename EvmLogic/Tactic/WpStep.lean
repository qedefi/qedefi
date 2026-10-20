import Lean
import EvmLogic.Tactic.EvmStep
import EvmLogic.Program.Logic
import EvmLogic.Program.Code
import EvmLogic.Word
import EvmLogic.Step.Memory

/-!
# Symbolic execution in the frame-local logic: `wp_step`

The step lemmas of `evm_step`, applied to goals `WP m Q H` (`EvmLogic.Program.Logic`) through
`WP.of_step` / `WP.halt_of_step`, with `SameFrame` by `same_frame`. Code bytes and pushed
immediates are kernel-checked facts read from the literal code. See `docs/proving.md` §3.
-/

section

namespace EvmLogic.Program
open EvmLean Lean Elab Tactic EvmLogic.Tactic Meta EvmLean.Interpreter

/-- Prove `SameFrame m m'` field by field with `dsimp only`, which unlike `rfl` never compares
whole machines (that can unfold the code and the jump table). -/
macro "same_frame" : tactic =>
  `(tactic| (constructor <;> first | (dsimp only [outputMachine]; done) | exact rfl))

initialize registerTraceClass `EvmLean.wp

/-- The step lemmas to try for an opcode byte, and whether it halts the frame (not `PUSHn`). -/
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
  extraStepLemmas : List (Nat × Name) := []

/-- Run `tac`; any failure, including runtime exceptions (recursion limit), gives `false`. -/
def tryTac (tac : TacticM Unit) : TacticM Bool := do
  let saved ← saveState
  tryCatchRuntimeEx (do withoutRecover tac; return true)
    (fun _ => do saved.restore; return false)

/-- Discharge a step-lemma side condition. Order matters for speed: inequalities go to
`evm_gas` before `decide`, equalities to `exact rfl`, `assumption` last. -/
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

/-- Close `code[pc]? = some b` for literal code and a numeral `pc` (kernel-checked). -/
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

/-- Advance `WP m Q H` by one instruction; `false` (goal unchanged) if no step lemma applies. -/
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
    trace[EvmLean.symStep] "pc {pc}, byte {b}"
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

/-- Advance a goal `WP m Q H` by one instruction. -/
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

def wpRunTo (pcs : List Nat) (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma))
    (limit : Nat := 1000000) : TacticM Unit := do
  for i in [0:limit] do
    let g ← getMainGoal
    if i > 0 then
      if let some pc ← wpGoalPc? g then
        if pcs.contains pc then return
    unless ← wpStep extra do return

/-- `wp_run_to pc₁, … [h₁, …]`: step until the pc is one of the `pcᵢ` (after at least one
step, so it can loop back to its head) or no step lemma applies. -/
syntax "wp_run_to " num,+ (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| wp_run_to $pcs,* $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    wpRunTo (pcs.getElems.toList.map (·.getNat)) extra

/-- Destructure the machine `m` into fields `m_ctx`, `m_world`, … and substitute equations
about them (the jump table is kept as a `JumpTable` hypothesis). -/
syntax "wp_intro " ident : tactic

/-- Turn every hypothesis `x = validJumpDests c` into `JumpTable x c` (so `subst` keeps it). -/
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

end EvmLogic.Program

end

section

/-!
## Gas side conditions over symbolic memory

With memory a variable `M`, expansion costs are `if`s on `M.size` that `omega` cannot see
through; `evm_gas` is extended to rewrite with hypotheses `Memory.size M = n` (`rw_mem_sizes`).
-/

namespace EvmLogic.Program
open EvmLean Lean Elab Tactic EvmLogic.Tactic Meta EvmLean.Interpreter

/-- Rewrite the goal and other hypotheses with each hypothesis `Memory.size M = n`. -/
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

/-- `wp_generalize_gas g h`: replace the gas of a `WP` goal's machine by a variable `g`
(`h : expr = g`); keeps side conditions cheap after a call's large gas expression. -/
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

end EvmLogic.Program

end
