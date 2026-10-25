import Verified.Solady.Spec.AnyGas
import EvmLogic.Tactic.PrefixStep

/-!
# `hwp_step` / `hwp_steps`: symbolic execution for any gas and any postcondition

`apwp_steps` (`EvmLogic.Tactic.PrefixStep`) with the rules of `Verified.Solady.Spec.AnyGas`:
goals `WP m Q H` with a hypothesis `FailH H` in context (found by `assumption`), no gas lower
bound. `JUMPI` splits on symbolic conditions (closing branches the normalization decides),
`REVERT` and `INVALID` close their goal, `SSTORE` and `LOG3` are stepped in any frame (a static
one fails), the gas is generalized after each step (unlike `apwp_steps`, the substate is kept:
a success's logs are part of the postcondition). A goal stops at `STOP`,
`RETURN`, or an instruction without a rule. The helpers (normalization, generalization,
branch closing) are those of `apwp_steps`; only the choice of rules differs.
-/

namespace Verified.Solady.Spec.AnyGasTactic
open EvmLean Lean Meta Elab Tactic EvmLean.Interpreter EvmLogic.Program
open EvmLogic.Tactic.PrefixStep Verified.Solady.Spec.AnyGas

/-- The rule of a byte, if it is applied uniformly (not `PUSH`/`DUP`/`SWAP`/`JUMPI`/halts). -/
def ruleFor (b : Nat) : Option Rule :=
  let bin : List (Nat × Name) := [(0x01, ``pwp_add), (0x02, ``pwp_mul), (0x03, ``pwp_sub),
    (0x04, ``pwp_div), (0x06, ``pwp_mod), (0x10, ``pwp_lt), (0x11, ``pwp_gt),
    (0x12, ``pwp_slt), (0x13, ``pwp_sgt), (0x14, ``pwp_eq), (0x16, ``pwp_and),
    (0x17, ``pwp_or), (0x18, ``pwp_xor), (0x1a, ``pwp_byte), (0x1b, ``pwp_shl),
    (0x1c, ``pwp_shr), (0x1d, ``pwp_sar), (0x15, ``pwp_iszero), (0x19, ``pwp_not),
    (0x20, ``pwp_keccak256), (0x35, ``pwp_calldataload), (0x51, ``pwp_mload_val),
    (0x54, ``pwp_sload), (0x0a, ``pwp_exp)]
  let pv : List (Nat × Name) := [(0x30, ``pwp_address), (0x33, ``pwp_caller),
    (0x34, ``pwp_callvalue), (0x36, ``pwp_calldatasize), (0x38, ``pwp_codesize),
    (0x3d, ``pwp_returndatasize), (0x47, ``pwp_selfbalance), (0x58, ``pwp_pc),
    (0x59, ``pwp_msize), (0x5a, ``pwp_gas)]
  match bin.lookup b with
  | some l => some { lemma := l }
  | none =>
    match pv.lookup b with
    | some l => some { lemma := l, stk := false }
    | none =>
      if b = 0x50 then some { lemma := ``pwp_pop, intros := 1 }
      else if b = 0x52 then some { lemma := ``pwp_mstore, intros := 1 }
      else if b = 0x56 then some { lemma := ``pwp_jump }
      else if b = 0x5b then some { lemma := ``pwp_jumpdest, stk := false, intros := 1 }
      else none

/-- One step of the main goal. `none`: no rule applies (the goal is unchanged). -/
def hwpStep (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TacticM (Option (List MVarId)) := withMainContext do
  let g ← getMainGoal
  let some m ← wpGoalMachine? g | return none
  let fr ← whnfR (mkApp (mkConst ``Machine.frame) m)
  let code ← whnfR (mkApp (mkConst ``Frame.code) fr)
  let pcE ← whnfR (mkApp (mkConst ``Frame.pc) fr)
  let some pc ← (evalNat (← instantiateMVars pcE)).run | return none
  let some bytes ← codeBytes? code | return none
  let some b := bytes[pc]? | return none
  let hb ← Term.exprToSyntax (← codeFact code pc b)
  let bn := b.toNat
  let norm : TacticM Unit := do
    try evalTactic (← `(tactic| apwp_norm [$extra,*])) catch _ => pure ()
    let gs ← getGoals
    let mut out : List MVarId := []
    for gi in gs do
      setGoals [gi]
      try generalizeGas catch _ => pure ()
      out := out ++ (← getGoals)
    setGoals out
  let drop (k : Nat) : TacticM Unit := do
    for _ in [0:k] do
      evalTactic (← `(tactic| (intro h; clear h)))
  let run (t : TSyntax `tactic) (k : Nat) : TacticM (Option (List MVarId)) := do
    if ← attempt (do evalTactic t; drop k; norm) then return some (← getGoals) else return none
  if bn = 0xfd then
    if ← attempt (evalTactic (← `(tactic| exact pwp_revert ‹_› $hb rfl))) then
      return some [] else return none
  if bn = 0xfe then
    if ← attempt (evalTactic (← `(tactic| exact pwp_invalid ‹_› $hb))) then
      return some [] else return none
  if 0x5f ≤ bn ∧ bn ≤ 0x7f then
    let n := bn - 0x5f
    let hv ← Term.exprToSyntax (← pushFact code bytes pc n)
    let nS := Syntax.mkNumLit (toString n)
    return ← run (← `(tactic| refine pwp_push $nS (by decide) ‹_› $hb $hv ?_)) 2
  if 0x80 ≤ bn ∧ bn < 0x90 then
    let nS := Syntax.mkNumLit (toString (bn - 0x80))
    return ← run (← `(tactic| refine pwp_dup ⟨$nS, by decide⟩ ‹_› $hb rfl ?_)) 2
  if 0x90 ≤ bn ∧ bn < 0xa0 then
    let nS := Syntax.mkNumLit (toString (bn - 0x90))
    return ← run (← `(tactic| refine pwp_swap ⟨$nS, by decide⟩ ‹_› $hb rfl rfl ?_)) 1
  if bn = 0x39 then
    return ← run (← `(tactic| refine pwp_codecopy ‹_› $hb rfl (by decide) ?_)) 1
  if bn = 0x55 ∨ bn = 0xa3 then
    -- keep the `isStatic = false` the rule provides (a success's postcondition needs it)
    let lS := mkIdent (if bn = 0x55 then ``pwp_sstore_any else ``pwp_log3)
    if ← attempt (do
        evalTactic (← `(tactic| refine $lS ‹_› $hb rfl ?_))
        evalTactic (← `(tactic| intro hstatic))
        drop (if bn = 0x55 then 2 else 1)
        norm) then
      return some (← getGoals)
    return none
  if bn = 0x57 then
    let ok ← attempt do
      evalTactic (← `(tactic| refine pwp_jumpi ‹_› $hb rfl ?_ ?_))
      let gs ← getGoals
      let mut out : List MVarId := []
      for (gi, k) in gs.zip [1, 2] do
        setGoals [gi]
        evalTactic (← `(tactic| intro hc))
        drop k
        closeBranch extra
        if (← getGoals).isEmpty then continue
        norm
        out := out ++ (← getGoals)
      setGoals out
    if ok then return some (← getGoals) else return none
  match ruleFor bn with
  | none => return none
  | some r =>
    let lS := mkIdent r.lemma
    let t ← if r.stk then `(tactic| refine $lS ‹_› $hb rfl ?_)
      else `(tactic| refine $lS ‹_› $hb ?_)
    run t r.intros

/-- The pc of the machine of a goal `WP m Q H`, if it is a numeral. -/
def goalPc? (g : MVarId) : MetaM (Option Nat) := g.withContext do
  let some m ← wpGoalMachine? g | return none
  let fr ← whnfR (mkApp (mkConst ``Machine.frame) m)
  let pcE ← whnfR (mkApp (mkConst ``Frame.pc) fr)
  (evalNat (← instantiateMVars pcE)).run

/-- Step every goal until it stops (at most `fuel` steps in all); a goal whose pc is in `stops`
is left as it is. -/
def hwpSteps (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (fuel : Nat)
    (stops : List Nat := []) : TacticM Unit := do
  let mut todo ← getGoals
  let mut stopped : List MVarId := []
  for _ in [0:fuel] do
    match todo with
    | [] => break
    | g :: rest =>
      if !stops.isEmpty then
        if let some pc ← goalPc? g then
          if stops.contains pc then
            stopped := stopped ++ [g]; todo := rest; continue
      setGoals [g]
      match ← hwpStep extra with
      | none => stopped := stopped ++ [g]; todo := rest
      | some new => todo := new ++ rest
  setGoals (stopped ++ todo)

/-- `hwp_steps [h₁, …]`: step every goal until each stops at `STOP`, `RETURN` or an
instruction without a rule; `hwp_steps stop_at [q₁, …]` also stops on reaching a pc `qᵢ`. -/
syntax "hwp_steps" (ppSpace num)? (" stop_at " "[" num,* "]")?
  (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| hwp_steps $[$n]? $[stop_at [$stops,*]]? $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let stops := ((stops.map (·.getElems)).getD #[]).toList.map (·.getNat)
    hwpSteps extra ((n.map (·.getNat)).getD 100000) stops

end Verified.Solady.Spec.AnyGasTactic
