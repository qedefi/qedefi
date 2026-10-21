import EvmLogic.Tactic.WpStep
import EvmLogic.Solidity.Memory
import EvmLogic.Program.Reentrancy.PrefixOps

/-!
# `apwp_step` / `apwp_steps`: symbolic execution of a prefix, for any gas

The prefix rules (`EvmLogic.Program.Reentrancy.Prefix`, `…PrefixOps`) prove goals
`WP m Q (FailOk Good)` with **no gas lower bound**: each rule takes the next instruction or
absorbs its failure, given the `Good` rollback snapshot (a hypothesis `Good m.frame.snapshot.1`,
found by `assumption`). `apwp_step` reads the byte at the (numeral) pc of a literal code (with
its `code_table`, if any), applies the rule of that byte, introduces the facts the rule
provides (gas and stack bounds, which it drops; branch conditions, which it keeps), and
normalizes the new machine as `wp_step` does. `JUMPI` produces two goals (`c = 0`, `c ≠ 0`);
a branch whose condition is decided by the normalization (`decide`, or `simp` with the extra
lemmas and the branch hypotheses) is closed. `REVERT` and `INVALID` close their goal. After
each step the gas and the substate of the machine are generalized to fresh variables (gas costs
are only consumed), keeping a bound `g ≤ B` if the context has one for the previous gas (the
bound a `CALL` rule needs).

`apwp_steps [h₁, …]` steps every goal until each one stops at an instruction the calculus leaves
to the caller: `STOP`/`RETURN` (prove the world `Good`, `pwp_stop`/`pwp_return`), `CALL`
(`pwp_call_v`) or an instruction without a rule. Everything is checked by the kernel: the tactic
only chooses rules.
-/

namespace EvmLogic.Tactic.PrefixStep
open EvmLean Lean Meta Elab Tactic EvmLean.Interpreter EvmLogic.Program
open EvmLogic.Program.Reentrancy

/-- How a rule is applied: the lemma, whether it takes a `hstk := rfl` argument, the number of
hypotheses its continuation introduces. -/
structure Rule where
  /-- The rule. -/
  lemma : Name
  /-- It takes `hstk` (the stack shape), proved by `rfl`. -/
  stk : Bool := true
  /-- The number of hypotheses its continuation introduces (all dropped). -/
  intros : Nat := 2

/-- The rule of a byte, if it is applied uniformly (not `PUSH`/`DUP`/`SWAP`/`JUMPI`/halts). -/
def ruleFor (b : Nat) : Option Rule :=
  let bin : List (Nat × Name) := [(0x01, ``pwp_add), (0x02, ``pwp_mul), (0x03, ``pwp_sub),
    (0x04, ``pwp_div), (0x06, ``pwp_mod), (0x10, ``pwp_lt), (0x11, ``pwp_gt),
    (0x12, ``pwp_slt), (0x13, ``pwp_sgt), (0x14, ``pwp_eq), (0x16, ``pwp_and),
    (0x17, ``pwp_or), (0x18, ``pwp_xor), (0x1a, ``pwp_byte), (0x1b, ``pwp_shl),
    (0x1c, ``pwp_shr), (0x1d, ``pwp_sar), (0x15, ``pwp_iszero), (0x19, ``pwp_not),
    (0x20, ``pwp_keccak256), (0x35, ``pwp_calldataload), (0x51, ``pwp_mload_val),
    (0x54, ``pwp_sload)]
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

/-- The simp set normalizing the machine after a step (that of `wp_step`). -/
macro "apwp_norm" " [" extra:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| evm_norm [List.set_cons_zero, List.set_cons_succ, Nat.sub_sub,
      Memory.loadWord_expand, Memory.read_expand, Memory.loadWord_storeWord, Memory.read_storeWord,
      Memory.loadWord_storeWord_of_disjoint, Memory.read_storeWord_of_disjoint, true_or, or_true,
      reduceClosedWord, Bytes.size_ofWord, Memory.read_64, $extra,*])

/-- The `Frame` field `f` of the machine of a goal `WP m Q H`, after `whnfR`. -/
def frameField? (g : MVarId) (f : Name) : MetaM (Option Expr) := g.withContext do
  let some m ← wpGoalMachine? g | return none
  let fr ← whnfR (mkApp (mkConst ``Machine.frame) m)
  return some (← instantiateMVars (← whnfR (mkApp (mkConst f) fr)))

/-- Generalize the gas of the goal's machine (if it is not a variable) to a fresh variable,
carrying a bound `base ≤ B` of the variable it was computed from (`base - c`) over to it. -/
def generalizeGas : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let some gas ← frameField? g ``Frame.gasLeft | return
  if gas.isFVar then return
  let mut base := gas
  for _ in [0:64] do
    let b := base.consumeMData
    if b.isAppOfArity ``HSub.hSub 6 then base := b.getArg! 4 else break
  let mut bound : Option LocalDecl := none
  if base.isFVar then
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      if let some (_, _, lhs, _) := ty.app4? ``LE.le then
        if lhs == base then bound := some decl
  let gasS ← Term.exprToSyntax gas
  let gn := mkIdent (← mkFreshUserName `gas)
  match bound with
  | some h =>
    let hS := mkIdent h.userName
    let hb := mkIdent (← mkFreshUserName `hgas)
    evalTactic (← `(tactic| (
      have $hb:ident : $gasS ≤ _ := Nat.le_trans (Nat.sub_le _ _) $hS
      generalize $gasS = $gn:ident at $hb:ident ⊢
      try clear $hS:ident)))
    if base.isFVar then
      try evalTactic (← `(tactic| clear $(← Term.exprToSyntax base))) catch _ => pure ()
  | none =>
    evalTactic (← `(tactic| generalize $gasS = $gn:ident))
    if base.isFVar then
      try evalTactic (← `(tactic| clear $(← Term.exprToSyntax base))) catch _ => pure ()

/-- Generalize the substate of the goal's machine (if it is not a variable). -/
def generalizeSub : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let some sub ← frameField? g ``Frame.sub | return
  if sub.isFVar then return
  let subS ← Term.exprToSyntax sub
  let sn := mkIdent (← mkFreshUserName `sub)
  evalTactic (← `(tactic| generalize $subS = $sn:ident))
  -- drop the variables it was computed from, if they no longer occur
  for fv in (collectFVars {} sub).fvarIds do
    try evalTactic (← `(tactic| clear $(← Term.exprToSyntax (mkFVar fv)))) catch _ => pure ()

/-- Run `tac` on the main goal; restore the state and give `false` on any failure. -/
def attempt (tac : TacticM Unit) : TacticM Bool := do
  let saved ← saveState
  tryCatchRuntimeEx (do withoutRecover tac; return true) (fun _ => do saved.restore; return false)

/-- Close the main goal if its last hypothesis (a branch condition) is contradictory. -/
def closeBranch (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Unit := do
  let tacs : List (TSyntax `tactic) := [← `(tactic| (exfalso; revert ‹_›; decide)),
    ← `(tactic| (exfalso; revert ‹_›; simp only [$extra,*]; done)),
    ← `(tactic| (exfalso; simp_all only [$extra,*]; done))]
  for t in tacs do
    if ← attempt (evalTactic t) then return

/-- One step of the main goal. `none`: no rule applies (the goal is unchanged); `some gs`: the
new goals. -/
def apwpStep (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
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
      try generalizeSub catch _ => pure ()
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
  if bn = 0x55 then
    return ← run (← `(tactic| refine pwp_sstore ‹_› $hb rfl (by assumption) ?_)) 2
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

/-- `apwp_step [h₁, …]`: one step of the main goal (see the module docstring). -/
syntax "apwp_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| apwp_step $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let gs ← getGoals
    let some new ← apwpStep extra | throwError "apwp_step: no prefix rule applies"
    setGoals (new ++ gs.drop 1)

/-- Step every goal until it stops (at most `fuel` steps in all). -/
def apwpSteps (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (fuel : Nat) :
    TacticM Unit := do
  let mut todo ← getGoals
  let mut stopped : List MVarId := []
  for _ in [0:fuel] do
    match todo with
    | [] => break
    | g :: rest =>
      setGoals [g]
      match ← apwpStep extra with
      | none => stopped := stopped ++ [g]; todo := rest
      | some new => todo := new ++ rest
  setGoals (stopped ++ todo)

/-- `apwp_steps [h₁, …]`: step every goal until each stops at `STOP`, `RETURN`, `CALL` or an
instruction without a rule (see the module docstring). -/
syntax "apwp_steps" (ppSpace num)? (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| apwp_steps $[$n]? $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    apwpSteps extra ((n.map (·.getNat)).getD 100000)

end EvmLogic.Tactic.PrefixStep
