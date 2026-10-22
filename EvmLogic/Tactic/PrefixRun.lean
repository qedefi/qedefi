import EvmLogic.Tactic.PrefixStep
import EvmLogic.Program.Reentrancy.AnyCaller

/-!
# `apwp_run`: a whole frame in the any-gas prefix calculus

`apwp_steps` stops at every instruction the calculus leaves to the caller: `CALL`,
`STATICCALL`, `DELEGATECALL`, `LOG*`, `STOP`, `RETURN`. In a function that writes, logs and
calls several times (an ERC-20 transfer that notifies a rewards controller twice, emits four
events and calls back the pool) the frame continues after each of them. `apwp_run … using h`
runs `apwp_steps`, applies the user's **handler** `h` to every goal it stops at, and steps
again every goal the handler leaves that is still a `WP` goal; the other goals the handler
leaves (typically `Good` of the world at a call, a log or the end of the frame) are returned.

The handler is ordinary tactic code, written by the proof for its invariant (it knows the
`GoodOps` instance, the context and the summaries): typically `pwp_call_any`/`pwp_staticcall`/
`pwp_delegatecall` with `wp_of_resume` for the continuation, `pwp_safe_le` for a `LOG`,
`pwp_stop`/`pwp_return` at the end, each followed by `apwp_cont`, which normalizes the machine
of a continuation (as after a step) and carries the gas bound over. Everything is checked by the
kernel: the tactic only chooses rules.
-/

namespace EvmLogic.Tactic.PrefixStep
open EvmLean Lean Meta Elab Tactic EvmLean.Interpreter EvmLogic.Program
open EvmLogic.Program.Reentrancy

/-- `apwp_cont [h₁, …]`: after introducing the variables of a continuation (its last hypothesis
the bound `g ≤ g₀` of the new gas), normalize the machine and replace the bound by one on the
bound the context has for `g₀`. -/
syntax "apwp_cont" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| apwp_cont $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    withMainContext chainLastBound
    try evalTactic (← `(tactic| apwp_norm [$extra,*])) catch _ => pure ()
    try generalizeSub catch _ => pure ()

/-- The `Frame` stack of the machine of a goal `WP m Q H`, as a list of expressions. -/
def goalStack? (g : MVarId) : MetaM (Option (List Expr)) := g.withContext do
  let some st ← frameField? g ``Frame.stack | return none
  let rec go (e : Expr) (acc : List Expr) (fuel : Nat) : MetaM (Option (List Expr)) := do
    match fuel with
    | 0 => return none
    | fuel + 1 =>
      let e ← whnfR e
      if e.isAppOfArity ``List.cons 3 then go (e.getArg! 2) (acc ++ [e.getArg! 1]) fuel
      else if e.isAppOfArity ``List.nil 1 then return some acc
      else return none
  go st [] 1100

/-- `apwp_forget`: generalize every stack word of the goal's machine that mentions a local
variable (keeping the numerals: jump targets), and clear the branch conditions on words. For the
code after an untrusted call: the world is a fresh `Good` one, so what the stack remembers of the
world before the call (event data, return values) is no longer needed, and forgetting it keeps
the terms small. Sound: generalizing only weakens the goal's hypotheses. -/
elab "apwp_forget" : tactic => withMainContext do
  -- generalize one compound word at a time (generalizing one may change the others)
  let mut tried : Array Expr := #[]
  for _ in [0:256] do
    let g ← getMainGoal
    let some st ← g.withContext (goalStack? g) | break
    let mut pick : Option Expr := none
    for e in st do
      let e ← instantiateMVars e
      if !e.hasFVar || e.isFVar || tried.contains e then continue
      pick := some e; break
    let some e := pick | break
    tried := tried.push e
    let eS ← Term.exprToSyntax e
    let n := mkIdent (← mkFreshUserName `x)
    try withMainContext (evalTactic (← `(tactic| generalize $eS = $n:ident))) catch _ => pure ()
  withMainContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let t ← instantiateMVars decl.type
      let ty? := match t.eq?, t.ne? with
        | some (ty, _, _), _ => some ty
        | _, some (ty, _, _) => some ty
        | _, _ => none
      let some ty := ty? | continue
      if (← whnfR ty).isAppOfArity ``BitVec 1 then
        try evalTactic (← `(tactic| clear $(mkIdent decl.userName))) catch _ =>
          try (do let g ← getMainGoal; let g' ← g.clear decl.fvarId; replaceMainGoal [g']) catch _ =>
            pure ()

/-- Run `apwp_steps`, then the handler on every stopped goal, and repeat on the `WP` goals it
leaves (at most `fuel` rounds). -/
def apwpRun (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (stops : List Nat)
    (handler : TSyntax `Lean.Parser.Tactic.tacticSeq) (fuel : Nat) : TacticM Unit := do
  let mut todo ← getGoals
  let mut out : List MVarId := []
  for _ in [0:fuel] do
    match todo with
    | [] => break
    | g :: rest =>
      todo := rest
      if (← g.isAssigned) then continue
      setGoals [g]
      apwpSteps extra 100000 stops
      for s in ← getGoals do
        if (← s.isAssigned) then continue
        if let some pc ← goalPc? s then
          if stops.contains pc then out := out ++ [s]; continue
        setGoals [s]
        if ← attempt (evalTactic handler) then
          for n in ← getGoals do
            if (← n.isAssigned) then continue
            if (← wpGoalMachine? n).isSome then todo := todo ++ [n] else out := out ++ [n]
        else out := out ++ [s]
  setGoals (out ++ todo)

/-- `apwp_run [h₁, …] stop_at [q₁, …] using handler` (see the module docstring). -/
syntax "apwp_run" (" stop_at " "[" num,* "]")? (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  " using " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| apwp_run $[stop_at [$stops,*]]? $[[$extra,*]]? using $h) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let stops := ((stops.map (·.getElems)).getD #[]).toList.map (·.getNat)
    apwpRun extra stops h 100000

end EvmLogic.Tactic.PrefixStep
