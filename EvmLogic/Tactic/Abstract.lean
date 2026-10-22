import Lean
import EvmLogic.Program.Call

/-!
# Cheap abstraction of machine fields, and access-cost bounds

* `wp_abstract`: replace a field of a `WP` goal's machine by a variable, cheaply;
* `access_bounds`: bound every `Gas.accessCost` in the goal.

## `wp_abstract`

`wp_abstract memory M h` (also `gas`, `sub`, `world`) turns the goal `WP m Q H`, whose machine is a
structure literal, into `WP m' Q H` with the field replaced by a fresh variable `M` and
`h : <old value> = M` in context. Unlike `wp_generalize_mem`/`wp_generalize_gas` (which call
`generalize`, i.e. `kabstract` over the whole goal), it rebuilds the machine at the known
argument position and closes the original goal by `rfl`, so its cost does not depend on the
size of the goal: on the Aave AToken's `mint` path, after three `SSTORE`s and four mapping reads,
`generalize` did not finish in minutes.
-/

namespace EvmLogic.Tactic
open EvmLean EvmLean.Interpreter EvmLogic.Program Lean Elab Tactic Meta

/-- See the module doc. -/
elab "wp_abstract " fld:ident x:ident h:ident : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let_expr WP m q hh := t | throwError "wp_abstract: not a WP goal"
  unless m.isAppOfArity ``Machine.mk 8 do throwError "wp_abstract: machine is not a literal"
  let margs := m.getAppArgs
  let fr := margs[6]!
  unless fr.isAppOfArity ``Frame.mk 11 do throwError "wp_abstract: frame is not a literal"
  let fargs := fr.getAppArgs
  let mkFrame (i : Nat) (v : Expr) : Expr :=
    mkAppN (mkConst ``Machine.mk)
      (margs.set! 6 (mkAppN (mkConst ``Frame.mk) (fargs.set! i v)))
  let (val, mk) ← match fld.getId with
    | `memory => pure (fargs[5]!, mkFrame 5)
    | `gas => pure (fargs[6]!, mkFrame 6)
    | `sub => pure (fargs[8]!, mkFrame 8)
    | `world => pure (margs[2]!, fun v => mkAppN (mkConst ``Machine.mk) (margs.set! 2 v))
    | _ => throwError "wp_abstract: field must be memory, gas, sub or world"
  let ty ← inferType val
  let newTy ← withLocalDeclD x.getId ty fun xv => do
    let eq ← mkEq val xv
    withLocalDeclD h.getId eq fun hv => do
      mkForallFVars #[xv, hv] (mkApp3 (mkConst ``WP) (mk xv) q hh)
  let ng ← mkFreshExprSyntheticOpaqueMVar newTy
  g.assign (mkApp2 ng val (← mkEqRefl val))
  let (_, ng') ← ng.mvarId!.introN 2 [x.getId, h.getId]
  replaceMainGoal [ng']

/-- Add `Gas.accessCost b ≤ 2600` for every access cost `Gas.accessCost b` in the goal (the
warm set after a few storage accesses is a large term; `evm_gas` does not bound it). -/
elab "access_bounds" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let found ← IO.mkRef (#[] : Array Expr)
  forEachExpr t fun e => do
    if e.isAppOfArity ``Gas.accessCost 1 then found.modify (·.push e.appArg!)
  for b in ← found.get do
    let pf ← mkAppM ``accessCost_le #[b]
    let g ← getMainGoal
    let (_, g') ← (← g.assert `hacc (← inferType pf) pf).intro1P
    replaceMainGoal [g']

end EvmLogic.Tactic
