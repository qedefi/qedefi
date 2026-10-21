import Lean

/-!
# `kernel_rfl` and `kernel_decide`: evaluation by the kernel alone

Like `decide +kernel`, but the goal may mention local variables, and no auxiliary declaration is
added: the proof term (`Eq.refl`, or `of_decide_eq_true (Eq.refl true)`) is assigned without
elaborator checks and evaluated by the kernel when it checks the enclosing declaration. Plain
`rfl`/`decide` use `Meta.isDefEq`, which does not finish on whole-program runs. Adding an
auxiliary declaration (as `decide +kernel` does) waits for the kernel to finish every earlier
declaration of the file, which serializes the elaboration of a file's proofs. If the computation
inspects a free variable, the kernel gets stuck (type mismatch, reported for the enclosing
declaration); use the step lemmas instead. See `docs/proving.md` §1.
-/

namespace EvmLogic.Tactic

open Lean Elab Tactic EvmLogic.Tactic Meta

/-- Close `lhs = rhs` by kernel reduction only (checked with the enclosing declaration). -/
syntax (name := kernelRfl) "kernel_rfl" : tactic

@[tactic kernelRfl, inherit_doc kernelRfl]
def evalKernelRfl : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  if t.hasMVar then throwError "kernel_rfl: goal contains metavariables{indentExpr t}"
  let some (_, lhs, _) := t.eq? | throwError "kernel_rfl: goal is not an equality{indentExpr t}"
  g.assign (mkExpectedPropHint (← mkEqRefl lhs) t)
  replaceMainGoal []

/-- Close a decidable goal by kernel evaluation of `decide p` (checked with the enclosing
declaration).
Prefer it to `kernel_rfl` when the sides only meet after evaluating to numbers (gas arithmetic):
lazy unfolding can hit the kernel's recursion limit. -/
syntax (name := kernelDecide) "kernel_decide" : tactic

@[tactic kernelDecide, inherit_doc kernelDecide]
def evalKernelDecide : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  if t.hasMVar then throwError "kernel_decide: goal contains metavariables{indentExpr t}"
  let inst ← synthInstance (mkApp (mkConst ``Decidable) t)
  let dec := mkApp2 (mkConst ``Decidable.decide) t inst
  let rflTrue := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  g.assign (mkApp3 (mkConst ``of_decide_eq_true) t inst
    (mkExpectedPropHint rflTrue (← mkEq dec (mkConst ``Bool.true))))
  replaceMainGoal []

end EvmLogic.Tactic
