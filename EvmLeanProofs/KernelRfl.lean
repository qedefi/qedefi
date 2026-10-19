import Lean

/-!
# `kernel_rfl`: reflexivity checked by the kernel alone

`decide +kernel` evaluates a closed proposition in the kernel, but refuses goals with free
variables. `rfl` and `decide` accept free variables but check definitional equality in the
elaborator (`Meta.isDefEq`), which is orders of magnitude slower than the kernel on
interpreter code and does not finish on whole-program runs.

`kernel_rfl` closes a goal `lhs = rhs` (possibly mentioning local variables) by adding the
auxiliary theorem `∀ xs, lhs = rhs := fun xs => Eq.refl lhs` directly to the environment, so
only the kernel checks `lhs ≡ rhs`. This is sound for the same reason `decide +kernel` is:
the kernel is the arbiter; the elaborator is skipped. The resulting proof depends on no
axioms beyond those of the definitions involved.

Use it when the free variables are *not inspected* by the computation, e.g. a run of
bytecode that never hashes, stated for an arbitrary `Crypto`. When the computation branches
on a free variable the kernel gets stuck and reports a type mismatch; use the step lemmas
(`EvmLeanProofs.Step*`) instead.
-/

namespace EvmLean.Tactic

open Lean Elab Tactic Meta

/-- Close `lhs = rhs` by kernel reduction only, abstracting the local context. -/
syntax (name := kernelRfl) "kernel_rfl" : tactic

@[tactic kernelRfl, inherit_doc kernelRfl]
def evalKernelRfl : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  if t.hasMVar then throwError "kernel_rfl: goal contains metavariables{indentExpr t}"
  let some (_, lhs, _) := t.eq? | throwError "kernel_rfl: goal is not an equality{indentExpr t}"
  let fvars := (← getLCtx).foldl (init := #[]) fun acc d =>
    if d.isAuxDecl || d.isImplementationDetail then acc else acc.push d.toExpr
  let ty ← mkForallFVars fvars t
  let pf ← mkLambdaFVars fvars (← mkEqRefl lhs)
  let levels := (collectLevelParams {} ty).params.toList
  let name ← withOptions (Elab.async.set · false) <| mkAuxLemma levels ty pf
  g.assign (mkAppN (mkConst name (levels.map Level.param)) fvars)
  replaceMainGoal []

end EvmLean.Tactic
