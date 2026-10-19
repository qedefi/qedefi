import Lean
import EvmLeanProofs.Tactic
import EvmLeanProofs.Program.Logic

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

namespace EvmLean.Program

open Lean Elab Tactic Meta
open Interpreter

/-- Prove `SameFrame m m'` when `m'` only changes mutable fields of `m` (checked by `rfl`). -/
macro "same_frame" : tactic => `(tactic| exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

-- Try hypotheses first: with large code, jump-destination validity is supplied as a fact.
macro_rules | `(tactic| evm_disch) => `(tactic| assumption)

/-- Prove `step m = finishFrame ?mf ?o` for a halting instruction, in any frame. -/
syntax "wp_halt_core" : tactic

macro_rules | `(tactic| wp_halt_core) => `(tactic| first
  | evm_apply step_stop
  | evm_apply step_return
  | evm_apply step_revert
  | evm_apply step_invalid
  | fail "no halting step lemma applies")

/-- Advance a goal `WP m Q H` by one instruction (see the module docstring). -/
syntax "wp_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| wp_step) => `(tactic| wp_step [])
  | `(tactic| wp_step [$extra,*]) => `(tactic| (
    first
      | (apply WP.of_step
         case h => evm_step_core
         case hs => same_frame)
      | (apply WP.halt_of_step
         case h => wp_halt_core
         case hs => same_frame)
      | fail "wp_step: no step lemma applies to the next instruction"
    try evm_norm [$extra,*]))

/-- Repeat `wp_step` while it succeeds (at most `n` times if a bound is given). -/
syntax "wp_steps" (ppSpace num)? (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| wp_steps) => `(tactic| repeat wp_step)
  | `(tactic| wp_steps [$extra,*]) => `(tactic| repeat wp_step [$extra,*])
  | `(tactic| wp_steps $n) => `(tactic| iterate $n wp_step)
  | `(tactic| wp_steps $n [$extra,*]) => `(tactic| iterate $n wp_step [$extra,*])

/-- The program counter of the machine in a goal `WP m Q H`, if it is a numeral. -/
def wpGoalPc? (g : MVarId) : MetaM (Option Nat) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let_expr WP m _ _ := t | return none
  let pc ← whnfD (mkApp (mkConst ``Frame.pc) (mkApp (mkConst ``Machine.frame) m))
  (evalNat (← instantiateMVars pc)).run

/-- Step a `WP` goal until its pc is one of `pcs` (after at least one step), or `wp_step`
fails, or `limit` steps were taken. -/
def wpRunTo (pcs : List Nat) (step : TSyntax `tactic) (limit : Nat := 100000) : TacticM Unit := do
  let mut first := true
  for _ in [0:limit] do
    let gs ← getGoals
    let some g := gs.head? | return
    unless first do
      if let some pc ← wpGoalPc? g then
        if pcs.contains pc then return
    first := false
    let saved ← saveState
    try evalTactic step
    catch _ =>
      saved.restore
      return
    if (← getGoals).length != gs.length then return

/-- `wp_run_to pc₁, … [h₁, …]`: step until the pc is one of the `pcᵢ` (see the module
docstring). -/
syntax "wp_run_to " num,+ (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| wp_run_to $pcs,* $[[$extra,*]]?) => do
    let targets := pcs.getElems.toList.map (·.getNat)
    let step ← match extra with
      | some extra => `(tactic| wp_step [$extra,*])
      | none => `(tactic| wp_step)
    wpRunTo targets step

/-- Destructure the machine variable `m` into its fields and substitute equations about them
from the context. -/
syntax "wp_intro " ident : tactic

macro_rules
  | `(tactic| wp_intro $m) => `(tactic| (
    obtain ⟨ctx, pre, world, transient, originalWorld, created,
      ⟨msg, code, jumpDests, pc, stack, memory, gasLeft, returnData, sub, snapshot, kind⟩,
      parents⟩ := $m
    dsimp only at *
    subst_vars))

end EvmLean.Program
