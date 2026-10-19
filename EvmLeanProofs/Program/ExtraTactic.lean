import EvmLeanProofs.Program.Tactic

/-!
# Gas side conditions over symbolic memory

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
