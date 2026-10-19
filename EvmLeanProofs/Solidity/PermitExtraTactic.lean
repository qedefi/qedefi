import EvmLeanProofs.Program.ExtraTactic

/-!
# Generalizing the memory of a `WP` goal

During a long symbolic execution solc's memory becomes a deep term of `expand`s and
`storeWord`s, and every step (normalization, memory-expansion gas) traverses it. Once the
words that the rest of the code reads are known (typically the free-memory pointer and the
memory size), `wp_generalize_mem M h` replaces the memory of the goal's machine by a variable
`M` (with `h : term = M`), from which the caller derives the few facts it keeps
(`M.loadWord 64 = …`, `M.size = …`) before clearing `h`.
-/

namespace EvmLean.Program

open Lean Elab Tactic Meta
open EvmLean.Interpreter

/-- `wp_generalize_mem M h`: in a goal `WP m Q H` whose machine is a structure literal,
replace the frame's memory by a new variable `M` (with `h : term = M`). -/
elab "wp_generalize_mem " M:ident h:ident : tactic => withMainContext do
  let some m ← wpGoalMachine? (← getMainGoal) | throwError "wp_generalize_mem: not a WP goal"
  let fr ← whnfR (mkApp (mkConst ``Machine.frame) m)
  let mem ← whnfR (mkApp (mkConst ``Frame.memory) fr)
  let memS ← Term.exprToSyntax mem
  evalTactic (← `(tactic| generalize $h : $memS = $M))

end EvmLean.Program
