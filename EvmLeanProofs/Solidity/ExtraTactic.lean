import EvmLeanProofs.Program.Tactic
import EvmLeanProofs.Program.ExtraTactic
import EvmLeanProofs.Solidity.Tactic

/-!
# `CODECOPY` in the frame-local logic

`wp_step` (`EvmLeanProofs.Program.Tactic`) has no lemma for `CODECOPY`, which solc uses to
load 32-byte constants (event topics, revert strings) from the end of the code.
`wp_codecopy` performs one `CODECOPY` of a literal range of literal code: it applies
`step_codecopy`, then evaluates the copied bytes with `reduceCodeImm` (a kernel-checked
evaluation, as `sol_step` does) and turns the copied word into an `MSTORE`
(`Memory.write_ofWord`), so that later reads of it reduce.
-/

namespace EvmLean.Program

open EvmLean.Interpreter

/-- Execute a `CODECOPY` of a non-empty literal range in a `WP` goal (see the module
docstring). -/
macro "wp_codecopy" : tactic => `(tactic| (
  apply WP.of_step
  case h =>
    apply EvmLean.Interpreter.step_codecopy (by code_fact) rfl (by decide) (by evm_gas)
  case hs => same_frame
  simp only [EvmLean.Solidity.Exec.reduceCodeImm, Memory.write_ofWord, BitVec.reduceToNat,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub, memoryCost, Gas.extendMemory,
    List.foldl, Gas.ceil32, Gas.memoryCost, Gas.words, Gas.memoryPerWord, Memory.size_storeWord,
    Memory.size_expand, Memory.size_empty, Memory.wordsAfter, Memory.words, Nat.reduceLeDiff,
    Nat.reduceEqDiff, Nat.max_def, ↓reduceIte]))

end EvmLean.Program
