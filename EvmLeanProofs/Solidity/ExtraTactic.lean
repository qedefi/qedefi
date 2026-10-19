import EvmLeanProofs.Program.Tactic
import EvmLeanProofs.Program.ExtraTactic
import EvmLeanProofs.Solidity.Tactic
import EvmLeanProofs.Solidity.ExtraPatchedWP

/-!
# `CODECOPY` in the frame-local logic

`wp_step` (`EvmLeanProofs.Program.Tactic`) has no lemma for `CODECOPY`, which solc uses to
load 32-byte constants (event topics, revert strings) from the end of the code.
`pwp_codecopy` performs one `CODECOPY` of a literal range of literal or patched code
(`EvmLeanProofs.Solidity.ExtraPatchedWP`; the range must avoid the patches): it applies
`step_codecopy`, then evaluates the copied bytes with `reducePatchedRead` and `reduceCodeImm`
(kernel-checked evaluations, as `psol_step` does) and turns the copied word into an `MSTORE`
(`Memory.write_ofWord`), so that later reads of it reduce.
-/

namespace EvmLean.Program

open EvmLean.Interpreter

/-- Execute a `CODECOPY` of a non-empty literal range in a `WP` goal (see the module
docstring). -/
macro "pwp_codecopy" : tactic => `(tactic| (
  apply WP.of_step
  case h =>
    apply EvmLean.Interpreter.step_codecopy (by pcode_fact) rfl (by decide) (by evm_gas)
  case hs => same_frame
  simp only [EvmLean.Solidity.Patched.reducePatchedRead, EvmLean.Solidity.Exec.reduceCodeImm, Memory.write_ofWord, BitVec.reduceToNat,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub, memoryCost, Gas.extendMemory,
    List.foldl, Gas.ceil32, Gas.memoryCost, Gas.words, Gas.memoryPerWord, Memory.size_storeWord,
    Memory.size_expand, Memory.size_empty, Memory.wordsAfter, Memory.words, Nat.reduceLeDiff,
    Nat.reduceEqDiff, Nat.max_def, ↓reduceIte]))

end EvmLean.Program
