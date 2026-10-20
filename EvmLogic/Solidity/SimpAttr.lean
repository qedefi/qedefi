import Lean

/-!
# The `sol_norm` simp set

Lemmas tagged `@[sol_norm]` are used by `sol_step` (`EvmLeanProofs.Solidity.Tactic`) to
normalize the machine after every instruction, on top of `evm_norm`: solc idioms on words
(address masks, `EQ x x`), calldata decoding of ABI-encoded calls, and reads of solc's
scratch and free memory. (A simp attribute must be declared in a module of its own before it
can be used.)
-/

/-- Normalization lemmas for symbolic execution of solc output (see `sol_step`). -/
register_simp_attr sol_norm
