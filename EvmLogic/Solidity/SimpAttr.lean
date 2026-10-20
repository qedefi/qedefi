import Lean

/-!
# The `sol_norm` simp set

Lemmas tagged `@[sol_norm]` are used by `sol_step` (`EvmLeanProofs.Solidity.Tactic`) to
normalize the machine after every instruction, on top of `evm_norm`: solc idioms on words
(address masks, `EQ x x`), calldata decoding of ABI-encoded calls, and reads of solc's
scratch and free memory. (A simp attribute must be declared in a module of its own before it
can be used.)
-/

section

/-- Normalization lemmas for symbolic execution of solc output (see `sol_step`). -/
register_simp_attr sol_norm

end

section

/-!
## The `permit_norm` simp set

Extra normalization for long symbolic executions over generalized memory (Solmate's
`permit`): the memory-size and memory-expansion-cost lemmas that `evm_gas` uses, so that the
gas left of the machine stays a closed sum (with memory sizes known from hypotheses
`M.size = n` passed alongside) instead of accumulating expansion-cost `if`s over the memory
term. Passed to `pwp_steps [permit_norm, …]`.
-/

/-- Gas and memory-size normalization for `pwp_steps` (see the module docstring). -/
register_simp_attr permit_norm

end
