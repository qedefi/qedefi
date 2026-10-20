import Lean

/-!
# The `permit_norm` simp set

Extra normalization for long symbolic executions over generalized memory (Solmate's
`permit`): the memory-size and memory-expansion-cost lemmas that `evm_gas` uses, so that the
gas left of the machine stays a closed sum (with memory sizes known from hypotheses
`M.size = n` passed alongside) instead of accumulating expansion-cost `if`s over the memory
term. Passed to `pwp_steps [permit_norm, …]`.
-/

/-- Gas and memory-size normalization for `pwp_steps` (see the module docstring). -/
register_simp_attr permit_norm
