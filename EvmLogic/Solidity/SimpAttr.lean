import Lean

/-!
# The `sol_norm` and `permit_norm` simp sets

`sol_norm`: solc idioms normalized by `sol_step` after every instruction. `permit_norm`: gas
and memory-size lemmas for long `pwp_steps` runs over generalized memory. (A simp attribute
must be declared in a module of its own before it can be used.)
-/

section

/-- Normalization lemmas for symbolic execution of solc output (see `sol_step`). -/
register_simp_attr sol_norm

end

section

/-- Gas and memory-size normalization for `pwp_steps`: keeps the gas left a closed sum
instead of accumulating memory-expansion `if`s (Solmate's `permit`). -/
register_simp_attr permit_norm

end
