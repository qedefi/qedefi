import EvmLogic.Tactic.Mcopy

/-!
# Tactics of the `permit` proofs

The `permit` proofs generalize the memory of long symbolic executions with
`wp_generalize_mem M h` (defined in `EvmLeanProofs.Solidity.StringsTactic`, re-exported here):
the memory term is replaced by a variable from which the few facts the rest of the code reads
(the free-memory pointer, the memory size) are derived before the equation is cleared.
-/
