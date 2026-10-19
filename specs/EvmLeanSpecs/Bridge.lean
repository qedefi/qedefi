import EvmLeanSpecs.Vault
import EvmLean

/-!
# Bridge to evm-lean

This file checks that the specification package can import both Mathlib (through the
vault model) and the evm-lean semantics (by path dependency on the parent package), and
fixes the actor type used by the refinement proofs: EVM addresses.
-/

namespace EvmLeanSpecs

/-- The Solmate vault model over EVM addresses, as used by the refinement proofs. -/
abbrev SolmateVaultState := Vault.Solmate.State EvmLean.Address

end EvmLeanSpecs
