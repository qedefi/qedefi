import Defi.Math.Arith
import Defi.ERC20.Token
import Defi.ERC4626.Solmate
import Defi.ERC4626.SolmateEffects
import Defi.Math.RoundTripAlgebra
import Defi.ERC4626.SolmateProps
import Defi.ERC4626.Oz
import Defi.ERC4626.OzProps
import Defi.ERC4626.InflationAlgebra
import Defi.ERC4626.Inflation
import Defi.ERC4626.Witnesses
import Defi.ERC4626.MoreProps
import Defi.ERC4626.Events
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
