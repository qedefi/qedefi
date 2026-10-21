import QEDefi.ERC20.Permit
import QEDefi.ERC20.Rep
import QEDefi.ERC20.RepOz
import QEDefi.ERC20.Token
import QEDefi.ERC20.Variant
import QEDefi.ERC20.VariantDeprecation
import QEDefi.ERC20.VariantExtras
import QEDefi.ERC20.VariantProps
import QEDefi.ERC4626.Agree
import QEDefi.ERC4626.AssetVariants
import QEDefi.ERC4626.Events
import QEDefi.ERC4626.Inflation
import QEDefi.ERC4626.Integration
import QEDefi.ERC4626.IntegrationUsdt
import QEDefi.ERC4626.Logs
import QEDefi.ERC4626.MoreProps
import QEDefi.ERC4626.Oz
import QEDefi.ERC4626.OzProps
import QEDefi.ERC4626.Price
import QEDefi.ERC4626.Solmate
import QEDefi.ERC4626.SolmateProps
import QEDefi.ERC4626.Witnesses
import QEDefi.Math.Arith
import QEDefi.Staking.Deps
import QEDefi.Staking.Model
import QEDefi.Trace.Lift
import QEDefi.Trace.Time
import QEDefi.Vesting.Model

/-!
# QEDefi

Reusable DeFi verification kits (Mathlib): `uint256` arithmetic (`QEDefi.Math`), ERC-20 ledgers
and their word-level representation (`QEDefi.ERC20`), the Solmate and OpenZeppelin ERC-4626
vault models with their properties (`QEDefi.ERC4626`), and EVM-independent lifting of per-call
refinement to traces (`QEDefi.Trace`).
-/
