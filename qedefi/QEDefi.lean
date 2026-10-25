import QEDefi.Aave.Accrual
import QEDefi.Aave.Frame
import QEDefi.Aave.Health
import QEDefi.Aave.Invariants
import QEDefi.Aave.MathUtils
import QEDefi.Aave.Pool
import QEDefi.Aave.Reserve
import QEDefi.Aave.ScaledToken
import QEDefi.Aave.WadRayMath
import QEDefi.Actor.Action
import QEDefi.Actor.Config
import QEDefi.Actor.Delay
import QEDefi.Actor.Derive
import QEDefi.Actor.Lib.AccessControl
import QEDefi.Actor.Lib.Ownable
import QEDefi.Actor.Lib.Ownable2Step
import QEDefi.Actor.Lib.Safe
import QEDefi.Actor.Lib.Sys
import QEDefi.Actor.Lib.Timelock
import QEDefi.Actor.Trace
import QEDefi.ERC20.Permit
import QEDefi.ERC20.Rep
import QEDefi.ERC20.RepOz
import QEDefi.ERC20.Spec.Asset
import QEDefi.ERC20.Spec.Bytecode
import QEDefi.ERC20.Spec.Callee
import QEDefi.ERC20.Spec.Invariant
import QEDefi.ERC20.Spec.Laws
import QEDefi.ERC20.Spec.Model
import QEDefi.ERC20.Spec.Storage
import QEDefi.ERC20.Spec.TopLevel
import QEDefi.ERC20.Spec.VariantLaws
import QEDefi.ERC20.Token
import QEDefi.ERC20.Variant
import QEDefi.ERC20.VariantDeprecation
import QEDefi.ERC20.VariantExtras
import QEDefi.ERC20.VariantProps
import QEDefi.ERC4626.Agree
import QEDefi.ERC4626.AssetModel
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
import QEDefi.Solvency.Bank
import QEDefi.Solvency.Deps
import QEDefi.Solvency.Tx
import QEDefi.Trace.Lift
import QEDefi.Trace.Time
import QEDefi.Vesting.Model

/-!
# QEDefi

Reusable DeFi verification kits (Mathlib): `uint256` arithmetic (`QEDefi.Math`), the Aave v3.7
Pool's core accounting with its invariants (`QEDefi.Aave`), ERC-20 ledgers
and their word-level representation (`QEDefi.ERC20`), the Solmate and OpenZeppelin ERC-4626
vault models with their properties (`QEDefi.ERC4626`), EVM-independent lifting of per-call
refinement to traces (`QEDefi.Trace`), and the actor model: who can cause an effect, through
roles, relays, thresholds, configuration changes and delays (`QEDefi.Actor`,
`docs/access-control.md`), and bank solvency as a world invariant, kept across whole transactions with all ether
accounted for (`QEDefi.Solvency`).
-/
