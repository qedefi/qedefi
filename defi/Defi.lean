import Defi.ERC20.Permit
import Defi.ERC20.Rep
import Defi.ERC20.Token
import Defi.ERC4626.Agree
import Defi.ERC4626.Events
import Defi.ERC4626.Inflation
import Defi.ERC4626.Logs
import Defi.ERC4626.MoreProps
import Defi.ERC4626.Oz
import Defi.ERC4626.OzProps
import Defi.ERC4626.Price
import Defi.ERC4626.Solmate
import Defi.ERC4626.SolmateProps
import Defi.ERC4626.Witnesses
import Defi.Math.Arith
import Defi.Trace.Lift

/-!
# Defi

Reusable DeFi verification kits (Mathlib): `uint256` arithmetic (`Defi.Math`), ERC-20 ledgers
and their word-level representation (`Defi.ERC20`), the Solmate and OpenZeppelin ERC-4626
vault models with their properties (`Defi.ERC4626`), and EVM-independent lifting of per-call
refinement to traces (`Defi.Trace`).
-/
