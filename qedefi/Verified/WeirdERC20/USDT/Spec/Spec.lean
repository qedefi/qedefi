import Verified.WeirdERC20.USDT.Spec.Views
import Verified.WeirdERC20.USDT.Spec.Fallback
import Verified.WeirdERC20.USDT.Spec.TransferFrom
import Verified.WeirdERC20.USDT.Spec.Ops

/-!
# USDT satisfies `ERC20Spec`

`usdt_erc20Spec`: the mainnet `TetherToken` runtime code is `usdtModel` through `usdtAbs`, from
gas `g₀ = 200000`, for every actor set: the three calls (`usdt_transfer`, `usdt_transferFrom`,
`usdt_approve`; `other` and `permit` are not ABI calls of the spec), the three views, the
fallback on unknown selectors and short calldata, and the admin entry points `ops` decodes.

The scope is `usdtAbs`'s `Live` (not deprecated, six decimals, the owner an actor); outside it
the abstraction reads a state the model's invariant excludes. `pause()`/`unpause()` are not
among `ops` (the code reverts on a repeated pause, the model's `setPaused` does not).
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean QEDefi.ERC20 QEDefi.ERC20.Spec

/-- **`CallSpec` for every call.** -/
theorem usdt_calls (c : Call Address) : CallSpec Contracts.USDT.runtimeCode usdtAbs M g₀ c := by
  cases c with
  | transfer dst v => exact usdt_transfer dst v
  | transferFrom src dst v => exact usdt_transferFrom src dst v
  | approve sp v => exact usdt_approve sp v
  | other _ => intro _ _ _ hE; exact hE.elim
  | permit _ _ _ _ _ => intro _ _ _ hE; exact hE.elim

/-- **USDT satisfies `ERC20Spec`**, at any gas. -/
theorem usdt_erc20Spec : usdtSpec where
  calls := usdt_calls
  views := usdt_views
  fallback := usdt_fallback
  ops := usdt_ops

end Verified.WeirdERC20.USDT.Spec
