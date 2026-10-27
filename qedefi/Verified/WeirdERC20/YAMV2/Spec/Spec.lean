import Verified.WeirdERC20.YAMV2.Spec.OpsCall
import Verified.WeirdERC20.YAMV2.Spec.TransferFromCall
import Verified.WeirdERC20.YAMV2.Spec.Fallback

/-!
# YAMv2 meets the spec

**`yamv2_spec : yamv2Spec`**: the deployed YAMv2 runtime code (solc 0.6.12, 50 000 optimizer
runs) is `QEDefi.ERC20.Spec.YAMV2.model` through `abs`, for every finite set of actors whose
rows are distinct (`ActorRows`), in every fresh frame whose state the model can reach
(`Start.wf`: the actors' balances add up to at most the supply), from `g₀ = 100000` gas; below
it, with value or static, a frame may only fail instead.

Each obligation is two symbolic runs, an exact one (`pwp_xsteps`) and an any-gas one
(`hwp_steps`): the views (`Views.lean`), unknown selectors (`Fallback.lean`), `approve`
(`Approve.lean`), `transfer` (`Transfer.lean`, `TransferHigh.lean`, `TransferCall.lean`),
`transferFrom` (`TransferFrom*.lean`), `mint` and `increaseAllowance` (`Ops.lean`),
`decreaseAllowance` (`Decrease.lean`), assembled in `OpsCall.lean`. solc 0.6.12 builds its
revert reasons in memory; the runs abstract the memory after each copied reason string
(`Common.lean`).
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.YAMV2.Contracts

/-- **The ERC-20 calls.** -/
theorem calls_spec (c : Call Address) : CallSpec YAMV2.runtimeCode abs M g₀ c := by
  cases c with
  | transfer dst v => exact call_transfer dst v
  | transferFrom src dst v => exact call_transferFrom src dst v
  | approve sp v => exact call_approve sp v
  | other _ => intro _ _ _ h; exact h.elim
  | permit _ _ _ _ _ => intro _ _ _ h; exact h.elim

/-- **YAMv2 is its model.** -/
theorem yamv2_spec : yamv2Spec := ⟨calls_spec, views, fallback_spec, ops_spec⟩

end Verified.WeirdERC20.YAMV2.Spec
