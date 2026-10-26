import Verified.WeirdERC20.STA.Spec.OpsCall

/-!
# STA (Statera) meets the spec

**`sta_spec : staSpec`**: the mainnet Statera runtime code is `staModel` (`Variant.sta` with its
two `Transfer` events per move) through `staAbs`, for every finite set of actors whose rows are
distinct (`staSound`), in every fresh frame whose state the model can reach (`Start.wf`: in
particular `basePercent = 100`), from `g₀ = 200000` gas; below it or static, a frame may only fail
instead.

Each obligation is two symbolic runs: `transfer` (`Transfer.lean`, `TransferCall.lean`),
`transferFrom` (`TransferFrom.lean`, `TransferFromCall.lean`), `approve` (`Approve.lean`), the
views (`Views.lean`), unknown selectors and short calldata (`Fallback.lean`), `destroy`,
`destroyFrom`, `upAllowance` and `downAllowance` (`Ops.lean`, `OpsCall.lean`).
-/

namespace Verified.WeirdERC20.STA.Spec
open EvmLean EvmLogic QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.STA.Contracts

/-- **The ERC-20 calls.** -/
theorem calls_spec (c : Call Address) : CallSpec STA.runtimeCode staAbs M g₀ c := by
  cases c with
  | transfer dst v => exact call_transfer dst v
  | transferFrom src dst v => exact call_transferFrom src dst v
  | approve sp v => exact call_approve sp v
  | other _ => intro _ _ _ h; exact h.elim
  | permit _ _ _ _ _ => intro _ _ _ h; exact h.elim

/-- **Statera is its model.** -/
theorem sta_spec : staSpec := ⟨calls_spec, views, fallback_spec, ops_spec⟩

end Verified.WeirdERC20.STA.Spec
