import Verified.WeirdERC20.AMPL.Spec.OwnerCall

/-!
# AMPL (`UFragments`) meets the spec

**`ampl_spec : amplSpec`**: the `UFragments` implementation code, running in the proxy's storage
(`Abs.lean`), is `amplModel` (`Variant.ampl`: balances in gons, `balanceOf = gons /
gonsPerFragment`; with the owner, the monetary policy and their entry points) through `amplAbs`, for every finite set of actors whose rows are distinct
(`amplSound`), in every fresh frame whose state the model can reach (`Start.wf`), from
`g₀ = 100000` gas; below it or static, a frame may only fail instead.

Each obligation is two symbolic runs: `transfer` (`Transfer.lean`, `TransferCall.lean`),
`transferFrom` (`TransferFrom.lean`, `TransferFromCall.lean`), `approve` (`Approve.lean`), the
views (`Views.lean`), unknown selectors and short calldata (`Fallback.lean`), `transferAll`,
`transferAllFrom`, `increaseAllowance` and `decreaseAllowance` (`Ops.lean`, `OpsCall.lean`),
`setMonetaryPolicy`, `transferOwnership`, `renounceOwnership` (`Owner.lean`) and `rebase`
(`Rebase.lean`), bridged in `OwnerCall.lean`.
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLogic QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open QEDefi.ERC20.Spec.AMPL (AState AState.setAllowance liftR AmplOp amplOp rebaseOp rebaseSupply)

/-- **The ERC-20 calls.** -/
theorem calls_spec (c : Call Address) : CallSpec AMPL.runtimeCode amplAbs M g₀ c := by
  cases c with
  | transfer dst v => exact call_transfer dst v
  | transferFrom src dst v => exact call_transferFrom src dst v
  | approve sp v => exact call_approve sp v
  | other _ => intro _ _ _ h; exact h.elim
  | permit _ _ _ _ _ => intro _ _ _ h; exact h.elim

/-- **`UFragments` is its model.** -/
theorem ampl_spec : amplSpec := ⟨calls_spec, views, fallback_spec, ops_spec⟩

end Verified.WeirdERC20.AMPL.Spec
