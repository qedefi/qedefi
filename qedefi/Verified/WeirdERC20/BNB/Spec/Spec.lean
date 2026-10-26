import Verified.WeirdERC20.BNB.Spec.Ops

/-!
# BNB meets the spec

**`bnb_spec : bnbSpec`**: the mainnet BNB runtime code is `bnbModel` (`Variant.bnb` with BNB's
events and its credit-overflow guard) through `bnbAbs`, for every finite set of actors whose
rows are distinct (`bnbSound`), in every fresh frame, from `g₀ = 100000` gas; below it or
static, a frame may only fail instead.

Each obligation is two symbolic runs: `transfer` (`Transfer.lean`), `transferFrom`
(`TransferFrom.lean`), `approve` (`Approve.lean`), the views (`Views.lean`), the payable
fallback (`Fallback.lean`), `burn`, `freeze` and `unfreeze` (`Ops.lean`).
-/

namespace Verified.WeirdERC20.BNB.Spec
open EvmLean EvmLogic QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.BNB.Contracts

/-- **The ERC-20 calls.** -/
theorem calls_spec (c : Call Address) : CallSpec BNB.runtimeCode bnbAbs M g₀ c := by
  cases c with
  | transfer dst v => exact call_transfer dst v
  | transferFrom src dst v => exact call_transferFrom src dst v
  | approve sp v => exact call_approve sp v
  | other _ => intro _ _ _ h; exact h.elim
  | permit _ _ _ _ _ => intro _ _ _ h; exact h.elim

/-- **BNB is its model.** -/
theorem bnb_spec : bnbSpec := ⟨calls_spec, views, fallback_spec, ops_spec⟩

end Verified.WeirdERC20.BNB.Spec
