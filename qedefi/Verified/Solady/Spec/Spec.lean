import Verified.Solady.Spec.TransferFrom
import Verified.Solady.Spec.Ops
import Verified.Solady.Spec.Fallback

/-!
# Solady `ERC20` meets the ERC-20 spec

**`solady_spec : soladySpec`**: the compiled `SoladyToken` (Solady `ERC20` v0.1.26 with open
`mint`/`burn`) is the model `soladyModel PERMIT2` through `soladyAbs`, for every finite set of
actors whose rows are distinct (`SoladySound`), in every fresh frame (top level or any depth),
from `g₀ = 100000` gas; below it, static or with value, a frame may only fail instead.

Each obligation is two symbolic runs (`Common.lean`): `transfer` (`Transfer.lean`),
`transferFrom` (`TransferFrom.lean`, Permit2, infinite and finite allowances), `approve`
(`Approve.lean`, the Permit2 revert), the views (`Views.lean`), unknown selectors and short
calldata (`Fallback.lean`), `mint` and `burn` (`Ops.lean`).
-/

namespace Verified.Solady.Spec
open EvmLean EvmLogic QEDefi.ERC20 QEDefi.ERC20.Spec Verified.Solady.Contracts

/-- **The ERC-20 calls.** -/
theorem calls_spec (c : Call Address) : CallSpec SoladyToken.runtimeCode soladyAbs M g₀ c := by
  cases c with
  | transfer dst v => exact call_transfer dst v
  | transferFrom src dst v => exact call_transferFrom src dst v
  | approve sp v => exact call_approve sp v
  | other _ => intro _ _ _ h; exact h.elim
  | permit _ _ _ _ _ => intro _ _ _ h; exact h.elim

/-- **`SoladyToken` is Solady's model.** -/
theorem solady_spec : soladySpec := ⟨calls_spec, views, fallback_spec, ops_spec⟩

end Verified.Solady.Spec
