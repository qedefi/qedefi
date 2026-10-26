import Verified.WeirdERC20.LEND.Spec.TransferFromCall
import Verified.WeirdERC20.LEND.Spec.Ops

/-!
# LEND meets the spec

**`lend_spec : lendSpec`**: the mainnet LEND runtime code is `QEDefi.ERC20.Spec.LEND.model`
through `abs`, for every finite set of actors whose rows are distinct (`ActorRows`), in every
fresh frame of a token in the final sale state (the model's invariant: `ICOFinished`, transfers
enabled), from `g₀ = 150000` gas; below it, static or with value, a frame may only fail
instead.

Each obligation is two symbolic runs (enough gas, any gas): `transfer` (`Transfer.lean`,
`TransferCall.lean`), `transferFrom` (`TransferFrom.lean`, `TransferFromCall.lean`), `approve`
(`Approve.lean`, `TransferCall.lean`), the views (`Views.lean`), the fallback
(`Fallback.lean`), the sale and administration entry points (`Ops.lean`; the purchases and
`setState` revert in the final state at any gas).
-/

namespace Verified.WeirdERC20.LEND.Spec
open EvmLean EvmLogic QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.LEND.Contracts

/-- **The ERC-20 calls.** -/
theorem calls_spec (c : Call Address) : CallSpec LEND.runtimeCode abs M g₀ c := by
  cases c with
  | transfer dst v => exact call_transfer dst v
  | transferFrom src dst v => exact call_transferFrom src dst v
  | approve sp v => exact call_approve sp v
  | other _ => intro _ _ _ h; exact h.elim
  | permit _ _ _ _ _ => intro _ _ _ h; exact h.elim

/-- **LEND is its model** (in the final sale state). -/
theorem lend_spec : lendSpec := ⟨calls_spec, views, fallback_spec, ops_spec⟩

end Verified.WeirdERC20.LEND.Spec
