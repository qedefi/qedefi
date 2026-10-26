import Verified.WeirdERC20.ZRX.Spec.TransferFromCall
import Verified.WeirdERC20.ZRX.Spec.Fallback

/-!
# ZRX meets the spec

**`zrx_spec : zrxSpec`**: the mainnet ZRX runtime code is `QEDefi.ERC20.Spec.ZRX.model` through
`abs`, for every finite set of actors whose rows are distinct (`ActorRows`), in every fresh
frame, from `g₀ = 100000` gas; below it, static or with value, a frame may only fail instead.

Each obligation is two symbolic runs (enough gas, any gas): `transfer` (`Transfer.lean`,
`TransferCall.lean`), `transferFrom` (`TransferFrom.lean`, `TransferFromCall.lean`), `approve`
(`Approve.lean`), the views (`ViewSpec.lean`), the fallback (`Fallback.lean`). ZRX has no other
entry point (`ops` decodes nothing).
-/

namespace Verified.WeirdERC20.ZRX.Spec
open EvmLean EvmLogic QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.ZRX.Contracts

/-- **The ERC-20 calls.** -/
theorem calls_spec (c : Call Address) : CallSpec ZRX.runtimeCode abs M g₀ c := by
  cases c with
  | transfer dst v => exact call_transfer dst v
  | transferFrom src dst v => exact call_transferFrom src dst v
  | approve sp v => exact call_approve sp v
  | other _ => intro _ _ _ h; exact h.elim
  | permit _ _ _ _ _ => intro _ _ _ h; exact h.elim

/-- **No other entry point**: the decoder accepts nothing. -/
theorem ops_spec : OpSpec ZRX.runtimeCode abs M g₀ ops opAddrs := by
  intro _ _ _ _ h
  simp [ops] at h

/-- **ZRX is its model.** -/
theorem zrx_spec : zrxSpec := ⟨calls_spec, views, fallback_spec, ops_spec⟩

end Verified.WeirdERC20.ZRX.Spec
