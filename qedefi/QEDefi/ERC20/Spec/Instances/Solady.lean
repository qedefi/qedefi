module

public import QEDefi.ERC20.Spec.Model

/-!
# Solady `ERC20` as a token model

`soladyModel p` is `Variant.solady p` (Permit2 at `p`) with Solady's events
(`contracts/lib/solady/src/tokens/ERC20.sol`, v0.1.26, through `contracts/src/SoladyToken.sol`):

* `transfer(dst, v)` logs `Transfer(caller, dst, v)`;
* `transferFrom(src, dst, v)` logs `Transfer(src, dst, v)` only: spending the allowance emits no
  `Approval` (neither for a finite allowance nor for Permit2);
* `approve(sp, v)` logs `Approval(caller, sp, v)`;
* `permit(o, sp, v, …)` logs `Approval(o, sp, v)`;
* an unknown selector reverts (no fallback), so it has no event.

The events are only read for successful calls (`Matches`).
-/
@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.Solady

open QEDefi.ERC20

variable {A : Type} [DecidableEq A] [Zero A]

/-- Solady's events of a successful call by `caller`. -/
def soladyEvents (_s : VState A) (caller : A) : Call A → List (Event A)
  | .transfer dst v => [.transfer caller dst v]
  | .transferFrom src dst v => [.transfer src dst v]
  | .approve sp v => [.approval caller sp v]
  | .other _ => []
  | .permit o sp v _ _ => [.approval o sp v]

/-- **Solady `ERC20`** (`SoladyToken`) with the Permit2 spender `p`. -/
def soladyModel (p : A) : TokenModel (VState A) A (Variant.Op A) :=
  (Variant.solady p).model soladyEvents

end QEDefi.ERC20.Spec.Solady
