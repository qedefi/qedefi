module

public import QEDefi.ERC20.Spec.Model

/-!
# STA (Statera) as a token model

`staModel` is `Variant.sta` with Statera's events (`contracts/mainnet/STA/source/Statera.sol`,
solc 0.5.0). A transfer of `v` burns `cut(v) = Variant.sta.feeOf s v` and logs two events, in
this order:

* `transfer(dst, v)`: `Transfer(caller, dst, v − cut(v))`, then `Transfer(caller, 0, cut(v))`;
* `transferFrom(src, dst, v)`: `Transfer(src, dst, v − cut(v))`, then `Transfer(src, 0, cut(v))`
  (spending the allowance logs no `Approval`);
* `approve(sp, v)` logs `Approval(caller, sp, v)`;
* there is no fallback (an unknown selector reverts) and no `permit`.

The fee depends on `v` only (`FeeRule.ceilPercent 100`), so its value in the state before the
call is the one the code computes.
-/
@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.STA

open QEDefi.ERC20

variable {A : Type} [DecidableEq A] [Zero A]

/-- Statera's events of a successful call by `caller`. -/
def staEvents (s : VState A) (caller : A) : Call A → List (Event A)
  | .transfer dst v =>
    [.transfer caller dst (v - Variant.sta.feeOf s v), .transfer caller 0 (Variant.sta.feeOf s v)]
  | .transferFrom src dst v =>
    [.transfer src dst (v - Variant.sta.feeOf s v), .transfer src 0 (Variant.sta.feeOf s v)]
  | .approve sp v => [.approval caller sp v]
  | .other _ => []
  | .permit .. => []

/-- **STA** (Statera). -/
def staModel : TokenModel (VState A) A (Variant.Op A) := Variant.sta.model staEvents

end QEDefi.ERC20.Spec.STA
