module

public import QEDefi.ERC20.Spec.Model

/-!
# BNB as a token model

`bnbModel` is `Variant.bnb` with BNB's events (`contracts/mainnet/BNB/source/BNB.sol`, solc
0.4.12):

* `transfer(dst, v)` logs `Transfer(caller, dst, v)`;
* `transferFrom(src, dst, v)` logs `Transfer(src, dst, v)`;
* `approve` logs nothing: BNB declares no `Approval` event;
* the payable fallback (every unknown selector, `permit` included) logs nothing.
-/
@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.BNB

open QEDefi.ERC20

variable {A : Type} [DecidableEq A] [Zero A]

/-- BNB's events of a successful call by `caller`. -/
def bnbEvents (_s : VState A) (caller : A) : Call A → List (Event A)
  | .transfer dst v => [.transfer caller dst v]
  | .transferFrom src dst v => [.transfer src dst v]
  | .approve _ _ => []
  | .other _ => []
  | .permit .. => []

/-- **BNB**. -/
def bnbModel : TokenModel (VState A) A (Variant.Op A) := Variant.bnb.model bnbEvents

end QEDefi.ERC20.Spec.BNB
