module

public import QEDefi.ERC20.Spec.Model

/-!
# AMPL (`UFragments`) as a token model

`amplModel` is `Variant.ampl` with the events of `UFragments`
(`contracts/mainnet/AMPL/source/contracts/UFragments.sol`, solc 0.7.6, behind its proxy):

* `transfer(dst, v)` logs `Transfer(caller, dst, v)` with the fragment amount `v` (not gons);
* `transferFrom(src, dst, v)` logs `Transfer(src, dst, v)` (spending the allowance logs no
  `Approval`);
* `approve(sp, v)` logs `Approval(caller, sp, v)`;
* `permit(o, sp, v, …)` logs `Approval(o, sp, v)`;
* an unknown selector reverts (no fallback in `UFragments`).

`rebase` is an operation (`Variant.Op.rebase`), not an ERC-20 call: it changes every balance and
logs no `Transfer` (only `LogRebase`, which is not an ERC-20 event).
-/
@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.AMPL

open QEDefi.ERC20

variable {A : Type} [DecidableEq A] [Zero A]

/-- The events of `UFragments` for a successful call by `caller`. -/
def amplEvents (_s : VState A) (caller : A) : Call A → List (Event A)
  | .transfer dst v => [.transfer caller dst v]
  | .transferFrom src dst v => [.transfer src dst v]
  | .approve sp v => [.approval caller sp v]
  | .other _ => []
  | .permit o sp v _ _ => [.approval o sp v]

/-- **AMPL** (`UFragments`). -/
def amplModel : TokenModel (VState A) A (Variant.Op A) := Variant.ampl.model amplEvents

end QEDefi.ERC20.Spec.AMPL
