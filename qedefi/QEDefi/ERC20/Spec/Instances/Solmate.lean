module

public import QEDefi.ERC20.Spec.Model

/-!
# Solmate's `ERC20` as a token model

`solmateModel` is the variant `Variant.standard` (Solmate's `ERC20` with `MockERC20`'s open
`mint`/`burn`) with Solmate's event rule `solmateEvents`, read off
`contracts/lib/solmate/src/tokens/ERC20.sol`:

* `transfer` and `transferFrom` emit `Transfer(from, to, amount)`; `transferFrom` spends the
  allowance without an `Approval` event;
* `approve` emits `Approval(msg.sender, spender, amount)`;
* `permit` emits `Approval(owner, spender, value)`;
* the fallback (there is none: an unknown selector reverts) emits nothing.

`_mint`/`_burn` emit `Transfer(0, to, amount)`/`Transfer(from, 0, amount)`; operations are
outside the event part of the spec (`OpSpec`), so the rule does not mention them.
-/
@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.Solmate
open QEDefi.ERC20

variable {A : Type} [DecidableEq A] [Zero A]

/-- **Solmate's events**: the events of a successful call by `caller` (the state is not used:
Solmate emits the amounts the caller passed). -/
def solmateEvents (_s : VState A) (caller : A) : Call A → List (Event A)
  | .transfer dst v => [.transfer caller dst v]
  | .transferFrom src dst v => [.transfer src dst v]
  | .approve sp v => [.approval caller sp v]
  | .other _ => []
  | .permit o sp v _ _ => [.approval o sp v]

/-- **Solmate's `ERC20` (`MockERC20`) as a token model.** -/
def solmateModel : TokenModel (VState A) A (Variant.Op A) :=
  (Variant.standard : Variant A).model solmateEvents

@[simp] theorem solmateModel_call :
    (solmateModel : TokenModel (VState A) A (Variant.Op A)).call = Variant.standard.call := rfl

@[simp] theorem solmateModel_events :
    (solmateModel : TokenModel (VState A) A (Variant.Op A)).events = solmateEvents := rfl

@[simp] theorem solmateModel_op :
    (solmateModel : TokenModel (VState A) A (Variant.Op A)).op = Variant.standard.stepOp := rfl

@[simp] theorem solmateModel_wf :
    (solmateModel : TokenModel (VState A) A (Variant.Op A)).wf = Variant.standard.WF := rfl

end QEDefi.ERC20.Spec.Solmate
