module

public import QEDefi.ERC20.Spec.Model

/-!
# OpenZeppelin `ERC20` v5 (`ERC20Mock`) as a token model

`ozModel` is the policy record `Variant.oz` (zero-address checks, allowances `≥ MAX`
infinite, the allowance decrease through `_approve`, no `permit`, open `mint`/`burn`) with
OpenZeppelin v5's events (`ozEvents`): `Transfer(caller, dst, v)` on `transfer`,
`Transfer(src, dst, v)` on `transferFrom` and **no** `Approval` when it spends an allowance
(v5's `_spendAllowance` calls `_approve(…, false)`), `Approval(caller, spender, v)` on
`approve`. `mint`/`burn` emit `Transfer` from/to `0`; they are model operations (`Op.mint`,
`Op.burn`), whose events are not part of the spec's interface yet.
-/
@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.Oz
open QEDefi.ERC20

variable {A : Type} [DecidableEq A] [Zero A]

/-- OpenZeppelin v5's events of a successful ERC-20 call by `caller`. -/
def ozEvents (_ : VState A) (caller : A) : Call A → List (Event A)
  | .transfer dst v => [.transfer caller dst v]
  | .transferFrom src dst v => [.transfer src dst v]
  | .approve sp v => [.approval caller sp v]
  | .other _ => []
  | .permit .. => []

/-- **OpenZeppelin `ERC20Mock` v5.** -/
def ozModel : TokenModel (VState A) A (Variant.Op A) := (Variant.oz : Variant A).model ozEvents

@[simp] theorem ozModel_call : (ozModel : TokenModel (VState A) A (Variant.Op A)).call =
    (Variant.oz : Variant A).call := rfl
@[simp] theorem ozModel_events :
    (ozModel : TokenModel (VState A) A (Variant.Op A)).events = ozEvents := rfl
@[simp] theorem ozModel_op : (ozModel : TokenModel (VState A) A (Variant.Op A)).op =
    (Variant.oz : Variant A).stepOp := rfl
@[simp] theorem ozModel_wf : (ozModel : TokenModel (VState A) A (Variant.Op A)).wf =
    (Variant.oz : Variant A).WF := rfl

end QEDefi.ERC20.Spec.Oz
