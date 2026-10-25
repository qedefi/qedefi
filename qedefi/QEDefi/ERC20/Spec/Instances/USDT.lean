module

public import QEDefi.ERC20.Spec.Model
public import QEDefi.ERC20.VariantExtras

/-!
# USDT as a token model

`usdtModel` is mainnet `TetherToken` (solc 0.4.18) as a `TokenModel`: the policy record
`Variant.usdt` (no return data, `INVALID` on a short balance or allowance and on the SafeMath
overflow of the fee, the approve race guard, a capped basis-point fee paid to the owner, pause
and blacklist on transfers, owner-only `issue`/`redeem`, `destroyBlackFunds`) with USDT's event
rule `usdtEvents`, read off the verified source (`contracts/mainnet/USDT/source/`):

* `transfer(to, v)` by `c` (`BasicToken.transfer`) and `transferFrom(from, to, v)`
  (`StandardToken.transferFrom`) emit `Transfer(src, owner, fee)` when the fee is nonzero, then
  `Transfer(src, to, v − fee)`, where `src` is the payer (`c`, resp. `from`), `owner` the fee
  sink and `fee = min(v · basisPointsRate / 10⁴, maximumFee)`, all as in the state before the
  call (the allowance step changes neither);
* `approve(spender, v)` emits `Approval(c, spender, v)`;
* everything else emits no ERC-20 event (`issue`, `redeem`, `destroyBlackFunds`, the admin
  entry points emit their own events, which the bytecode spec of other entry points does not
  check; unknown selectors revert).

The deprecation forwarding (`deprecate(a)`, after which every entry point forwards to the token
at `a`) is not part of this model: it is the two-contract system of `VariantDeprecation.lean`.
The storage abstraction of the bytecode spec (`Verified.WeirdERC20.USDT.Spec`) represents only
non-deprecated deployments.
-/

@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.USDT
open QEDefi.ERC20 QEDefi.ERC20.Variant

variable {A : Type} [DecidableEq A] [Zero A]

/-- The two `Transfer` events of a USDT transfer of `v` paid by `src` to `dst` in state `s`:
the fee to the owner (only when it is nonzero), then the rest to `dst`. -/
def usdtMoveEvents (s : VState A) (src dst : A) (v : ℕ) : List (Event A) :=
  let fee := (usdt : Variant A).feeOf s v
  (if fee = 0 then [] else [.transfer src s.admin fee]) ++ [.transfer src dst (v - fee)]

/-- **USDT's events**: `Transfer`s of a transfer (`usdtMoveEvents`), `Approval` of an approve. -/
def usdtEvents (s : VState A) (caller : A) : Call A → List (Event A)
  | .transfer dst v => usdtMoveEvents s caller dst v
  | .transferFrom src dst v => usdtMoveEvents s src dst v
  | .approve sp v => [.approval caller sp v]
  | .other _ => []
  | .permit .. => []

/-- **USDT as a token model.** -/
def usdtModel : TokenModel (VState A) A (Op A) := (usdt : Variant A).model usdtEvents

@[simp] theorem usdtModel_call : (usdtModel : TokenModel (VState A) A (Op A)).call =
    (usdt : Variant A).call := rfl

@[simp] theorem usdtModel_events : (usdtModel : TokenModel (VState A) A (Op A)).events =
    usdtEvents := rfl

@[simp] theorem usdtModel_op : (usdtModel : TokenModel (VState A) A (Op A)).op =
    (usdt : Variant A).stepOp := rfl

@[simp] theorem usdtModel_wf : (usdtModel : TokenModel (VState A) A (Op A)).wf =
    (usdt : Variant A).WF := rfl

@[simp] theorem usdtModel_balanceOf (s : VState A) (a : A) :
    (usdtModel : TokenModel (VState A) A (Op A)).balanceOf s a = s.bal a := rfl

@[simp] theorem usdtModel_totalSupply (s : VState A) :
    (usdtModel : TokenModel (VState A) A (Op A)).totalSupply s = s.supply := rfl

@[simp] theorem usdtModel_allowance (s : VState A) (o sp : A) :
    (usdtModel : TokenModel (VState A) A (Op A)).allowance s o sp = s.allowance o sp := rfl

end QEDefi.ERC20.Spec.USDT
