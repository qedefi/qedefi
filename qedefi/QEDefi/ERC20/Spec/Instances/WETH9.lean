module

public import QEDefi.ERC20.Spec.Model

/-!
# WETH9 as a token model

`weth9Model` is the policy record `Variant.weth9` (`QEDefi.ERC20.Variant`: `totalSupply()` is the
contract's ether, a depositing fallback, `transferFrom` by the owner skipping the allowance,
`2²⁵⁶ − 1` allowances never spent, no zero-address checks) with WETH9's ERC-20 events
(`weth9Events`). The bytecode side (`Verified/WETH9/Spec/`) proves the deployed contract is this
model.
-/
@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.WETH9
open QEDefi.ERC20

variable {A : Type} [DecidableEq A] [Zero A]

/-- **WETH9's ERC-20 events**: `transfer(dst, v)` by `caller` logs `Transfer(caller, dst, v)`
(the source's `transfer` is `transferFrom(msg.sender, dst, v)`), `transferFrom(src, dst, v)` logs
`Transfer(src, dst, v)`, `approve(sp, v)` logs `Approval(caller, sp, v)`.

The fallback (`.other value`) is WETH9's `deposit()`, which logs `Deposit(msg.sender, value)`
(topic `0xe1fffcc4…`), even for `value = 0`; `withdraw` logs `Withdrawal`. Neither is an ERC-20
event, and the `Event` type has only `Transfer` and `Approval`, so this rule gives them the empty
list. `Matches` requires the logs appended by a successful call to be exactly the model's events
(`mf.frame.sub.logs = m.frame.sub.logs ++ evs.map eventLog`), so with this rule (or any rule over
`Event`) the fallback's `Deposit` log can never match: `FallbackSpec` is false for WETH9 as the
spec stands (see `Verified.WETH9.Spec`). A `permit` call reaches the same fallback (no
`permit`), so it gets the empty list as well. -/
def weth9Events (_s : VState A) (caller : A) : Call A → List (Event A)
  | .transfer dst v => [.transfer caller dst v]
  | .transferFrom src dst v => [.transfer src dst v]
  | .approve sp v => [.approval caller sp v]
  | .other _ => []
  | .permit .. => []

/-- **WETH9 as a token model.** -/
def weth9Model : TokenModel (VState A) A (Variant.Op A) := Variant.weth9.model weth9Events

end QEDefi.ERC20.Spec.WETH9
