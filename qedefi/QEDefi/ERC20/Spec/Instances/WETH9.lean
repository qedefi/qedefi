module

public import QEDefi.ERC20.Spec.Model

/-!
# WETH9 as a token model

`weth9Model` is the policy record `Variant.weth9` (`QEDefi.ERC20.Variant`: `totalSupply()` is the
contract's ether, a depositing fallback, `transferFrom` by the owner skipping the allowance,
`2²⁵⁶ − 1` allowances never spent, no zero-address checks) with WETH9's events
(`weth9Events`: `Transfer`, `Approval`, and `Deposit` on the fallback). The bytecode side (`Verified/WETH9/Spec/`) proves the deployed contract is this
model.
-/
@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.WETH9
open QEDefi.ERC20

variable {A : Type} [DecidableEq A] [Zero A]

/-- WETH9's `Deposit(address indexed dst, uint wad)` topic,
`keccak256("Deposit(address,uint256)")` (the generated `WETH9.events`; the `PUSH32` before its
`LOG2`). -/
def depositTopic : ℕ := 0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c

/-- `Deposit(dst, wad)`: topics the signature and `dst`, data `wad`. -/
def depositEvent (dst : A) (wad : ℕ) : Event A := .log [.inr depositTopic, .inl dst] [.inr wad]

/-- **WETH9's events**: `transfer(dst, v)` by `caller` logs `Transfer(caller, dst, v)` (the
source's `transfer` is `transferFrom(msg.sender, dst, v)`), `transferFrom(src, dst, v)` logs
`Transfer(src, dst, v)`, `approve(sp, v)` logs `Approval(caller, sp, v)`, and the fallback with
`value` wei runs `deposit()`, which logs `Deposit(caller, value)` (`depositEvent`, also for
`value = 0`). A `permit` call reaches the same fallback (WETH9 has no `permit`), which the model
runs with no value: `Deposit(caller, 0)`. -/
def weth9Events (_s : VState A) (caller : A) : Call A → List (Event A)
  | .transfer dst v => [.transfer caller dst v]
  | .transferFrom src dst v => [.transfer src dst v]
  | .approve sp v => [.approval caller sp v]
  | .other value => [depositEvent caller value]
  | .permit .. => [depositEvent caller 0]

/-- **WETH9 as a token model.** -/
def weth9Model : TokenModel (VState A) A (Variant.Op A) := Variant.weth9.model weth9Events

end QEDefi.ERC20.Spec.WETH9
