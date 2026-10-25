import Verified.WETH9.Spec.TransferFromCall
import Verified.WETH9.Spec.DepositSpec

/-!
# WETH9 (mainnet bytecode) satisfies `ERC20Spec`

**`weth9_erc20Spec`**: the deployed WETH9 (`Verified.WETH9.Contracts.WETH9`, solc 0.4.19,
unoptimised) is the model `weth9Model` (`QEDefi.ERC20.Spec.WETH9`: `Variant.weth9` with WETH9's
events, `Deposit` included) through the storage abstraction `weth9Abs` (`balanceOf` at slot `3`,
`allowance` at slot `4`, the ether is the contract's balance; `Sound` is `ActorRows` for the two
mappings), exactly from gas `weth9Gas` (`100000`), with dispatcher selectors `weth9Sel` and the
decoder `weth9Ops` (`deposit()`, payable, as `Op.deposit caller value`; `withdraw` calls the
caller's code and is covered by `Verified.WETH9.withdraw_halts_refines`). Every obligation holds
for every gas: below `weth9Gas` a frame fails or ends the same way (the lockstep is run along the
symbolic execution, `Verified.WETH9.Spec.LowGas`).

* `weth9_callSpec`: `transfer`, `transferFrom`, `approve`; with value they revert (solc 0.4.19
  checks `CALLVALUE`), in a static frame their first `SSTORE` fails.
* `weth9_viewSpec`: `balanceOf`, `allowance`, `totalSupply` (the contract's balance).
* `weth9_fallbackSpec`: calldata shorter than a selector or an unknown selector runs `deposit()`
  with the frame's value (`Deposit(caller, value)`).
* `weth9_opSpec`: `deposit()`.
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.WETH9 Verified.WETH9.Contracts

/-- **WETH9's ERC-20 calls are exact**, for every gas (`CallSpec` for every call). -/
theorem weth9_callSpec (c : Call Address) :
    CallSpec WETH9.runtimeCode weth9Abs weth9Model weth9Gas c := by
  intro Act m hS hE hA
  cases c with
  | transfer dst v => exact transfer_callPost hS hE (hA dst (by simp [Call.addrs]))
  | transferFrom src dst v =>
    exact transferFrom_callPost hS hE (hA src (by simp [Call.addrs]))
      (hA dst (by simp [Call.addrs]))
  | approve sp v => exact approve_callPost hS hE (hA sp (by simp [Call.addrs]))
  | other _ => exact hE.elim
  | permit _ _ _ _ _ => exact hE.elim

/-- **WETH9 satisfies `ERC20Spec`**, for every gas. -/
theorem weth9_erc20Spec :
    ERC20Spec WETH9.runtimeCode weth9Abs weth9Model weth9Gas weth9Sel weth9Ops weth9OpAddrs where
  calls := weth9_callSpec
  views := weth9_viewSpec
  fallback := weth9_fallbackSpec
  ops := weth9_opSpec

end Verified.WETH9.Spec
