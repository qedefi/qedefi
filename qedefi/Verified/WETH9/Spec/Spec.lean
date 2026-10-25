import Verified.WETH9.Spec.TransferFromCall
import Verified.WETH9.Spec.DepositLow

/-!
# WETH9 (mainnet bytecode) against `ERC20Spec`

The deployed WETH9 (`Verified.WETH9.Contracts.WETH9`, solc 0.4.19, unoptimised) is the model
`weth9Model` (`QEDefi.ERC20.Spec.WETH9`: `Variant.weth9` with WETH9's ERC-20 events) through the
storage abstraction `weth9Abs` (`balanceOf` at slot `3`, `allowance` at slot `4`, the ether is the
contract's balance; `Sound` is `ActorRows` for the two mappings), exactly from gas `weth9Gas`
(`100000`), with dispatcher selectors `weth9Sel` and the decoder `weth9Ops` (`deposit()`).

Proved, for every gas (below `weth9Gas` a frame fails or ends the same way; the lockstep is run
along the symbolic execution, `Verified.WETH9.Spec.LowGas`):

* **`weth9_callSpec`**: `transfer`, `transferFrom`, `approve` (`CallSpec`): exact with enough gas,
  no value and a non-static frame; with value they revert (solc 0.4.19 checks `CALLVALUE`), in a
  static frame their first `SSTORE` fails.
* **`weth9_viewSpec`**: `balanceOf`, `allowance`, `totalSupply` (`ViewSpec`).

Not provable as the spec stands (so `ERC20Spec` itself is not proved):

* **`FallbackSpec`**: WETH9's fallback runs `deposit()`, which logs `Deposit(msg.sender,
  msg.value)` on success, for any value (`deposit_low` shows the body). `Matches` requires a
  successful call to append exactly the model's events, and `Event` has only `Transfer` and
  `Approval`, so no event rule makes the `Deposit` log match: every non-static frame with calldata
  shorter than four bytes (or an unknown selector) and enough gas is a counterexample.
* **`OpSpec`** for `Op.deposit` (what `weth9Ops` decodes): the model adds the value to the
  contract's ether *as read in the snapshot* (`pre` reads the world before the value moved),
  while the bytecode's world after the frame has the ether that `transferValue` moved. They
  differ in two cases the frame-level `Start` does not exclude: (1) the caller is the token
  itself (`caller = currentTarget`, value `v > 0`): `moveEther` from an account to itself is the
  identity, so the ether stays `B` while the model says `B + v` (WETH9 never calls itself and its
  address holds code, so EIP-3607 keeps it from sending transactions, but `Start` allows such a
  frame); (2) the balance wraps: `snapshot balance + v ≥ 2²⁵⁶` makes the `Word` balance wrap in
  `transferValue`, while the model's `ether` is a natural number (total ether is far below
  `2²⁵⁶` on a real chain, but `Start` does not say so). The fallback has the same two problems
  in addition to the `Deposit` log. A fix: `Start` (or `OpSpec`) could require `caller ≠
  currentTarget ∨ value = 0` and `(snapshot balance of currentTarget).toNat + value < 2²⁵⁶`, and
  `Matches` could allow a token's own non-ERC-20 logs (or `Event` could carry them).
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

end Verified.WETH9.Spec
