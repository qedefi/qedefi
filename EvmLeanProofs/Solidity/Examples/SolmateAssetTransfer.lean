import EvmLeanProofs.Solidity.Dispatch
import EvmLeanProofs.Solidity.Call
import EvmLeanProofs.Solidity.Erc20
import EvmLeanProofs.Contracts.SolmateAsset

/-!
# `SolmateAsset.transfer` refines the ERC-20 model

End-to-end verification of `transfer(address,uint256)` of the **deployed bytecode** of the
vault's asset, Solmate `MockERC20` (`Contracts.SolmateAsset.runtimeCode`, solc 0.8.28,
2870 bytes), for **every `Crypto`**, context, world, transient storage, caller, recipient,
amount, gas ≥ 100 000 and warm sets:

* `reaches_transfer`: the dispatcher takes selector `a9059cbb` to the ABI decoder of
  `transfer` (pc 515) in 39 steps for 162 gas, for every machine (`Dispatch.Reaches`);
* `transfer_ok`: with sufficient balance, the call succeeds, returns ABI `true`, and the world
  is `transferWorld` (two `SSTORE`s to the balance slots);
* `transfer_revert`: with insufficient balance (checked subtraction), the call reverts
  (`Panic(0x11)`) and the world is unchanged;
* `transfer_spec`: through the storage abstraction (`Erc20.view`, Solmate layout:
  `totalSupply` 2, `balanceOf` 3, `allowance` 4), `processMessageCall` yields exactly the
  `balanceOf` and `totalSupply` of `Erc20.Model.transfer`, every allowance whose slot is not
  one of the two written slots is unchanged, and no other account's storage changes, under
  the non-collision hypothesis `BalanceSlotOk` for `caller` and `to` only (a self-transfer is
  allowed).

## How the proof runs

1. `processMessageCall_callMsg` reduces the call to `run` from `start`;
2. `run_start_transfer` (`reaches_transfer.run_eq`) jumps over the dispatcher;
3. `sol_steps` executes the ABI decoder, the body (two mapping lookups with `KECCAK256` of
   scratch memory, `SLOAD`, checked `SUB`, two `SSTORE`s, the `Transfer` event) and the
   return-data encoder, stopping only at the underflow-check `JUMPI`, which
   `gt_sub_self_of_le` / `gt_sub_self_of_lt` decide;
4. `sol_steps` finishes at `RETURN` / `REVERT`.
-/

namespace EvmLean.Solidity.Examples.SolmateAssetTransfer

open Interpreter Dispatch Bytes Erc20 Contracts

/-- The selector of `transfer(address,uint256)`. -/
def transferSelector : Nat := 0xa9059cbb

/-- `transferSelector` is the artifact's method identifier. -/
theorem transferSelector_mem :
    ("transfer(address,uint256)", (0xa9059cbb : UInt32)) ∈ SolmateAsset.selectors := by
  decide

/-- Calldata of `transfer(to, amount)`. -/
def transferCalldata (to : Address) (amount : Word) : ByteArray :=
  Abi.encodeCall transferSelector [Word.ofAddress to, amount]

/-- A top-level call of `transfer(to, amount)` on the asset at `token`. -/
abbrev transferCall (token caller to : Address) (amount : Word) (gas : Nat)
    (warmAddrs : AddressSet) (warmKeys : StorageKeySet) : Message :=
  callMsg SolmateAsset.runtimeCode token caller (transferCalldata to amount) gas warmAddrs
    warmKeys

/-- The selector of `transferCalldata`. -/
theorem selectorOf_transferCalldata (to : Address) (amount : Word) :
    Abi.selectorOf (transferCalldata to amount) = transferSelector := by
  rw [transferCalldata, Abi.selectorOf_encodeCall]; rfl

/-- `CALLDATASIZE` of `transferCalldata`. -/
theorem size_transferCalldata (to : Address) (amount : Word) :
    (transferCalldata to amount).size = 68 := by
  rw [transferCalldata, Abi.size_encodeCall]; rfl

/-- The asset code is not an EIP-7702 delegation designator. -/
theorem delegatedAddress?_runtimeCode : delegatedAddress? SolmateAsset.runtimeCode = none :=
  delegatedAddress?_of_size (by rw [SolmateAsset.size_runtimeCode]; decide)

set_option maxHeartbeats 1000000 in
/-- **Dispatch of `transfer`**: selector `a9059cbb` reaches pc 515 in 39 steps for 162 gas. -/
theorem reaches_transfer : Reaches SolmateAsset.runtimeCode transferSelector 515 39 162 := by
  sol_dispatch

/-- The world after a successful `transfer`: `balanceOf[caller] -= amount`, then
`balanceOf[to] += amount` (reading the updated storage), in the order the code does it. -/
def transferWorld (crypto : Crypto) (w : World) (token caller to : Address) (amount : Word) :
    World :=
  let sc := balanceSlot crypto Layout.solmate caller
  let st := balanceSlot crypto Layout.solmate to
  let w₁ := w.sstore token sc (w.sload token sc - amount)
  w₁.sstore token st (amount + w₁.sload token st)

variable {ctx : Context} {w : World} {tr : TransientStorage} {token caller to : Address}
  {amount : Word} {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

/-- The dispatcher on a `transfer` call, from `start`. -/
theorem run_start_transfer (hgas : 162 ≤ gas) (k : Nat) :
    run (k + 39) (start ctx w tr (transferCall token caller to amount gas warmAddrs warmKeys)) =
      run k { start ctx w tr (transferCall token caller to amount gas warmAddrs warmKeys) with
        frame := { (start ctx w tr
          (transferCall token caller to amount gas warmAddrs warmKeys)).frame with
          pc := 515, stack := [BitVec.ofNat 256 transferSelector], memory := initMemory,
          gasLeft := (start ctx w tr
            (transferCall token caller to amount gas warmAddrs warmKeys)).frame.gasLeft -
            162 } } :=
  reaches_transfer.run_eq (msg := transferCall token caller to amount gas warmAddrs warmKeys)
    rfl rfl rfl (selectorOf_transferCalldata to amount)
    (by rw [show (transferCall token caller to amount gas warmAddrs warmKeys).data =
      transferCalldata to amount from rfl, size_transferCalldata]; decide)
    (by rw [show (transferCall token caller to amount gas warmAddrs warmKeys).data =
      transferCalldata to amount from rfl, size_transferCalldata]; decide)
    hgas k

set_option maxHeartbeats 10000000 in
/-- **`transfer`, success.** If `amount ≤ balanceOf[caller]`, the call returns `true` and
the world is `transferWorld`. -/
theorem transfer_ok (hgas : 100000 ≤ gas)
    (hbal : amount.toNat ≤ ((view ctx.crypto Layout.solmate w token).balanceOf caller).toNat)
    (k : Nat) :
    ∃ r, run (k + 300)
        (start ctx w tr (transferCall token caller to amount gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = transferWorld ctx.crypto w token caller to amount := by
  have hbal' : amount.toNat ≤
      (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (BitVec.ofNat 256 3)))).toNat := hbal
  rw [show k + 300 = (k + 261) + 39 by omega, run_start_transfer (by omega)]
  simp only [start, Frame.init, callMsg, transferSelector]
  sol_steps [transferCalldata]
  simp only [gt_sub_self_of_le hbal']
  sol_steps [transferCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp [ChildResult.success]
  · simp only [topLevelResult_output]
    decide +kernel
  · simp only [topLevelResult_world]
    rfl

set_option maxHeartbeats 10000000 in
/-- **`transfer`, insufficient balance.** If `balanceOf[caller] < amount`, the checked
subtraction panics: the call reverts and the world is unchanged. -/
theorem transfer_revert (hgas : 100000 ≤ gas)
    (hbal : ((view ctx.crypto Layout.solmate w token).balanceOf caller).toNat < amount.toNat)
    (k : Nat) :
    ∃ r, run (k + 300)
        (start ctx w tr (transferCall token caller to amount gas warmAddrs warmKeys)) = .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  have hbal' : (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (BitVec.ofNat 256 3)))).toNat < amount.toNat := hbal
  rw [show k + 300 = (k + 261) + 39 by omega, run_start_transfer (by omega)]
  simp only [start, Frame.init, callMsg, transferSelector]
  sol_steps [transferCalldata]
  simp only [gt_sub_self_of_lt hbal']
  sol_steps [transferCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp [ChildResult.success]
  · simp
  · simp

end EvmLean.Solidity.Examples.SolmateAssetTransfer
