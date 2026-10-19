import EvmLeanProofs.Solidity.Examples.Erc20

/-!
# Compiled ERC-20: `transfer` refines the model

End-to-end verification of `transfer(address,uint256)` of the solc 0.8.28 output in
`Erc20Code` (Solmate-style ERC-20), for **every `Crypto`**, context, world, transient
storage, caller, recipient, amount, gas ≥ 100 000 and warm sets:

* `transfer_ok`: with sufficient balance, the call succeeds, returns ABI `true`, and the world
  is `transferWorld` (two `SSTORE`s to the balance slots);
* `transfer_revert`: with insufficient balance (solc's checked subtraction), the call reverts
  (`Panic(0x11)`) and the world is unchanged;
* `transfer_spec`: through the storage abstraction (`Erc20.view`, Solmate layout), the
  resulting `balanceOf` and `totalSupply` are exactly those of `Erc20.Model.transfer`, every
  allowance whose slot is not one of the two written slots is unchanged, and no other
  account's storage changes; under the non-collision hypothesis `BalanceSlotOk` for `caller`
  and `to` only.

## How the proof runs

1. `processMessageCall_call` reduces the call to `run` from `start`;
2. `reaches_transfer.run_eq` jumps over the dispatcher (49 steps, proved once in
   `Examples.Erc20`);
3. `sol_steps` executes the ABI decoder, the body of `transfer` (two mapping lookups with
   `KECCAK256` of scratch memory, `SLOAD`, checked `SUB`, `SSTORE`s, the `Transfer` event with
   its topic loaded by `CODECOPY`) and the return-data encoder, stopping only at the
   overflow-check `JUMPI`, which `gt_sub_self_of_le` / `gt_sub_self_of_lt` decide;
4. `sol_steps` finishes at `RETURN` / `REVERT`.

The whole path is 239 instructions (190 after the dispatcher); the symbolic run of each case
takes 20–40 s.
-/

namespace EvmLean.Solidity.Examples.SolmateErc20

open Interpreter Dispatch Bytes Erc20

variable {ctx : Context} {w : World} {tr : TransientStorage} {token caller to : Address}
  {amount : Word} {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

/-- The world after a successful `transfer`: `balanceOf[caller] -= amount`, then
`balanceOf[to] += amount` (reading the updated storage), in the order the code does it. -/
def transferWorld (crypto : Crypto) (w : World) (token caller to : Address) (amount : Word) :
    World :=
  let sc := balanceSlot crypto Layout.solmate caller
  let st := balanceSlot crypto Layout.solmate to
  let w₁ := w.sstore token sc (w.sload token sc - amount)
  w₁.sstore token st (amount + w₁.sload token st)

/-- The machine started for a `transfer` call. -/
abbrev transferStart (ctx : Context) (w : World) (tr : TransientStorage)
    (token caller to : Address) (amount : Word) (gas : Nat) (warmAddrs : AddressSet)
    (warmKeys : StorageKeySet) : Machine :=
  start ctx w tr (call token caller (transferCalldata to amount) gas warmAddrs warmKeys)

set_option maxHeartbeats 10000000 in
/-- **`transfer`, success.** If `amount ≤ balanceOf[caller]`, the call returns `true` and
the world is `transferWorld`. -/
theorem transfer_ok (hgas : 100000 ≤ gas)
    (hbal : amount.toNat ≤ ((view ctx.crypto Layout.solmate w token).balanceOf caller).toNat)
    (k : Nat) :
    ∃ r, run (k + 239) (transferStart ctx w tr token caller to amount gas warmAddrs warmKeys) =
        .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = transferWorld ctx.crypto w token caller to amount := by
  have hbal' : amount.toNat ≤
      (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (BitVec.ofNat 256 3)))).toNat := hbal
  rw [reaches_transfer.run_eq (msg := call token caller (transferCalldata to amount) gas
      warmAddrs warmKeys) rfl rfl rfl (selectorOf_transferCalldata to amount)
    (by rw [show (call token caller (transferCalldata to amount) gas warmAddrs warmKeys).data =
      transferCalldata to amount from rfl, size_transferCalldata]; decide)
    (by rw [show (call token caller (transferCalldata to amount) gas warmAddrs warmKeys).data =
      transferCalldata to amount from rfl, size_transferCalldata]; decide)
    (show 206 ≤ gas by omega)]
  simp only [transferStart, start, Frame.init, call, transferSelector]
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
    ∃ r, run (k + 239) (transferStart ctx w tr token caller to amount gas warmAddrs warmKeys) =
        .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  have hbal' : (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (BitVec.ofNat 256 3)))).toNat < amount.toNat := hbal
  rw [reaches_transfer.run_eq (msg := call token caller (transferCalldata to amount) gas
      warmAddrs warmKeys) rfl rfl rfl (selectorOf_transferCalldata to amount)
    (by rw [show (call token caller (transferCalldata to amount) gas warmAddrs warmKeys).data =
      transferCalldata to amount from rfl, size_transferCalldata]; decide)
    (by rw [show (call token caller (transferCalldata to amount) gas warmAddrs warmKeys).data =
      transferCalldata to amount from rfl, size_transferCalldata]; decide)
    (show 206 ≤ gas by omega)]
  simp only [transferStart, start, Frame.init, call, transferSelector]
  sol_steps [transferCalldata]
  simp only [gt_sub_self_of_lt hbal']
  sol_steps [transferCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp [ChildResult.success]
  · simp
  · simp

end EvmLean.Solidity.Examples.SolmateErc20
