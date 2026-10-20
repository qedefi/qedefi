import EvmLogic.Solidity.Dispatch
import EvmLogic.Solidity.Call
import EvmLogic.Solidity.ERC20
import Examples.Solmate.Contracts.SolmateAsset
import Examples.Solmate.ERC20.BalanceOf
import EvmLogic.Tactic.Patched

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

section

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

end

section

/-!
## `SolmateAsset.transfer`: the refinement theorem

`transfer_spec` lifts `transfer_ok` / `transfer_revert` (bytecode level) through the ERC-20
storage abstraction: a top-level call of `transfer(to, amount)` on the deployed asset
behaves as `Erc20.Model.transfer` on `Erc20.view` of the world.
-/

namespace EvmLean.Solidity.Examples.SolmateAssetTransfer

open Interpreter Erc20 Contracts

variable {ctx : Context} {w : World} {tr : TransientStorage} {token caller to : Address}
  {amount : Word} {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

set_option maxHeartbeats 1000000 in
/-- **`transfer` refines `Model.transfer`** on the deployed `SolmateAsset` bytecode, for every
`Crypto`, context without EIP-7702 authorizations (or before Prague), world, transient
storage, caller, recipient (possibly the caller), amount, gas ≥ 100 000, warm sets and fuel
≥ 300, assuming only that the balance slots of `caller` and `to` do not collide with other
balance/allowance-row slots or with `totalSupply` (`BalanceSlotOk`):

* if the model succeeds with `s'`, the call succeeds, returns `true`, and the abstract
  `totalSupply` and `balanceOf` after the call are those of `s'`; allowances whose slots are
  not the written slots equal those of `s'` (that is, are unchanged); no other account's
  storage changes;
* if the model reverts (insufficient balance), the call reverts and the world is unchanged. -/
theorem transfer_spec (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 100000 ≤ gas)
    (hc : BalanceSlotOk ctx.crypto Layout.solmate caller)
    (ht : BalanceSlotOk ctx.crypto Layout.solmate to) (fuel : Nat) (hfuel : 300 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (transferCall token caller to amount gas warmAddrs warmKeys) = .ok r ∧
      match Model.transfer (view ctx.crypto Layout.solmate w token) caller to amount with
      | some s' =>
        r.success = true ∧ r.output = Bytes.ofWord 1 ∧
        (view ctx.crypto Layout.solmate r.world token).totalSupply = s'.totalSupply ∧
        (view ctx.crypto Layout.solmate r.world token).balanceOf = s'.balanceOf ∧
        (∀ o s, allowanceSlot ctx.crypto Layout.solmate o s ≠
            balanceSlot ctx.crypto Layout.solmate caller →
          allowanceSlot ctx.crypto Layout.solmate o s ≠ balanceSlot ctx.crypto Layout.solmate to →
          (view ctx.crypto Layout.solmate r.world token).allowance o s = s'.allowance o s) ∧
        (∀ b k, b ≠ token → r.world.sload b k = w.sload b k)
      | none => r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 300 := ⟨fuel - 300, by omega⟩
  rw [transferCall, processMessageCall_callMsg hdeleg delegatedAddress?_runtimeCode hpre]
  split
  · rename_i s' hm
    have hbal : amount.toNat ≤ ((view ctx.crypto Layout.solmate w token).balanceOf caller).toNat := by
      unfold Model.transfer at hm
      split at hm
      · assumption
      · cases hm
    obtain ⟨r, hr, hs, ho, hw⟩ := transfer_ok (tr := tr) (to := to) (warmAddrs := warmAddrs)
      (warmKeys := warmKeys) hgas hbal k
    obtain ⟨h1, h2, h3, h4⟩ := view_transferWorld hc ht hm
    refine ⟨r, hr, hs, ho, ?_, ?_, ?_, ?_⟩ <;> rw [hw]
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · rename_i hm
    have hbal : ((view ctx.crypto Layout.solmate w token).balanceOf caller).toNat < amount.toNat := by
      unfold Model.transfer at hm
      split at hm
      · cases hm
      · omega
    exact transfer_revert hgas hbal k

end EvmLean.Solidity.Examples.SolmateAssetTransfer

end

section

/-!
## The asset's `transfer` as a callee summary

`transfer_halts_ok` / `transfer_halts_revert`: `transfer(to, amount)` of the deployed asset
(Solmate `MockERC20`, any immutables), run in any fresh frame (non-static for the success
case: the code writes storage and emits a log), either returns ABI `true` with the world
`transferWorld` (the two balance writes, in the code's order; shared with the solidity
package's top-level `transfer_spec`), or, when the caller's balance does not cover `amount`,
reverts with `Panic(0x11)`. Both bound the gas used, so that a caller can continue after the
call (`WP.call`). `AssetSpec` relates them to `Token.transfer`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLean.Solidity.Erc20 (transferWorld)

/-- Calldata of a function taking two static words `x`, `y`, with selector `sel`. -/
structure TwoWordCall (data : ByteArray) (sel : Nat) (x y : Word) : Prop where
  /-- The selector. -/
  selector : Abi.selectorOf data = sel
  /-- Two argument words. -/
  size : 68 ≤ data.size
  /-- The first argument. -/
  arg0 : Bytes.toWord (readBytes data 4 32) = x
  /-- The second argument. -/
  arg1 : Bytes.toWord (readBytes data 36 32) = y

/-- What a successful `transfer(to, amount)` of the asset ends with: it returns ABI `true`, the
world is `transferWorld` (the two balance writes, in the order the code does them), transient
storage and created accounts are unchanged, and at most 55000 gas is used. -/
def TransferOk (to : Address) (amount : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord 1) ∧
  mf.world = transferWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller
    to amount ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 55000

/-- What a reverting call ends with: a `REVERT` (some data), at most `g` gas used. -/
def Reverts (g : Nat) (m mf : Machine) (o : Outcome) : Prop :=
  (∃ out, o = .revert out) ∧ m.frame.gasLeft ≤ mf.frame.gasLeft + g

set_option maxHeartbeats 0 in
/-- **`transfer(to, amount)` of the asset, success**, in any non-static frame: when the
caller's balance covers `amount`. -/
theorem transfer_halts_ok {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {to : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress to) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller)).toNat) :
    Halts m (TransferOk to amount m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [balanceSlot_solmate] at hbal
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_sub_self_of_le hbal, iszero_zero]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  pwp_codecopy
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine ⟨rfl, by simp only [outputMachine, transferWorld, balanceSlot_solmate], rfl, rfl, ?_⟩
  dsimp only [outputMachine]
  evm_gas

set_option maxHeartbeats 0 in
/-- **`transfer(to, amount)` of the asset, insufficient balance**, in any frame: the checked
subtraction panics (`Panic(0x11)`). -/
theorem transfer_halts_revert {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) {to : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress to) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 10000 ≤ m.frame.gasLeft)
    (hbal : (m.world.sload m.frame.msg.currentTarget
      (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller)).toNat <
        amount.toNat) :
    Halts m (Reverts 10000 m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [balanceSlot_solmate] at hbal
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_sub_self_of_lt hbal, iszero_one]
  pwp_steps
  refine ⟨⟨_, rfl⟩, ?_⟩
  dsimp only [outputMachine]
  evm_gas

end EvmLeanSpecs.Refinement

end
