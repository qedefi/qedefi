import Examples.Solmate.ERC20.Approve
import Defi.ERC4626.Logs

/-!
# Events of the asset's `transfer` and `approve`: bytecode

Companions of `transfer_halts_ok` (`AssetTransfer.lean`) and `approve_halts`
(`AssetApprove.lean`) that also determine the frame's logs: the same symbolic execution, with
the postcondition strengthened by the log the `LOG3` appends.

* `transfer_halts_ok_events`: `TransferOk` and the frame's logs gain exactly
  `Transfer(caller, dst, amount)` emitted by the asset;
* `approve_halts_events`: `ApproveOk` and the logs gain exactly `Approval(caller, spender,
  amount)`.

The topic is the `PUSH32` / code-copied constant of the bytecode; the indexed addresses are the
masked calldata words; the data is the amount, stored at the free pointer.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLean.Solidity.Erc20 (transferWorld)

set_option maxHeartbeats 0 in
/-- **`transfer(dst, amount)` of the asset, success, with its log**: as `transfer_halts_ok`,
and the frame's logs gain `Transfer(caller, dst, amount)`. -/
theorem transfer_halts_ok_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {dst : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller)).toNat) :
    Halts m (fun mf o => TransferOk dst amount m mf o ∧
      mf.frame.sub.logs = m.frame.sub.logs.push
        (transferLog m.frame.msg.currentTarget m.frame.msg.caller dst amount)) := by
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
  refine ⟨⟨rfl, by simp only [outputMachine, transferWorld, balanceSlot_solmate], rfl, rfl, ?_⟩,
    ?_⟩
  · dsimp only [outputMachine]
    evm_gas
  · dsimp only [outputMachine]
    event_log [amount]

set_option maxHeartbeats 0 in
/-- **`approve(spender, amount)` of the asset, with its log**: as `approve_halts`, and the
frame's logs gain `Approval(caller, spender, amount)`. -/
theorem approve_halts_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {spender : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x095ea7b3 (Word.ofAddress spender) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 40000 ≤ m.frame.gasLeft) :
    Halts m (fun mf o => ApproveOk spender amount m mf o ∧
      mf.frame.sub.logs = m.frame.sub.logs.push
        (approvalLog m.frame.msg.currentTarget m.frame.msg.caller spender amount)) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  refine ⟨⟨rfl, ?_, rfl, rfl, ?_⟩, ?_⟩
  · simp only [outputMachine, Erc20.approveWorld, allowanceSlot_solmate]
  · dsimp only [outputMachine]
    evm_gas
  · dsimp only [outputMachine]
    event_log [amount]

end EvmLeanSpecs.Refinement
