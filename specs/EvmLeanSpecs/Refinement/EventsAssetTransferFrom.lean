import EvmLeanSpecs.Refinement.AssetTransferFrom
import EvmLeanSpecs.Refinement.EventsLog

/-!
# Events of the asset's `transferFrom`: bytecode

`transferFrom_halts_ok_events`: the companion of `transferFrom_halts_ok`
(`AssetTransferFrom.lean`) that also determines the frame's logs — on both success paths
(infinite and finite allowance) the frame's logs gain exactly `Transfer(src, dst, amount)`
emitted by the asset. Solmate emits **no** `Approval` when it spends the allowance.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLean.Solidity.Examples.SolmateAssetTransfer (transferWorld)

set_option maxHeartbeats 0 in
/-- **`transferFrom(src, dst, amount)` of the asset, success, with its log**: as
`transferFrom_halts_ok`, and the frame's logs gain `Transfer(src, dst, amount)` (and nothing
else: no `Approval`). -/
theorem transferFrom_halts_ok_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src dst : Address}
    {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (hspend : m.world.sload m.frame.msg.currentTarget
        (Erc20.allowanceSlot m.ctx.crypto Erc20.Layout.solmate src m.frame.msg.caller) =
        Erc20.maxWord ∨
      amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
        (Erc20.allowanceSlot m.ctx.crypto Erc20.Layout.solmate src m.frame.msg.caller)).toNat)
    (hbal : amount.toNat ≤ ((Erc20.spendWorld m.ctx.crypto m.world m.frame.msg.currentTarget src
      m.frame.msg.caller amount).sload m.frame.msg.currentTarget
        (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate src)).toNat) :
    Halts m (fun mf o => TransferFromOk src dst amount m mf o ∧
      mf.frame.sub.logs = m.frame.sub.logs.push
        (transferLog m.frame.msg.currentTarget src dst amount)) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [Erc20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate, allowanceSlot_solmate] at hbal hspend
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  by_cases hmax : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 4#256)))) = MAXW
  · simp only [hmax, Solidity.eq_self, ↓reduceIte] at hbal ⊢
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [gt_sub_self_of_le hbal, iszero_zero]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    pwp_codecopy
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine ⟨⟨rfl, ?_, rfl, rfl, ?_⟩, ?_⟩
    · simp only [outputMachine, Erc20.transferFromWorld, Erc20.transferWorld, transferWorld,
        Erc20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate,
        allowanceSlot_solmate, hmax, ↓reduceIte]
    · dsimp only [outputMachine]
      evm_gas
    · dsimp only [outputMachine]
      event_log [amount]
  · simp only [eq_of_ne hmax, hmax, ↓reduceIte] at hbal ⊢
    have hle := hspend.resolve_left hmax
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [gt_sub_self_of_le hle, iszero_zero]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [gt_sub_self_of_le hbal, iszero_zero]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    pwp_codecopy
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine ⟨⟨rfl, ?_, rfl, rfl, ?_⟩, ?_⟩
    · simp only [outputMachine, Erc20.transferFromWorld, Erc20.transferWorld, transferWorld,
        Erc20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate,
        allowanceSlot_solmate, hmax, ↓reduceIte]
    · dsimp only [outputMachine]
      evm_gas
    · dsimp only [outputMachine]
      event_log [amount]

end EvmLeanSpecs.Refinement
