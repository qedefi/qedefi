import Examples.Solmate.ERC20.Approve
import Defi.ERC4626.Logs
import Examples.Solmate.ERC20.TransferFrom
import Examples.Solmate.ERC4626.Invariants.Calldata
import Examples.Solmate.ERC4626.Events

/-!
# Logs of the asset's `transfer`, `approve` and `transferFrom`

Companions of the bytecode theorems with the logs they append; split from `Events.lean` (which
adds `mint`/`burn` and the frame and top-level forms) so the vault's internal functions can use
them early.
-/

section

namespace Examples.Solmate.ERC20
open Examples.Solmate.ERC4626 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open EvmLogic.Solidity.ERC20 (transferWorld)

set_option maxHeartbeats 0 in
/-- **`transfer_halts_ok` with its log** `Transfer(caller, dst, amount)`. -/
theorem transfer_halts_ok_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {dst : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)).toNat) :
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
/-- **`approve_halts` with its log** `Approval(caller, spender, amount)`. -/
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
  · simp only [outputMachine, ERC20.approveWorld, allowanceSlot_solmate]
  · dsimp only [outputMachine]
    evm_gas
  · dsimp only [outputMachine]
    event_log [amount]

end Examples.Solmate.ERC20

end

section

/-! ## `transferFrom`: bytecode -/

namespace Examples.Solmate.ERC20
open Examples.Solmate.ERC4626 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open EvmLogic.Solidity.ERC20 (transferWorld)

set_option maxHeartbeats 0 in
/-- **`transferFrom_halts_ok` with its log** `Transfer(src, dst, amount)` only: Solmate emits
no `Approval` when spending an allowance. -/
theorem transferFrom_halts_ok_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src dst : Address}
    {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (hspend : m.world.sload m.frame.msg.currentTarget
        (ERC20.allowanceSlot m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.caller) =
        ERC20.maxWord ∨
      amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
        (ERC20.allowanceSlot m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.caller)).toNat)
    (hbal : amount.toNat ≤ ((ERC20.spendWorld m.ctx.crypto m.world m.frame.msg.currentTarget src
      m.frame.msg.caller amount).sload m.frame.msg.currentTarget
        (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat) :
    Halts m (fun mf o => TransferFromOk src dst amount m mf o ∧
      mf.frame.sub.logs = m.frame.sub.logs.push
        (transferLog m.frame.msg.currentTarget src dst amount)) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [ERC20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate, allowanceSlot_solmate] at hbal hspend
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
    · simp only [outputMachine, ERC20.transferFromWorld, ERC20.transferWorld, transferWorld,
        ERC20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate,
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
    · simp only [outputMachine, ERC20.transferFromWorld, ERC20.transferWorld, transferWorld,
        ERC20.spendWorld, maxWord_eq_MAXW, balanceSlot_solmate,
        allowanceSlot_solmate, hmax, ↓reduceIte]
    · dsimp only [outputMachine]
      evm_gas
    · dsimp only [outputMachine]
      event_log [amount]

end Examples.Solmate.ERC20

end
