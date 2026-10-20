import Examples.Solmate.ERC20.AssetBurn
import Defi.ERC4626.Logs

/-!
# Events of the asset's `mint` and `burn`: bytecode

Companions of `mint_halts_ok` (`AssetMint.lean`) and `burn_halts_ok` (`AssetBurn.lean`) that
also determine the frame's logs: `MockERC20.mint(dst, amount)` emits `Transfer(0, dst, amount)`
and `burn(src, amount)` emits `Transfer(src, 0, amount)` (Solmate's `_mint` / `_burn`).
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

set_option maxHeartbeats 0 in
/-- **`mint(dst, amount)` of the asset, success, with its log**: as `mint_halts_ok`, and the
frame's logs gain `Transfer(0, dst, amount)`. -/
theorem mint_halts_ok_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {dst : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x40c10f19 (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hov : (m.world.sload m.frame.msg.currentTarget 2#256).toNat + amount.toNat < 2 ^ 256) :
    Halts m (fun mf o => MintOk dst amount m mf o ∧
      mf.frame.sub.logs = m.frame.sub.logs.push
        (transferLog m.frame.msg.currentTarget 0 dst amount)) := by
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
  simp only [gt_add_self_of_lt hov, iszero_zero]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  pwp_codecopy
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine WP.halt_of_step (step_stop ?_) (by same_frame) ⟨⟨rfl, ?_, rfl, rfl, ?_⟩, ?_⟩
  · pcode_fact
  · simp only [mintWorld, balanceSlot_solmate]
  · evm_gas
  · event_log [amount]

set_option maxHeartbeats 0 in
/-- **`burn(src, amount)` of the asset, success, with its log**: as `burn_halts_ok`, and the
frame's logs gain `Transfer(src, 0, amount)`. -/
theorem burn_halts_ok_events {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate src)).toNat) :
    Halts m (fun mf o => BurnOk src amount m mf o ∧
      mf.frame.sub.logs = m.frame.sub.logs.push
        (transferLog m.frame.msg.currentTarget src 0 amount)) := by
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
  refine WP.halt_of_step (step_stop ?_) (by same_frame) ⟨⟨rfl, ?_, rfl, rfl, ?_⟩, ?_⟩
  · pcode_fact
  · simp only [burnWorld, balanceSlot_solmate]
  · evm_gas
  · event_log [amount]

end EvmLeanSpecs.Refinement
