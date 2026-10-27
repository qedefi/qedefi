import Verified.Solmate.Constructor.AssetDefs
import Verified.Solmate.Constructor.AssetCode
import EvmLogic.Tactic.StepExt

/-!
# The `MockERC20` constructor, second segment

From `0x018f` (`At399`) to the `RETURN`: the `MCOPY` of the symbol, the storage of the name and
symbol in slots 0 and 1 (short strings), `computeDomainSeparator()`, the `CODECOPY` of the
runtime code and the stores of the three immutables into it (`output_eq`).
-/

namespace Verified.Solmate.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Tactic
open Verified.Solmate.Contracts

set_option maxHeartbeats 0 in
/-- **The second segment**: from `At399` (slots 0 and 1 empty), the constructor returns the
runtime code with `Asset.immutables` and writes the name and symbol slots. -/
theorem asset_seg2 (m : Machine) (hc : m.frame.code = SolmateAsset.initCode)
    (hj : JumpTable m.frame.jumpDests SolmateAsset.initCode) (hpc : m.frame.pc = 399)
    (hs : m.frame.stack = [544#256, 416#256, 4#256, 512#256, 4#256, 0#256, 384#256, 448#256,
      509#256, 160#256, 0#256, 0#256, 448#256, 224#256, 448#256, 46#256])
    (hA : MemA m.frame.memory) (hstatic : m.frame.msg.isStatic = false)
    (hs0 : m.world.sload m.frame.msg.currentTarget 0#256 = 0#256)
    (hs1 : m.world.sload m.frame.msg.currentTarget 1#256 = 0#256)
    (hg : 900000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun _ => False) (fun mf o =>
      o = .success (SolmateAsset.runtimeCodeWith
        (Asset.immutables m.ctx.crypto m.ctx.block.chainId m.frame.msg.currentTarget)) ∧
      mf.world = (m.world.sstore m.frame.msg.currentTarget 0#256 Asset.nameSlot).sstore
        m.frame.msg.currentTarget 1#256 Asset.symbolSlot ∧
      m.frame.gasLeft ≤ mf.frame.gasLeft + 100000) := by
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, M, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs
  obtain ⟨M_size, M_fp, h416, h288, h448, h480, h512⟩ := hA
  have hs1' : ∀ v, (m_world.sstore m_msg.currentTarget 0#256 v).sload m_msg.currentTarget 1#256 =
      0#256 := fun v => by rw [World.sload_sstore_ne_key _ _ _ (by decide), hs1]
  have hs0' : ∀ v v', ((m_world.sstore m_msg.currentTarget 0#256 v).sstore m_msg.currentTarget 1#256
      v').sload m_msg.currentTarget 0#256 = v := fun v v' => by
    rw [World.sload_sstore_ne_key _ _ _ (by decide), World.sload_sstore_self]
  pwp_xsteps 405 [hs0, hs1', hs0', Memory.loadWord_storeWord_zero_tail', Memory.read_write_extract, M_size, M_fp, h416, h288, h448, h480, h512, Memory.mcopy_eq,
    Memory.read_storeWord_prefix, Memory.loadWord_storeWord_zero_tail, Memory.read_write_of_size,
    Memory.read_write_of_disjoint, Memory.loadWord_write_of_disjoint, ByteArray.size_extract,
    Memory.size_write, Bytes.size_zeros, Asset.toWord_name, Asset.toWord_symbol]
  wp_abstract_mem M1 with hM1
  have h128 : M1.loadWord 128 = 18#256 := by subst hM1; mem_fact
  have h160 : M1.loadWord 160 = ofNat m_ctx.block.chainId := by subst hM1; mem_fact
  have h64 : M1.loadWord 64 = 576#256 := by subst hM1; mem_fact [M_fp]
  clear hM1
  pwp_xsteps 45 [h64, h128, h160, Memory.read_160]
  wp_abstract_mem M2 with hM2
  have h128' : M2.loadWord 128 = 18#256 := by subst hM2; mem_fact [h128]
  have h160' : M2.loadWord 160 = ofNat m_ctx.block.chainId := by subst hM2; mem_fact [h160]
  clear hM2
  pwp_xsteps 20 [h128', h160']
  pwp_xsteps 1
  pwp_xsteps 1
  pwp_xsteps 1
  pwp_xsteps 1
  wp_abstract_mem M3 with hM3
  simp only [EvmLean.Interpreter.size_readBytes] at M3_size
  pwp_xsteps 20 [M3_size]
  have hM : ∀ j < 2870, Bytes.getD M3.bytes j =
      Bytes.getD (readBytes SolmateAsset.initCode 1015 2870) j := fun j hj => by
    rw [← hM3]; exact getD_write_runtime _ j hj
  refine ⟨?_, rfl, ?_⟩
  · rw [output_eq M3 hM]; rfl
  · dsimp only [outputMachine]; evm_gas

end Verified.Solmate.Constructor
