import Verified.Solmate.Constructor.AssetDefs
import EvmLogic.Tactic.StepExt

/-!
# The `MockERC20` constructor, first segment

From the start of the init code to `0x018f`: the `CALLVALUE` check, the `CODECOPY` of the
constructor arguments and the ABI decoding of the name (`MCOPY` of its bytes).
-/

namespace Verified.Solmate.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Tactic
open Verified.Solmate.Contracts

set_option maxHeartbeats 0 in
/-- From the start to `0x018f`: the value check, the `CODECOPY` of the arguments, the ABI
decoding of the name. -/
theorem asset_seg1 (m : Machine) (hf : Fresh SolmateAsset.initCode m)
    (hval : m.frame.msg.value = 0) (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (At399 m) (fun _ _ => False) := by
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  clear hf
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  wp_hide_jump_tables
  subst hs hpc hc hmem
  pwp_xsteps 400 [hval, SolmateAsset.size_initCode]
  rw [Asset.write_args (by simp only [Memory.size_expand, Memory.size_storeWord,
    Memory.size_empty, Memory.wordsAfter, Memory.words]; decide)]
  wp_abstract_mem M0 with hM0
  have h224 : M0.loadWord 224 = 0x60#256 := by subst hM0; mem_fact
  have h256 : M0.loadWord 256 = 0xa0#256 := by subst hM0; mem_fact
  have h288 : M0.loadWord 288 = 0x12#256 := by subst hM0; mem_fact
  have h320 : M0.loadWord 320 = 0x0d#256 := by subst hM0; mem_fact
  have h384 : M0.loadWord 384 = 0x04#256 := by subst hM0; mem_fact
  have h352 : M0.read 352 13 = (Bytes.ofWord Asset.nameWord).extract 0 13 := by
    subst hM0; mem_fact
  have h416 : M0.read 416 4 = (Bytes.ofWord Asset.symbolWord).extract 0 4 := by
    subst hM0; mem_fact
  clear hM0
  pwp_xsteps 400 [h224, h256, h288, h320, h384, h352, h416, Memory.mcopy_eq,
    Memory.read_storeWord_prefix, Memory.loadWord_storeWord_zero_tail, Memory.read_write_of_size,
    Memory.read_write_of_disjoint, Memory.loadWord_write_of_disjoint, ByteArray.size_extract,
    Memory.size_write, Bytes.size_zeros, Asset.toWord_name, Asset.toWord_symbol]
  wp_abstract_mem M with hM
  have hA : MemA M := by
    subst hM
    refine ⟨M_size, M_fp, ?_, ?_, ?_, ?_, ?_⟩
    · mem_fact [h416]
    · mem_fact [h288]
    · mem_fact
    · mem_fact [h352, Asset.toWord_name]
    · mem_fact
  clear hM
  apply WP.ret
  refine ⟨rfl, hj, rfl, rfl, hA, rfl, ?_, ?_⟩ <;> dsimp only <;> simp only [M0_size] <;> evm_gas

end Verified.Solmate.Constructor
