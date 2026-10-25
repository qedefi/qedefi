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
  -- the name: decoded, then the memory abstracted again (`M1`)
  pwp_xrun_to 411 [M0_size, M0_fp, h224, h256, h288, h320, h384, h352, h416, Memory.mcopy_eq,
    Memory.read_storeWord_prefix, Memory.read_write_of_size, Memory.read_write_of_disjoint,
    Memory.loadWord_write_of_disjoint, ByteArray.size_extract, Memory.size_write,
    Bytes.size_zeros]
  wp_abstract_mem M1 with hM1
  have g64 : M1.loadWord 64 = 512#256 := by subst hM1; mem_fact
  have g256 : M1.loadWord 256 = 0xa0#256 := by subst hM1; mem_fact [h256]
  have g288 : M1.loadWord 288 = 0x12#256 := by subst hM1; mem_fact [h288]
  have g384 : M1.loadWord 384 = 0x04#256 := by subst hM1; mem_fact [h384]
  have g416 : M1.read 416 4 = (Bytes.ofWord Asset.symbolWord).extract 0 4 := by
    subst hM1; mem_fact [h416]
  have g448 : M1.loadWord 448 = 0x0d#256 := by subst hM1; mem_fact
  have g480 : M1.loadWord 480 = Asset.nameWord := by
    subst hM1; mem_fact [h352, Asset.toWord_name]
  clear hM1
  -- the symbol, to the second `MCOPY`
  pwp_xrun_to 399 [M1_size, g64, g256, g288, g384, g416, g448, g480, Memory.mcopy_eq,
    Memory.read_storeWord_prefix, Memory.read_write_of_size, Memory.read_write_of_disjoint,
    Memory.loadWord_write_of_disjoint, ByteArray.size_extract, Memory.size_write,
    Bytes.size_zeros]
  wp_abstract_mem M with hM
  have hA : MemA M := by
    subst hM
    refine ⟨M_size, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · mem_fact
    · mem_fact [g416]
    · mem_fact [g288]
    · mem_fact [g448]
    · mem_fact [g480]
    · mem_fact
  clear hM
  apply WP.ret
  refine ⟨rfl, hj, rfl, rfl, hA, rfl, ?_, ?_⟩ <;> dsimp only <;> evm_gas

end Verified.Solmate.Constructor
