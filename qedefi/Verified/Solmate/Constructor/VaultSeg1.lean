import Verified.Solmate.Constructor.VaultDefs
import EvmLogic.Tactic.StepExt

/-!
# The `MockERC4626` constructor, first segment

From the start of the init code of a vault over `asset` to `0x0068` (`Vault.At104`): the zero
writes of the hook counters (slots 6 and 7), the `CALLVALUE` check, the `CODECOPY` of the
arguments, their ABI decoding (the asset address, the name and the symbol) and the calldata of
`asset.decimals()`. The init code's jump table is described by `jumpTable_initCodeFor`: the
argument bytes depend on `asset`, the creation code's jump destinations do not.
-/

namespace Verified.Solmate.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Tactic
open Verified.Solmate.Contracts

set_option maxHeartbeats 0 in
/-- **The first segment** of the vault's constructor, to `Vault.At104`. -/
theorem vault_seg1 (asset : Address) (m : Machine)
    (hf : Fresh (SolmateVault.initCodeFor asset) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    (hg : 1000000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (Vault.At104 asset m) (fun _ _ => False) := by
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  clear hf
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  wp_hide_jump_tables
  subst hs hpc hc hmem
  have hJ := SolmateVault.jumpTable_initCodeFor hj
  pwp_xsteps 400 [hval, SolmateVault.size_initCodeFor]
  rw [Vault.write_args (by simp only [Memory.size_expand, Memory.size_storeWord,
    Memory.size_empty, Memory.wordsAfter, Memory.words]; decide)]
  wp_abstract_mem M0 with hM0
  have h256 : M0.loadWord 256 = Word.ofAddress asset := by subst hM0; mem_fact
  have h288 : M0.loadWord 288 = 0x60#256 := by subst hM0; mem_fact
  have h320 : M0.loadWord 320 = 0xa0#256 := by subst hM0; mem_fact
  have h352 : M0.loadWord 352 = 0x0d#256 := by subst hM0; mem_fact
  have h416 : M0.loadWord 416 = 0x06#256 := by subst hM0; mem_fact
  have h384 : M0.read 384 13 = (Bytes.ofWord SolmateVault.nameWord).extract 0 13 := by
    subst hM0; mem_fact
  have h448 : M0.read 448 6 = (Bytes.ofWord SolmateVault.symbolWord).extract 0 6 := by
    subst hM0; mem_fact
  clear hM0
  pwp_xrun_to 534 [M0_size, M0_fp, h256, h288, h320, h352, h416, h384, h448, Memory.mcopy_eq,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self,
    Memory.read_storeWord_prefix, Memory.loadWord_storeWord_zero_tail', Memory.read_write_extract,
    Memory.read_write_of_disjoint, Memory.loadWord_write_of_disjoint, ByteArray.size_extract,
    Memory.size_write, Bytes.size_zeros, Vault.toWord_name, Vault.toWord_symbol]
  wp_abstract_mem M1 with hM1
  have g256 : M1.loadWord 256 = Word.ofAddress asset := by subst hM1; mem_fact [h256]
  have g320 : M1.loadWord 320 = 0xa0#256 := by subst hM1; mem_fact [h320]
  have g416 : M1.loadWord 416 = 0x06#256 := by subst hM1; mem_fact [h416]
  have g448 : M1.read 448 6 = (Bytes.ofWord SolmateVault.symbolWord).extract 0 6 := by
    subst hM1; mem_fact [h448]
  have g480 : M1.loadWord 480 = 0x0d#256 := by subst hM1; mem_fact
  have g512 : M1.loadWord 512 = SolmateVault.nameWord := by
    subst hM1; mem_fact [h384, Vault.toWord_name]
  have g64 : M1.loadWord 64 = 544#256 := by subst hM1; mem_fact
  clear hM1
  pwp_xrun_to 104 [M1_size, g64, g256, g320, g416, g448, g480, g512, Memory.mcopy_eq,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self,
    Memory.read_storeWord_prefix, Memory.loadWord_storeWord_zero_tail', Memory.read_write_extract,
    Memory.read_write_of_disjoint, Memory.loadWord_write_of_disjoint, ByteArray.size_extract,
    Memory.size_write, Bytes.size_zeros, Vault.toWord_name, Vault.toWord_symbol]
  wp_abstract_mem M with hM
  have hA : Vault.MemA M := by
    subst hM
    refine ⟨M_size, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · mem_fact
    · mem_fact [g480]
    · mem_fact [g512]
    · mem_fact
    · mem_fact [g448, Vault.toWord_symbol]
    · mem_fact; rfl
    · mem_fact; rfl
  clear hM
  apply WP.ret
  refine ⟨rfl, hj, rfl, rfl, hA, rfl, ?_, ?_⟩ <;> dsimp only <;> evm_gas

end Verified.Solmate.Constructor
