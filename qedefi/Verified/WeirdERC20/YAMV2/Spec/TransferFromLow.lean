import Verified.WeirdERC20.YAMV2.Spec.TransferFrom

/-!
# YAMv2 under the spec: `transferFrom`, the any-gas run

Any gas, value or static flag: the frame fails or ends in `TransferFromPost`. The memory is
abstracted after the allowance's reason string is copied, keeping the free-memory pointer and
the string's length (the revert's encoding loop reads it).
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.YAMV2.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626
open Verified.WeirdERC20.AMPL.Spec (iszero_lt_size ampl_addr_ne')

set_option maxHeartbeats 0 in
theorem transferFrom_low (m : Machine) (src dst : Address) (v : Word)
    (hf : Fresh YAMV2.runtimeCode m)
    (hd : Args m.frame.msg.data 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (TransferFromPost m src dst v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  have harg2 := harg 2 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1 harg2
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps stop_at [1248] [hsel', hz, harg0, harg1, harg2, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self,
    loadWord_write_of_disjoint, Memory.read_write_of_disjoint, size_readBytes]
  wp_abstract memory M hM
  have hM64 : M.loadWord 64 = 320#256 := by
    subst hM; simp [loadWord_write_of_disjoint, Memory.loadWord_storeWord_of_disjoint,
      Memory.loadWord_storeWord]
  have hM224 : M.loadWord 224 = 40#256 := by
    subst hM; simp [loadWord_write_of_disjoint, Memory.loadWord_storeWord]
  clear hM
  hwp_steps [hsel', hz, harg0, harg1, harg2, hM64, hM224, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  have hs0 := ampl_addr_ne' (by with_reducible assumption : Word.ofAddress src ≠ 0)
  have hd0 := ampl_addr_ne' (by with_reducible assumption : Word.ofAddress dst ≠ 0)
  have hc0 := ampl_addr_ne' (by with_reducible assumption : Word.ofAddress m_msg.caller ≠ 0)
  have hsb0 : (v.gt (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto src))).iszero ≠ 0 := by
    simp only [balSlot, mappingSlot]; with_reducible assumption
  have hsb := Verified.Solady.Spec.le_of_iszero_gt hsb0
  have hab0 : (v.gt ((moveWorld m_ctx.crypto m_world m_msg.currentTarget src dst v).sload
      m_msg.currentTarget (allowSlot m_ctx.crypto src m_msg.caller))).iszero ≠ 0 := by
    simp only [moveWorld, debitWorld, allowSlot, balSlot, mappingSlot2, mappingSlot]
    with_reducible assumption
  have hab := Verified.Solady.Spec.le_of_iszero_gt hab0
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
    ⟨fun h => absurd hv h, fun h => ?_, fun _ _ _ _ _ =>
      ⟨fun h => absurd (Nat.lt_of_lt_of_le h hab) (Nat.lt_irrefl _),
       fun _ => ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩⟩⟩
  · rcases h with h | h | h | h
    · exact absurd h hs0
    · exact absurd h hd0
    · exact absurd h hc0
    · exact absurd (Nat.lt_of_lt_of_le h hsb) (Nat.lt_irrefl _)
  · simp only [outputData]
    apwp_norm []
    rfl
  · simp only [outputMachine]
    logs_simp []
    refine congrArg₂ Array.push ?_ ?_
    · event_log [v]
    · rw [approvalLog]
      refine logEntry_eq_eventLog ?_
      event_data
      try rfl

end Verified.WeirdERC20.YAMV2.Spec
