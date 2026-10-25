import Verified.AaveV3.ATokenProxy.Basic

/-!
# Aave V3 aToken proxy: the delegation block

`delegate_halts`: from the proxy's `CALLDATACOPY` at pc 1129 (stack `0, 0, calldatasize,
implementation word, …`, memory after `mstore(0x40, 0x80)`), the frame copies the calldata,
`DELEGATECALL`s the implementation (`WP.delegatecall`: the implementation's code runs in a fresh
frame at the proxy's address, with the proxy's caller, value and calldata), copies the output
back and returns or reverts with it. For every way the implementation's frame can end
(`resumeAfter_success`/`_revert`/`_halt`) the proxy's end is `Forwarded`.

Memory and gas are abstracted (`wp_abstract`) after each copy, so the calldata and output sizes
stay symbolic: the copies are `step_calldatacopy_any`/`step_returndatacopy_any` (empty or not),
their expansion costs are bounded by `extendMemory_cost_le`, and the call's input window and the
final `RETURN`/`REVERT` cost nothing (`extendMemory_cost_eq_zero`). The implementation keeps all
but 1/64 of the gas, so the copy-back is affordable if 1/64 covers an output of `B` bytes.
-/

namespace Verified.AaveV3.ATokenProxy
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.AaveV3.Contracts

set_option hygiene false in
/-- `DelegatedFrom` for the child of the proxy's `DELEGATECALL` (in `delegate_halts`). -/
local macro "delegated_from" : tactic => `(tactic| (
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp only [Frame.init, childMsg, callMemory, hsz, BitVec.toNat_zero, readBytes_bytes,
      Memory.read_expand, hM1r]
  · simp only [Frame.init, childMsg, Bool.false_or]))

set_option hygiene false in
/-- After the implementation's frame ended with output `out` (in `delegate_halts`): up to the
final `RETURN`/`REVERT`, with the output copied to memory `M2` (`hM2r`, `hM2s`, `hoc`). -/
local macro "copy_back" : tactic => `(tactic| (
  dsimp only [delegateCaller, callerFrame, callMemory]
  have hos : (ofNat out.size).toNat = out.size := by
    simp only [ofNat, BitVec.toNat_ofNat]; omega
  wp_abstract memory M1' hM1'
  clear hM1'
  wp_abstract gas g2 hg2
  simp only [callCost, callGas, callExt, hL, hsz, BitVec.toNat_zero, hext, hmcg,
    Gas.maxMessageCallGas] at hg2
  simp only [Nat.reduceAdd]
  pwp_steps
  have hrc := extendMemory_cost_le M1'.size out.size
  have hmB := memoryCost_mono hB'
  apply WP.of_step
  case h =>
    refine step_returndatacopy_any (by pcode_fact) rfl
      (by simp only [hos, BitVec.toNat_zero]; omega) ?_
    simp only [memoryCost, hos, BitVec.toNat_zero]
    omega
  case hs => same_frame
  dsimp only
  wp_abstract memory M2 hM2
  simp only [hos, BitVec.toNat_zero, Nat.zero_add, ByteArray.extract_zero_size] at hM2
  have hM2r : M2.read 0 out.size = out := by rw [← hM2]; exact read_copyMemory _ _ _
  have hM2s : out.size ≤ M2.size := by rw [← hM2]; exact (size_copyMemory _ _).2
  clear hM2
  wp_abstract gas g3 hg3
  simp only [memoryCost, hos, BitVec.toNat_zero] at hg3
  pwp_steps
  have hoc : (Gas.extendMemory M2.size [(0, out.size)]).cost = 0 :=
    extendMemory_cost_eq_zero hM2s))

set_option hygiene false in
/-- The proxy's gas bound in `Forwarded` (in `delegate_halts`). -/
local macro "proxy_gas" : tactic => `(tactic| (
  simp only [Frame.init, childMsg, callGas, callExt, hL, hsz, BitVec.toNat_zero, hext, hmcg,
    Gas.maxMessageCallGas, Gas.copyCost, Gas.copyPerWord, Gas.words, Gas.memoryCost,
    Gas.memoryPerWord] at hg hg1' hmB hrc hBm ⊢
  omega))

set_option maxHeartbeats 0 in
/-- **The delegation block** (`_delegate`, from its `CALLDATACOPY` at pc 1129): the proxy frame
ends as `Forwarded` after the implementation's frame, for every end `Hc` allows. Hypotheses: the
implementation's frame (code of `Word.toAddress w`) `Halts` with `Hc` whenever it starts with at
least `G` gas, with at most `B` bytes of output; enough gas for `G`, the calldata copy and
64 times the output copy; the call can be made. -/
theorem delegate_halts (M : Machine) {w : Word} {rest : List Word} {B G : Nat}
    {Hc : Machine → Machine → Outcome → Prop}
    (hcode : M.frame.code = ATokenProxy.runtimeCode)
    (hjd : M.frame.jumpDests = validJumpDests ATokenProxy.runtimeCode)
    (hpc : M.frame.pc = 1129)
    (hstk : M.frame.stack = 0#256 :: 0#256 :: ofNat M.frame.msg.data.size :: w :: rest)
    (hlen : rest.length ≤ 1000) (hmem : M.frame.memory = mem0)
    (hsize : M.frame.msg.data.size < 2 ^ 64)
    (hdel : M.ctx.fork < .prague ∨ delegatedAddress? (M.world.code (Word.toAddress w)) = none)
    (hpre : M.precompiles.isPrecompile (Word.toAddress w) = false)
    (hdepth : M.frame.msg.depth < 1024)
    (hg : 2 * G + 64 * (Gas.copyCost B + Gas.memoryCost B) + Gas.copyCost M.frame.msg.data.size +
      Gas.memoryCost M.frame.msg.data.size + 8000 ≤ M.frame.gasLeft)
    (hgu : M.frame.gasLeft < 2 ^ 256)
    (hB : ∀ mc mcf oc, Hc mc mcf oc → (outputOf oc).size ≤ B)
    (hchild : ∀ mc, Fresh (M.world.code (Word.toAddress w)) mc → DelegatedFrom M mc →
      G ≤ mc.frame.gasLeft → Halts mc (Hc mc)) :
    Halts M (fun mf o => ∃ mc mcf oc, DelegatedFrom M mc ∧ Hc mc mcf oc ∧
      Forwarded M (3000 + Gas.copyCost M.frame.msg.data.size +
        Gas.memoryCost M.frame.msg.data.size + Gas.copyCost B + Gas.memoryCost B)
        mc mcf oc mf o) := by
  apply WP.halts_of_false
  obtain ⟨M_ctx, M_pre, M_world, M_transient, M_originalWorld, M_created,
    ⟨M_msg, M_code, M_jumpDests, M_pc, M_stack, M_memory, M_gasLeft, M_returnData, M_sub,
      M_snapshot, M_kind⟩, M_parents⟩ := M
  dsimp only at *
  wp_hide_jump_tables
  subst hcode hpc hstk hmem
  have hsz : (ofNat M_msg.data.size).toNat = M_msg.data.size := by
    simp only [ofNat, BitVec.toNat_ofNat]; omega
  have hmc := extendMemory_cost_le mem0.size M_msg.data.size
  simp only [Gas.copyCost, Gas.copyPerWord, Gas.words] at hg
  -- `calldatacopy(0, 0, calldatasize())`
  apply WP.of_step
  case h =>
    refine step_calldatacopy_any (by pcode_fact) rfl ?_
    simp only [memoryCost, hsz, BitVec.toNat_zero]
    omega
  case hs => same_frame
  dsimp only
  wp_abstract gas g1 hg1
  have hg1' : M_gasLeft ≤ g1 + 3 + 3 * ((M_msg.data.size + 31) / 32) +
      Gas.memoryCost M_msg.data.size := by
    rw [← hg1]; simp only [memoryCost, hsz, BitVec.toNat_zero] at hmc ⊢; omega
  have hg1'' : g1 ≤ M_gasLeft := by rw [← hg1]; omega
  clear hg1
  wp_abstract memory M1 hM1
  rw [hsz, BitVec.toNat_zero, readBytes_zero_size] at hM1
  have hM1r : M1.read 0 M_msg.data.size = M_msg.data := by
    rw [← hM1]
    exact read_copyMemory mem0 0 M_msg.data
  have hM1s := size_copyMemory mem0 M_msg.data
  rw [hM1] at hM1s
  clear hM1
  pwp_norm
  pwp_steps
  -- `delegatecall(gas(), implementation, 0, calldatasize(), 0, 0)`
  have hacc := accessCost_le (M_sub.accessedAddresses.contains (Word.toAddress w))
  have hL : (ofNat (g1 - 16)).toNat = g1 - 16 := by simp only [ofNat, BitVec.toNat_ofNat]; omega
  have hext : (Gas.extendMemory M1.size [(0, M_msg.data.size), (0, 0)]).cost = 0 :=
    extendMemory_cost_eq_zero₂ hM1s.2
  have hmcg := messageCallGas_zero (g := g1 - 16) (L := g1 - 16) (mc := 0)
    (extra := Gas.accessCost (M_sub.accessedAddresses.contains (Word.toAddress w)) + 0 + 0 + 0)
    (by omega)
  refine WP.delegatecall (by pcode_fact) rfl hdel ?_ (by simp only [Gas.stackDepthLimit]; omega)
    hpre (hchild _ (fresh_delegateChild _ _ _ _ _ _ _ _) ?_ ?_) ?_
  · simp only [callCost, callGas, callExt, hL, hsz, BitVec.toNat_zero, hext, hmcg,
      Gas.maxMessageCallGas]
    omega
  · delegated_from
  · simp only [Frame.init, childMsg, callGas, callExt, hL, hsz, BitVec.toNat_zero, hext, hmcg,
      Gas.maxMessageCallGas]
    omega
  -- back in the proxy: `returndatacopy`, then `return`/`revert`
  · intro mf o hc hsame
    have hk : mf.frame.kind = .call 0 0 := hsame.kind
    have hs1 : mf.ctx = M_ctx := hsame.ctx
    have hs2 : mf.precompiles = M_pre := hsame.precompiles
    have hs3 : mf.originalWorld = M_originalWorld := hsame.originalWorld
    have hsnap : mf.frame.snapshot = (M_world, M_transient) := hsame.snapshot
    have hB' := hB _ _ _ hc
    have hBm : 3 * ((B + 31) / 32) ≤ Gas.memoryCost B := by
      unfold Gas.memoryCost Gas.words Gas.memoryPerWord; dsimp only; omega
    cases o with
    | success out =>
      simp only [outputOf] at hB'
      rw [resumeAfter_success hk]
      simp only [hs1, hs2, hs3]
      copy_back
      apply WP.halt_of_step
      case h =>
        exact step_return (by pcode_fact) rfl
          (by simp only [outputCost, hos, BitVec.toNat_zero, hoc]; exact Nat.zero_le _)
      case hs => same_frame
      refine ⟨_, _, _, by delegated_from, hc, ?_⟩
      simp only [Forwarded, outputData, outputMachine, outputCost, hos, BitVec.toNat_zero, hoc,
        readBytes_bytes, Memory.read_expand, hM2r]
      refine ⟨trivial, trivial, trivial, trivial, rfl, ?_⟩
      proxy_gas
    | revert out =>
      simp only [outputOf] at hB'
      rw [resumeAfter_revert hk]
      simp only [hs1, hs2, hs3, hsnap]
      copy_back
      apply WP.halt_of_step
      case h =>
        exact step_revert (by pcode_fact) rfl
          (by simp only [outputCost, hos, BitVec.toNat_zero, hoc]; exact Nat.zero_le _)
      case hs => same_frame
      refine ⟨_, _, _, by delegated_from, hc, ?_⟩
      simp only [Forwarded, outputData, outputMachine, outputCost, hos, BitVec.toNat_zero, hoc,
        readBytes_bytes, Memory.read_expand, hM2r]
      refine ⟨trivial, trivial, trivial, trivial, failSub_logs _ _ _ _, ?_⟩
      proxy_gas
    | halt e =>
      simp only [outputOf] at hB'
      obtain ⟨out, hout⟩ : ∃ out : ByteArray, out = .empty := ⟨_, rfl⟩
      rw [← hout] at hB'
      rw [resumeAfter_halt hk]
      simp only [hs1, hs2, hs3, hsnap]
      rw [← hout]
      copy_back
      apply WP.halt_of_step
      case h =>
        exact step_revert (by pcode_fact) rfl
          (by simp only [outputCost, hos, BitVec.toNat_zero, hoc]; exact Nat.zero_le _)
      case hs => same_frame
      refine ⟨_, _, _, by delegated_from, hc, ?_⟩
      simp only [Forwarded, hout.symm, outputData, outputMachine, outputCost, hos,
        BitVec.toNat_zero, hoc, readBytes_bytes, Memory.read_expand, hM2r]
      refine ⟨trivial, trivial, trivial, trivial, failSub_logs _ _ _ _, ?_⟩
      proxy_gas

end Verified.AaveV3.ATokenProxy
