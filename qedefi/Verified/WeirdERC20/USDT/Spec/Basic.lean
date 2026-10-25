import Verified.WeirdERC20.USDT.Spec.PatchedFacts
import Verified.WeirdERC20.USDT.Spec.Abs
import EvmLogic.Tactic.Patched
import EvmLogic.Solidity.Dispatch
import EvmLogic.Program.Call

/-!
# USDT bytecode proofs: shared vocabulary

Every obligation is proved the same way. A frame `m` of the real code (`Start` gives
`Fresh USDT.runtimeCode m`) is followed by its **lift** `lift patchedCode d m` (the patched code
without the forwarding calls, `d = g₀ - gas` more gas, at the top level). The lift runs
symbolically (`lift_intro`, then `usdt_run` to the next halting instruction), and each exit is
closed by `usdt_return`/`usdt_revert`/`usdt_stop`/`usdt_invalid` (`ExitsWith`), with enough gas
by construction. `halts_of_high` turns that into the frame's end at any gas: the lift's
outcome, or (only below `g₀`) a failure (`LowGas.lean`).

This file also has the facts the runs need: solc 0.4's selector extraction, the cost of `EXP`
for the exponents the code uses, the packed fields as the code reads them, and `live_of_start`
(a frame `Start` admits is live: not deprecated, six decimals, owner an actor).
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.WeirdERC20.USDT.Contracts EvmLogic.Program.Nested EvmLogic.GasMono
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math

/-! ## Words the code computes -/

/-- solc 0.4's selector extraction (`CALLDATALOAD 0 / 2²²⁴ & 0xffffffff`). -/
theorem div_selector (data : ByteArray) :
    (4294967295#256 &&& Word.div (Bytes.toWord (readBytes data 0 32))
      26959946667150639794667015087019630673637144422540572481103610249216#256) =
      BitVec.ofNat 256 (Abi.selectorOf data) := by
  have hs := Abi.shr_calldataload_zero data
  have hsel : Abi.selectorOf data < 2 ^ 32 := by
    have := Bytes.toNat_lt (readBytes data 0 4)
    rw [size_readBytes] at this
    unfold Abi.selectorOf; simpa using this
  have hdiv : Word.div (Bytes.toWord (readBytes data 0 32))
      26959946667150639794667015087019630673637144422540572481103610249216#256 =
      Word.shr (BitVec.ofNat 256 224) (Bytes.toWord (readBytes data 0 32)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [Word.div, Word.shr, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight,
      BitVec.toNat_udiv, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow]
  rw [hdiv, hs]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : Abi.selectorOf data < 2 ^ 256),
    show (4294967295 : Nat) % 2 ^ 256 = 2 ^ 32 - 1 by decide, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hsel]

theorem lt_size_four {n : Nat} (h₁ : 4 ≤ n) (h₂ : n < 2 ^ 256) :
    Word.lt (ofNat n) (BitVec.ofNat 256 4) = 0 := by
  rw [Word.lt_eq_zero_iff]; simp only [ofNat, BitVec.toNat_ofNat]; omega

theorem expCost_0 : Gas.expCost 0 = 10 := by decide
theorem expCost_20 : Gas.expCost 20 = 60 := by decide

/-- A byte field at byte 20 as the code reads it (`slot / 0x100²⁰ & 0xff`). -/
theorem byte20_get (k : Word) (v : Word) :
    (⟨k, 20, 1⟩ : Field).get v =
      255#256 &&& v.div 1461501637330902918203684832716283019655932542976#256 := by
  apply BitVec.eq_of_toNat_eq
  simp only [Field.get, Field.mask, Word.div, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_udiv, BitVec.toNat_ofNat]
  rw [show (BitVec.allOnes 256).toNat >>> (256 - 8 * 1) = 255 by decide,
    Nat.shiftRight_eq_div_pow, Nat.and_comm]

theorem deprecatedField_get (v : Word) :
    deprecatedField.get v =
      255#256 &&& v.div 1461501637330902918203684832716283019655932542976#256 :=
  byte20_get _ v

theorem pausedField_get (v : Word) :
    pausedField.get v =
      255#256 &&& v.div 1461501637330902918203684832716283019655932542976#256 :=
  byte20_get _ v

/-! ## The lift of a fresh frame -/

theorem zero_mem_boundaries : 0 ∈ boundaries patchedCode := by
  have h : 0 < patchedCode.size := by decide +kernel
  unfold boundaries
  rw [show patchedCode.size = 11074 + 1 by decide +kernel, boundariesFrom_succ]
  simp only [h, ↓reduceIte]
  exact List.mem_cons_self

/-- A fresh frame of the real code is a `Low` frame of the lockstep. -/
theorem low_of_fresh {m : Machine} (hf : Fresh USDT.runtimeCode m) :
    Low USDT.runtimeCode patchedCode m := by
  obtain ⟨hc, hj, hpc, -, -, -, -⟩ := hf.frame
  obtain ⟨msg, kind, snap, hfr, hmc⟩ := hf
  refine ⟨hc, ?_, hj, ?_⟩
  · rw [hfr]; exact hmc
  · rw [hpc]; exact .inl zero_mem_boundaries

/-- **From the lift's symbolic run to the frame's end at any gas.** If the lift with `g₀ - gas`
more gas reaches an exit with `Post` (which does not distinguish exceptional halts and reads no
field `lift` changes), the frame ends with `Post`, or fails with less than `g₀` gas. -/
theorem halts_of_high {m : Machine} (hf : Fresh USDT.runtimeCode m)
    {Post : Machine → Outcome → Prop} (hH : ∀ mf e e', Post mf (.halt e) → Post mf (.halt e'))
    (hl : ∀ mf o, Post (lift patchedCode (g₀ - m.frame.gasLeft) mf) o → Post mf o)
    (hw : WP (lift patchedCode (g₀ - m.frame.gasLeft) m)
      (fun mh' => mh'.frame.pc ∉ patchPcs ∧ ExitsWith Post mh') (fun _ _ => False)) :
    Halts m (fun mf o => (Fails o ∧ m.frame.gasLeft < g₀) ∨ Post mf o) := by
  refine (halts_of_lift patchOk hH (low_of_fresh hf) hw).mono fun mf o _ h => ?_
  rcases h with ⟨hfail, hd⟩ | h
  · refine .inl ⟨?_, by omega⟩
    cases o with
    | success out => exact absurd rfl (hfail out)
    | revert out => trivial
    | halt e => trivial
  · exact .inr (hl _ _ h)

set_option hygiene false in
/-- Open the lift of a fresh frame (`hf : Fresh USDT.runtimeCode m`) for symbolic execution: a
literal machine running `patchedCode`, with its jump table as a hypothesis. -/
macro "lift_intro" : tactic => `(tactic| (
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  clear hf
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  rw [← patchOk.jumpDests] at hj
  wp_hide_jump_tables
  subst hs hpc hc hmem
  simp only [lift, bump, withCode]))

/-- Memory normalization at an exit (as the stepper's). -/
macro "usdt_mem_norm" : tactic => `(tactic| evm_norm [Memory.loadWord_expand, Memory.read_expand,
  Memory.loadWord_storeWord, Memory.read_storeWord, Memory.loadWord_storeWord_of_disjoint,
  Memory.read_storeWord_of_disjoint, true_or, or_true])

/-- Close a checkpoint at `RETURN`, leaving the postcondition. -/
macro "usdt_return" : tactic => `(tactic| (
  refine WP.ret ⟨by dsimp only; decide, _, _, exitOf_return (by code_fact) rfl (by evm_gas), ?_⟩
  usdt_mem_norm))

/-- Close a checkpoint at `REVERT`, leaving the postcondition. -/
macro "usdt_revert" : tactic => `(tactic| (
  refine WP.ret ⟨by dsimp only; decide, _, _, exitOf_revert (by code_fact) rfl (by evm_gas), ?_⟩))

/-- Close a checkpoint at `STOP`, leaving the postcondition. -/
macro "usdt_stop" : tactic => `(tactic| (
  refine WP.ret ⟨by dsimp only; decide, _, _, exitOf_stop (by code_fact), ?_⟩))

/-- Close a checkpoint at `INVALID`, leaving the postcondition. -/
macro "usdt_invalid" : tactic => `(tactic| (
  refine WP.ret ⟨by dsimp only; decide, _, _, exitOf_invalid (by code_fact), ?_⟩))

/-! ## Frames `Start` admits -/

/-- The model of the token: `usdtModel` on addresses. -/
noncomputable abbrev M : TokenModel (VState Address) Address (Variant.Op Address) :=
  QEDefi.ERC20.Spec.USDT.usdtModel

/-- A frame `Start` admits is live (in its snapshot), and its state is the abstraction's. -/
theorem live_of_start {Act : Finset Address} {m : Machine}
    (hs : Start USDT.runtimeCode usdtAbs M Act m) :
    Live Act m.frame.snapshot.1 m.frame.msg.currentTarget ∧
      pre usdtAbs Act m = readState m.ctx.crypto Act m.frame.snapshot.1 m.frame.msg.currentTarget := by
  have hw := hs.wf
  simp only [M, QEDefi.ERC20.Spec.USDT.usdtModel_wf, pre, usdtAbs, read] at hw ⊢
  by_cases hl : Live Act m.frame.snapshot.1 m.frame.msg.currentTarget
  · simp only [hl, ↓reduceIte, and_self]
  · simp only [hl, ↓reduceIte, QEDefi.ERC20.Spec.YAMV2.SubSupply] at hw
    exact absurd hw.2 (by simp [U256, MAX])

/-- With no value, the frame's world is its snapshot. -/
theorem world_of_start {Act : Finset Address} {m : Machine}
    (hs : Start USDT.runtimeCode usdtAbs M Act m) (hval : m.frame.msg.value = 0) :
    m.world = m.frame.snapshot.1 := by
  rw [hs.launched, transferValue_zero _ _ hval]

end Verified.WeirdERC20.USDT.Spec
