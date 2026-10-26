import Verified.Solady.Spec.Views
import Verified.Solady.Spec.Write

/-!
# Solady `ERC20` under the spec: `approve`
-/

namespace Verified.Solady.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open EvmLean.Interpreter EvmLogic.Tactic Verified.Solady.Contracts Verified.Solady.Spec.AnyGas
open QEDefi.ERC4626

/-- `approve(sp, v)`'s code-level end: the Permit2 revert, or success with the allowance row
written and the `Approval` log. -/
def ApprovePost (m : Machine) (sp : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (sp = PERMIT2 ∧ v ≠ ~~~0 → ∃ out, o = .revert out) ∧
  (¬ (sp = PERMIT2 ∧ v ≠ ~~~0) → m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧
    o = .success (Bytes.ofWord 1) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp) v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (approvalLog m.frame.msg.currentTarget m.frame.msg.caller sp v))

set_option maxHeartbeats 0 in
theorem approve_low (m : Machine) (sp : Address) (v : Word)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0x095ea7b3 [Word.ofAddress sp, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ApprovePost m sp v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0 harg1
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
    Nat.mul_one] at harg0 harg1
  hwp_steps [hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
    ofAddress_and_addressMask, Solidity.eq_self]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  rw [read_allowRow _ m_msg.caller sp allowSeed]
  rotate_left
  · decide
  · simp only [Memory.read_storeWord]
  · rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
      read_storeWord_slice' _ 12 20 12 32 _ (by omega) rfl]
    rfl
  · rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
      Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
      read_storeWord_slice' _ 32 12 20 44 _ (by omega) rfl]
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨?_, fun _ => ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩⟩
  · intro h
    exact absurd ((approve_test sp v).mpr h) (by with_reducible assumption)
  · simp only [outputData]
    apwp_norm []
    rfl
  · simp only [outputMachine]
    logs_simp []
    rw [shr_loadWord_addr]
    event_log [v]

set_option maxHeartbeats 0 in
theorem approve_high (m : Machine) (sp : Address) (v : Word)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0x095ea7b3 [Word.ofAddress sp, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ApprovePost m sp v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0 harg1
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
    Nat.mul_one] at harg0 harg1
  by_cases hp : sp = PERMIT2 ∧ v ≠ ~~~0
  · have hp' := (approve_test sp v).mpr hp
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1, hok,
      ofAddress_and_addressMask, Solidity.eq_self, hp']
    exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd hp h⟩
  · have hp' : (~~~v).iszero ||| 180847076211518657644945212059388835#256 ^^^ Word.ofAddress sp
        ≠ 0 := fun h => hp ((approve_test sp v).mp h)
    pwp_steps [hval, hst, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
      hok, ofAddress_and_addressMask, Solidity.eq_self, hp']
    rw [read_allowRow _ m_msg.caller sp allowSeed]
    rotate_left
    · decide
    · simp only [Memory.read_storeWord]
    · rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
        read_storeWord_slice' _ 12 20 12 32 _ (by omega) rfl]
      rfl
    · rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
        Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
        read_storeWord_slice' _ 32 12 20 44 _ (by omega) rfl]
    refine ⟨fun h => absurd h hp, fun _ => ⟨hval, hst, ?_, rfl, rfl, rfl, ?_⟩⟩
    · rfl
    · simp only [outputMachine]
      logs_simp []
      rw [shr_loadWord_addr]
      event_log [v]

/-! ## The obligation -/

theorem word_ne_not_zero {v : ℕ} (hv : v < 2 ^ 256) : word v ≠ ~~~0 ↔ v ≠ QEDefi.Math.MAX := by
  have e : (~~~(0 : Word)).toNat = 2 ^ 256 - 1 := by decide
  constructor
  · intro h hm
    apply h; apply BitVec.eq_of_toNat_eq
    rw [e, word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, hm]; rfl
  · intro h hw
    apply h
    have := congrArg BitVec.toNat hw
    rw [e, word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] at this
    rw [this]; rfl

theorem solady_call_approve (s : VState Address) (c sp : Address) (v : ℕ) :
    M.call s c (.approve sp v) =
      if sp = PERMIT2 ∧ v ≠ QEDefi.Math.MAX then .halt .revert
      else .ok (s.setAllowance c sp v) (.word true) := by
  by_cases h : sp = PERMIT2 ∧ v ≠ QEDefi.Math.MAX
  · obtain ⟨rfl, hv⟩ := h
    simp [M, Solady.soladyModel, Variant.call, Variant.step, Variant.approve,
      Variant.approveOk, Variant.solady, Variant.standard, Variant.failKind, Variant.guardOk,
      Variant.failWith, hv]
  · rw [ite_neg' h]
    have h' : ¬ PERMIT2 = sp ∨ v = QEDefi.Math.MAX := by
      by_cases e : PERMIT2 = sp
      · exact .inr (by by_contra hv; exact h ⟨e.symm, hv⟩)
      · exact .inl e
    simp only [M, Solady.soladyModel, Variant.model_call, Variant.call, Variant.step,
      Variant.approve, Variant.approveOk, Variant.retData]
    simp [Variant.solady, Variant.standard, h']

/-- **`approve(sp, v)`**: the Permit2 revert, or the allowance set and `Approval` logged. -/
theorem call_approve (sp : Address) (v : ℕ) :
    CallSpec SoladyToken.runtimeCode soladyAbs M g₀ (.approve sp v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hsA : sp ∈ Act := haddr sp (by simp [Call.addrs])
  refine halts_split (G := Normal g₀ m)
    (fun hG => approve_high m sp (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1)
    (approve_low m sp (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  rw [solady_call_approve]
  by_cases hp : sp = PERMIT2 ∧ v ≠ QEDefi.Math.MAX
  · rw [ite_pos' hp]
    exact hrev ⟨hp.1, (word_ne_not_zero hv256).mpr hp.2⟩
  · rw [ite_neg' hp]
    have hp' : ¬ (sp = PERMIT2 ∧ word v ≠ ~~~0) := fun h =>
      hp ⟨h.1, (word_ne_not_zero hv256).mp h.2⟩
    obtain ⟨hv, -, ho, hw, ht, hcr, hl⟩ := hok hp'
    refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
    · show read _ _ _ _ = _
      rw [hw, read_sstore_allow hs.sound hs.caller hsA, pre_eq hs hv, word,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
    · rw [hw]; exact FrameKeeps.sstore (allow_mem _ _ hs.caller hsA) frameKeeps_refl
    · rw [hl]
      simp [M, Solady.soladyModel, Solady.soladyEvents, Spec.eventLog]

end Verified.Solady.Spec
