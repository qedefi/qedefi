import Verified.WeirdERC20.STA.Spec.Views
import Verified.WeirdERC20.BNB.Spec.Write

/-!
# STA under the spec: `approve`

`approve(sp, v)` of BNB: `require(_value > 0)` (an allowance cannot be reset to `0`), then the
allowance row written, `true` returned, no event (BNB declares no `Approval`).
-/

namespace Verified.WeirdERC20.STA.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.STA.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

theorem ne_zero_of_iszero2 {sp : Address} (h : (Word.ofAddress sp).iszero.iszero ≠ 0) :
    sp ≠ 0 := by
  rintro rfl; exact h (by decide)

theorem iszero2_of_ne {sp : Address} (h : sp ≠ 0) : (Word.ofAddress sp).iszero.iszero = 1 := by
  have : Word.ofAddress sp ≠ 0 := by
    intro h0
    apply h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h0
    have hs : sp.toNat < 2 ^ 160 := sp.isLt
    simp only [Word.ofAddress, BitVec.toNat_setWidth] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    simpa using this
  have h' : (Word.ofAddress sp == 0#256) = false := by simpa using this
  simp [Word.iszero, Word.ofBool, h']

/-- `approve(sp, v)`'s code-level end: the zero spender reverts, or the allowance row written,
`Approval(caller, sp, v)` logged, `true` returned. -/
def ApprovePost (m : Machine) (sp : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (sp = 0 → ∃ out, o = .revert out) ∧
  (sp ≠ 0 → m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧
    o = .success (Bytes.ofWord 1) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget
      (mappingSlot2 m.ctx.crypto (Word.ofAddress m.frame.msg.caller) (Word.ofAddress sp) 4#256) v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (QEDefi.ERC4626.approvalLog m.frame.msg.currentTarget m.frame.msg.caller sp v))

set_option maxHeartbeats 0 in
theorem approve_low (m : Machine) (sp : Address) (v : Word) (hf : Fresh STA.runtimeCode m)
    (hd : Args m.frame.msg.data 0x095ea7b3 [Word.ofAddress sp, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ApprovePost m sp v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  have hs0 := ne_zero_of_iszero2 (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
    ⟨fun h => absurd h hs0, fun _ => ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩⟩
  · simp only [outputData]
    apwp_norm []
    rfl
  · simp only [outputMachine]
    logs_simp []
    event_log [v]

set_option maxHeartbeats 0 in
theorem approve_high (m : Machine) (sp : Address) (v : Word) (hf : Fresh STA.runtimeCode m)
    (hd : Args m.frame.msg.data 0x095ea7b3 [Word.ofAddress sp, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ApprovePost m sp v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hs0 : sp = 0
  · subst hs0
    have hc : (Word.ofAddress (0 : Address)).iszero.iszero = 0 := by decide
    pwp_steps [hval, hst, hsel', hz, hl, hc, harg0, harg1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd rfl h⟩
  · have hc := iszero2_of_ne hs0
    pwp_steps [hval, hst, hsel', hz, hl, hc, harg0, harg1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    refine ⟨fun h => absurd h hs0, fun _ => ⟨hval, hst, rfl, rfl, rfl, rfl, ?_⟩⟩
    simp only [outputMachine]
    logs_simp []
    event_log [v]

/-! ## The obligation -/

theorem sta_call_approve (s : VState Address) (c sp : Address) (v : ℕ) :
    M.call s c (.approve sp v) =
      if sp = 0 then .halt .revert else .ok (s.setAllowance c sp v) (.word true) := by
  by_cases h : sp = 0
  · subst h
    simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.call, Variant.step, Variant.approve,
      Variant.approveOk, Variant.sta, Variant.standard, Variant.failKind, Variant.guardOk,
      Variant.failWith]
  · have h' : ¬ sp = 0#160 := h
    simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.call, Variant.step, Variant.approve,
      Variant.approveOk, Variant.sta, Variant.standard, Variant.retData, h']

theorem staRead_sstore_allow {crypto : Crypto} {Act : Finset Address} {w : World} {t o sp : Address}
    (hS : staSound crypto Act) (ho : o ∈ Act) (hs : sp ∈ Act) (x : Word) :
    staRead crypto Act
        (w.sstore t (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 4#256) x) t =
      (staRead crypto Act w t).setAllowance o sp x.toNat := by
  simp only [staRead, VState.setAllowance]
  rw [BNB.Spec.readMap_sstore_map2 hS (by simp) (by simp) ho hs,
    BNB.Spec.readMap2_sstore hS (by simp) ho hs,
    BNB.Spec.readSlot_sstore_map2 (k := 5#256) hS (by simp) (by simp) ho hs,
    BNB.Spec.readSlot_sstore_map2 (k := 6#256) hS (by simp) (by simp) ho hs, World.balance_sstore]

/-- **`approve(sp, v)`**: the zero spender reverts; otherwise the allowance is set, `true`,
`Approval`. -/
theorem call_approve (sp : Address) (v : ℕ) :
    CallSpec STA.runtimeCode staAbs M g₀ (.approve sp v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hsA : sp ∈ Act := haddr sp (by simp [Call.addrs])
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  refine halts_split' (G := Normal g₀ m)
    (fun hG => approve_high m sp (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1)
    (approve_low m sp (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  by_cases hs0 : sp = 0
  · obtain ⟨out, rfl⟩ := hrev hs0
    by_cases hG : Normal g₀ m
    · left; rw [sta_call_approve, ite_pos' hs0]; exact ⟨out, rfl⟩
    · exact .inr ⟨trivial, hG⟩
  left
  obtain ⟨hv, -, ho, hw, ht, hcr, hl⟩ := hok hs0
  rw [sta_call_approve, ite_neg' hs0]
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show staRead _ _ _ _ = _
    rw [hw, staRead_sstore_allow hs.sound hs.caller hsA, pre_eq hs hv, hwv]
  · rw [hw]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr ⟨_, hs.caller, _, hsA, rfl⟩)))
      BNB.Spec.frameKeeps_refl'
  · rw [hl]
    simp [M, QEDefi.ERC20.Spec.STA.staModel, QEDefi.ERC20.Spec.STA.staEvents, Spec.eventLog]

end Verified.WeirdERC20.STA.Spec
