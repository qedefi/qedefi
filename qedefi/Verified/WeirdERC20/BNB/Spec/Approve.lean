import Verified.WeirdERC20.BNB.Spec.Views
import Verified.WeirdERC20.BNB.Spec.Write

/-!
# BNB under the spec: `approve`

`approve(sp, v)` of BNB: `require(_value > 0)` (an allowance cannot be reset to `0`), then the
allowance row written, `true` returned, no event (BNB declares no `Approval`).
-/

namespace Verified.WeirdERC20.BNB.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.BNB.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas

theorem ne_zero_of_gt {v : Word} (h : (Word.gt v 0#256).iszero.iszero ≠ 0) : v ≠ 0 := by
  rintro rfl; exact h (by decide)

theorem gt_zero_iszero2 {v : Word} (h : v ≠ 0) : (Word.gt v 0#256).iszero.iszero = 1 := by
  have : BitVec.ult 0#256 v = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
    have : v.toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq h0)
    omega
  simp [Word.gt, Word.ofBool, Word.iszero, this]

/-- `approve(sp, v)`'s code-level end. -/
def ApprovePost (m : Machine) (sp : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (v = 0 → ∃ out, o = .revert out) ∧
  (v ≠ 0 → m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧
    o = .success (Bytes.ofWord 1) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget
      (mappingSlot2 m.ctx.crypto (Word.ofAddress m.frame.msg.caller) (Word.ofAddress sp) 7#256) v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs)

set_option maxHeartbeats 0 in
theorem approve_low (m : Machine) (sp : Address) (v : Word) (hf : Fresh BNB.runtimeCode m)
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
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  have hv0 := ne_zero_of_gt (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
    ⟨fun h => absurd h hv0, fun _ => ⟨hv, ‹_›, ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [outputData]
  apwp_norm []
  rfl

set_option maxHeartbeats 0 in
theorem approve_high (m : Machine) (sp : Address) (v : Word) (hf : Fresh BNB.runtimeCode m)
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
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hv0 : v = 0
  · subst hv0
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd rfl h⟩
  · have hc := gt_zero_iszero2 hv0
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, hc, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun h => absurd h hv0, fun _ => ⟨hval, hst, rfl, rfl, rfl, rfl, rfl⟩⟩

/-! ## The obligation -/

theorem bnb_call_approve (s : VState Address) (c sp : Address) (v : ℕ) :
    M.call s c (.approve sp v) =
      if v = 0 then .halt .revert else .ok (s.setAllowance c sp v) (.word true) := by
  by_cases h : v = 0
  · subst h
    simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.call, Variant.step, Variant.approve,
      Variant.approveOk, Variant.bnb, Variant.standard, Variant.failKind, Variant.guardOk, BNB.bnbGuard,
      Variant.failWith]
  · simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.call, Variant.step, Variant.approve,
      Variant.approveOk, Variant.bnb, Variant.standard, Variant.retData, h, BNB.bnbGuard]

theorem bnbRead_sstore_allow {crypto : Crypto} {Act : Finset Address} {w : World} {t o sp : Address}
    (hS : bnbSound crypto Act) (ho : o ∈ Act) (hs : sp ∈ Act) (x : Word) :
    bnbRead crypto Act
        (w.sstore t (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 7#256) x) t =
      (bnbRead crypto Act w t).setAllowance o sp x.toNat := by
  simp only [bnbRead, VState.setAllowance]
  rw [readMap_sstore_map2 hS (by simp) (by simp) ho hs, readMap_sstore_map2 hS (by simp) (by simp) ho hs,
    readMap2_sstore hS (by simp) ho hs, readSlot_sstore_map2 hS (by simp) (by simp) ho hs,
    sload_sstore_map2 hS (by simp) (by simp) ho hs, World.balance_sstore]

/-- **`approve(sp, v)`**: zero reverts; otherwise the allowance is set, `true`, no event. -/
theorem call_approve (sp : Address) (v : ℕ) :
    CallSpec BNB.runtimeCode bnbAbs M g₀ (.approve sp v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hsA : sp ∈ Act := haddr sp (by simp [Call.addrs])
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  refine halts_split' (G := Normal g₀ m)
    (fun hG => approve_high m sp (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1)
    (approve_low m sp (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  by_cases hv0 : v = 0
  · obtain ⟨out, rfl⟩ := hrev (by rw [hv0]; rfl)
    by_cases hG : Normal g₀ m
    · left; rw [bnb_call_approve, ite_pos' hv0]; exact ⟨out, rfl⟩
    · exact .inr ⟨trivial, hG⟩
  left
  have hw0 : word v ≠ 0 := fun h => hv0 (by rw [← hwv, h]; rfl)
  obtain ⟨hv, -, ho, hw, ht, hcr, hl⟩ := hok hw0
  rw [bnb_call_approve, ite_neg' hv0]
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show bnbRead _ _ _ _ = _
    rw [hw, bnbRead_sstore_allow hs.sound hs.caller hsA, pre_eq hs hv, hwv]
  · rw [hw]
    exact FrameKeeps.sstore' (.inr (.inr (.inr (.inr ⟨_, hs.caller, _, hsA, rfl⟩))))
      frameKeeps_refl'
  · rw [hl]
    simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, QEDefi.ERC20.Spec.BNB.bnbEvents]

end Verified.WeirdERC20.BNB.Spec
