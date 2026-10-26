import Verified.WeirdERC20.ZRX.Spec.ViewSpec

/-!
# ZRX under the spec: `approve`

`approve(sp, v)` of ZRX (solc 0.4.11): no check at all; the allowance row written,
`Approval(caller, sp, v)` logged, `true` returned. A frame with value ends at the non-payable
check's `INVALID`.
-/

namespace Verified.WeirdERC20.ZRX.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.ZRX.Contracts
open Verified.Solady.Spec (LowHalts halts_split eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-- The allowance row `allowed[o][sp]` (slot 1). -/
abbrev allowSlot (crypto : Crypto) (o sp : Address) : Word :=
  mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 1#256

/-- `approve(sp, v)`'s code-level end: the allowance row written, `Approval` logged, `true`. -/
def ApprovePost (m : Machine) (sp : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp) v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (approvalLog m.frame.msg.currentTarget m.frame.msg.caller sp v)

set_option maxHeartbeats 0 in
theorem approve_low (m : Machine) (sp : Address) (v : Word) (hf : Fresh ZRX.runtimeCode m)
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
  zrx_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [outputData]
    apwp_norm []
    rfl
  · simp only [outputMachine]
    logs_simp []
    event_log [v]

set_option maxHeartbeats 0 in
theorem approve_high (m : Machine) (sp : Address) (v : Word) (hf : Fresh ZRX.runtimeCode m)
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
  zrx_fresh_intro
  pwp_steps [hval, hst, hsel', hz, harg0, harg1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64]
  refine ⟨hval, hst, rfl, rfl, rfl, rfl, ?_⟩
  simp only [outputMachine]
  logs_simp []
  event_log [v]

/-! ## The obligation -/

theorem zrx_call_approve (s : VState Address) (c sp : Address) (v : ℕ) :
    M.call s c (.approve sp v) = .ok (s.setAllowance c sp v) (.word true) := by
  simp [M, QEDefi.ERC20.Spec.ZRX.model, Variant.model, Variant.call, Variant.step,
    Variant.approve, Variant.approveOk, QEDefi.ERC20.Spec.ZRX.variant, Variant.standard,
    Variant.retData]

theorem zrx_events_approve (s : VState Address) (c sp : Address) (v : ℕ) :
    M.events s c (.approve sp v) = [.approval c sp v] := by
  simp [M, QEDefi.ERC20.Spec.ZRX.model, Variant.model, QEDefi.ERC20.Spec.ZRX.events,
    Variant.step, Variant.approve, Variant.approveOk, QEDefi.ERC20.Spec.ZRX.variant,
    Variant.standard]

/-- The allowance row of two actors written: that entry of the model's allowances. -/
theorem read_sstore_allow {crypto : Crypto} {Act : Finset Address} {w : World} {t o sp : Address}
    (hS : abs.Sound crypto Act) (ho : o ∈ Act) (hs : sp ∈ Act) (x : Word) :
    read crypto Act (w.sstore t (allowSlot crypto o sp) x) t =
      (read crypto Act w t).setAllowance o sp x.toNat := by
  simp only [read, VState.ofToken, VState.setAllowance, allowSlot]
  rw [show (1#256 : Word) = allowedSlot from rfl,
    BNB.Spec.readMap_sstore_map2 hS (by simp) (by simp) ho hs,
    BNB.Spec.readMap2_sstore hS (by simp) ho hs,
    BNB.Spec.readSlot_sstore_map2 (k := supplySlot) hS (by simp [supplySlot]) (by simp) ho hs]

/-- **`approve(sp, v)`**: the allowance is set, `true`, `Approval`. -/
theorem call_approve (sp : Address) (v : ℕ) : CallSpec ZRX.runtimeCode abs M g₀ (.approve sp v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hsA : sp ∈ Act := haddr sp (by simp [Call.addrs])
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  refine halts_split (G := Normal g₀ m)
    (fun hG => approve_high m sp (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1)
    (approve_low m sp (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hv, -, ho, hw, ht, hcr, hl⟩
  rw [zrx_call_approve, zrx_events_approve]
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show read _ _ _ _ = _
    rw [hw, read_sstore_allow hs.sound hs.caller hsA, pre_eq hs hv, hwv]
  · rw [hw]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr ⟨_, hs.caller, _, hsA, rfl⟩))
      BNB.Spec.frameKeeps_refl'
  · rw [hl]
    simp [Spec.eventLog]

end Verified.WeirdERC20.ZRX.Spec
