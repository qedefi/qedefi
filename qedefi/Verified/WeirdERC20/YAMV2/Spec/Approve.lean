import Verified.WeirdERC20.YAMV2.Spec.Common

/-!
# YAMv2 under the spec: `approve`

`approve(sp, v)` of YAMv2 (OpenZeppelin-3 `_approve`): a zero owner (the caller) or spender
reverts with a reason string; otherwise the allowance row is written, `Approval(caller, sp, v)`
logged and `true` returned.
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.YAMV2.Contracts
open Verified.Solady.Spec (LowHalts halts_split halts_split' eq_zero_of_iszero_ne)
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626
open Verified.WeirdERC20.AMPL.Spec (iszero_lt_size ampl_addr_ne')

/-- `approve(sp, v)`'s code-level end. -/
def ApprovePost (m : Machine) (sp : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.value ≠ 0 → ∃ out, o = .revert out) ∧
  (m.frame.msg.caller = 0 ∨ sp = 0 → ∃ out, o = .revert out) ∧
  (m.frame.msg.caller ≠ 0 → sp ≠ 0 →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp) v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (approvalLog m.frame.msg.currentTarget m.frame.msg.caller sp v))

set_option maxHeartbeats 0 in
theorem approve_low (m : Machine) (sp : Address) (v : Word) (hf : Fresh YAMV2.runtimeCode m)
    (hd : Args m.frame.msg.data 0x095ea7b3 [Word.ofAddress sp, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ApprovePost m sp v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  have hc0 : Word.ofAddress m_msg.caller ≠ 0 := by with_reducible assumption
  have hs0 : Word.ofAddress sp ≠ 0 := by with_reducible assumption
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun h => absurd hv h, fun h => ?_,
    fun _ _ => ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩⟩
  · rcases h with h | h
    · exact absurd h (ampl_addr_ne' hc0)
    · exact absurd h (ampl_addr_ne' hs0)
  · simp only [outputData]
    apwp_norm []
    rfl
  · simp only [outputMachine]
    logs_simp []
    event_log [v]

set_option maxHeartbeats 0 in
theorem approve_high (m : Machine) (sp : Address) (v : Word) (hf : Fresh YAMV2.runtimeCode m)
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
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hc0 : m_msg.caller = 0
  · have hcw0 : Word.ofAddress m_msg.caller = 0 := by rw [hc0]; rfl
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hcw0, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self,
      loadWord_write_of_disjoint, Memory.size_write, size_readBytes]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun h => absurd hc0 h⟩
  have hcw := ofAddress_ne_zero hc0
  by_cases hs0 : sp = 0
  · subst hs0
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hcw, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self,
      loadWord_write_of_disjoint, Memory.size_write, size_readBytes]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ h => absurd rfl h⟩
  have hsw := ofAddress_ne_zero hs0
  pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hcw, hsw, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self,
      loadWord_write_of_disjoint, Memory.size_write, size_readBytes]
  refine ⟨fun h => absurd hval h, fun h => ?_, fun _ _ => ⟨hval, hst, rfl, rfl, rfl, rfl, ?_⟩⟩
  · rcases h with h | h
    · exact absurd h hc0
    · exact absurd h hs0
  simp only [outputMachine]
  logs_simp []
  event_log [v]

/-! ## The obligation -/

theorem yam_call_approve (s : VState Address) (c sp : Address) (v : ℕ) :
    M.call s c (.approve sp v) =
      if c = 0 ∨ sp = 0 then .halt .revert else .ok (s.setAllowance c sp v) (.word true) := by
  by_cases h : c = 0 ∨ sp = 0
  · rcases h with h | h <;>
    simp [h, M, QEDefi.ERC20.Spec.YAMV2.model, Variant.call, Variant.step, Variant.approve,
      Variant.approveOk, QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard, Variant.failKind,
      Variant.guardOk, Variant.failWith]
  · simp only [not_or] at h
    have h1 : ¬ c = 0#160 := h.1
    have h2 : ¬ sp = 0#160 := h.2
    simp [h1, h2, M, QEDefi.ERC20.Spec.YAMV2.model, Variant.call, Variant.step,
      Variant.approve, Variant.approveOk, QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard,
      Variant.retData]

theorem read_sstore_allow {crypto : Crypto} {Act : Finset Address} {w : World}
    {t o sp : Address} (hS : abs.Sound crypto Act) (ho : o ∈ Act) (hs : sp ∈ Act) (x : Word) :
    read crypto Act (w.sstore t (allowSlot crypto o sp) x) t =
      (read crypto Act w t).setAllowance o sp x.toNat := by
  simp only [read, VState.setAllowance, VState.ofToken, allowSlot,
    show balancesSlot = 1#256 from rfl, show supplySlot = 3#256 from rfl,
    show allowancesSlot = 2#256 from rfl, show minterSlot = 0#256 from rfl]
  rw [BNB.Spec.readMap_sstore_map2 (base := 1#256) hS (by decide) (by decide) ho hs,
    BNB.Spec.readMap2_sstore hS (by decide) ho hs,
    BNB.Spec.readSlot_sstore_map2 (k := 3#256) hS (by decide) (by decide) ho hs,
    BNB.Spec.sload_sstore_map2 (k := 0#256) hS (by decide) (by decide) ho hs]

/-- **`approve(sp, v)`**: a zero caller or spender reverts; otherwise the allowance set,
`true`, `Approval`. -/
theorem call_approve (sp : Address) (v : ℕ) :
    CallSpec YAMV2.runtimeCode abs M g₀ (.approve sp v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hsA : sp ∈ Act := haddr sp (by simp [Call.addrs])
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  refine halts_split' (G := Normal g₀ m)
    (fun hG => approve_high m sp (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1)
    (approve_low m sp (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hval0, hrev, hok⟩
  by_cases hv0 : m.frame.msg.value = 0
  swap
  · obtain ⟨out, rfl⟩ := hval0 hv0
    exact .inr ⟨trivial, fun hG => hv0 hG.2.2⟩
  left
  rw [yam_call_approve]
  by_cases hr : m.frame.msg.caller = 0 ∨ sp = 0
  · rw [Verified.Solady.Spec.ite_pos' hr]
    exact hrev hr
  rw [Verified.Solady.Spec.ite_neg' hr]
  simp only [not_or] at hr
  obtain ⟨-, -, ho, hw, ht, hcr, hl⟩ := hok hr.1 hr.2
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show read _ _ _ _ = _
    rw [hw, read_sstore_allow hs.sound hs.caller hsA, pre_eq hs hv0, hwv]
  · rw [hw]
    exact BNB.Spec.FrameKeeps.sstore'
      (.inr (.inr (.inr ⟨_, hs.caller, _, hsA, rfl⟩))) BNB.Spec.frameKeeps_refl'
  · rw [hl]
    simp [M, QEDefi.ERC20.Spec.YAMV2.model, QEDefi.ERC20.Spec.YAMV2.events, Spec.eventLog]

end Verified.WeirdERC20.YAMV2.Spec
