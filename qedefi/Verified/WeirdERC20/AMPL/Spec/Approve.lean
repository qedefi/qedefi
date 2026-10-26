import Verified.WeirdERC20.AMPL.Spec.Views
import Verified.WeirdERC20.BNB.Spec.Write
import EvmLogic.Tactic.StepExt

/-!
# AMPL under the spec: `approve`

`approve(sp, v)` of `UFragments` (any spender, any value): the allowance row written,
`Approval(caller, sp, v)` logged, `true` returned.
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.Solady.Spec (LowHalts halts_split eq_zero_of_iszero_ne)
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-- `approve(sp, v)`'s code-level end. -/
def ApprovePost (m : Machine) (sp : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget
      (mappingSlot2 m.ctx.crypto (Word.ofAddress m.frame.msg.caller) (Word.ofAddress sp)
        159#256) v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (approvalLog m.frame.msg.currentTarget m.frame.msg.caller sp v)

set_option maxHeartbeats 0 in
theorem approve_low (m : Machine) (sp : Address) (v : Word) (hf : Fresh AMPL.runtimeCode m)
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
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [outputData]
    apwp_norm []
    rfl
  · simp only [outputMachine]
    logs_simp []
    event_log [v]

set_option maxHeartbeats 0 in
theorem approve_high (m : Machine) (sp : Address) (v : Word) (hf : Fresh AMPL.runtimeCode m)
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
  pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  refine ⟨hval, hst, rfl, rfl, rfl, rfl, ?_⟩
  simp only [outputMachine]
  logs_simp []
  event_log [v]

/-! ## The obligation -/

theorem ampl_call_approve (s : VState Address) (c sp : Address) (v : ℕ) :
    M.call s c (.approve sp v) = .ok (s.setAllowance c sp v) (.word true) := by
  simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.call, Variant.step, Variant.approve,
    Variant.approveOk, Variant.ampl, Variant.standard, Variant.retData]

theorem amplRead_sstore_allow {crypto : Crypto} {Act : Finset Address} {w : World}
    {t o sp : Address} (hS : amplSound crypto Act) (ho : o ∈ Act) (hs : sp ∈ Act) (x : Word) :
    amplRead crypto Act
        (w.sstore t (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 159#256) x) t =
      (amplRead crypto Act w t).setAllowance o sp x.toNat := by
  simp only [amplRead, VState.setAllowance]
  rw [BNB.Spec.readMap_sstore_map2 (base := 158#256) hS (by simp) (by simp) ho hs,
    BNB.Spec.readMap_sstore_map2 (base := 160#256) hS (by simp) (by simp) ho hs,
    BNB.Spec.readMap2_sstore hS (by simp) ho hs,
    BNB.Spec.readSlot_sstore_map2 (k := 156#256) hS (by simp) (by simp) ho hs,
    BNB.Spec.readSlot_sstore_map2 (k := 157#256) hS (by simp) (by simp) ho hs,
    BNB.Spec.sload_sstore_map2 (k := 155#256) hS (by simp) (by simp) ho hs, World.balance_sstore]

/-- **`approve(sp, v)`**: the allowance set, `true`, `Approval`. -/
theorem call_approve (sp : Address) (v : ℕ) :
    CallSpec AMPL.runtimeCode amplAbs M g₀ (.approve sp v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hsA : sp ∈ Act := haddr sp (by simp [Call.addrs])
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  refine halts_split (G := Normal g₀ m)
    (fun hG => approve_high m sp (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1)
    (approve_low m sp (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hv, -, ho, hw, ht, hcr, hl⟩
  rw [ampl_call_approve]
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show amplRead _ _ _ _ = _
    rw [hw, amplRead_sstore_allow hs.sound hs.caller hsA, pre_eq hs hv, hwv]
  · rw [hw]
    exact BNB.Spec.FrameKeeps.sstore'
      (.inr (.inr (.inr (.inr (.inl ⟨_, hs.caller, _, hsA, rfl⟩))))) BNB.Spec.frameKeeps_refl'
  · rw [hl]
    simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, QEDefi.ERC20.Spec.AMPL.amplEvents, Spec.eventLog]

end Verified.WeirdERC20.AMPL.Spec
