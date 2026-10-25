import Verified.OpenZeppelin.ERC20.Spec.Bridge
import Verified.OpenZeppelin.ERC20.Spec.Lift
import Verified.OpenZeppelin.ERC20.Spec.Static
import Verified.OpenZeppelin.ERC20.Spec.Dispatch
import Verified.OpenZeppelin.ERC20.Spec.Code
import Verified.OpenZeppelin.ERC20.CalleeTransfer
import Verified.OpenZeppelin.ERC20.CalleeApprove

/-!
# `ERC20Mock`'s `transfer`, `transferFrom` and `approve` are `ozModel`'s

`CallSpec` for the three calls: from `ozG₀` gas, in a non-static frame without value, the
callee summaries (`transfer_halts_ok`, …) end as `Variant.oz` says through `ozAbs`; with value
the frame reverts (`value_halts`), in a static frame it fails (`transfer_static`, …); below
`ozG₀` it fails or ends the same way (`callSpec_of_high`).
-/

namespace Verified.OpenZeppelin.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Solidity.ERC20
open EvmLean.Interpreter QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.Oz QEDefi.Math
open Verified.OpenZeppelin.Contracts
open Verified.Solmate.ERC20 (TwoWordCall ThreeWordCall)

/-- The gas from which `ERC20Mock`'s outcomes are exact (its most expensive function,
`transferFrom`, needs at most 90000). -/
def ozG₀ : Nat := 100000

/-! ## Common facts -/

section Common

variable {Act : Finset Address} {m : Machine}

theorem start_world (hS : Start OzAsset.runtimeCode ozAbs ozModel Act m)
    (hv : m.frame.msg.value = 0) : m.world = m.frame.snapshot.1 := by
  rw [hS.launched, transferValue_zero _ _ hv]

theorem pre_eq (hS : Start OzAsset.runtimeCode ozAbs ozModel Act m)
    (hv : m.frame.msg.value = 0) :
    pre ozAbs Act m = ozRead m.ctx.crypto Act m.world m.frame.msg.currentTarget := by
  rw [start_world hS hv]; rfl

theorem start_wf (hS : Start OzAsset.runtimeCode ozAbs ozModel Act m)
    (hv : m.frame.msg.value = 0) :
    (ozRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).toToken.WF := by
  have h := hS.wf
  rw [pre_eq hS hv] at h
  exact wf_toToken h rfl

theorem word_toNat {v : ℕ} (h : v < 2 ^ 256) : (word v).toNat = v := by
  simp only [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem args_two {data : ByteArray} {sel : Nat} {x y : Word} (h : Args data sel [x, y]) :
    TwoWordCall data sel x y :=
  ⟨h.selector, by simpa using h.size, by simpa using h.arg 0 (by simp),
    by simpa using h.arg 1 (by simp)⟩

theorem args_three {data : ByteArray} {sel : Nat} {x y z : Word} (h : Args data sel [x, y, z]) :
    ThreeWordCall data sel x y z :=
  ⟨h.selector, by simpa using h.size, by simpa using h.arg 0 (by simp),
    by simpa using h.arg 1 (by simp), by simpa using h.arg 2 (by simp)⟩

theorem not_normal_of_value (hv : m.frame.msg.value ≠ 0) : ¬ Normal ozG₀ m :=
  fun h => hv h.2.2

theorem not_normal_of_static (hst : m.frame.msg.isStatic = true) : ¬ Normal ozG₀ m :=
  fun h => by rw [h.2.1] at hst; cases hst

end Common

/-! ## `transfer` -/

section Transfer

variable {Act : Finset Address} {m : Machine}

set_option maxHeartbeats 1000000 in
/-- `transfer` in a `Normal` frame. -/
theorem transfer_normal (hS : Start OzAsset.runtimeCode ozAbs ozModel Act m) {dst : Address}
    {v : ℕ} (henc : (Call.transfer dst v).Encodes m.frame.msg.data) (hdst : dst ∈ Act)
    (hN : Normal ozG₀ m) :
    Halts m fun mf o =>
      Matches ozAbs Act m mf o (ozModel.events (pre ozAbs Act m) m.frame.msg.caller
        (.transfer dst v)) (ozModel.call (pre ozAbs Act m) m.frame.msg.caller (.transfer dst v)) := by
  obtain ⟨hg, hst, hv⟩ := hN
  obtain ⟨hvlt, hargs⟩ := henc
  have hd := args_two hargs
  have hvn := word_toNat hvlt
  have hR : ozSound m.ctx.crypto Act := hS.sound
  have hc := hS.caller
  have hr := rep_actorView (crypto := m.ctx.crypto) (Act := Act) (w := m.world)
    (token := m.frame.msg.currentTarget)
  have hw := start_wf hS hv
  rw [pre_eq hS hv]
  simp only [ozModel_call, oz_call_transfer]
  have hiff := ozTransfer_isSome_iff hr m.frame.msg.caller dst (word v)
  rw [hvn] at hiff
  split
  · rename_i t' ht
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [ht]))
    have hrep := rep_ozTransfer hr hw hm (by rw [hvn]; exact ht)
    have hview := actorView_moveWorld hR hc hdst hm
    have hm' := hm
    unfold Model.ozTransfer at hm'
    split at hm'
    · cases hm'
    rename_i hc0
    split at hm'
    · cases hm'
    rename_i hd0
    have hbal : (word v).toNat ≤ ((assetView m).balanceOf m.frame.msg.caller).toNat := by
      unfold Model.transfer at hm'
      split at hm'
      · rwa [view_balanceOf_eq hc]
      · cases hm'
    refine (transfer_halts_ok m hS.fresh hv hst hd hS.size (by unfold ozG₀ at hg; omega) hc0 hd0
      hbal).mono fun mf o _ hok => ?_
    obtain ⟨ho, hwf, htr, hcr, hlog, -⟩ := hok
    refine ⟨ho, ?_, ?_, htr, hcr, ?_⟩
    · show ozRead _ _ _ _ = _
      rw [hwf]
      exact ozRead_of_rep (hview ▸ hrep)
    · rw [hwf]; exact frameKeeps_moveWorld hc hdst
    · rw [hlog]; rfl
  · rename_i ht
    have hnone : Model.ozTransfer (actorView m.ctx.crypto Act m.world m.frame.msg.currentTarget)
        m.frame.msg.caller dst (word v) = none := by
      cases h : Model.ozTransfer (actorView m.ctx.crypto Act m.world m.frame.msg.currentTarget)
        m.frame.msg.caller dst (word v)
      · rfl
      · have := hiff.1 (by simp [h]); simp [ht] at this
    exact (transfer_halts_revert m hS.fresh hv hd hS.size (by unfold ozG₀ at hg; omega)
      (ozTransfer_none_of hc hnone)).mono fun _ _ _ h => h.1

/-- **`transfer` is `ozModel`'s.** -/
theorem oz_callSpec_transfer (dst : Address) (v : ℕ) :
    CallSpec OzAsset.runtimeCode ozAbs ozModel ozG₀ (.transfer dst v) := by
  refine callSpec_of_high noGasCode_oz fun Act m hS henc hadd hg => ?_
  have hdst : dst ∈ Act := hadd dst (by simp [Call.addrs])
  by_cases hv : m.frame.msg.value = 0
  · cases hst : m.frame.msg.isStatic
    · exact (transfer_normal hS henc hdst ⟨hg, hst, hv⟩).mono fun _ _ _ h => .inl h
    · exact (transfer_static m hS.fresh hv hst (args_two henc.2) hS.size
        (by unfold ozG₀ at hg; omega)).mono fun _ _ _ h => .inr ⟨h, not_normal_of_static hst⟩
  · exact (value_halts m hS.fresh hv (by unfold ozG₀ at hg; omega)).mono
      fun _ _ _ ⟨_, ho⟩ => .inr ⟨by rw [ho]; trivial, not_normal_of_value hv⟩

end Transfer

/-! ## `approve` -/

section Approve

variable {Act : Finset Address} {m : Machine}

set_option maxHeartbeats 1000000 in
/-- `approve` in a `Normal` frame. -/
theorem approve_normal (hS : Start OzAsset.runtimeCode ozAbs ozModel Act m) {sp : Address}
    {v : ℕ} (henc : (Call.approve sp v).Encodes m.frame.msg.data) (hsp : sp ∈ Act)
    (hN : Normal ozG₀ m) :
    Halts m fun mf o =>
      Matches ozAbs Act m mf o (ozModel.events (pre ozAbs Act m) m.frame.msg.caller
        (.approve sp v)) (ozModel.call (pre ozAbs Act m) m.frame.msg.caller (.approve sp v)) := by
  obtain ⟨hg, hst, hv⟩ := hN
  obtain ⟨hvlt, hargs⟩ := henc
  have hd := args_two hargs
  have hvn := word_toNat hvlt
  have hR : ozSound m.ctx.crypto Act := hS.sound
  have hc := hS.caller
  have hr := rep_actorView (crypto := m.ctx.crypto) (Act := Act) (w := m.world)
    (token := m.frame.msg.currentTarget)
  rw [pre_eq hS hv]
  simp only [ozModel_call, oz_call_approve]
  have hiff := ozApprove_isSome_iff
    (s := actorView m.ctx.crypto Act m.world m.frame.msg.currentTarget)
    (t := (ozRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).toToken)
    m.frame.msg.caller sp (word v) v
  split
  · rename_i t' ht
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [ht]))
    have hrep := rep_ozApprove hr hvn hm ht
    have hm' := hm
    unfold Model.ozApprove at hm'
    split at hm'
    · cases hm'
    rename_i hc0
    split at hm'
    · cases hm'
    rename_i hs0
    cases hm'
    have hview := actorView_allowanceWorld (w := m.world) (token := m.frame.msg.currentTarget)
      (amount := word v) hR hc hsp
    refine (approve_halts_ok m hS.fresh hv hst hd hS.size (by unfold ozG₀ at hg; omega) hc0
      hs0).mono fun mf o _ hok => ?_
    obtain ⟨ho, hwf, htr, hcr, hlog, -⟩ := hok
    refine ⟨ho, ?_, ?_, htr, hcr, ?_⟩
    · show ozRead _ _ _ _ = _
      rw [hwf]
      exact ozRead_of_rep (hview ▸ hrep)
    · rw [hwf]; exact frameKeeps_allowanceWorld hc hsp
    · rw [hlog]; rfl
  · rename_i ht
    have hnone : Model.ozApprove (actorView m.ctx.crypto Act m.world m.frame.msg.currentTarget)
        m.frame.msg.caller sp (word v) = none := by
      cases h : Model.ozApprove (actorView m.ctx.crypto Act m.world m.frame.msg.currentTarget)
        m.frame.msg.caller sp (word v)
      · rfl
      · have := hiff.1 (by simp [h]); simp [ht] at this
    exact (approve_halts_revert m hS.fresh hv hd hS.size (by unfold ozG₀ at hg; omega)
      (ozApprove_none_of hnone)).mono fun _ _ _ h => h.1

/-- **`approve` is `ozModel`'s.** -/
theorem oz_callSpec_approve (sp : Address) (v : ℕ) :
    CallSpec OzAsset.runtimeCode ozAbs ozModel ozG₀ (.approve sp v) := by
  refine callSpec_of_high noGasCode_oz fun Act m hS henc hadd hg => ?_
  have hsp : sp ∈ Act := hadd sp (by simp [Call.addrs])
  by_cases hv : m.frame.msg.value = 0
  · cases hst : m.frame.msg.isStatic
    · exact (approve_normal hS henc hsp ⟨hg, hst, hv⟩).mono fun _ _ _ h => .inl h
    · exact (approve_static m hS.fresh hv hst (args_two henc.2) hS.size
        (by unfold ozG₀ at hg; omega)).mono fun _ _ _ h => .inr ⟨h, not_normal_of_static hst⟩
  · exact (value_halts m hS.fresh hv (by unfold ozG₀ at hg; omega)).mono
      fun _ _ _ ⟨_, ho⟩ => .inr ⟨by rw [ho]; trivial, not_normal_of_value hv⟩

end Approve

/-! ## `transferFrom` -/

section TransferFrom

variable {Act : Finset Address} {m : Machine}

set_option maxHeartbeats 1000000 in
/-- `transferFrom` in a `Normal` frame. -/
theorem transferFrom_normal (hS : Start OzAsset.runtimeCode ozAbs ozModel Act m)
    {src dst : Address} {v : ℕ} (henc : (Call.transferFrom src dst v).Encodes m.frame.msg.data)
    (hs : src ∈ Act) (hdst : dst ∈ Act) (hN : Normal ozG₀ m) :
    Halts m fun mf o =>
      Matches ozAbs Act m mf o (ozModel.events (pre ozAbs Act m) m.frame.msg.caller
        (.transferFrom src dst v))
        (ozModel.call (pre ozAbs Act m) m.frame.msg.caller (.transferFrom src dst v)) := by
  obtain ⟨hg, hst, hv⟩ := hN
  obtain ⟨hvlt, hargs⟩ := henc
  have hd := args_three hargs
  have hvn := word_toNat hvlt
  have hR : ozSound m.ctx.crypto Act := hS.sound
  have hc := hS.caller
  have hr := rep_actorView (crypto := m.ctx.crypto) (Act := Act) (w := m.world)
    (token := m.frame.msg.currentTarget)
  have hw := start_wf hS hv
  have hcond := transferFromCond_iff_actors m src dst (word v) hR hs hc
  rw [pre_eq hS hv]
  simp only [ozModel_call, oz_call_transferFrom]
  have hiff := ozTransferFrom_isSome_iff hr m.frame.msg.caller src dst (word v)
  rw [hvn] at hiff
  split
  · rename_i t' ht
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [ht]))
    have hrep := rep_ozTransferFrom hr hw hm (by rw [hvn]; exact ht)
    have hview := actorView_ozTransferFromWorld hR hc hs hdst hm
    refine (transferFrom_halts_ok m hS.fresh hv hst hd hS.size (by unfold ozG₀ at hg; omega)
      (hcond.2 (by simp [hm]))).mono fun mf o _ hok => ?_
    obtain ⟨ho, hwf, htr, hcr, hlog, -⟩ := hok
    refine ⟨ho, ?_, ?_, htr, hcr, ?_⟩
    · show ozRead _ _ _ _ = _
      rw [hwf]
      exact ozRead_of_rep (hview ▸ hrep)
    · rw [hwf]; exact frameKeeps_ozTransferFromWorld hc hs hdst
    · rw [hlog]; rfl
  · rename_i ht
    have hnc : ¬ TransferFromCond m src dst (word v) := fun h => by
      have := hiff.1 (hcond.1 h); simp [ht] at this
    exact (transferFrom_halts_revert m hS.fresh hv hst hd hS.size (by unfold ozG₀ at hg; omega)
      hnc).mono fun _ _ _ h => h.1

/-- **`transferFrom` is `ozModel`'s.** -/
theorem oz_callSpec_transferFrom (src dst : Address) (v : ℕ) :
    CallSpec OzAsset.runtimeCode ozAbs ozModel ozG₀ (.transferFrom src dst v) := by
  refine callSpec_of_high noGasCode_oz fun Act m hS henc hadd hg => ?_
  have hs : src ∈ Act := hadd src (by simp [Call.addrs])
  have hdst : dst ∈ Act := hadd dst (by simp [Call.addrs])
  by_cases hv : m.frame.msg.value = 0
  · cases hst : m.frame.msg.isStatic
    · exact (transferFrom_normal hS henc hs hdst ⟨hg, hst, hv⟩).mono fun _ _ _ h => .inl h
    · exact (transferFrom_static m hS.fresh hv hst (args_three henc.2) hS.size
        (by unfold ozG₀ at hg; omega)).mono fun _ _ _ h => .inr ⟨h, not_normal_of_static hst⟩
  · exact (value_halts m hS.fresh hv (by unfold ozG₀ at hg; omega)).mono
      fun _ _ _ ⟨_, ho⟩ => .inr ⟨by rw [ho]; trivial, not_normal_of_value hv⟩

end TransferFrom

/-- **The three ERC-20 calls of `ERC20Mock` are `ozModel`'s.** -/
theorem oz_callSpec (c : Call Address) : CallSpec OzAsset.runtimeCode ozAbs ozModel ozG₀ c := by
  cases c with
  | transfer dst v => exact oz_callSpec_transfer dst v
  | transferFrom src dst v => exact oz_callSpec_transferFrom src dst v
  | approve sp v => exact oz_callSpec_approve sp v
  | other v => exact fun _ _ _ h => h.elim
  | permit o sp v live r => exact fun _ _ _ h => h.elim

end Verified.OpenZeppelin.ERC20.Spec
