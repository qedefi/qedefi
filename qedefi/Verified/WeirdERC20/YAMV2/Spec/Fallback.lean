import Verified.WeirdERC20.YAMV2.Spec.Views
import Verified.Solady.Spec.Fallback

/-!
# YAMv2 under the spec: unknown selectors and short calldata

YAMv2 (solc 0.6.12) has no fallback function: a value (every entry point is non-payable, so the
dispatcher checks `CALLVALUE` first), calldata shorter than a selector, or a selector none of
the dispatcher's thirteen reverts, as the model's `other` call does.
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.YAMV2.Contracts
open Verified.Solady.Spec (LowHalts halts_split RevertPost lt_size_four_one)
open Verified.Solady.Spec.AnyGas

/-- The dispatcher's `EQ` tests all fail on an unknown selector. -/
theorem yam_unknown {data : ByteArray} (h : Abi.selectorOf data ∉ sel) :
    let s := BitVec.ofNat 256 (Abi.selectorOf data)
    Word.eq 0xdd62ed3e#256 s = 0 ∧
    Word.eq 0x095ea7b3#256 s = 0 ∧
    Word.eq 0x70a08231#256 s = 0 ∧
    Word.eq 0x313ce567#256 s = 0 ∧
    Word.eq 0xa457c2d7#256 s = 0 ∧
    Word.eq 0x39509351#256 s = 0 ∧
    Word.eq 0x40c10f19#256 s = 0 ∧
    Word.eq 0x07546172#256 s = 0 ∧
    Word.eq 0x06fdde03#256 s = 0 ∧
    Word.eq 0x95d89b41#256 s = 0 ∧
    Word.eq 0x18160ddd#256 s = 0 ∧
    Word.eq 0xa9059cbb#256 s = 0 ∧
    Word.eq 0x23b872dd#256 s = 0 := by
  have hs := Verified.Solady.Spec.selectorOf_lt data
  simp only [sel, YAMV2.selectors, List.map, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨Verified.Solady.Spec.eq_sel_ne (k := 0xdd62ed3e) hs (by decide) (by simpa using h1),
    Verified.Solady.Spec.eq_sel_ne (k := 0x095ea7b3) hs (by decide) (by simpa using h2),
    Verified.Solady.Spec.eq_sel_ne (k := 0x70a08231) hs (by decide) (by simpa using h3),
    Verified.Solady.Spec.eq_sel_ne (k := 0x313ce567) hs (by decide) (by simpa using h4),
    Verified.Solady.Spec.eq_sel_ne (k := 0xa457c2d7) hs (by decide) (by simpa using h5),
    Verified.Solady.Spec.eq_sel_ne (k := 0x39509351) hs (by decide) (by simpa using h6),
    Verified.Solady.Spec.eq_sel_ne (k := 0x40c10f19) hs (by decide) (by simpa using h7),
    Verified.Solady.Spec.eq_sel_ne (k := 0x07546172) hs (by decide) (by simpa using h8),
    Verified.Solady.Spec.eq_sel_ne (k := 0x06fdde03) hs (by decide) (by simpa using h9),
    Verified.Solady.Spec.eq_sel_ne (k := 0x95d89b41) hs (by decide) (by simpa using h10),
    Verified.Solady.Spec.eq_sel_ne (k := 0x18160ddd) hs (by decide) (by simpa using h11),
    Verified.Solady.Spec.eq_sel_ne (k := 0xa9059cbb) hs (by decide) (by simpa using h12),
    Verified.Solady.Spec.eq_sel_ne (k := 0x23b872dd) hs (by decide) (by simpa using h13)⟩

set_option maxHeartbeats 0 in
theorem fallback_low (m : Machine) (hf : Fresh YAMV2.runtimeCode m)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hd : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel) :
    LowHalts m RevertPost := by
  intro H hF _
  apply WP.halts_of_false
  by_cases h4 : m.frame.msg.data.size < 4
  · have hlt := lt_size_four_one h4
    solady_fresh_intro
    hwp_steps [hlt]
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ :=
      yam_unknown (hd.resolve_left h4)
    have hlt := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
    solady_fresh_intro
    hwp_steps [hlt, Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12,
      e13]

set_option maxHeartbeats 0 in
theorem fallback_high (m : Machine) (hf : Fresh YAMV2.runtimeCode m)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hd : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m RevertPost := by
  simp only [g₀] at hg
  apply WP.halts_of_false
  by_cases hv : m.frame.msg.value = 0
  swap
  · have hv' := iszero_of_ne hv
    solady_fresh_intro
    pwp_steps [hv']
    exact ⟨_, rfl⟩
  by_cases h4 : m.frame.msg.data.size < 4
  · have hlt := lt_size_four_one h4
    solady_fresh_intro
    pwp_steps [hv, hlt]
    exact ⟨_, rfl⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ :=
    yam_unknown (hd.resolve_left h4)
  have hs := Verified.Solady.Spec.selectorOf_lt m.frame.msg.data
  have hlt := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  by_cases c1 : Abi.selectorOf m.frame.msg.data < 0x39509351
  · have g1 := Verified.Solady.Spec.gt_sel_one hs (by decide) c1
    by_cases c2 : Abi.selectorOf m.frame.msg.data < 0x18160ddd
    · have g2 := Verified.Solady.Spec.gt_sel_one hs (by decide) c2
      solady_fresh_intro
      pwp_steps [hv, hlt, Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11,
        e12, e13, g1, g2]
      exact ⟨_, rfl⟩
    · have g2 := Verified.Solady.Spec.gt_sel_zero hs (by decide) c2
      solady_fresh_intro
      pwp_steps [hv, hlt, Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11,
        e12, e13, g1, g2]
      exact ⟨_, rfl⟩
  · have g1 := Verified.Solady.Spec.gt_sel_zero hs (by decide) c1
    by_cases c3 : Abi.selectorOf m.frame.msg.data < 0x95d89b41
    · have g3 := Verified.Solady.Spec.gt_sel_one hs (by decide) c3
      solady_fresh_intro
      pwp_steps [hv, hlt, Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11,
        e12, e13, g1, g3]
      exact ⟨_, rfl⟩
    · have g3 := Verified.Solady.Spec.gt_sel_zero hs (by decide) c3
      solady_fresh_intro
      pwp_steps [hv, hlt, Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11,
        e12, e13, g1, g3]
      exact ⟨_, rfl⟩

theorem yam_call_other (s : VState Address) (c : Address) (v : ℕ) :
    M.call s c (.other v) = .halt .revert := by
  simp [M, QEDefi.ERC20.Spec.YAMV2.model, Variant.call, Variant.step, Variant.fallbackCall,
    QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard, Variant.failKind, Variant.guardOk,
    Variant.failWith]

/-- **Unknown selectors and short calldata** revert, as the model's `other` call. -/
theorem fallback_spec : FallbackSpec YAMV2.runtimeCode abs M g₀ sel := by
  intro Act m hs hd
  refine halts_split (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => fallback_high m hs.fresh hs.size hd hG.1) (fallback_low m hs.fresh hs.size hd) ?_
  rintro mf o ⟨out, rfl⟩
  rw [yam_call_other]
  exact ⟨out, rfl⟩

end Verified.WeirdERC20.YAMV2.Spec
