import Verified.WeirdERC20.AMPL.Spec.Views
import Verified.Solady.Spec.Fallback

/-!
# AMPL under the spec: unknown selectors and short calldata

`UFragments` (solc 0.7.6) has no fallback function: a value, calldata shorter than a selector,
or a selector none of the dispatcher's thirty reverts, as the model's `other` call does.
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.Solady.Spec (LowHalts halts_split RevertPost lt_size_four_one)
open Verified.Solady.Spec.AnyGas

/-- The dispatcher's `EQ` tests all fail on an unknown selector. -/
theorem ampl_unknown {data : ByteArray} (h : Abi.selectorOf data ∉ sel) :
    let s := BitVec.ofNat 256 (Abi.selectorOf data)
    Word.eq 0x3644e515#256 s = 0 ∧
    Word.eq 0xe1b11da4#256 s = 0 ∧
    Word.eq 0x78160376#256 s = 0 ∧
    Word.eq 0x30adf81f#256 s = 0 ∧
    Word.eq 0xdd62ed3e#256 s = 0 ∧
    Word.eq 0x095ea7b3#256 s = 0 ∧
    Word.eq 0x70a08231#256 s = 0 ∧
    Word.eq 0x313ce567#256 s = 0 ∧
    Word.eq 0xa457c2d7#256 s = 0 ∧
    Word.eq 0x39509351#256 s = 0 ∧
    Word.eq 0xc4d66de8#256 s = 0 ∧
    Word.eq 0x1624f6c6#256 s = 0 ∧
    Word.eq 0x8f32d59b#256 s = 0 ∧
    Word.eq 0x8e27d7d7#256 s = 0 ∧
    Word.eq 0x06fdde03#256 s = 0 ∧
    Word.eq 0x7ecebe00#256 s = 0 ∧
    Word.eq 0x8da5cb5b#256 s = 0 ∧
    Word.eq 0xd505accf#256 s = 0 ∧
    Word.eq 0x7a43e23f#256 s = 0 ∧
    Word.eq 0x715018a6#256 s = 0 ∧
    Word.eq 0x1da24f3e#256 s = 0 ∧
    Word.eq 0xb1bf962d#256 s = 0 ∧
    Word.eq 0x8b5a6a08#256 s = 0 ∧
    Word.eq 0x95d89b41#256 s = 0 ∧
    Word.eq 0x18160ddd#256 s = 0 ∧
    Word.eq 0xa9059cbb#256 s = 0 ∧
    Word.eq 0xa3a7e7f3#256 s = 0 ∧
    Word.eq 0x84d4b410#256 s = 0 ∧
    Word.eq 0x23b872dd#256 s = 0 ∧
    Word.eq 0xf2fde38b#256 s = 0 := by
  have hs := Verified.Solady.Spec.selectorOf_lt data
  simp only [sel, AMPL.selectors, List.map, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := h
  exact ⟨Verified.Solady.Spec.eq_sel_ne (k := 0x3644e515) hs (by decide) (by simpa using h1),
    Verified.Solady.Spec.eq_sel_ne (k := 0xe1b11da4) hs (by decide) (by simpa using h2),
    Verified.Solady.Spec.eq_sel_ne (k := 0x78160376) hs (by decide) (by simpa using h3),
    Verified.Solady.Spec.eq_sel_ne (k := 0x30adf81f) hs (by decide) (by simpa using h4),
    Verified.Solady.Spec.eq_sel_ne (k := 0xdd62ed3e) hs (by decide) (by simpa using h5),
    Verified.Solady.Spec.eq_sel_ne (k := 0x095ea7b3) hs (by decide) (by simpa using h6),
    Verified.Solady.Spec.eq_sel_ne (k := 0x70a08231) hs (by decide) (by simpa using h7),
    Verified.Solady.Spec.eq_sel_ne (k := 0x313ce567) hs (by decide) (by simpa using h8),
    Verified.Solady.Spec.eq_sel_ne (k := 0xa457c2d7) hs (by decide) (by simpa using h9),
    Verified.Solady.Spec.eq_sel_ne (k := 0x39509351) hs (by decide) (by simpa using h10),
    Verified.Solady.Spec.eq_sel_ne (k := 0xc4d66de8) hs (by decide) (by simpa using h11),
    Verified.Solady.Spec.eq_sel_ne (k := 0x1624f6c6) hs (by decide) (by simpa using h12),
    Verified.Solady.Spec.eq_sel_ne (k := 0x8f32d59b) hs (by decide) (by simpa using h13),
    Verified.Solady.Spec.eq_sel_ne (k := 0x8e27d7d7) hs (by decide) (by simpa using h14),
    Verified.Solady.Spec.eq_sel_ne (k := 0x06fdde03) hs (by decide) (by simpa using h15),
    Verified.Solady.Spec.eq_sel_ne (k := 0x7ecebe00) hs (by decide) (by simpa using h16),
    Verified.Solady.Spec.eq_sel_ne (k := 0x8da5cb5b) hs (by decide) (by simpa using h17),
    Verified.Solady.Spec.eq_sel_ne (k := 0xd505accf) hs (by decide) (by simpa using h18),
    Verified.Solady.Spec.eq_sel_ne (k := 0x7a43e23f) hs (by decide) (by simpa using h19),
    Verified.Solady.Spec.eq_sel_ne (k := 0x715018a6) hs (by decide) (by simpa using h20),
    Verified.Solady.Spec.eq_sel_ne (k := 0x1da24f3e) hs (by decide) (by simpa using h21),
    Verified.Solady.Spec.eq_sel_ne (k := 0xb1bf962d) hs (by decide) (by simpa using h22),
    Verified.Solady.Spec.eq_sel_ne (k := 0x8b5a6a08) hs (by decide) (by simpa using h23),
    Verified.Solady.Spec.eq_sel_ne (k := 0x95d89b41) hs (by decide) (by simpa using h24),
    Verified.Solady.Spec.eq_sel_ne (k := 0x18160ddd) hs (by decide) (by simpa using h25),
    Verified.Solady.Spec.eq_sel_ne (k := 0xa9059cbb) hs (by decide) (by simpa using h26),
    Verified.Solady.Spec.eq_sel_ne (k := 0xa3a7e7f3) hs (by decide) (by simpa using h27),
    Verified.Solady.Spec.eq_sel_ne (k := 0x84d4b410) hs (by decide) (by simpa using h28),
    Verified.Solady.Spec.eq_sel_ne (k := 0x23b872dd) hs (by decide) (by simpa using h29),
    Verified.Solady.Spec.eq_sel_ne (k := 0xf2fde38b) hs (by decide) (by simpa using h30)⟩

set_option maxHeartbeats 0 in
theorem fallback_low (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hd : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel) :
    LowHalts m RevertPost := by
  intro H hF _
  apply WP.halts_of_false
  by_cases h4 : m.frame.msg.data.size < 4
  · have hlt := lt_size_four_one h4
    solady_fresh_intro
    hwp_steps [hlt]
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30⟩ := ampl_unknown (hd.resolve_left h4)
    have hlt := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
    solady_fresh_intro
    hwp_steps [hlt, Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30]

set_option maxHeartbeats 0 in
theorem fallback_high (m : Machine) (hf : Fresh AMPL.runtimeCode m)
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
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30⟩ := ampl_unknown (hd.resolve_left h4)
  have hs := Verified.Solady.Spec.selectorOf_lt m.frame.msg.data
  have hlt := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  by_cases c1 : Abi.selectorOf m.frame.msg.data < 0x84d4b410
  · have g1 := Verified.Solady.Spec.gt_sel_one hs (by decide) c1
    by_cases c2 : Abi.selectorOf m.frame.msg.data < 0x313ce567
    · have g2 := Verified.Solady.Spec.gt_sel_one hs (by decide) c2
      by_cases c3 : Abi.selectorOf m.frame.msg.data < 0x18160ddd
      · have g3 := Verified.Solady.Spec.gt_sel_one hs (by decide) c3
        solady_fresh_intro
        pwp_steps [hv, hlt, Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, g1, g2, g3]
        exact ⟨_, rfl⟩
      · have g3 := Verified.Solady.Spec.gt_sel_zero hs (by decide) c3
        solady_fresh_intro
        pwp_steps [hv, hlt, Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, g1, g2, g3]
        exact ⟨_, rfl⟩
    · have g2 := Verified.Solady.Spec.gt_sel_zero hs (by decide) c2
      by_cases c4 : Abi.selectorOf m.frame.msg.data < 0x715018a6
      · have g4 := Verified.Solady.Spec.gt_sel_one hs (by decide) c4
        solady_fresh_intro
        pwp_steps [hv, hlt, Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, g1, g2, g4]
        exact ⟨_, rfl⟩
      · have g4 := Verified.Solady.Spec.gt_sel_zero hs (by decide) c4
        solady_fresh_intro
        pwp_steps [hv, hlt, Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, g1, g2, g4]
        exact ⟨_, rfl⟩
  · have g1 := Verified.Solady.Spec.gt_sel_zero hs (by decide) c1
    by_cases c5 : Abi.selectorOf m.frame.msg.data < 0xa457c2d7
    · have g5 := Verified.Solady.Spec.gt_sel_one hs (by decide) c5
      by_cases c6 : Abi.selectorOf m.frame.msg.data < 0x8e27d7d7
      · have g6 := Verified.Solady.Spec.gt_sel_one hs (by decide) c6
        solady_fresh_intro
        pwp_steps [hv, hlt, Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, g1, g5, g6]
        exact ⟨_, rfl⟩
      · have g6 := Verified.Solady.Spec.gt_sel_zero hs (by decide) c6
        solady_fresh_intro
        pwp_steps [hv, hlt, Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, g1, g5, g6]
        exact ⟨_, rfl⟩
    · have g5 := Verified.Solady.Spec.gt_sel_zero hs (by decide) c5
      by_cases c7 : Abi.selectorOf m.frame.msg.data < 0xd505accf
      · have g7 := Verified.Solady.Spec.gt_sel_one hs (by decide) c7
        solady_fresh_intro
        pwp_steps [hv, hlt, Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, g1, g5, g7]
        exact ⟨_, rfl⟩
      · have g7 := Verified.Solady.Spec.gt_sel_zero hs (by decide) c7
        solady_fresh_intro
        pwp_steps [hv, hlt, Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, g1, g5, g7]
        exact ⟨_, rfl⟩

theorem ampl_call_other (s : VState Address) (c : Address) (v : ℕ) :
    M.call s c (.other v) = .halt .revert := by
  simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.call, Variant.step, Variant.fallbackCall,
    Variant.ampl, Variant.standard, Variant.failKind, Variant.guardOk, Variant.failWith]

/-- **Unknown selectors and short calldata** revert, as the model's `other` call. -/
theorem fallback_spec : FallbackSpec AMPL.runtimeCode amplAbs M g₀ sel := by
  intro Act m hs hd
  refine halts_split (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => fallback_high m hs.fresh hs.size hd hG.1) (fallback_low m hs.fresh hs.size hd) ?_
  rintro mf o ⟨out, rfl⟩
  rw [ampl_call_other]
  exact ⟨out, rfl⟩

end Verified.WeirdERC20.AMPL.Spec
