import Verified.WeirdERC20.STA.Spec.Views
import Verified.Solady.Spec.Fallback

/-!
# STA under the spec: unknown selectors and short calldata

Statera (solc 0.5.0) has no fallback function: calldata shorter than a selector, or whose
selector is none of the dispatcher's fifteen, reverts, as the model's `other` call does.
-/

namespace Verified.WeirdERC20.STA.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.STA.Contracts
open Verified.Solady.Spec (LowHalts halts_split RevertPost lt_size_four_one)
open Verified.Solady.Spec.AnyGas

theorem eq_comm_zero {a b : Word} (h : Word.eq a b = 0) : Word.eq b a = 0 := by
  have hab : a ≠ b := fun e => by subst e; simp [Word.eq, Word.ofBool] at h
  simp [Word.eq, Word.ofBool, Ne.symm hab]

/-- The dispatcher's `EQ` tests all fail on an unknown selector. -/
theorem sta_unknown {data : ByteArray} (h : Abi.selectorOf data ∉ sel) :
    let s := BitVec.ofNat 256 (Abi.selectorOf data)
    Word.eq 0xdd62ed3e#256 s = 0 ∧ Word.eq 0x095ea7b3#256 s = 0 ∧ Word.eq 0x70a08231#256 s = 0 ∧
    Word.eq 0xc5ac0ded#256 s = 0 ∧ Word.eq 0x09260db7#256 s = 0 ∧ Word.eq 0x313ce567#256 s = 0 ∧
    Word.eq 0x9d118770#256 s = 0 ∧ Word.eq 0x33393efa#256 s = 0 ∧ Word.eq 0xdf401a96#256 s = 0 ∧
    Word.eq 0x06fdde03#256 s = 0 ∧ Word.eq 0x95d89b41#256 s = 0 ∧ Word.eq 0x18160ddd#256 s = 0 ∧
    Word.eq 0xa9059cbb#256 s = 0 ∧ Word.eq 0x23b872dd#256 s = 0 ∧
    Word.eq 0xe5981a42#256 s = 0 := by
  have hs := Verified.Solady.Spec.selectorOf_lt data
  simp only [sel, STA.selectors, List.map, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨Verified.Solady.Spec.eq_sel_ne (k := 0xdd62ed3e) hs (by decide) (by simpa using h1),
    Verified.Solady.Spec.eq_sel_ne (k := 0x095ea7b3) hs (by decide) (by simpa using h2),
    Verified.Solady.Spec.eq_sel_ne (k := 0x70a08231) hs (by decide) (by simpa using h3),
    Verified.Solady.Spec.eq_sel_ne (k := 0xc5ac0ded) hs (by decide) (by simpa using h4),
    Verified.Solady.Spec.eq_sel_ne (k := 0x09260db7) hs (by decide) (by simpa using h5),
    Verified.Solady.Spec.eq_sel_ne (k := 0x313ce567) hs (by decide) (by simpa using h6),
    Verified.Solady.Spec.eq_sel_ne (k := 0x9d118770) hs (by decide) (by simpa using h7),
    Verified.Solady.Spec.eq_sel_ne (k := 0x33393efa) hs (by decide) (by simpa using h8),
    Verified.Solady.Spec.eq_sel_ne (k := 0xdf401a96) hs (by decide) (by simpa using h9),
    Verified.Solady.Spec.eq_sel_ne (k := 0x06fdde03) hs (by decide) (by simpa using h10),
    Verified.Solady.Spec.eq_sel_ne (k := 0x95d89b41) hs (by decide) (by simpa using h11),
    Verified.Solady.Spec.eq_sel_ne (k := 0x18160ddd) hs (by decide) (by simpa using h12),
    Verified.Solady.Spec.eq_sel_ne (k := 0xa9059cbb) hs (by decide) (by simpa using h13),
    Verified.Solady.Spec.eq_sel_ne (k := 0x23b872dd) hs (by decide) (by simpa using h14),
    Verified.Solady.Spec.eq_sel_ne (k := 0xe5981a42) hs (by decide) (by simpa using h15)⟩

set_option maxHeartbeats 0 in
theorem fallback_low (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hd : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel) :
    LowHalts m RevertPost := by
  intro H hF _
  apply WP.halts_of_false
  by_cases h4 : m.frame.msg.data.size < 4
  · have hlt := lt_size_four_one h4
    solady_fresh_intro
    hwp_steps [hlt]
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ :=
      sta_unknown (hd.resolve_left h4)
    have hsel' := div_selector m.frame.msg.data
    have hlt := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
    solady_fresh_intro
    hwp_steps [hlt, hsel', eq_comm_zero e10, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]

set_option maxHeartbeats 0 in
theorem fallback_high (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hd : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m RevertPost := by
  simp only [g₀] at hg
  apply WP.halts_of_false
  by_cases h4 : m.frame.msg.data.size < 4
  · have hlt := lt_size_four_one h4
    solady_fresh_intro
    pwp_steps [hlt]
    exact ⟨_, rfl⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ :=
    sta_unknown (hd.resolve_left h4)
  have hsel' := div_selector m.frame.msg.data
  have hlt := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  solady_fresh_intro
  pwp_steps [hlt, hsel', eq_comm_zero e10, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  exact ⟨_, rfl⟩

theorem sta_call_other (s : VState Address) (c : Address) (v : ℕ) :
    M.call s c (.other v) = .halt .revert := by
  simp [M, QEDefi.ERC20.Spec.STA.staModel, Variant.call, Variant.step, Variant.fallbackCall,
    Variant.sta, Variant.standard, Variant.failKind, Variant.guardOk, Variant.failWith]

/-- **Unknown selectors and short calldata** revert, as the model's `other` call. -/
theorem fallback_spec : FallbackSpec STA.runtimeCode staAbs M g₀ sel := by
  intro Act m hs hd
  refine halts_split (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => fallback_high m hs.fresh hs.size hd hG.1) (fallback_low m hs.fresh hs.size hd) ?_
  rintro mf o ⟨out, rfl⟩
  rw [sta_call_other]
  exact ⟨out, rfl⟩

end Verified.WeirdERC20.STA.Spec
