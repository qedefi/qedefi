import Verified.WeirdERC20.ZRX.Spec.ViewSpec
import Verified.WeirdERC20.BNB.Spec.Fallback

/-!
# ZRX under the spec: unknown selectors and short calldata

ZRX (solc 0.4.11) has no fallback function: empty calldata jumps straight to the dispatcher's
`INVALID`, and a selector none of the nine falls through to it. Calldata of one to three bytes
is read zero-padded; its padded selector has a zero low byte, and none of ZRX's has
(`zrx_not_sel`). Every such frame ends in an exceptional halt, as the model's `other` call
(`guardFail := .invalid`) says, at any gas.
-/

namespace Verified.WeirdERC20.ZRX.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.ZRX.Contracts
open Verified.Solady.Spec (LowHalts halts_split)
open Verified.Solady.Spec.AnyGas

/-- The dispatcher's `EQ` tests all fail on an unknown selector. -/
theorem zrx_unknown {data : ByteArray} (h : Abi.selectorOf data ∉ sel) :
    let s := BitVec.ofNat 256 (Abi.selectorOf data)
    Word.eq 0xdd62ed3e#256 s = 0 ∧ Word.eq 0x095ea7b3#256 s = 0 ∧
    Word.eq 0x70a08231#256 s = 0 ∧ Word.eq 0x313ce567#256 s = 0 ∧
    Word.eq 0x06fdde03#256 s = 0 ∧ Word.eq 0x95d89b41#256 s = 0 ∧
    Word.eq 0x18160ddd#256 s = 0 ∧ Word.eq 0xa9059cbb#256 s = 0 ∧
    Word.eq 0x23b872dd#256 s = 0 := by
  have hs := Verified.Solady.Spec.selectorOf_lt data
  simp only [sel, ZRX.selectors, List.map, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨Verified.Solady.Spec.eq_sel_ne (k := 0xdd62ed3e) hs (by decide) (by simpa using h1),
    Verified.Solady.Spec.eq_sel_ne (k := 0x095ea7b3) hs (by decide) (by simpa using h2),
    Verified.Solady.Spec.eq_sel_ne (k := 0x70a08231) hs (by decide) (by simpa using h3),
    Verified.Solady.Spec.eq_sel_ne (k := 0x313ce567) hs (by decide) (by simpa using h4),
    Verified.Solady.Spec.eq_sel_ne (k := 0x06fdde03) hs (by decide) (by simpa using h5),
    Verified.Solady.Spec.eq_sel_ne (k := 0x95d89b41) hs (by decide) (by simpa using h6),
    Verified.Solady.Spec.eq_sel_ne (k := 0x18160ddd) hs (by decide) (by simpa using h7),
    Verified.Solady.Spec.eq_sel_ne (k := 0xa9059cbb) hs (by decide) (by simpa using h8),
    Verified.Solady.Spec.eq_sel_ne (k := 0x23b872dd) hs (by decide) (by simpa using h9)⟩

/-- Short calldata reads as a selector none of ZRX's (every one has a nonzero low byte). -/
theorem zrx_not_sel {data : ByteArray}
    (hd : data.size < 4 ∨ Abi.selectorOf data ∉ sel) : Abi.selectorOf data ∉ sel := by
  rcases hd with h | h
  · have h0 := BNB.Spec.selectorOf_short h
    intro hm
    simp only [sel, ZRX.selectors, List.map, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h <;> simp at h <;> omega
  · exact h

/-- An exceptional halt. -/
def HaltPost (_mf : Machine) (o : Outcome) : Prop := ∃ e, o = .halt e

set_option maxHeartbeats 0 in
theorem fallback_low (m : Machine) (hf : Fresh ZRX.runtimeCode m)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hd : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel) :
    LowHalts m HaltPost := by
  intro H hF _
  apply WP.halts_of_false
  by_cases h0 : m.frame.msg.data.size = 0
  · have hz : Word.iszero (ofNat m.frame.msg.data.size) = 1 := by rw [h0]; decide
    zrx_fresh_intro
    hwp_steps [hz]
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := zrx_unknown (zrx_not_sel hd)
    have hsel' := div_selector m.frame.msg.data
    have hz := BNB.Spec.calldatasize_pos (n := m.frame.msg.data.size) (by omega) hsz
    zrx_fresh_intro
    hwp_steps [hz, hsel', e1, e2, e3, e4, e5, e6, e7, e8, e9]

set_option maxHeartbeats 0 in
theorem fallback_high (m : Machine) (hf : Fresh ZRX.runtimeCode m)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hd : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m HaltPost := by
  simp only [g₀] at hg
  apply WP.halts_of_false
  by_cases h0 : m.frame.msg.data.size = 0
  · have hz : Word.iszero (ofNat m.frame.msg.data.size) = 1 := by rw [h0]; decide
    zrx_fresh_intro
    pwp_steps [hz]
    exact WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _) ⟨_, rfl⟩
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := zrx_unknown (zrx_not_sel hd)
    have hsel' := div_selector m.frame.msg.data
    have hz := BNB.Spec.calldatasize_pos (n := m.frame.msg.data.size) (by omega) hsz
    zrx_fresh_intro
    pwp_steps [hz, hsel', e1, e2, e3, e4, e5, e6, e7, e8, e9]
    exact WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _) ⟨_, rfl⟩

theorem zrx_call_other (s : VState Address) (c : Address) (v : ℕ) :
    M.call s c (.other v) = .halt .invalid :=
  QEDefi.ERC20.Spec.ZRX.call_other s c v

/-- **Empty calldata and unknown selectors** end in `INVALID`, as the model's `other` call. -/
theorem fallback_spec : FallbackSpec ZRX.runtimeCode abs M g₀ sel := by
  intro Act m hs hd
  refine halts_split (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => fallback_high m hs.fresh hs.size hd hG.1) (fallback_low m hs.fresh hs.size hd) ?_
  rintro mf o ⟨e, rfl⟩
  rw [zrx_call_other]
  exact ⟨e, rfl⟩

end Verified.WeirdERC20.ZRX.Spec
