import Verified.Solady.Spec.Views

/-!
# Solady `ERC20` under the spec: unknown selectors and short calldata

`SoladyToken` has no fallback: every frame whose calldata is shorter than a selector or whose
selector is none of the dispatcher's reverts, as the model's `other` call does.
-/

namespace Verified.Solady.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open EvmLean.Interpreter EvmLogic.Tactic Verified.Solady.Contracts Verified.Solady.Spec.AnyGas

theorem selectorOf_lt (data : ByteArray) : Abi.selectorOf data < 2 ^ 32 := by
  have := Bytes.toNat_lt (readBytes data 0 4)
  rw [EvmLean.Interpreter.size_readBytes] at this
  simp only [Abi.selectorOf]; omega

/-- `EQ` of the selector word with a selector it is not. -/
theorem eq_sel_ne {s k : Nat} (hs : s < 2 ^ 32) (hk : k < 2 ^ 32) (h : s ≠ k) :
    Word.eq (BitVec.ofNat 256 k) (BitVec.ofNat 256 s) = 0 := by
  have : BitVec.ofNat 256 k ≠ BitVec.ofNat 256 s := by
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact h this.symm
  simp [Word.eq, Word.ofBool, this]

theorem gt_sel_one {s k : Nat} (hs : s < 2 ^ 32) (hk : k < 2 ^ 32) (h : s < k) :
    Word.gt (BitVec.ofNat 256 k) (BitVec.ofNat 256 s) = 1 := by
  have : BitVec.ult (BitVec.ofNat 256 s) (BitVec.ofNat 256 k) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simpa using h
  simp [Word.gt, Word.ofBool, this]

theorem gt_sel_zero {s k : Nat} (hs : s < 2 ^ 32) (hk : k < 2 ^ 32) (h : ¬ s < k) :
    Word.gt (BitVec.ofNat 256 k) (BitVec.ofNat 256 s) = 0 := by
  have : BitVec.ult (BitVec.ofNat 256 s) (BitVec.ofNat 256 k) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simpa using h
  simp [Word.gt, Word.ofBool, this]

theorem lt_size_four_one {n : Nat} (h : n < 4) :
    Word.lt (ofNat n) (BitVec.ofNat 256 4) = 1 := by
  have : BitVec.ult (ofNat n) (BitVec.ofNat 256 4) = true := by
    simp only [BitVec.ult, ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    simpa using h
  simp [Word.lt, Word.ofBool, this]

/-- The dispatcher's facts for an unknown selector: every `EQ` test fails. -/
structure UnknownSel (s : Nat) : Prop where
  e1 : Word.eq 0x9dc29fac#256 (BitVec.ofNat 256 s) = 0
  e2 : Word.eq 0xa9059cbb#256 (BitVec.ofNat 256 s) = 0
  e3 : Word.eq 0xd505accf#256 (BitVec.ofNat 256 s) = 0
  e4 : Word.eq 0xdd62ed3e#256 (BitVec.ofNat 256 s) = 0
  e5 : Word.eq 0x70a08231#256 (BitVec.ofNat 256 s) = 0
  e6 : Word.eq 0x7ecebe00#256 (BitVec.ofNat 256 s) = 0
  e7 : Word.eq 0x95d89b41#256 (BitVec.ofNat 256 s) = 0
  e8 : Word.eq 0x23b872dd#256 (BitVec.ofNat 256 s) = 0
  e9 : Word.eq 0x313ce567#256 (BitVec.ofNat 256 s) = 0
  e10 : Word.eq 0x3644e515#256 (BitVec.ofNat 256 s) = 0
  e11 : Word.eq 0x40c10f19#256 (BitVec.ofNat 256 s) = 0
  e12 : Word.eq 0x06fdde03#256 (BitVec.ofNat 256 s) = 0
  e13 : Word.eq 0x095ea7b3#256 (BitVec.ofNat 256 s) = 0
  e14 : Word.eq 0x18160ddd#256 (BitVec.ofNat 256 s) = 0

theorem unknownSel {data : ByteArray} (h : Abi.selectorOf data ∉ sel) :
    UnknownSel (Abi.selectorOf data) := by
  have hs := selectorOf_lt data
  simp only [sel, SoladyToken.selectors, List.map, List.mem_cons, not_or,
    List.not_mem_nil, not_false_eq_true, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨eq_sel_ne hs (by decide) (by simpa using h5), eq_sel_ne hs (by decide) (by simpa using h13),
    eq_sel_ne hs (by decide) (by simpa using h10), eq_sel_ne hs (by decide) (by simpa using h2),
    eq_sel_ne hs (by decide) (by simpa using h4), eq_sel_ne hs (by decide) (by simpa using h9),
    eq_sel_ne hs (by decide) (by simpa using h11), eq_sel_ne hs (by decide) (by simpa using h14),
    eq_sel_ne hs (by decide) (by simpa using h6), eq_sel_ne hs (by decide) (by simpa using h1),
    eq_sel_ne hs (by decide) (by simpa using h7), eq_sel_ne hs (by decide) (by simpa using h8),
    eq_sel_ne hs (by decide) (by simpa using h3), eq_sel_ne hs (by decide) (by simpa using h12)⟩

/-- A revert. -/
def RevertPost (_mf : Machine) (o : Outcome) : Prop := ∃ out, o = .revert out

set_option maxHeartbeats 0 in
theorem fallback_low (m : Machine) (hf : Fresh SoladyToken.runtimeCode m)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hd : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel) :
    LowHalts m RevertPost := by
  intro H hF _
  apply WP.halts_of_false
  by_cases h4 : m.frame.msg.data.size < 4
  · have hlt := lt_size_four_one h4
    solady_fresh_intro
    hwp_steps [hlt]
  · have hu := unknownSel (hd.resolve_left h4)
    have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
    solady_fresh_intro
    hwp_steps [hlt, Abi.shr_calldataload_zero, hu.e1, hu.e2, hu.e3, hu.e4, hu.e5, hu.e6, hu.e7,
      hu.e8, hu.e9, hu.e10, hu.e11, hu.e12, hu.e13, hu.e14]

set_option maxHeartbeats 0 in
theorem fallback_high (m : Machine) (hf : Fresh SoladyToken.runtimeCode m)
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
  have hu := unknownSel (hd.resolve_left h4)
  have hs := selectorOf_lt m.frame.msg.data
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  by_cases c1 : Abi.selectorOf m.frame.msg.data < 0x70a08231
  · have g1 := gt_sel_one hs (by decide) c1
    by_cases c2 : Abi.selectorOf m.frame.msg.data < 0x23b872dd
    · have g2 := gt_sel_one hs (by decide) c2
      solady_fresh_intro
      pwp_steps [hv, hlt, Abi.shr_calldataload_zero, g1, g2, hu.e1, hu.e2, hu.e3, hu.e4, hu.e5,
        hu.e6, hu.e7, hu.e8, hu.e9, hu.e10, hu.e11, hu.e12, hu.e13, hu.e14]
      exact ⟨_, rfl⟩
    · have g2 := gt_sel_zero hs (by decide) c2
      solady_fresh_intro
      pwp_steps [hv, hlt, Abi.shr_calldataload_zero, g1, g2, hu.e1, hu.e2, hu.e3, hu.e4, hu.e5,
        hu.e6, hu.e7, hu.e8, hu.e9, hu.e10, hu.e11, hu.e12, hu.e13, hu.e14]
      exact ⟨_, rfl⟩
  · have g1 := gt_sel_zero hs (by decide) c1
    by_cases c2 : Abi.selectorOf m.frame.msg.data < 0x9dc29fac
    · have g2 := gt_sel_one hs (by decide) c2
      solady_fresh_intro
      pwp_steps [hv, hlt, Abi.shr_calldataload_zero, g1, g2, hu.e1, hu.e2, hu.e3, hu.e4, hu.e5,
        hu.e6, hu.e7, hu.e8, hu.e9, hu.e10, hu.e11, hu.e12, hu.e13, hu.e14]
      exact ⟨_, rfl⟩
    · have g2 := gt_sel_zero hs (by decide) c2
      solady_fresh_intro
      pwp_steps [hv, hlt, Abi.shr_calldataload_zero, g1, g2, hu.e1, hu.e2, hu.e3, hu.e4, hu.e5,
        hu.e6, hu.e7, hu.e8, hu.e9, hu.e10, hu.e11, hu.e12, hu.e13, hu.e14]
      exact ⟨_, rfl⟩

theorem solady_call_other (s : VState Address) (c : Address) (v : ℕ) :
    M.call s c (.other v) = .halt .revert := by
  simp [M, Solady.soladyModel, Variant.call, Variant.step, Variant.fallbackCall, Variant.solady,
    Variant.standard, Variant.failKind, Variant.guardOk, Variant.failWith]

/-- **Unknown selectors and short calldata** revert, as the model's `other` call. -/
theorem fallback_spec : FallbackSpec SoladyToken.runtimeCode soladyAbs M g₀ sel := by
  intro Act m hs hd
  refine halts_split (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => fallback_high m hs.fresh hs.size hd hG.1) (fallback_low m hs.fresh hs.size hd) ?_
  rintro mf o ⟨out, rfl⟩
  rw [solady_call_other]
  exact ⟨out, rfl⟩

end Verified.Solady.Spec
