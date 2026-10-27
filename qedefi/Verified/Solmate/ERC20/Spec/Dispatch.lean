import Verified.Solmate.ERC20.Spec.AssetCerts
import Verified.Solmate.ERC20.Spec.Normal

/-!
# The asset's dispatcher reaches a target

Every frame of the asset with value, short calldata, an unknown selector, or the selector of
one of the eight functions of the spec (the ERC-20 calls and views, `mint`, `burn`) reaches
one of the `targets` (`reaches_target`): the `REVERT`s of the dispatcher or the function's
entry. With `noGasRead_of_steps`, such a frame reads no gas.
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic
open Verified.Solmate.Contracts Verified.Solmate.ERC20 Verified.Solmate.ERC4626

variable {ia : SolmateAsset.Immutables}

/-- The selectors of the spec's functions. -/
def specSelectors : List Nat :=
  [0xa9059cbb, 0x23b872dd, 0x095ea7b3, 0x70a08231, 0xdd62ed3e, 0x18160ddd, 0x40c10f19,
    0x9dc29fac]

theorem wp_target {m : Machine} {H : Machine → Outcome → Prop} (h : m.frame.pc ∈ targets) :
    WP m (fun m' => m'.frame.pc ∈ targets) H :=
  .inl ⟨m, .refl m, h⟩

set_option maxHeartbeats 0 in
theorem reaches_value (m : Machine) (hf : Fresh (code ia) m) (hval : m.frame.msg.value ≠ 0)
    (hg : 100 ≤ m.frame.gasLeft) :
    WP m (fun m' => m'.frame.pc ∈ targets) (fun _ _ => False) := by
  have hz := iszero_of_ne hval
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_run_to 14 [hz]
  exact wp_target (by simp [targets])

set_option maxHeartbeats 0 in
theorem reaches_short (m : Machine) (hf : Fresh (code ia) m) (hval : m.frame.msg.value = 0)
    (hsize : m.frame.msg.data.size < 4) (hg : 1000 ≤ m.frame.gasLeft) :
    WP m (fun m' => m'.frame.pc ∈ targets) (fun _ _ => False) := by
  have hlt := lt_size_four_one hsize
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_run_to 232 [hval, hlt]
  exact wp_target (by simp [targets])

set_option maxHeartbeats 0 in
theorem reaches_unknown (m : Machine) (hf : Fresh (code ia) m) (hval : m.frame.msg.value = 0)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 1000 ≤ m.frame.gasLeft) (hn : Abi.selectorOf m.frame.msg.data ∉ assetSelectors) :
    WP m (fun m' => m'.frame.pc ∈ targets) (fun _ _ => False) := by
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hagree := assetJumpDestsAgree ia
  have hS := selectorOf_lt m.frame.msg.data
  generalize hSd : Abi.selectorOf m.frame.msg.data = S at hn hS
  have hsel' := Dispatch.selector_eq hSd
  simp only [assetSelectors] at hn
  have e1 := eq_lit_zero (C := 0x06fdde03) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e2 := eq_lit_zero (C := 0x095ea7b3) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e3 := eq_lit_zero (C := 0x18160ddd) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e4 := eq_lit_zero (C := 0x23b872dd) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e5 := eq_lit_zero (C := 0x313ce567) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e6 := eq_lit_zero (C := 0x3644e515) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e7 := eq_lit_zero (C := 0x40c10f19) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e8 := eq_lit_zero (C := 0x70a08231) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e9 := eq_lit_zero (C := 0x7ecebe00) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e10 := eq_lit_zero (C := 0x95d89b41) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e11 := eq_lit_zero (C := 0x9dc29fac) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e12 := eq_lit_zero (C := 0xa9059cbb) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e13 := eq_lit_zero (C := 0xd505accf) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e14 := eq_lit_zero (C := 0xdd62ed3e) (by decide) hS (by rintro rfl; exact hn (by decide))
  fresh_intro
  rcases Nat.lt_or_ge S 0x70a08231 with h1 | h1
  · have g1 := gt_lit_one (C := 0x70a08231) (by decide) hS h1
    rcases Nat.lt_or_ge S 0x23b872dd with h2 | h2
    · have g2 := gt_lit_one (C := 0x23b872dd) (by decide) hS h2
      pwp_run_to 98, 135, 194, 232 [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4,
        e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, g1, g2]
      exact wp_target (by simp [targets])
    · have g2 := gt_lit_zero (C := 0x23b872dd) (by decide) hS h2
      pwp_run_to 98, 135, 194, 232 [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4,
        e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, g1, g2]
      exact wp_target (by simp [targets])
  · have g1 := gt_lit_zero (C := 0x70a08231) (by decide) hS h1
    rcases Nat.lt_or_ge S 0x9dc29fac with h2 | h2
    · have g2 := gt_lit_one (C := 0x9dc29fac) (by decide) hS h2
      pwp_run_to 98, 135, 194, 232 [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4,
        e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, g1, g2]
      exact wp_target (by simp [targets])
    · have g2 := gt_lit_zero (C := 0x9dc29fac) (by decide) hS h2
      pwp_run_to 98, 135, 194, 232 [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4,
        e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, g1, g2]
      exact wp_target (by simp [targets])

set_option maxHeartbeats 0 in
theorem reaches_known (m : Machine) (hf : Fresh (code ia) m) (hval : m.frame.msg.value = 0)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 1000 ≤ m.frame.gasLeft) (hn : Abi.selectorOf m.frame.msg.data ∈ specSelectors) :
    WP m (fun m' => m'.frame.pc ∈ targets) (fun _ _ => False) := by
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hagree := assetJumpDestsAgree ia
  simp only [specSelectors, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h | h | h | h | h | h | h | h <;>
  · have hsel' := Dispatch.selector_eq h
    fresh_intro
    pwp_run_to 515, 321, 263, 426, 553, 298, 405, 496 [hval, hsel', hlt,
      Abi.shr_calldataload_zero]
    exact wp_target (by simp [targets])

/-- **The asset's dispatcher reaches a target.** -/
theorem reaches_target (m : Machine) (hf : Fresh (code ia) m)
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hg : 1000 ≤ m.frame.gasLeft)
    (h : m.frame.msg.value ≠ 0 ∨ m.frame.msg.data.size < 4 ∨
      Abi.selectorOf m.frame.msg.data ∉ assetSelectors ∨
      Abi.selectorOf m.frame.msg.data ∈ specSelectors) :
    ∃ mT, Steps m mT ∧ mT.frame.pc ∈ targets := by
  have hw : WP m (fun m' => m'.frame.pc ∈ targets) (fun _ _ => False) := by
    by_cases hval : m.frame.msg.value = 0
    · rcases h with h | h | h | h
      · exact absurd hval h
      · exact reaches_short m hf hval h hg
      · by_cases h4 : m.frame.msg.data.size < 4
        · exact reaches_short m hf hval h4 hg
        · exact reaches_unknown m hf hval (by omega) hsize' hg h
      · by_cases h4 : m.frame.msg.data.size < 4
        · exact reaches_short m hf hval h4 hg
        · exact reaches_known m hf hval (by omega) hsize' hg h
    · exact reaches_value m hf hval (by omega)
  rcases hw with ⟨mT, hs, hq⟩ | hh
  · exact ⟨mT, hs, hq⟩
  · obtain ⟨_, _, _, _, _, hf⟩ := hh; exact hf.elim

end Verified.Solmate.ERC20.Spec
