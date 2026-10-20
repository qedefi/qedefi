import EvmLeanSpecs.Refinement.ViewsRest

/-!
# Unknown selectors and short calldata revert

solc's dispatcher (`EvmLeanProofs/Solidity/Dispatch.lean`) compares the selector
`calldata[0:4]` against the contract's function selectors — a binary split on `GT` against
pivots, then linear `EQ` chains — and falls through to `PUSH0 PUSH0 REVERT` when nothing
matches; calldata shorter than four bytes jumps straight to the fallback, which reverts too
(neither contract has a `fallback` or `receive` function). Proved for the deployed bytecode
(any immutables), in any fresh frame, with no value (a call with value reverts earlier,
`Nested.vault_value_reverts`):

* `vault_unknown_reverts`, `asset_unknown_reverts`: a selector not in `vaultSelectors` /
  `assetSelectors` (the selectors of the contracts' ABI, `SolmateVault.selectors` /
  `SolmateAsset.selectors`: `vaultSelectors_eq`, `assetSelectors_eq`) reverts, whatever the
  rest of the calldata;
* `vault_short_reverts`, `asset_short_reverts`: calldata of fewer than four bytes reverts.

Each run is the dispatcher only (at most 1000 gas). Calldata that selects a function but is
malformed (too short for the arguments, dirty address words, `v` not a `uint8` in `permit`) is
rejected by that function's ABI decoder; that is **not** proved here.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-! ## Selectors -/

/-- The vault's function selectors, ascending. -/
def vaultSelectors : List Nat :=
  [0x01e1d114, 0x06fdde03, 0x07a2d13a, 0x095ea7b3, 0x0a28a477, 0x18160ddd, 0x23b872dd,
    0x313ce567, 0x3644e515, 0x38d52e0f, 0x402d267d, 0x4cdad506, 0x6e553f65, 0x70a08231,
    0x7ecebe00, 0x94bf804d, 0x95d89b41, 0xa9059cbb, 0xb3d7f6b9, 0xb460af94, 0xba087652,
    0xbc368a8a, 0xc63d75b6, 0xc6e6f592, 0xce96cb77, 0xd505accf, 0xd905777e, 0xdd62ed3e,
    0xef8b30f7, 0xfc407ae7]

/-- The asset's function selectors, ascending. -/
def assetSelectors : List Nat :=
  [0x06fdde03, 0x095ea7b3, 0x18160ddd, 0x23b872dd, 0x313ce567, 0x3644e515, 0x40c10f19,
    0x70a08231, 0x7ecebe00, 0x95d89b41, 0x9dc29fac, 0xa9059cbb, 0xd505accf, 0xdd62ed3e]

/-- `vaultSelectors` are the selectors of the vault's ABI. -/
theorem vaultSelectors_eq (n : Nat) :
    n ∈ vaultSelectors ↔ n ∈ SolmateVault.selectors.map fun p => p.2.toNat := by
  have h : (∀ x ∈ vaultSelectors, x ∈ SolmateVault.selectors.map fun p => p.2.toNat) ∧
      ∀ x ∈ SolmateVault.selectors.map (fun p => p.2.toNat), x ∈ vaultSelectors := by decide
  exact ⟨h.1 n, h.2 n⟩

/-- `assetSelectors` are the selectors of the asset's ABI. -/
theorem assetSelectors_eq (n : Nat) :
    n ∈ assetSelectors ↔ n ∈ SolmateAsset.selectors.map fun p => p.2.toNat := by
  have h : (∀ x ∈ assetSelectors, x ∈ SolmateAsset.selectors.map fun p => p.2.toNat) ∧
      ∀ x ∈ SolmateAsset.selectors.map (fun p => p.2.toNat), x ∈ assetSelectors := by decide
  exact ⟨h.1 n, h.2 n⟩

/-! ## Comparisons with a selector -/

/-- `EQ` of two different 32-bit numbers. -/
theorem eq_lit_zero {C S : Nat} (hC : C < 2 ^ 32) (hS : S < 2 ^ 32) (h : S ≠ C) :
    Word.eq (BitVec.ofNat 256 C) (BitVec.ofNat 256 S) = 0 := by
  unfold Word.eq Word.ofBool
  have : (BitVec.ofNat 256 C == BitVec.ofNat 256 S) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact h this.symm
  rw [this]; rfl

/-- `GT` of 32-bit numbers, true. -/
theorem gt_lit_one {C S : Nat} (hC : C < 2 ^ 32) (hS : S < 2 ^ 32) (h : S < C) :
    Word.gt (BitVec.ofNat 256 C) (BitVec.ofNat 256 S) = 1 := by
  rw [Word.gt_eq_one_iff]; simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact h

/-- `GT` of 32-bit numbers, false. -/
theorem gt_lit_zero {C S : Nat} (hC : C < 2 ^ 32) (hS : S < 2 ^ 32) (h : C ≤ S) :
    Word.gt (BitVec.ofNat 256 C) (BitVec.ofNat 256 S) = 0 := by
  unfold Word.gt Word.ofBool
  have : BitVec.ult (BitVec.ofNat 256 S) (BitVec.ofNat 256 C) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_lt]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact h
  rw [this]; rfl

/-- The selector is a 32-bit number. -/
theorem selectorOf_lt (data : ByteArray) : Abi.selectorOf data < 2 ^ 32 := by
  have := Bytes.toNat_lt (readBytes data 0 4)
  rw [size_readBytes] at this; unfold Abi.selectorOf; omega

/-- The dispatcher's `CALLDATASIZE < 4` test holds for calldata shorter than a selector. -/
theorem lt_size_four_one {n : Nat} (h : n < 4) : Word.lt (ofNat n) (BitVec.ofNat 256 4) = 1 := by
  rw [Word.lt_eq_one_iff]; simp only [ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact h

/-! ## The vault -/

set_option maxHeartbeats 0 in
/-- **An unknown selector reverts in the vault**, in any frame. -/
theorem vault_unknown_reverts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 1000 ≤ m.frame.gasLeft) (hn : Abi.selectorOf m.frame.msg.data ∉ vaultSelectors) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hagree := Shares.jumpDestsAgree i
  have hS := selectorOf_lt m.frame.msg.data
  generalize hSd : Abi.selectorOf m.frame.msg.data = S at hn hS
  have hsel' := Dispatch.selector_eq hSd
  simp only [vaultSelectors] at hn
  have e1 := eq_lit_zero (C := 0x01e1d114) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e2 := eq_lit_zero (C := 0x06fdde03) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e3 := eq_lit_zero (C := 0x07a2d13a) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e4 := eq_lit_zero (C := 0x095ea7b3) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e5 := eq_lit_zero (C := 0x0a28a477) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e6 := eq_lit_zero (C := 0x18160ddd) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e7 := eq_lit_zero (C := 0x23b872dd) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e8 := eq_lit_zero (C := 0x313ce567) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e9 := eq_lit_zero (C := 0x3644e515) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e10 := eq_lit_zero (C := 0x38d52e0f) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e11 := eq_lit_zero (C := 0x402d267d) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e12 := eq_lit_zero (C := 0x4cdad506) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e13 := eq_lit_zero (C := 0x6e553f65) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e14 := eq_lit_zero (C := 0x70a08231) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e15 := eq_lit_zero (C := 0x7ecebe00) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e16 := eq_lit_zero (C := 0x94bf804d) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e17 := eq_lit_zero (C := 0x95d89b41) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e18 := eq_lit_zero (C := 0xa9059cbb) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e19 := eq_lit_zero (C := 0xb3d7f6b9) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e20 := eq_lit_zero (C := 0xb460af94) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e21 := eq_lit_zero (C := 0xba087652) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e22 := eq_lit_zero (C := 0xbc368a8a) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e23 := eq_lit_zero (C := 0xc63d75b6) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e24 := eq_lit_zero (C := 0xc6e6f592) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e25 := eq_lit_zero (C := 0xce96cb77) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e26 := eq_lit_zero (C := 0xd505accf) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e27 := eq_lit_zero (C := 0xd905777e) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e28 := eq_lit_zero (C := 0xdd62ed3e) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e29 := eq_lit_zero (C := 0xef8b30f7) (by decide) hS (by rintro rfl; exact hn (by decide))
  have e30 := eq_lit_zero (C := 0xfc407ae7) (by decide) hS (by rintro rfl; exact hn (by decide))
  fresh_intro
  rcases Nat.lt_or_ge S 0x94bf804d with h1 | h1
  · have g1 := gt_lit_one (C := 0x94bf804d) (by decide) hS h1
    rcases Nat.lt_or_ge S 0x313ce567 with h2 | h2
    · have g2 := gt_lit_one (C := 0x313ce567) (by decide) hS h2
      rcases Nat.lt_or_ge S 0x095ea7b3 with h3 | h3
      · have g3 := gt_lit_one (C := 0x095ea7b3) (by decide) hS h3
        pwp_steps [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8,
          e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26,
          e27, e28, e29, e30, g1, g2, g3]
        exact ⟨_, rfl⟩
      · have g3 := gt_lit_zero (C := 0x095ea7b3) (by decide) hS h3
        pwp_steps [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8,
          e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26,
          e27, e28, e29, e30, g1, g2, g3]
        exact ⟨_, rfl⟩
    · have g2 := gt_lit_zero (C := 0x313ce567) (by decide) hS h2
      rcases Nat.lt_or_ge S 0x4cdad506 with h3 | h3
      · have g3 := gt_lit_one (C := 0x4cdad506) (by decide) hS h3
        pwp_steps [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8,
          e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26,
          e27, e28, e29, e30, g1, g2, g3]
        exact ⟨_, rfl⟩
      · have g3 := gt_lit_zero (C := 0x4cdad506) (by decide) hS h3
        pwp_steps [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8,
          e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26,
          e27, e28, e29, e30, g1, g2, g3]
        exact ⟨_, rfl⟩
  · have g1 := gt_lit_zero (C := 0x94bf804d) (by decide) hS h1
    rcases Nat.lt_or_ge S 0xc63d75b6 with h2 | h2
    · have g2 := gt_lit_one (C := 0xc63d75b6) (by decide) hS h2
      rcases Nat.lt_or_ge S 0xb3d7f6b9 with h3 | h3
      · have g3 := gt_lit_one (C := 0xb3d7f6b9) (by decide) hS h3
        pwp_steps [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8,
          e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26,
          e27, e28, e29, e30, g1, g2, g3]
        exact ⟨_, rfl⟩
      · have g3 := gt_lit_zero (C := 0xb3d7f6b9) (by decide) hS h3
        pwp_steps [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8,
          e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26,
          e27, e28, e29, e30, g1, g2, g3]
        exact ⟨_, rfl⟩
    · have g2 := gt_lit_zero (C := 0xc63d75b6) (by decide) hS h2
      rcases Nat.lt_or_ge S 0xd905777e with h3 | h3
      · have g3 := gt_lit_one (C := 0xd905777e) (by decide) hS h3
        pwp_steps [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8,
          e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26,
          e27, e28, e29, e30, g1, g2, g3]
        exact ⟨_, rfl⟩
      · have g3 := gt_lit_zero (C := 0xd905777e) (by decide) hS h3
        pwp_steps [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8,
          e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26,
          e27, e28, e29, e30, g1, g2, g3]
        exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- **Calldata shorter than a selector reverts in the vault**, in any frame. -/
theorem vault_short_reverts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hsize : m.frame.msg.data.size < 4) (hg : 1000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four_one hsize
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hlt]
  exact ⟨_, rfl⟩

/-! ## The asset -/

set_option maxHeartbeats 0 in
/-- **An unknown selector reverts in the asset**, in any frame. -/
theorem asset_unknown_reverts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 1000 ≤ m.frame.gasLeft) (hn : Abi.selectorOf m.frame.msg.data ∉ assetSelectors) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
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
      pwp_steps [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9,
        e10, e11, e12, e13, e14, g1, g2]
      exact ⟨_, rfl⟩
    · have g2 := gt_lit_zero (C := 0x23b872dd) (by decide) hS h2
      pwp_steps [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9,
        e10, e11, e12, e13, e14, g1, g2]
      exact ⟨_, rfl⟩
  · have g1 := gt_lit_zero (C := 0x70a08231) (by decide) hS h1
    rcases Nat.lt_or_ge S 0x9dc29fac with h2 | h2
    · have g2 := gt_lit_one (C := 0x9dc29fac) (by decide) hS h2
      pwp_steps [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9,
        e10, e11, e12, e13, e14, g1, g2]
      exact ⟨_, rfl⟩
    · have g2 := gt_lit_zero (C := 0x9dc29fac) (by decide) hS h2
      pwp_steps [hval, hlt, hsel', Abi.shr_calldataload_zero, e1, e2, e3, e4, e5, e6, e7, e8, e9,
        e10, e11, e12, e13, e14, g1, g2]
      exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- **Calldata shorter than a selector reverts in the asset**, in any frame. -/
theorem asset_short_reverts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hsize : m.frame.msg.data.size < 4) (hg : 1000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four_one hsize
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hlt]
  exact ⟨_, rfl⟩

end EvmLeanSpecs.Refinement
