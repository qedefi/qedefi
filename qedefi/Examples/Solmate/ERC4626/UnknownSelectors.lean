import Examples.Solmate.ERC4626.ViewsSpec

/-!
# Unknown selectors and short calldata revert

`*_unknown_reverts`: a selector outside the contract's ABI reverts in solc's dispatcher, whatever
the rest of the calldata; `*_short_reverts`: calldata shorter than four bytes reverts. For both
contracts (any immutables), any fresh frame, no value. Also the definitions used by
`Malformed.lean`. See `docs/erc4626/details.md` §5.
-/

section

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

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

theorem gt_lit_one {C S : Nat} (hC : C < 2 ^ 32) (hS : S < 2 ^ 32) (h : S < C) :
    Word.gt (BitVec.ofNat 256 C) (BitVec.ofNat 256 S) = 1 := by
  rw [Word.gt_eq_one_iff]; simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact h

theorem gt_lit_zero {C S : Nat} (hC : C < 2 ^ 32) (hS : S < 2 ^ 32) (h : C ≤ S) :
    Word.gt (BitVec.ofNat 256 C) (BitVec.ofNat 256 S) = 0 := by
  unfold Word.gt Word.ofBool
  have : BitVec.ult (BitVec.ofNat 256 S) (BitVec.ofNat 256 C) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_lt]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact h
  rw [this]; rfl

theorem selectorOf_lt (data : ByteArray) : Abi.selectorOf data < 2 ^ 32 := by
  have := Bytes.toNat_lt (readBytes data 0 4)
  rw [size_readBytes] at this; unfold Abi.selectorOf; omega

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

end Examples.Solmate.ERC4626

end

section

/-! ## Malformed calldata: definitions (theorems in `Malformed.lean`) -/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

/-! ## Argument words -/

/-- Argument word `j` of calldata `d`, as `CALLDATALOAD(4 + 32·j)` reads it. -/
def argWord (d : ByteArray) (j : Nat) : Word := Bytes.toWord (readBytes d (4 + 32 * j) 32)

/-- Argument word `j` is a clean `address`: its high 96 bits are zero. -/
def CleanAddr (d : ByteArray) (j : Nat) : Prop := argWord d j &&& addressMask = argWord d j

/-- Calldata `d` is malformed for a function taking `k` argument words with `address`
arguments at positions `addrs`: fewer than `k` argument words, or a dirty `address` argument
after clean ones. -/
def Malformed (d : ByteArray) (k : Nat) (addrs : List Nat) : Prop :=
  d.size < 4 + 32 * k ∨
    (4 + 32 * k ≤ d.size ∧ ∃ j ∈ addrs, (∀ j' ∈ addrs, j' < j → CleanAddr d j') ∧ ¬ CleanAddr d j)

theorem cleanAddr_lit {d : ByteArray} {j : Nat} (h : CleanAddr d j) :
    argWord d j &&& 1461501637330902918203684832716283019655932542975#256 = argWord d j := by
  rw [← addressMask_eq]; exact h

theorem eq_and_mask_zero {d : ByteArray} {j : Nat} (h : ¬ CleanAddr d j) :
    Word.eq (argWord d j)
      (argWord d j &&& 1461501637330902918203684832716283019655932542975#256) = 0 := by
  unfold Word.eq Word.ofBool
  have : (argWord d j == argWord d j &&& 1461501637330902918203684832716283019655932542975#256)
      = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro he
    exact h (by unfold CleanAddr; rw [addressMask_eq]; exact he.symm)
  rw [this]; rfl

theorem iszero_slt_short {size n : Nat} (h1 : 4 ≤ size) (h2 : size < 4 + n) (hn : n < 2 ^ 255) :
    Word.iszero (Word.slt (BitVec.ofNat 256 size - 4#256) (BitVec.ofNat 256 n)) = 0 := by
  have hx : (BitVec.ofNat 256 size - 4#256).toNat = size - 4 := by
    rw [BitVec.toNat_sub_of_le] <;> simp [BitVec.le_def] <;> omega
  simp only [Word.iszero, Word.slt, Word.ofBool, BitVec.slt_eq_ult, BitVec.msb_eq_decide, hx,
    BitVec.ult, BitVec.toNat_ofNat]
  simp (disch := omega) [Nat.mod_eq_of_lt]
  rw [decide_eq_false (by omega), decide_eq_false (by omega), decide_eq_true (by omega)]
  decide

/-! ## Function shapes -/

/-- The vault's functions with arguments: selector, number of argument words, positions of the
`address` arguments. -/
def vaultArgShapes : List (Nat × Nat × List Nat) :=
  [(0xdd62ed3e, 2, [0, 1]), (0x095ea7b3, 2, [0]), (0x70a08231, 1, [0]), (0x07a2d13a, 1, []),
    (0xc6e6f592, 1, []), (0x6e553f65, 2, [1]), (0x402d267d, 1, [0]), (0xc63d75b6, 1, [0]),
    (0xd905777e, 1, [0]), (0xce96cb77, 1, [0]), (0x94bf804d, 2, [1]), (0x7ecebe00, 1, [0]),
    (0xd505accf, 7, [0, 1]), (0xef8b30f7, 1, []), (0xb3d7f6b9, 1, []), (0x4cdad506, 1, []),
    (0x0a28a477, 1, []), (0xba087652, 3, [1, 2]), (0xa9059cbb, 2, [0]), (0x23b872dd, 3, [0, 1]),
    (0xb460af94, 3, [1, 2])]

/-- The asset's functions with arguments: selector, number of argument words, positions of the
`address` arguments. -/
def assetArgShapes : List (Nat × Nat × List Nat) :=
  [(0xdd62ed3e, 2, [0, 1]), (0x095ea7b3, 2, [0]), (0x70a08231, 1, [0]), (0x9dc29fac, 2, [0]),
    (0x40c10f19, 2, [0]), (0x7ecebe00, 1, [0]), (0xd505accf, 7, [0, 1]), (0xa9059cbb, 2, [0]),
    (0x23b872dd, 3, [0, 1])]

end Examples.Solmate.ERC4626

end
