import Verified.WeirdERC20.AMPL.Spec.Owner

/-!
# AMPL under the spec: `rebase(epoch, Δ)`, the bytecode runs

`rebase(epoch, supplyDelta)` (`onlyMonetaryPolicy`: the caller is the address part of slot
155): `Δ = 0` returns the supply and changes nothing; otherwise the supply moves by the signed
`Δ` with `SafeMath` (`SafeMathInt.abs` rejecting `−2²⁵⁵`), is capped at `2¹²⁸ − 1`, and
`_gonsPerFragment` becomes `TOTAL_GONS / supply` (`SafeMath.div`, rejecting supply `0`).
`rebaseW` is the new supply before the cap as the code computes it on words.
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-- `MAX_SUPPLY = 2¹²⁸ − 1`. -/
abbrev capW : Word := 340282366920938463463374607431768211455#256

/-- `TOTAL_GONS`. -/
abbrev gonsW : Word :=
  115792089237316195423570985008687907853269984665640564039457550000000000000000#256

/-- `−2²⁵⁵` as a word. -/
abbrev minW : Word :=
  57896044618658097711785492504343953926634992332820282019728792003956564819968#256

/-- `rebase`'s new supply before the cap, on words, as the code computes it: `S − |Δ|` for a
negative `Δ` (failing at `−2²⁵⁵` and below `0`), `Δ + S` otherwise (failing above `2²⁵⁶ − 1`). -/
def rebaseW (S d : Word) : Option Word :=
  if 2 ^ 255 ≤ d.toNat then
    if d.toNat = 2 ^ 255 then none
    else if S.toNat < (0#256 - d).toNat then none else some (S - (0#256 - d))
  else if 2 ^ 256 ≤ d.toNat + S.toNat then none else some (d + S)

theorem slt_one {d : Word} (h : 2 ^ 255 ≤ d.toNat) : Word.slt d 0#256 = 1 := by
  have : BitVec.slt d 0#256 = true := by
    simp [BitVec.slt, BitVec.toInt_eq_toNat_cond]; omega
  simp [Word.slt, Word.ofBool, this]

theorem slt_zero {d : Word} (h : d.toNat < 2 ^ 255) : Word.slt d 0#256 = 0 := by
  have : BitVec.slt d 0#256 = false := by
    simp [BitVec.slt, BitVec.toInt_eq_toNat_cond]; omega
  simp [Word.slt, Word.ofBool, this]

theorem neg_of_slt {d : Word} (h : (Word.slt d 0#256).iszero = 0) : 2 ^ 255 ≤ d.toNat := by
  by_contra hc
  rw [slt_zero (Nat.lt_of_not_le hc)] at h
  exact absurd h (by decide)

theorem neg_of_slt' {d : Word} (h : Word.slt d 0#256 ≠ 0) : 2 ^ 255 ≤ d.toNat := by
  by_contra hc
  exact h (slt_zero (Nat.lt_of_not_le hc))

theorem nonneg_of_slt {d : Word} (h : (Word.slt d 0#256).iszero ≠ 0) : d.toNat < 2 ^ 255 := by
  by_contra hc
  rw [slt_one (Nat.le_of_not_lt hc)] at h
  exact h (by decide)

theorem ne_min_of {d : Word} (h : (d.eq minW).iszero ≠ 0) : d.toNat ≠ 2 ^ 255 := by
  intro e
  have : d = minW := BitVec.eq_of_toNat_eq (by rw [e]; rfl)
  subst this
  exact h (by decide)

theorem eq_min_one {d : Word} (h : d.toNat ≠ 2 ^ 255) : (d.eq minW).iszero = 1 := by
  have : d ≠ minW := fun e => h (by subst e; rfl)
  have h' : (d == minW) = false := by simpa using this
  simp [Word.eq, Word.ofBool, Word.iszero, h']

theorem rebaseW_neg {S d : Word} (hn : 2 ^ 255 ≤ d.toNat) (hm : d.toNat ≠ 2 ^ 255)
    (hs : (0#256 - d).toNat ≤ S.toNat) : rebaseW S d = some (S - (0#256 - d)) := by
  unfold rebaseW
  rw [ite_pos' hn, ite_neg' hm, ite_neg' (Nat.not_lt.2 hs)]

theorem rebaseW_pos {S d : Word} (hn : d.toNat < 2 ^ 255) (hf : d.toNat + S.toNat < 2 ^ 256) :
    rebaseW S d = some (d + S) := by
  unfold rebaseW
  rw [ite_neg' (Nat.not_le.2 hn), ite_neg' (Nat.not_le.2 hf)]

theorem rebaseW_min {S d : Word} (hn : d.toNat = 2 ^ 255) : rebaseW S d = none := by
  unfold rebaseW
  rw [ite_pos' (Nat.le_of_eq hn.symm), ite_pos' hn]

theorem rebaseW_under {S d : Word} (hn : 2 ^ 255 ≤ d.toNat) (hs : S.toNat < (0#256 - d).toNat) :
    rebaseW S d = none := by
  unfold rebaseW
  rw [ite_pos' hn]
  split <;> simp_all

theorem rebaseW_over {S d : Word} (hn : d.toNat < 2 ^ 255) (hf : ¬ d.toNat + S.toNat < 2 ^ 256) :
    rebaseW S d = none := by
  unfold rebaseW
  rw [ite_neg' (Nat.not_le.2 hn), ite_pos' (Nat.le_of_not_lt hf)]

/-- `rebase(epoch, Δ)`'s code-level end. -/
def RebasePost (m : Machine) (d : Word) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.caller ≠ (m.world.sload m.frame.msg.currentTarget 155#256).toAddress → Fails o) ∧
  (m.frame.msg.caller = (m.world.sload m.frame.msg.currentTarget 155#256).toAddress → d = 0 →
    (∃ out, o = .success out) ∧ mf.world = m.world ∧ mf.transient = m.transient ∧
    mf.createdAccounts = m.createdAccounts) ∧
  (m.frame.msg.caller = (m.world.sload m.frame.msg.currentTarget 155#256).toAddress → d ≠ 0 →
    rebaseW (m.world.sload m.frame.msg.currentTarget 156#256) d = none → Fails o) ∧
  (m.frame.msg.caller = (m.world.sload m.frame.msg.currentTarget 155#256).toAddress → d ≠ 0 →
    ∀ S1, rebaseW (m.world.sload m.frame.msg.currentTarget 156#256) d = some S1 →
      (min S1.toNat (2 ^ 128 - 1) = 0 → Fails o) ∧
      (min S1.toNat (2 ^ 128 - 1) ≠ 0 →
        (∃ out, o = .success out) ∧
        (∃ w1 X S2, (w1 = m.world.sstore m.frame.msg.currentTarget 156#256 X ∨
            w1 = (m.world.sstore m.frame.msg.currentTarget 156#256 X).sstore
              m.frame.msg.currentTarget 156#256 capW) ∧
          w1.sload m.frame.msg.currentTarget 156#256 = S2 ∧
          S2.toNat = min S1.toNat (2 ^ 128 - 1) ∧
          mf.world = w1.sstore m.frame.msg.currentTarget 157#256 (Word.div gonsW S2)) ∧
        mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts))

set_option maxHeartbeats 0 in
theorem rebase_low (m : Machine) (e d : Word) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0x7a43e23f [e, d])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (RebasePost m d) := by
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
    Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, World.sload_sstore_self]
  · have hown := owner_of_eq (x := m_world.sload m_msg.currentTarget 155#256)
      (by with_reducible assumption)
    have hd0 : d = 0 := by with_reducible assumption
    exact pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun h => absurd hown h,
      fun _ _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩, fun _ h => absurd hd0 h, fun _ h => absurd hd0 h⟩
  · exfalso
    have h1 : (Word.slt d 0#256).iszero = 0 := by with_reducible assumption
    have h2 : Word.slt d 0#256 = 0 := by with_reducible assumption
    rw [h2] at h1
    exact absurd h1 (by decide)
  · exfalso
    have h1 : (Word.slt d 0#256).iszero = 0 := by with_reducible assumption
    have h2 : Word.slt d 0#256 = 0 := by with_reducible assumption
    rw [h2] at h1
    exact absurd h1 (by decide)
  · have hown := owner_of_eq (x := m_world.sload m_msg.currentTarget 155#256)
      (by with_reducible assumption)
    have hd0 : d ≠ 0 := by with_reducible assumption
    have hn := neg_of_slt (by with_reducible assumption)
    have hm := ne_min_of (by with_reducible assumption)
    have hs := Verified.Solady.Spec.le_of_iszero_gt (v := 0#256 - d)
      (b := m_world.sload m_msg.currentTarget 156#256) (by with_reducible assumption)
    have hcap := ampl_lt_of_iszero_zero (a := capW)
      (b := m_world.sload m_msg.currentTarget 156#256 - (0#256 - d)) (by with_reducible assumption)
    have hW := rebaseW_neg hn hm hs
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ?_
    refine ⟨fun h => absurd hown h, fun _ h => absurd h hd0, fun _ _ h => ?_, fun _ _ S1 h => ?_⟩
    · dsimp only at h
      rw [hW] at h
      cases h
    dsimp only at h ⊢
    rw [hW] at h
    cases h
    have hmin : min (m_world.sload m_msg.currentTarget 156#256 - (0#256 - d)).toNat (2 ^ 128 - 1) = 2 ^ 128 - 1 := by
      have : capW.toNat = 2 ^ 128 - 1 := rfl
      omega
    exact ⟨fun hz => absurd hz (by rw [hmin]; decide), fun _ => ⟨⟨_, rfl⟩,
      ⟨_, _, capW, .inr rfl, by simp, by rw [hmin]; rfl, rfl⟩, rfl, rfl⟩⟩
  · have hown := owner_of_eq (x := m_world.sload m_msg.currentTarget 155#256)
      (by with_reducible assumption)
    have hd0 : d ≠ 0 := by with_reducible assumption
    have hn := neg_of_slt (by with_reducible assumption)
    have hm := ne_min_of (by with_reducible assumption)
    have hs := Verified.Solady.Spec.le_of_iszero_gt (v := 0#256 - d)
      (b := m_world.sload m_msg.currentTarget 156#256) (by with_reducible assumption)
    have hcap := ampl_le_of_lt_iszero (a := capW)
      (b := m_world.sload m_msg.currentTarget 156#256 - (0#256 - d)) (by with_reducible assumption)
    have hW := rebaseW_neg hn hm hs
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ?_
    refine ⟨fun h => absurd hown h, fun _ h => absurd h hd0, fun _ _ h => ?_, fun _ _ S1 h => ?_⟩
    · dsimp only at h
      rw [hW] at h
      cases h
    dsimp only at h ⊢
    rw [hW] at h
    cases h
    have hmin : min (m_world.sload m_msg.currentTarget 156#256 - (0#256 - d)).toNat (2 ^ 128 - 1) = (m_world.sload m_msg.currentTarget 156#256 - (0#256 - d)).toNat := by
      have : capW.toNat = 2 ^ 128 - 1 := rfl
      omega
    have hS2 : m_world.sload m_msg.currentTarget 156#256 - (0#256 - d) ≠ 0 := by with_reducible assumption
    have hpos : (m_world.sload m_msg.currentTarget 156#256 - (0#256 - d)).toNat ≠ 0 := fun h0 => hS2 (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
    exact ⟨fun hz => absurd (hmin ▸ hz) hpos, fun _ => ⟨⟨_, rfl⟩,
      ⟨_, _, m_world.sload m_msg.currentTarget 156#256 - (0#256 - d), .inl rfl, by simp, hmin.symm, rfl⟩, rfl, rfl⟩⟩
  · have hown := owner_of_eq (x := m_world.sload m_msg.currentTarget 155#256)
      (by with_reducible assumption)
    have hd0 : d ≠ 0 := by with_reducible assumption
    have hn := nonneg_of_slt (by with_reducible assumption)
    have hf := ampl_add_ok (S := d) (v := m_world.sload m_msg.currentTarget 156#256)
      (by with_reducible assumption)
    have hcap := ampl_lt_of_iszero_zero (a := capW)
      (b := d + m_world.sload m_msg.currentTarget 156#256) (by with_reducible assumption)
    have hW := rebaseW_pos hn hf
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ?_
    refine ⟨fun h => absurd hown h, fun _ h => absurd h hd0, fun _ _ h => ?_, fun _ _ S1 h => ?_⟩
    · dsimp only at h
      rw [hW] at h
      cases h
    dsimp only at h ⊢
    rw [hW] at h
    cases h
    have hmin : min (d + m_world.sload m_msg.currentTarget 156#256).toNat (2 ^ 128 - 1) = 2 ^ 128 - 1 := by
      have : capW.toNat = 2 ^ 128 - 1 := rfl
      omega
    exact ⟨fun hz => absurd hz (by rw [hmin]; decide), fun _ => ⟨⟨_, rfl⟩,
      ⟨_, _, capW, .inr rfl, by simp, by rw [hmin]; rfl, rfl⟩, rfl, rfl⟩⟩
  · have hown := owner_of_eq (x := m_world.sload m_msg.currentTarget 155#256)
      (by with_reducible assumption)
    have hd0 : d ≠ 0 := by with_reducible assumption
    have hn := nonneg_of_slt (by with_reducible assumption)
    have hf := ampl_add_ok (S := d) (v := m_world.sload m_msg.currentTarget 156#256)
      (by with_reducible assumption)
    have hcap := ampl_le_of_lt_iszero (a := capW)
      (b := d + m_world.sload m_msg.currentTarget 156#256) (by with_reducible assumption)
    have hW := rebaseW_pos hn hf
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ?_
    refine ⟨fun h => absurd hown h, fun _ h => absurd h hd0, fun _ _ h => ?_, fun _ _ S1 h => ?_⟩
    · dsimp only at h
      rw [hW] at h
      cases h
    dsimp only at h ⊢
    rw [hW] at h
    cases h
    have hmin : min (d + m_world.sload m_msg.currentTarget 156#256).toNat (2 ^ 128 - 1) = (d + m_world.sload m_msg.currentTarget 156#256).toNat := by
      have : capW.toNat = 2 ^ 128 - 1 := rfl
      omega
    have hS2 : d + m_world.sload m_msg.currentTarget 156#256 ≠ 0 := by with_reducible assumption
    have hpos : (d + m_world.sload m_msg.currentTarget 156#256).toNat ≠ 0 := fun h0 => hS2 (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
    exact ⟨fun hz => absurd (hmin ▸ hz) hpos, fun _ => ⟨⟨_, rfl⟩,
      ⟨_, _, d + m_world.sload m_msg.currentTarget 156#256, .inl rfl, by simp, hmin.symm, rfl⟩, rfl, rfl⟩⟩

set_option maxHeartbeats 0 in
theorem rebase_high (m : Machine) (e d : Word) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0x7a43e23f [e, d])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (RebasePost m d) := by
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
  by_cases hown : m_msg.caller = (m_world.sload m_msg.currentTarget 155#256).toAddress
  swap
  · have h1 := eq_addr_zero hown
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, World.sload_sstore_self]
    exact ⟨fun _ => trivial, fun h => absurd h hown, fun h => absurd h hown, fun h => absurd h hown⟩
  have h1 := eq_addr_one hown
  by_cases hd0 : d = 0
  · subst hd0
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, World.sload_sstore_self]
    exact ⟨fun h => absurd hown h, fun _ _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩, fun _ h => absurd rfl h,
      fun _ h => absurd rfl h⟩
  by_cases hn : 2 ^ 255 ≤ d.toNat
  · have h2 := slt_one hn
    by_cases hm : d.toNat = 2 ^ 255
    · have hdm : d = minW := BitVec.eq_of_toNat_eq (by rw [hm]; rfl)
      have hW := rebaseW_min (S := m_world.sload m_msg.currentTarget 156#256) hm
      subst hdm
      pwp_steps [h2, hval, hst, hsel', hz, hl, harg0, harg1, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, World.sload_sstore_self]
      refine ⟨fun h => absurd hown h, fun _ h => absurd h hd0, fun _ _ _ => trivial, fun _ _ S1 h => ?_⟩
      dsimp only at h
      rw [hW] at h
      cases h
    have h3 := eq_min_one hm
    by_cases hs : (m_world.sload m_msg.currentTarget 156#256).toNat < (0#256 - d).toNat
    · have h4 := Verified.Solady.Spec.iszero_gt_of_lt hs
      have hW := rebaseW_under hn hs
      pwp_steps [hd0, h2, h3, h4, hval, hst, hsel', hz, hl, harg0, harg1, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, World.sload_sstore_self]
      refine ⟨fun h => absurd hown h, fun _ h => absurd h hd0, fun _ _ _ => trivial, fun _ _ S1 h => ?_⟩
      dsimp only at h
      rw [hW] at h
      cases h
    have h4 := Verified.Solady.Spec.iszero_gt_of_le (Nat.le_of_not_lt hs)
    have hW := rebaseW_neg hn hm (Nat.le_of_not_lt hs)
    by_cases hcap : capW.toNat < (m_world.sload m_msg.currentTarget 156#256 - (0#256 - d)).toNat
    · have h7 := ampl_lt_iszero_zero (a := capW) (b := m_world.sload m_msg.currentTarget 156#256 - (0#256 - d)) hcap
      have h8 := ampl_gt_zero_one (x := capW) (by decide)
      pwp_xsteps [hd0, h2, h3, h4, h7, h8, hval, hst, hsel', hz, hl, harg0, harg1, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, World.sload_sstore_self]
      have hmin : min (m_world.sload m_msg.currentTarget 156#256 - (0#256 - d)).toNat (2 ^ 128 - 1) = 2 ^ 128 - 1 := by
        have : capW.toNat = 2 ^ 128 - 1 := rfl
        omega
      refine ⟨fun h => absurd hown h, fun _ h => absurd h hd0, fun _ _ h => ?_, fun _ _ S1 h => ?_⟩
      · dsimp only at h
        rw [hW] at h
        cases h
      dsimp only at h ⊢
      rw [hW] at h
      cases h
      exact ⟨fun hz => absurd hz (by rw [hmin]; decide), fun _ => ⟨⟨_, rfl⟩,
        ⟨_, _, capW, .inr rfl, by simp, by rw [hmin]; rfl, rfl⟩, rfl, rfl⟩⟩
    have h7 := ampl_lt_iszero_one (a := capW) (b := m_world.sload m_msg.currentTarget 156#256 - (0#256 - d)) (Nat.le_of_not_lt hcap)
    have hmin : min (m_world.sload m_msg.currentTarget 156#256 - (0#256 - d)).toNat (2 ^ 128 - 1) = (m_world.sload m_msg.currentTarget 156#256 - (0#256 - d)).toNat := by
      have : capW.toNat = 2 ^ 128 - 1 := rfl
      omega
    by_cases hX : m_world.sload m_msg.currentTarget 156#256 - (0#256 - d) = 0
    · have h8 : m_world.sload m_msg.currentTarget 156#256 - (0#256 - d) = 0 := hX
      pwp_steps [hd0, h2, h3, h4, h7, h8, hval, hst, hsel', hz, hl, harg0, harg1, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, World.sload_sstore_self]
      refine ⟨fun h => absurd hown h, fun _ h => absurd h hd0, fun _ _ _ => trivial, fun _ _ S1 h => ?_⟩
      dsimp only at h ⊢
      rw [hW] at h
      cases h
      refine ⟨fun _ => trivial, fun hne => absurd ?_ hne⟩
      rw [hmin, hX]
      rfl
    have h8 := ampl_gt_zero_one hX
    pwp_xsteps [hd0, h2, h3, h4, h7, h8, hX, hval, hst, hsel', hz, hl, harg0, harg1, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, World.sload_sstore_self]
    have hpos : (m_world.sload m_msg.currentTarget 156#256 - (0#256 - d)).toNat ≠ 0 := fun h0 => hX (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
    refine ⟨fun h => absurd hown h, fun _ h => absurd h hd0, fun _ _ h => ?_, fun _ _ S1 h => ?_⟩
    · dsimp only at h
      rw [hW] at h
      cases h
    dsimp only at h ⊢
    rw [hW] at h
    cases h
    exact ⟨fun hz => absurd (hmin ▸ hz) hpos, fun _ => ⟨⟨_, rfl⟩,
      ⟨_, _, m_world.sload m_msg.currentTarget 156#256 - (0#256 - d), .inl rfl, by simp, hmin.symm, rfl⟩, rfl, rfl⟩⟩
  have h2 := slt_zero (Nat.lt_of_not_le hn)
  by_cases hfit : d.toNat + (m_world.sload m_msg.currentTarget 156#256).toNat < 2 ^ 256
  swap
  · have h4 := ampl_add_lt_zero (Nat.le_of_not_lt hfit)
    have hW := rebaseW_over (Nat.lt_of_not_le hn) hfit
    pwp_steps [hd0, h2, h4, hval, hst, hsel', hz, hl, harg0, harg1, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, World.sload_sstore_self]
    refine ⟨fun h => absurd hown h, fun _ h => absurd h hd0, fun _ _ _ => trivial, fun _ _ S1 h => ?_⟩
    dsimp only at h
    rw [hW] at h
    cases h
  have h4 := ampl_add_lt_one hfit
  have hW := rebaseW_pos (Nat.lt_of_not_le hn) hfit
  by_cases hcap : capW.toNat < (d + m_world.sload m_msg.currentTarget 156#256).toNat
  · have h7 := ampl_lt_iszero_zero (a := capW) (b := d + m_world.sload m_msg.currentTarget 156#256) hcap
    have h8 := ampl_gt_zero_one (x := capW) (by decide)
    pwp_xsteps [hd0, h2, h4, h7, h8, hval, hst, hsel', hz, hl, harg0, harg1, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, World.sload_sstore_self]
    have hmin : min (d + m_world.sload m_msg.currentTarget 156#256).toNat (2 ^ 128 - 1) = 2 ^ 128 - 1 := by
      have : capW.toNat = 2 ^ 128 - 1 := rfl
      omega
    refine ⟨fun h => absurd hown h, fun _ h => absurd h hd0, fun _ _ h => ?_, fun _ _ S1 h => ?_⟩
    · dsimp only at h
      rw [hW] at h
      cases h
    dsimp only at h ⊢
    rw [hW] at h
    cases h
    exact ⟨fun hz => absurd hz (by rw [hmin]; decide), fun _ => ⟨⟨_, rfl⟩,
      ⟨_, _, capW, .inr rfl, by simp, by rw [hmin]; rfl, rfl⟩, rfl, rfl⟩⟩
  have h7 := ampl_lt_iszero_one (a := capW) (b := d + m_world.sload m_msg.currentTarget 156#256) (Nat.le_of_not_lt hcap)
  have hmin : min (d + m_world.sload m_msg.currentTarget 156#256).toNat (2 ^ 128 - 1) = (d + m_world.sload m_msg.currentTarget 156#256).toNat := by
    have : capW.toNat = 2 ^ 128 - 1 := rfl
    omega
  by_cases hX : d + m_world.sload m_msg.currentTarget 156#256 = 0
  · have h8 : d + m_world.sload m_msg.currentTarget 156#256 = 0 := hX
    have h4' := h4
    rw [hX] at h4'
    pwp_steps [hd0, h2, h4, h4', h7, h8, hval, hst, hsel', hz, hl, harg0, harg1, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, World.sload_sstore_self]
    refine ⟨fun h => absurd hown h, fun _ h => absurd h hd0, fun _ _ _ => trivial, fun _ _ S1 h => ?_⟩
    dsimp only at h ⊢
    rw [hW] at h
    cases h
    refine ⟨fun _ => trivial, fun hne => absurd ?_ hne⟩
    rw [hmin, hX]
    rfl
  have h8 := ampl_gt_zero_one hX
  pwp_xsteps [hd0, h2, h4, h7, h8, hX, hval, hst, hsel', hz, hl, harg0, harg1, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, World.sload_sstore_self]
  have hpos : (d + m_world.sload m_msg.currentTarget 156#256).toNat ≠ 0 := fun h0 => hX (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  refine ⟨fun h => absurd hown h, fun _ h => absurd h hd0, fun _ _ h => ?_, fun _ _ S1 h => ?_⟩
  · dsimp only at h
    rw [hW] at h
    cases h
  dsimp only at h ⊢
  rw [hW] at h
  cases h
  exact ⟨fun hz => absurd (hmin ▸ hz) hpos, fun _ => ⟨⟨_, rfl⟩,
    ⟨_, _, d + m_world.sload m_msg.currentTarget 156#256, .inl rfl, by simp, hmin.symm, rfl⟩, rfl, rfl⟩⟩

end Verified.WeirdERC20.AMPL.Spec
