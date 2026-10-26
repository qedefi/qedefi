import Verified.WeirdERC20.STA.Spec.Transfer

/-!
# STA under the spec: `transferFrom`, the bytecode runs

`transferFrom(src, dst, v)` of Statera: `require(v ≤ bal[src])`, `require(v ≤ allowed[src][caller])`,
`require(dst ≠ 0)`, the debit, `cut(v)` (reading `basePercent` after the debit), the credit of
`v − cut(v)`, the burn from the supply, then the allowance lowered (read after those writes),
two `Transfer`s, `true`.
-/

namespace Verified.WeirdERC20.STA.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.STA.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-- The `_allowed` row of `o` for `sp` (slot 4). -/
abbrev allowSlot (crypto : Crypto) (o sp : Address) : Word :=
  mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 4#256

/-- The world after `transferFrom`: the move, then the allowance row lowered by `v` (read after
the move). -/
def tfWorld (crypto : Crypto) (w : World) (t c src dst : Address) (v fee : Word) : World :=
  (staMoveWorld crypto w t src dst v fee).sstore t (allowSlot crypto src c)
    ((staMoveWorld crypto w t src dst v fee).sload t (allowSlot crypto src c) - v)

/-- `transferFrom(src, dst, v)`'s code-level end (`basePercent = 100` after the debit assumed
where it matters): a value or the checks revert; an overflow computing the fee is an
exceptional halt; otherwise (when the credit fits, the supply covers the fee and the allowance
read after the move covers `v`) the move, the allowance lowered, `true`, the two `Transfer`s. -/
def TFPost (m : Machine) (src dst : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.value ≠ 0 → ∃ out, o = .revert out) ∧
  (dst = 0 ∨
    (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat < v.toNat ∨
    (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat
      < v.toNat → ∃ out, o = .revert out) ∧
  (dst ≠ 0 → v.toNat ≤ (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat →
    v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat →
    (debitWorld m.ctx.crypto m.world m.frame.msg.currentTarget src v).sload
      m.frame.msg.currentTarget 6#256 = 100#256 →
    2 ^ 256 ≤ v.toNat + 100 ∨ 2 ^ 256 ≤ (v.toNat + 100 - 1) / 100 * 100 * 100 →
    ∃ e, o = .halt e) ∧
  (dst ≠ 0 → v.toNat ≤ (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat →
    v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat →
    (debitWorld m.ctx.crypto m.world m.frame.msg.currentTarget src v).sload
      m.frame.msg.currentTarget 6#256 = 100#256 →
    v.toNat + 100 < 2 ^ 256 → (v.toNat + 100 - 1) / 100 * 100 * 100 < 2 ^ 256 →
    ((debitWorld m.ctx.crypto m.world m.frame.msg.currentTarget src v).sload
      m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat + (v.toNat - cutN v.toNat) <
        2 ^ 256 →
    cutN v.toNat ≤ ((creditWorld m.ctx.crypto m.world m.frame.msg.currentTarget src
      dst v (word (cutN v.toNat))).sload m.frame.msg.currentTarget 5#256).toNat →
    v.toNat ≤ ((staMoveWorld m.ctx.crypto m.world m.frame.msg.currentTarget src dst v
      (word (cutN v.toNat))).sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = tfWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src dst
      v (word (cutN v.toNat)) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = (m.frame.sub.logs.push (transferLog m.frame.msg.currentTarget
      src dst (v - word (cutN v.toNat)))).push
        (transferLog m.frame.msg.currentTarget src 0 (word (cutN v.toNat))))

set_option maxHeartbeats 0 in
theorem transferFrom_low (m : Machine) (src dst : Address) (v : Word)
    (hf : Fresh STA.runtimeCode m)
    (hd : Args m.frame.msg.data 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (TFPost m src dst v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  have harg2 := harg 2 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1 harg2
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, harg2, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  all_goals
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    have hd0 := ne_zero_of_iszero2 (by with_reducible assumption)
    have hbc := Verified.Solady.Spec.le_of_iszero_gt (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 3#256)))
      (by with_reducible assumption)
    have hac := Verified.Solady.Spec.le_of_iszero_gt (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 4#256)))))
      (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
      ⟨fun h => absurd hv h, fun h => ?_, fun _ _ _ hbp hov => ?_,
        fun _ _ _ hbp _ _ _ _ _ => ?_⟩
    · rcases h with h | h | h
      · exact absurd h hd0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
      · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)
    · have hbp' : (m_world.sstore m_msg.currentTarget
          (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 3#256))
          (m_world.sload m_msg.currentTarget
            (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 3#256)) -
              v)).sload m_msg.currentTarget 6#256 = 100#256 := hbp
      first
      | exact absurd hov (by
          obtain ⟨h1, h2, -⟩ := sta_leaf1 hbp' (by with_reducible assumption)
            (by with_reducible assumption)
          omega)
      | exact (sta_leaf2 hbp' (by with_reducible assumption) (by with_reducible assumption)
          (by with_reducible assumption) (by with_reducible assumption)).elim
      | exact absurd hov (by
          obtain ⟨h1, h2, -⟩ := sta_leaf3 hbp' (by with_reducible assumption)
            (by with_reducible assumption) (by with_reducible assumption)
          omega)
    have hbp' : (m_world.sstore m_msg.currentTarget
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 3#256))
        (m_world.sload m_msg.currentTarget
          (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 3#256)) -
            v)).sload m_msg.currentTarget 6#256 = 100#256 := hbp
  · obtain ⟨-, -, hfee⟩ := sta_leaf1 hbp' (by with_reducible assumption)
      (by with_reducible assumption)
    refine ⟨hv, ‹_›, ?_, ?_, rfl, rfl, ?_⟩
    · simp only [outputData]
      apwp_norm []
      rfl
    · rw [hfee]
      rfl
    · simp only [outputMachine]
      logs_simp []
      rw [logEntry_eq_eventLog (data := [v - word (cutN v.toNat)]),
        logEntry_eq_eventLog (data := [word (cutN v.toNat)])]
      · rfl
      all_goals (rw [hfee]; event_data)
  · exact (sta_leaf2 hbp' (by with_reducible assumption) (by with_reducible assumption)
      (by with_reducible assumption) (by with_reducible assumption)).elim
  · obtain ⟨-, -, hfee⟩ := sta_leaf3 hbp' (by with_reducible assumption)
      (by with_reducible assumption) (by with_reducible assumption)
    refine ⟨hv, ‹_›, ?_, ?_, rfl, rfl, ?_⟩
    · simp only [outputData]
      apwp_norm []
      rfl
    · rw [hfee]
      rfl
    · simp only [outputMachine]
      logs_simp []
      rw [logEntry_eq_eventLog (data := [v - word (cutN v.toNat)]),
        logEntry_eq_eventLog (data := [word (cutN v.toNat)])]
      · rfl
      all_goals (rw [hfee]; event_data)

theorem sta_gt_zero' (X : Word) : (Word.gt 0 X).iszero = 1 :=
  Verified.Solady.Spec.iszero_gt_of_le (Nat.zero_le _)

set_option maxHeartbeats 0 in
theorem transferFrom_high (m : Machine) (src dst : Address) (v : Word)
    (hf : Fresh STA.runtimeCode m)
    (hd : Args m.frame.msg.data 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft)
    (hbp : (debitWorld m.ctx.crypto m.world m.frame.msg.currentTarget src v).sload
      m.frame.msg.currentTarget 6#256 = 100#256) :
    Halts m (TFPost m src dst v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  have harg2 := harg 2 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1 harg2
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 96) (by omega) hsz
  simp only [g₀] at hg
  simp only [debitWorld, balSlot, mappingSlot] at hbp
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hbc : v.toNat ≤ (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto src)).toNat
  swap
  · have h1 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le hbc)
    simp only [balSlot, mappingSlot] at h1
    pwp_steps [hval, hst, hsel', hz, hl, h1, harg0, harg1, harg2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ h => absurd h hbc,
      fun _ h => absurd h hbc⟩
  have h1 := Verified.Solady.Spec.iszero_gt_of_le hbc
  simp only [balSlot, mappingSlot] at h1
  by_cases hac : v.toNat ≤
      (m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto src m_msg.caller)).toNat
  swap
  · have h1a := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le hac)
    simp only [allowSlot, mappingSlot2, mappingSlot] at h1a
    pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, harg0, harg1, harg2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ h => absurd h hac,
      fun _ _ h => absurd h hac⟩
  have h1a := Verified.Solady.Spec.iszero_gt_of_le hac
  simp only [allowSlot, mappingSlot2, mappingSlot] at h1a
  by_cases hd0 : dst = 0
  · subst hd0
    have h2 : (Word.ofAddress (0 : Address)).iszero.iszero = 0 := by decide
    pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun h => absurd rfl h, fun h => absurd rfl h⟩
  have h2 := iszero2_of_ne hd0
  pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  by_cases hov : 2 ^ 256 ≤ (100#256 : Word).toNat + v.toNat
  · have h3 := sta_add_lt_zero hov
    pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, harg0, harg1, harg2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    rw [h3]
    pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, harg0, harg1, harg2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _)
      ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ _ => ⟨_, rfl⟩, fun _ _ _ _ h => ?_⟩
    · rcases h with h | h | h
      · exact absurd h hd0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
      · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)
    · simp at hov; omega
  have h3 := sta_add_lt_one (Nat.lt_of_not_le hov)
  have h4 := sta_gt_one_iszero (x := 100#256 + v) (by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (Nat.lt_of_not_le hov)]; simp; omega)
  have h5 : Word.iszero (Word.iszero (100#256 : Word)) = 1 := by decide
  by_cases hv0 : v = 0
  · subst hv0
    pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    rw [sta_zero_add_lt]
    pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    rw [sta_gt_zero]
    pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    rw [sta_gt_zero']
    pwp_xsteps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    have hc0 : word (cutN (BitVec.toNat (0 : Word))) = 0#256 := by decide
    refine ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ h => absurd h (by simp), fun _ _ _ _ _ _ _ _ _ =>
      ⟨hval, hst, rfl, ?_, rfl, rfl, ?_⟩⟩
    · rcases h with h | h | h
      · exact absurd h hd0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
      · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)
    · simp only [outputMachine, tfWorld, staMoveWorld, creditWorld, debitWorld, hc0, BitVec.sub_zero]
      rfl
    · simp only [outputMachine, hc0, BitVec.sub_zero]
      logs_simp []
      rw [logEntry_eq_eventLog (data := [0#256]), logEntry_eq_eventLog (data := [0#256])]
      · rfl
      all_goals event_data
  pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  rw [h3]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  have hq := sta_q_toNat (v := v) (by simp at hov; omega)
  have hvp : 0 < v.toNat := by
    rcases Nat.eq_zero_or_pos v.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simp [h])) hv0
    · exact h
  have h6 := sta_iszero2_of_pos (x := Word.div (100#256 + v - 1#256) 100#256) (by rw [hq]; omega)
  rw [h6]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, h6, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  have hvq : (v.toNat + 99) / 100 * 100 ≤ v.toNat + 99 := Nat.div_mul_le_self _ _
  have h7 := sta_mul_eq_one (a := Word.div (100#256 + v - 1#256) 100#256) (b := 100#256)
    (by rw [hq]; omega) (by rw [hq]; simp at hov ⊢; omega)
  rw [h7]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, h6, h7, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  have hr : (100#256 * Word.div (100#256 + v - 1#256) 100#256).toNat =
      100 * ((v.toNat + 99) / 100) := by
    rw [BitVec.toNat_mul, hq, Nat.mod_eq_of_lt (by simp at hov ⊢; omega)]; simp
  have h8 := sta_iszero2_of_pos (x := 100#256 * Word.div (100#256 + v - 1#256) 100#256)
    (by rw [hr]; omega)
  rw [h8]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, h6, h7, h8, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  by_cases hov2 : 2 ^ 256 ≤ (v.toNat + 100 - 1) / 100 * 100 * 100
  · have h9 := sta_mul_eq_zero (a := 100#256 * Word.div (100#256 + v - 1#256) 100#256)
      (b := 100#256) (by rw [hr]; omega) (by rw [hr]; simp; omega)
    rw [h9]
    pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, h6, h7, h8, h9, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _)
      ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ _ => ⟨_, rfl⟩, fun _ _ _ _ _ h => ?_⟩
    · rcases h with h | h | h
      · exact absurd h hd0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
      · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)
    · omega
  have h9 := sta_mul_eq_one (a := 100#256 * Word.div (100#256 + v - 1#256) 100#256)
    (b := 100#256) (by rw [hr]; omega) (by rw [hr]; simp; omega)
  rw [h9]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, h6, h7, h8, h9, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  have hF := sta_fee_eq (by simp at hov; omega) (Nat.lt_of_not_le hov2)
  have hcw : (word (cutN v.toNat)).toNat = cutN v.toNat := by
    rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (sta_cutN_lt v.isLt)]
  have h10 := Verified.Solady.Spec.iszero_gt_of_le (v := word (cutN v.toNat)) (b := v)
    (by rw [hcw]; exact sta_cutN_le _)
  rw [hF, h10]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, h6, h7, h8, h9, h10, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  have hsubw : (v - word (cutN v.toNat)).toNat = v.toNat - cutN v.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hcw]; exact sta_cutN_le _), hcw]
  by_cases hfit : ((debitWorld m_ctx.crypto m_world m_msg.currentTarget src v).sload
      m_msg.currentTarget (balSlot m_ctx.crypto dst)).toNat + (v.toNat - cutN v.toNat) < 2 ^ 256
  swap
  · have h11 := sta_add_lt_zero (S := v - word (cutN v.toNat))
      (v := (debitWorld m_ctx.crypto m_world m_msg.currentTarget src v).sload
        m_msg.currentTarget (balSlot m_ctx.crypto dst)) (by rw [hsubw]; omega)
    simp only [debitWorld, balSlot, mappingSlot] at h11
    rw [h11]
    pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, h6, h7, h8, h9, h10, harg0,
      harg1, harg2, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _)
      ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ h => absurd h (by simp at hov; omega), fun _ _ _ _ _ _ h => absurd h hfit⟩
    · rcases h with h | h | h
      · exact absurd h hd0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
      · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)
  have h11 := sta_add_lt_one (S := v - word (cutN v.toNat))
    (v := (debitWorld m_ctx.crypto m_world m_msg.currentTarget src v).sload
      m_msg.currentTarget (balSlot m_ctx.crypto dst)) (by rw [hsubw]; omega)
  simp only [debitWorld, balSlot, mappingSlot] at h11
  rw [h11]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, h6, h7, h8, h9, h10, h11, harg0,
    harg1, harg2, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  by_cases hsup : cutN v.toNat ≤ ((creditWorld m_ctx.crypto m_world m_msg.currentTarget
      src dst v (word (cutN v.toNat))).sload m_msg.currentTarget 5#256).toNat
  swap
  · have h12 := Verified.Solady.Spec.iszero_gt_of_lt (v := word (cutN v.toNat))
      (b := (creditWorld m_ctx.crypto m_world m_msg.currentTarget
      src dst v (word (cutN v.toNat))).sload m_msg.currentTarget 5#256)
      (by rw [hcw]; omega)
    simp only [creditWorld, debitWorld, balSlot, mappingSlot] at h12
    rw [h12]
    pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, h6, h7, h8, h9, h10, h11, harg0,
      harg1, harg2, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _)
      ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ h => absurd h (by simp at hov; omega), fun _ _ _ _ _ _ _ h => absurd h hsup⟩
    · rcases h with h | h | h
      · exact absurd h hd0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
      · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)
  have h12 := Verified.Solady.Spec.iszero_gt_of_le (v := word (cutN v.toNat))
    (b := (creditWorld m_ctx.crypto m_world m_msg.currentTarget
    src dst v (word (cutN v.toNat))).sload m_msg.currentTarget 5#256)
    (by rw [hcw]; omega)
  simp only [creditWorld, debitWorld, balSlot, mappingSlot] at h12
  rw [h12]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    harg0, harg1, harg2, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  by_cases ha3 : v.toNat ≤ ((staMoveWorld m_ctx.crypto m_world m_msg.currentTarget src dst v
      (word (cutN v.toNat))).sload m_msg.currentTarget (allowSlot m_ctx.crypto src m_msg.caller)).toNat
  swap
  · have h13 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le ha3)
    simp only [staMoveWorld, creditWorld, debitWorld, balSlot, allowSlot, mappingSlot2,
      mappingSlot] at h13
    rw [h13]
    pwp_steps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, harg0, harg1, harg2, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _)
      ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ h => absurd h (by simp at hov; omega),
        fun _ _ _ _ _ _ _ _ h => absurd h ha3⟩
    · rcases h with h | h | h
      · exact absurd h hd0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
      · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)
  have h13 := Verified.Solady.Spec.iszero_gt_of_le ha3
  simp only [staMoveWorld, creditWorld, debitWorld, balSlot, allowSlot, mappingSlot2,
    mappingSlot] at h13
  rw [h13]
  pwp_xsteps [hval, hst, hsel', hz, hl, h1, h1a, h2, hbp, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    harg0, harg1, harg2, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ h => absurd h (by simp at hov; omega),
    fun _ _ _ _ _ _ _ _ _ => ⟨hval, hst, rfl, ?_, rfl, rfl, ?_⟩⟩
  · rcases h with h | h | h
    · exact absurd h hd0
    · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
    · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)
  · simp only [outputMachine]
    rfl
  · simp only [outputMachine]
    logs_simp []
    rw [logEntry_eq_eventLog (data := [v - word (cutN v.toNat)]),
      logEntry_eq_eventLog (data := [word (cutN v.toNat)])]
    · rfl
    all_goals event_data


end Verified.WeirdERC20.STA.Spec
