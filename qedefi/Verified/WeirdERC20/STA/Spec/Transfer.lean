import Verified.WeirdERC20.STA.Spec.Approve
import EvmLogic.Tactic.StepExt

/-!
# STA under the spec: `transfer`
-/

namespace Verified.WeirdERC20.STA.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.STA.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-- The `_balances` row of `a` (slot 3). -/
abbrev balSlot (crypto : Crypto) (a : Address) : Word := mappingSlot crypto (Word.ofAddress a) 3#256

/-- `cut(v)` with `basePercent = 100`: `⌈v/100⌉`, as the model's fee. -/
def cutN (v : ℕ) : ℕ := (v + 100 - 1) / 100 * 100 * 100 / 10000

theorem sta_add_lt_one {S v : Word} (h : S.toNat + v.toNat < 2 ^ 256) :
    ((S + v).lt v).iszero = 1 := by
  have hm : (S.toNat + v.toNat) % 2 ^ 256 = S.toNat + v.toNat := Nat.mod_eq_of_lt h
  simp only [Word.lt, Word.ofBool, BitVec.ult, BitVec.toNat_add, hm, Word.iszero]
  have : ¬ S.toNat + v.toNat < v.toNat := by omega
  simp [this]

theorem sta_add_lt_zero {S v : Word} (h : 2 ^ 256 ≤ S.toNat + v.toNat) :
    ((S + v).lt v).iszero = 0 := by
  have hS := S.isLt
  have hm : (S.toNat + v.toNat) % 2 ^ 256 = S.toNat + v.toNat - 2 ^ 256 := by
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  simp only [Word.lt, Word.ofBool, BitVec.ult, BitVec.toNat_add, hm, Word.iszero]
  have : S.toNat + v.toNat - 2 ^ 256 < v.toNat := by omega
  simp only [this, decide_true, ite_true, beq_iff_eq]
  decide

theorem sta_gt_one_iszero {x : Word} (h : 1 ≤ x.toNat) : (Word.gt 1#256 x).iszero = 1 := by
  have : ¬ x.toNat < 1 := by omega
  simp [Word.gt, Word.ofBool, Word.iszero, BitVec.ult, this]

theorem sta_iszero2_of_pos {x : Word} (h : 0 < x.toNat) : x.iszero.iszero = 1 := by
  have : x ≠ 0 := fun e => by subst e; simp at h
  have h' : (x == 0#256) = false := by simpa using this
  simp [Word.iszero, Word.ofBool, h']

theorem sta_iszero2_of_zero {x : Word} (h : x.toNat = 0) : x.iszero.iszero = 0 := by
  have : x = 0 := BitVec.eq_of_toNat_eq (by simp [h])
  simp [Word.iszero, Word.ofBool, this]

theorem sta_zero_add_lt (X : Word) : (Word.lt (0#256 + X) X).iszero = 1 :=
  sta_add_lt_one (S := 0#256) (by simp [X.isLt])

theorem sta_q_toNat {v : Word} (h : 100 + v.toNat < 2 ^ 256) :
    (Word.div (100#256 + v - 1#256) 100#256).toNat = (v.toNat + 99) / 100 := by
  have h1 : (100#256 + v).toNat = 100 + v.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simpa using h)]; simp
  have h2 : (100#256 + v - 1#256).toNat = v.toNat + 99 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1]; simp; omega)]; rw [h1]; simp; omega
  simp only [Word.div, BitVec.toNat_udiv, h2]
  rfl

theorem sta_cutN_le (n : ℕ) : cutN n ≤ n := by
  unfold cutN; omega

theorem sta_cutN_lt {n : ℕ} (h : n < 2 ^ 256) : cutN n < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (sta_cutN_le n) h

theorem sta_fee_eq {v : Word} (hov : v.toNat + 100 < 2 ^ 256)
    (hov2 : (v.toNat + 100 - 1) / 100 * 100 * 100 < 2 ^ 256) :
    Word.div (100#256 * (100#256 * Word.div (100#256 + v - 1#256) 100#256)) 10000#256 =
      word (cutN v.toNat) := by
  have e : v.toNat + 100 - 1 = v.toNat + 99 := by omega
  rw [e] at hov2
  have hq := sta_q_toNat (v := v) (by omega)
  have h100 : (100#256 : Word).toNat = 100 := rfl
  have h1 : (100#256 * Word.div (100#256 + v - 1#256) 100#256).toNat =
      100 * ((v.toNat + 99) / 100) := by
    rw [BitVec.toNat_mul, hq, h100]; exact Nat.mod_eq_of_lt (by omega)
  have h2 : (100#256 * (100#256 * Word.div (100#256 + v - 1#256) 100#256)).toNat =
      100 * (100 * ((v.toNat + 99) / 100)) := by
    rw [BitVec.toNat_mul, h1, h100]; exact Nat.mod_eq_of_lt (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (sta_cutN_lt v.isLt)]
  rw [Word.div, BitVec.toNat_udiv, h2, show (10000#256 : Word).toNat = 10000 from rfl]
  unfold cutN
  rw [e]
  omega

theorem sta_gt_zero (X : Word) : (Word.gt 0#256 X).iszero = 1 :=
  Verified.Solady.Spec.iszero_gt_of_le (Nat.zero_le _)

theorem sta_mul_eq_one {a b : Word} (ha : 0 < a.toNat) (h : b.toNat * a.toNat < 2 ^ 256) :
    Word.eq (Word.div (b * a) a) b = 1 := by
  have : Word.div (b * a) a = b := by
    apply BitVec.eq_of_toNat_eq
    simp only [Word.div, BitVec.toNat_udiv, BitVec.toNat_mul, Nat.mod_eq_of_lt h]
    exact Nat.mul_div_cancel _ ha
  simp [Word.eq, Word.ofBool, this]

theorem sta_mul_eq_zero {a b : Word} (ha : 0 < a.toNat) (h : 2 ^ 256 ≤ b.toNat * a.toNat) :
    Word.eq (Word.div (b * a) a) b = 0 := by
  have : Word.div (b * a) a ≠ b := by
    intro e
    have := congrArg BitVec.toNat e
    simp only [Word.div, BitVec.toNat_udiv, BitVec.toNat_mul] at this
    have hlt : (b.toNat * a.toNat) % 2 ^ 256 < b.toNat * a.toNat :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) h
    have : (b.toNat * a.toNat) % 2 ^ 256 / a.toNat < b.toNat :=
      (Nat.div_lt_iff_lt_mul ha).2 hlt
    omega
  have h' : (Word.div (b * a) a == b) = false := by simpa using this
  simp [Word.eq, Word.ofBool, h']

theorem sta_ov1 {b v : Word} (hb : b = 100#256) (h : (Word.lt (b + v) v).iszero ≠ 0) :
    v.toNat + 100 < 2 ^ 256 := by
  subst hb
  by_contra hc
  exact h (sta_add_lt_zero (by simp only [show (100#256 : Word).toNat = 100 from rfl]; omega))

theorem sta_mul_ok {a b : Word} (ha : 0 < a.toNat) (h : Word.eq (Word.div (b * a) a) b ≠ 0) :
    b.toNat * a.toNat < 2 ^ 256 := by
  by_contra hc
  exact h (sta_mul_eq_zero ha (Nat.le_of_not_lt hc))

theorem sta_pos_of_iszero2 {x : Word} (h : x.iszero.iszero ≠ 0) : 0 < x.toNat := by
  rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
  · exact absurd (sta_iszero2_of_zero h0) h
  · exact h0

theorem sta_zero_of_iszero2 {x : Word} (h : x.iszero.iszero = 0) : x.toNat = 0 := by
  by_contra h0
  rw [sta_iszero2_of_pos (Nat.pos_of_ne_zero h0)] at h
  exact absurd h (by decide)

/-- The success path with `⌈(v + bp − 1)/bp⌉ = 0`, at `bp = 100`: `v = 0`, no fee. -/
theorem sta_leaf1 {b v : Word} (hb : b = 100#256) (hadd : (Word.lt (b + v) v).iszero ≠ 0)
    (hq : (Word.div (b + v - 1#256) b).iszero.iszero = 0) :
    v.toNat + 100 < 2 ^ 256 ∧ (v.toNat + 100 - 1) / 100 * 100 * 100 < 2 ^ 256 ∧
      word (cutN v.toNat) = 0#256 := by
  have h1 := sta_ov1 hb hadd
  subst hb
  have hq' := sta_zero_of_iszero2 hq
  rw [sta_q_toNat (by omega)] at hq'
  have hv : v.toNat = 0 := by omega
  refine ⟨h1, by omega, ?_⟩
  rw [hv]; decide

/-- The success path with a zero rounded value, impossible at `bp = 100`. -/
theorem sta_leaf2 {b v : Word} (hb : b = 100#256) (hadd : (Word.lt (b + v) v).iszero ≠ 0)
    (hq : (Word.div (b + v - 1#256) b).iszero.iszero ≠ 0)
    (hm : Word.eq (Word.div (b * Word.div (b + v - 1#256) b) (Word.div (b + v - 1#256) b)) b ≠ 0)
    (hr : (b * Word.div (b + v - 1#256) b).iszero.iszero = 0) : False := by
  have hq' := sta_pos_of_iszero2 hq
  have hm' := sta_mul_ok hq' hm
  have hr' := sta_zero_of_iszero2 hr
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hm'] at hr'
  subst hb
  simp only [show (100#256 : Word).toNat = 100 from rfl] at hr'
  omega

/-- The success path with a positive rounded value, at `bp = 100`: no overflow, the fee is
`cutN v`. -/
theorem sta_leaf3 {b v : Word} (hb : b = 100#256) (hadd : (Word.lt (b + v) v).iszero ≠ 0)
    (hr : (b * Word.div (b + v - 1#256) b).iszero.iszero ≠ 0)
    (hm : Word.eq (Word.div (b * (b * Word.div (b + v - 1#256) b))
      (b * Word.div (b + v - 1#256) b)) b ≠ 0) :
    v.toNat + 100 < 2 ^ 256 ∧ (v.toNat + 100 - 1) / 100 * 100 * 100 < 2 ^ 256 ∧
      word (cutN v.toNat) = Word.div (b * (b * Word.div (b + v - 1#256) b)) 10000#256 := by
  have h1 := sta_ov1 hb hadd
  have hr' := sta_pos_of_iszero2 hr
  have hm' := sta_mul_ok hr' hm
  subst hb
  have hq := sta_q_toNat (v := v) (by omega)
  have h100 : (100#256 : Word).toNat = 100 := rfl
  have hr2 : (100#256 * Word.div (100#256 + v - 1#256) 100#256).toNat =
      100 * ((v.toNat + 99) / 100) := by
    rw [BitVec.toNat_mul, hq, h100]; exact Nat.mod_eq_of_lt (by omega)
  rw [hr2, h100] at hm'
  have h2 : (v.toNat + 100 - 1) / 100 * 100 * 100 < 2 ^ 256 := by
    have e : v.toNat + 100 - 1 = v.toNat + 99 := by omega
    rw [e]; omega
  exact ⟨h1, h2, (sta_fee_eq h1 h2).symm⟩

/-- The world after the debit of `v` from `src`. -/
def debitWorld (crypto : Crypto) (w : World) (t src : Address) (v : Word) : World :=
  w.sstore t (balSlot crypto src) (w.sload t (balSlot crypto src) - v)

/-- The world after the debit of `v` from `src` and the credit of `v − fee` to `dst` (read
after the debit). -/
def creditWorld (crypto : Crypto) (w : World) (t src dst : Address) (v fee : Word) : World :=
  (debitWorld crypto w t src v).sstore t (balSlot crypto dst)
    (v - fee + (debitWorld crypto w t src v).sload t (balSlot crypto dst))

/-- The world after Statera's move of `v` from `src` to `dst` burning `fee`: the debit, the
credit, the supply lowered by `fee`. -/
def staMoveWorld (crypto : Crypto) (w : World) (t src dst : Address) (v fee : Word) : World :=
  (creditWorld crypto w t src dst v fee).sstore t 5#256
    ((creditWorld crypto w t src dst v fee).sload t 5#256 - fee)

/-- `transfer(dst, v)`'s code-level end (`basePercent = 100` assumed where it matters): a
value or the checks revert; an overflow computing the fee is an exceptional halt; otherwise (when the
credit fits and the supply covers the fee) the move, `true`, the two `Transfer` logs. -/
def TransferPost (m : Machine) (dst : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.value ≠ 0 → ∃ out, o = .revert out) ∧
  (dst = 0 ∨ (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat < v.toNat → ∃ out, o = .revert out) ∧
  (dst ≠ 0 → v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat →
    m.world.sload m.frame.msg.currentTarget 6#256 = 100#256 →
    2 ^ 256 ≤ v.toNat + 100 ∨ 2 ^ 256 ≤ (v.toNat + 100 - 1) / 100 * 100 * 100 →
    ∃ e, o = .halt e) ∧
  (dst ≠ 0 → v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat →
    m.world.sload m.frame.msg.currentTarget 6#256 = 100#256 →
    v.toNat + 100 < 2 ^ 256 → (v.toNat + 100 - 1) / 100 * 100 * 100 < 2 ^ 256 →
    ((debitWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller v).sload
      m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat + (v.toNat - cutN v.toNat) <
        2 ^ 256 →
    cutN v.toNat ≤ ((creditWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller
      dst v (word (cutN v.toNat))).sload m.frame.msg.currentTarget 5#256).toNat →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = staMoveWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller dst
      v (word (cutN v.toNat)) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = (m.frame.sub.logs.push (transferLog m.frame.msg.currentTarget
      m.frame.msg.caller dst (v - word (cutN v.toNat)))).push
        (transferLog m.frame.msg.currentTarget m.frame.msg.caller 0 (word (cutN v.toNat))))

set_option maxHeartbeats 0 in
theorem transfer_low (m : Machine) (dst : Address) (v : Word) (hf : Fresh STA.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa9059cbb [Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (TransferPost m dst v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  all_goals
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    have hd0 := ne_zero_of_iszero2 (by with_reducible assumption)
    have hbc := Verified.Solady.Spec.le_of_iszero_gt (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 3#256)))
      (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
      ⟨fun h => absurd hv h, fun h => ?_, fun _ _ hbp hov => ?_, fun _ _ hbp _ _ _ _ => ?_⟩
    · rcases h with h | h
      · exact absurd h hd0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
    · have hbp' : m_world.sload m_msg.currentTarget 6#256 = 100#256 := hbp
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
    have hbp' : m_world.sload m_msg.currentTarget 6#256 = 100#256 := hbp
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
      rw [hfee]
      rw [logEntry_eq_eventLog (data := [v - 0#256]),
        logEntry_eq_eventLog (data := [0#256])]
      · rfl
      all_goals event_data
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
      rw [hfee]
      rw [logEntry_eq_eventLog (data := [v - Word.div (m_world.sload m_msg.currentTarget 6#256 *
          (m_world.sload m_msg.currentTarget 6#256 * Word.div
            (m_world.sload m_msg.currentTarget 6#256 + v - 1#256)
            (m_world.sload m_msg.currentTarget 6#256))) 10000#256]),
        logEntry_eq_eventLog (data := [Word.div (m_world.sload m_msg.currentTarget 6#256 *
          (m_world.sload m_msg.currentTarget 6#256 * Word.div
            (m_world.sload m_msg.currentTarget 6#256 + v - 1#256)
            (m_world.sload m_msg.currentTarget 6#256))) 10000#256])]
      · rfl
      all_goals event_data

set_option maxHeartbeats 0 in
theorem transfer_high (m : Machine) (dst : Address) (v : Word) (hf : Fresh STA.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa9059cbb [Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) (hbp : m.world.sload m.frame.msg.currentTarget 6#256 = 100#256) :
    Halts m (TransferPost m dst v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hbc : v.toNat ≤
      (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto m_msg.caller)).toNat
  swap
  · have h1 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le hbc)
    simp only [balSlot, mappingSlot] at h1
    pwp_steps [hval, hst, hsel', hz, hl, h1, harg0, harg1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ h => absurd h hbc, fun _ h => absurd h hbc⟩
  have h1 := Verified.Solady.Spec.iszero_gt_of_le hbc
  simp only [balSlot, mappingSlot] at h1
  by_cases hd0 : dst = 0
  · subst hd0
    have h2 : (Word.ofAddress (0 : Address)).iszero.iszero = 0 := by decide
    pwp_steps [hval, hst, hsel', hz, hl, h1, h2, harg0, harg1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun h => absurd rfl h, fun h => absurd rfl h⟩
  have h2 := iszero2_of_ne hd0
  pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, harg0, harg1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64]
  by_cases hov : 2 ^ 256 ≤ (100#256 : Word).toNat + v.toNat
  · have h3 := sta_add_lt_zero hov
    pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, harg0, harg1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    rw [h3]
    pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, harg0, harg1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _)
      ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ => ⟨_, rfl⟩, fun _ _ _ h => ?_⟩
    · rcases h with h | h
      · exact absurd h hd0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
    · simp at hov; omega
  have h3 := sta_add_lt_one (Nat.lt_of_not_le hov)
  have h4 := sta_gt_one_iszero (x := 100#256 + v) (by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (Nat.lt_of_not_le hov)]; simp; omega)
  have h5 : Word.iszero (Word.iszero (100#256 : Word)) = 1 := by decide
  by_cases hv0 : v = 0
  · subst hv0
    pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    rw [sta_zero_add_lt]
    pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    rw [sta_gt_zero]
    pwp_xsteps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    have hc0 : word (cutN (BitVec.toNat (0 : Word))) = 0#256 := by decide
    refine ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ h => absurd h (by simp), fun _ _ _ _ _ _ _ =>
      ⟨hval, hst, rfl, ?_, rfl, rfl, ?_⟩⟩
    · rcases h with h | h
      · exact absurd h hd0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
    · simp only [outputMachine, staMoveWorld, creditWorld, debitWorld, hc0, BitVec.sub_zero]
      rfl
    · simp only [outputMachine, hc0, BitVec.sub_zero]
      logs_simp []
      rw [logEntry_eq_eventLog (data := [0#256]), logEntry_eq_eventLog (data := [0#256])]
      · rfl
      all_goals event_data
  pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  rw [h3]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  have hq := sta_q_toNat (v := v) (by simp at hov; omega)
  have hvp : 0 < v.toNat := by
    rcases Nat.eq_zero_or_pos v.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simp [h])) hv0
    · exact h
  have h6 := sta_iszero2_of_pos (x := Word.div (100#256 + v - 1#256) 100#256) (by rw [hq]; omega)
  rw [h6]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, h6, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  have hvq : (v.toNat + 99) / 100 * 100 ≤ v.toNat + 99 := Nat.div_mul_le_self _ _
  have h7 := sta_mul_eq_one (a := Word.div (100#256 + v - 1#256) 100#256) (b := 100#256)
    (by rw [hq]; omega) (by rw [hq]; simp at hov ⊢; omega)
  rw [h7]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, h6, h7, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  have hr : (100#256 * Word.div (100#256 + v - 1#256) 100#256).toNat =
      100 * ((v.toNat + 99) / 100) := by
    rw [BitVec.toNat_mul, hq, Nat.mod_eq_of_lt (by simp at hov ⊢; omega)]; simp
  have h8 := sta_iszero2_of_pos (x := 100#256 * Word.div (100#256 + v - 1#256) 100#256)
    (by rw [hr]; omega)
  rw [h8]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, h6, h7, h8, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  by_cases hov2 : 2 ^ 256 ≤ (v.toNat + 100 - 1) / 100 * 100 * 100
  · have h9 := sta_mul_eq_zero (a := 100#256 * Word.div (100#256 + v - 1#256) 100#256)
      (b := 100#256) (by rw [hr]; omega) (by rw [hr]; simp; omega)
    rw [h9]
    pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, h6, h7, h8, h9, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _)
      ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ => ⟨_, rfl⟩, fun _ _ _ _ h => ?_⟩
    · rcases h with h | h
      · exact absurd h hd0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
    · omega
  have h9 := sta_mul_eq_one (a := 100#256 * Word.div (100#256 + v - 1#256) 100#256)
    (b := 100#256) (by rw [hr]; omega) (by rw [hr]; simp; omega)
  rw [h9]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, h6, h7, h8, h9, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  have hF := sta_fee_eq (by simp at hov; omega) (Nat.lt_of_not_le hov2)
  have hcw : (word (cutN v.toNat)).toNat = cutN v.toNat := by
    rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (sta_cutN_lt v.isLt)]
  have h10 := Verified.Solady.Spec.iszero_gt_of_le (v := word (cutN v.toNat)) (b := v)
    (by rw [hcw]; exact sta_cutN_le _)
  rw [hF, h10]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, h6, h7, h8, h9, h10, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  have hsubw : (v - word (cutN v.toNat)).toNat = v.toNat - cutN v.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hcw]; exact sta_cutN_le _), hcw]
  by_cases hfit : ((debitWorld m_ctx.crypto m_world m_msg.currentTarget m_msg.caller v).sload
      m_msg.currentTarget (balSlot m_ctx.crypto dst)).toNat + (v.toNat - cutN v.toNat) < 2 ^ 256
  swap
  · have h11 := sta_add_lt_zero (S := v - word (cutN v.toNat))
      (v := (debitWorld m_ctx.crypto m_world m_msg.currentTarget m_msg.caller v).sload
        m_msg.currentTarget (balSlot m_ctx.crypto dst)) (by rw [hsubw]; omega)
    simp only [debitWorld, balSlot, mappingSlot] at h11
    rw [h11]
    pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, h6, h7, h8, h9, h10, harg0,
      harg1, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _)
      ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ h => absurd h (by simp at hov; omega), fun _ _ _ _ _ h => absurd h hfit⟩
    · rcases h with h | h
      · exact absurd h hd0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
  have h11 := sta_add_lt_one (S := v - word (cutN v.toNat))
    (v := (debitWorld m_ctx.crypto m_world m_msg.currentTarget m_msg.caller v).sload
      m_msg.currentTarget (balSlot m_ctx.crypto dst)) (by rw [hsubw]; omega)
  simp only [debitWorld, balSlot, mappingSlot] at h11
  rw [h11]
  pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, h6, h7, h8, h9, h10, h11, harg0,
    harg1, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  by_cases hsup : cutN v.toNat ≤ ((creditWorld m_ctx.crypto m_world m_msg.currentTarget
      m_msg.caller dst v (word (cutN v.toNat))).sload m_msg.currentTarget 5#256).toNat
  swap
  · have h12 := Verified.Solady.Spec.iszero_gt_of_lt (v := word (cutN v.toNat))
      (b := (creditWorld m_ctx.crypto m_world m_msg.currentTarget
      m_msg.caller dst v (word (cutN v.toNat))).sload m_msg.currentTarget 5#256)
      (by rw [hcw]; omega)
    simp only [creditWorld, debitWorld, balSlot, mappingSlot] at h12
    rw [h12]
    pwp_steps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, h6, h7, h8, h9, h10, h11, harg0,
      harg1, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _)
      ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ h => absurd h (by simp at hov; omega), fun _ _ _ _ _ _ h => absurd h hsup⟩
    · rcases h with h | h
      · exact absurd h hd0
      · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
  have h12 := Verified.Solady.Spec.iszero_gt_of_le (v := word (cutN v.toNat))
    (b := (creditWorld m_ctx.crypto m_world m_msg.currentTarget
    m_msg.caller dst v (word (cutN v.toNat))).sload m_msg.currentTarget 5#256)
    (by rw [hcw]; omega)
  simp only [creditWorld, debitWorld, balSlot, mappingSlot] at h12
  rw [h12]
  pwp_xsteps [hval, hst, hsel', hz, hl, h1, h2, hbp, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ h => absurd h (by simp at hov; omega),
    fun _ _ _ _ _ _ _ => ⟨hval, hst, rfl, ?_, rfl, rfl, ?_⟩⟩
  · rcases h with h | h
    · exact absurd h hd0
    · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
  · simp only [outputMachine]
    rfl
  · simp only [outputMachine]
    logs_simp []
    rw [logEntry_eq_eventLog (data := [v - word (cutN v.toNat)]),
      logEntry_eq_eventLog (data := [word (cutN v.toNat)])]
    · rfl
    all_goals event_data

end Verified.WeirdERC20.STA.Spec
