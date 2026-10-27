import Verified.WeirdERC20.BNB.Spec.Approve
import EvmLogic.Tactic.StepExt

/-!
# BNB under the spec: `transfer`
-/

namespace Verified.WeirdERC20.BNB.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.BNB.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

theorem ne_zero_of_eq_iszero {x : Word} (h : (Word.eq x 0#256).iszero ≠ 0) : x ≠ 0 := by
  rintro rfl; exact h (by decide)

theorem le_of_lt_iszero {b v : Word} (h : (Word.lt b v).iszero ≠ 0) : v.toNat ≤ b.toNat := by
  by_contra hlt
  have hu : BitVec.ult b v = true := by simp [BitVec.ult]; omega
  simp [Word.iszero, Word.lt, Word.ofBool, hu] at h

theorem addr_ne_of_word {a : Address} (h : Word.ofAddress a ≠ 0) : a ≠ 0 := by
  rintro rfl; exact h (by decide)

/-- The balance slot of `a` (`balanceOf` at slot 5). -/
abbrev balSlot (crypto : Crypto) (a : Address) : Word := mappingSlot crypto (Word.ofAddress a) 5#256

/-- The world after BNB's move of `v` from `src` to `dst`: debit, then credit read after it. -/
def moveWorld (crypto : Crypto) (w : World) (t src dst : Address) (v : Word) : World :=
  (w.sstore t (balSlot crypto src) (w.sload t (balSlot crypto src) - v)).sstore t
    (balSlot crypto dst)
    ((w.sstore t (balSlot crypto src) (w.sload t (balSlot crypto src) - v)).sload t
      (balSlot crypto dst) + v)

/-- `transfer(dst, v)`'s code-level end: the checks revert, or the move, no return data,
the `Transfer` log. -/
def TransferPost (m : Machine) (dst : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (dst = 0 ∨ v = 0 ∨
    (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat <
      v.toNat ∨
    2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat +
      v.toNat → ∃ out, o = .revert out) ∧
  (dst ≠ 0 → v ≠ 0 →
    v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat →
    (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat + v.toNat <
      2 ^ 256 →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success .empty ∧
    mf.world = moveWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller dst v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (transferLog m.frame.msg.currentTarget m.frame.msg.caller dst v))

set_option maxHeartbeats 0 in
theorem transfer_low (m : Machine) (dst : Address) (v : Word) (hf : Fresh BNB.runtimeCode m)
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
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  all_goals
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    have hd0 := addr_ne_of_word (ne_zero_of_eq_iszero (by with_reducible assumption))
    have hv0 := ne_zero_of_gt (by with_reducible assumption)
    have hbc := le_of_lt_iszero (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 5#256)))
      (by with_reducible assumption)
    have hbd := Verified.Solady.Spec.lt_add_iszero_ne (S := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress dst) ++ Bytes.ofWord 5#256)))
      (by with_reducible assumption)
    refine pwp_stop (by pcode_fact) (hok _ _ ⟨fun h => ?_, fun _ _ _ _ => ⟨hv, ‹_›, rfl, rfl, rfl,
      rfl, ?_⟩⟩)
    · simp only [balSlot, mappingSlot] at h
      rcases h with h | h | h | h
      · exact absurd h hd0
      · exact absurd h hv0
      · exact absurd hbc (by omega)
      · exact absurd hbd (by omega)
    · logs_simp []
      event_log [v]

theorem eq_zero_iszero_one {x : Word} (h : x ≠ 0) : (Word.eq x 0#256).iszero = 1 := by
  have : (x == 0#256) = false := by simpa using h
  simp [Word.eq, Word.ofBool, Word.iszero, this]

theorem lt_iszero_one {b v : Word} (h : v.toNat ≤ b.toNat) : (Word.lt b v).iszero = 1 := by
  have hu : BitVec.ult b v = false := by simp [BitVec.ult]; omega
  simp [Word.iszero, Word.lt, Word.ofBool, hu]

theorem lt_iszero_zero {b v : Word} (h : b.toNat < v.toNat) : (Word.lt b v).iszero = 0 := by
  have hu : BitVec.ult b v = true := by simp [BitVec.ult]; omega
  simp [Word.iszero, Word.lt, Word.ofBool, hu]

theorem word_ofAddress_ne {a : Address} (h : a ≠ 0) : Word.ofAddress a ≠ 0 := by
  intro h0
  apply h
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h0
  have hs : a.toNat < 2 ^ 160 := a.isLt
  simp only [Word.ofAddress, BitVec.toNat_setWidth] at this
  rw [Nat.mod_eq_of_lt (by omega)] at this
  simpa using this

theorem lt_add_iszero_one' {S v : Word} (h : S.toNat + v.toNat < 2 ^ 256) :
    ((S + v).lt v).iszero = 1 := by
  have hm : (S.toNat + v.toNat) % 2 ^ 256 = S.toNat + v.toNat := Nat.mod_eq_of_lt h
  simp only [Word.lt, Word.ofBool, BitVec.ult, BitVec.toNat_add, hm, Word.iszero]
  have : ¬ S.toNat + v.toNat < v.toNat := by omega
  simp [this]

/-- The credit's base after the debit fits: either the debited row itself or another row. -/
theorem credit_fits {w : World} {t : Address} {kc kd : Word} {v : Word}
    (hbc : v.toNat ≤ (w.sload t kc).toNat) (hbd : (w.sload t kd).toNat + v.toNat < 2 ^ 256) :
    ((w.sstore t kc (w.sload t kc - v)).sload t kd).toNat + v.toNat < 2 ^ 256 := by
  rw [World.sload_sstore]
  split
  · rename_i h
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hbc)]
    have := (w.sload t kc).isLt
    omega
  · exact hbd

set_option maxHeartbeats 0 in
theorem transfer_high (m : Machine) (dst : Address) (v : Word) (hf : Fresh BNB.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa9059cbb [Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (TransferPost m dst v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hd0 : dst = 0
  · subst hd0
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd rfl h⟩
  have h1 := eq_zero_iszero_one (word_ofAddress_ne hd0)
  by_cases hv0 : v = 0
  · subst hv0
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ h => absurd rfl h⟩
  have h2 := gt_zero_iszero2 hv0
  by_cases hbc : v.toNat ≤ (m_world.sload m_msg.currentTarget
      (balSlot m_ctx.crypto m_msg.caller)).toNat
  swap
  · have h3 := lt_iszero_zero (Nat.lt_of_not_le hbc)
    simp only [balSlot, mappingSlot] at h3
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, h1, h2, h3, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ _ h => absurd h hbc⟩
  have h3 := lt_iszero_one hbc
  simp only [balSlot, mappingSlot] at h3
  by_cases hbd : (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto dst)).toNat + v.toNat <
      2 ^ 256
  swap
  · have h4 := Verified.Solady.Spec.lt_add_iszero_zero (Nat.le_of_not_lt hbd)
    simp only [balSlot, mappingSlot] at h4
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, h1, h2, h3, h4, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ _ _ h => absurd h hbd⟩
  have h4 := Verified.Solady.Spec.lt_add_iszero_one hbd
  simp only [balSlot, mappingSlot] at h4
  have h5 := Verified.Solady.Spec.iszero_gt_of_le hbc
  have hX := credit_fits (t := m_msg.currentTarget) hbc hbd
  have h6 := Verified.Solady.Spec.lt_add_iszero_one hX
  have h7 := lt_add_iszero_one' hX
  simp only [balSlot, mappingSlot] at h5 h6 h7
  pwp_steps [hval, hst, hsel', hz, harg0, harg1, h1, h2, h3, h4, h5, h6, h7,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine pwp_stop (by pcode_fact) ⟨fun h => ?_, fun _ _ _ _ => ⟨hval, hst, rfl, rfl, rfl, rfl, ?_⟩⟩
  · rcases h with h | h | h | h
    · exact absurd h hd0
    · exact absurd h hv0
    · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
    · exact absurd (Nat.lt_of_lt_of_le hbd h) (Nat.lt_irrefl _)
  · logs_simp []
    event_log [v]

/-! ## The obligation -/

set_option linter.unusedSimpArgs false in
theorem bnb_call_transfer (s : VState Address) (c d : Address) (v : ℕ) :
    M.call s c (.transfer d v) =
      if QEDefi.Math.MAX < s.bal d + v ∨ d = 0 ∨ v = 0 ∨ s.bal c < v then .halt .revert
      else .ok { s with bal := s.bal - Finsupp.single c v + Finsupp.single d v } .empty := by
  simp only [M, QEDefi.ERC20.Spec.BNB.bnbModel_call, QEDefi.ERC20.Spec.BNB.bnbGuard]
  by_cases h1 : QEDefi.Math.MAX < s.bal d + v
  · simp [h1]
  by_cases h2 : d = 0
  · subst h2
    simp [h1, Variant.call, Variant.step, Variant.transfer, Variant.moveOk, Variant.bnb,
      Variant.standard, Variant.failKind, Variant.guardOk, Variant.failWith]
  by_cases h3 : v = 0
  · subst h3
    simp [h1, h2, Variant.call, Variant.step, Variant.transfer, Variant.moveOk, Variant.bnb,
      Variant.standard, Variant.failKind, Variant.guardOk, Variant.failWith]
  have h2' : ¬ d = 0#160 := h2
  by_cases h4 : s.bal c < v
  · simp [h1, h2', h3, h4, Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      Variant.move, Variant.units, Variant.bnb, Variant.standard, Variant.failKind,
      Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith]
  · simp [h1, h2', h3, h4, Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      Variant.move, Variant.units, Variant.bnb, Variant.standard, Variant.feeOverflow,
      Variant.feeOf, Variant.credit, Variant.retData]

/-- **BNB's move** through the abstraction: the model's move, when covered and not wrapping. -/
theorem bnbRead_moveWorld {crypto : Crypto} {Act : Finset Address} {w : World} {t c d : Address}
    {v : Word} (hS : bnbSound crypto Act) (hc : c ∈ Act) (hd : d ∈ Act)
    (hv : v.toNat ≤ (w.sload t (mappingSlot crypto (Word.ofAddress c) 5#256)).toNat)
    (hov : (w.sload t (mappingSlot crypto (Word.ofAddress d) 5#256)).toNat + v.toNat < 2 ^ 256) :
    bnbRead crypto Act (moveWorld crypto w t c d v) t =
      { bnbRead crypto Act w t with
        bal := (bnbRead crypto Act w t).bal - Finsupp.single c v.toNat +
          Finsupp.single d v.toNat } := by
  simp only [moveWorld, balSlot, bnbRead]
  rw [readMap_sstore_other (base' := 6#256) hS (by simp) (by simp) (by decide) hd,
    readMap_sstore_other (base' := 6#256) hS (by simp) (by simp) (by decide) hc,
    readMap2_sstore_map (base2 := 7#256) hS (by simp) (by simp) hd,
    readMap2_sstore_map (base2 := 7#256) hS (by simp) (by simp) hc,
    readSlot, readSlot, sload_sstore_map (k := 3#256) hS (by simp) (by simp) hd,
    sload_sstore_map (k := 3#256) hS (by simp) (by simp) hc,
    sload_sstore_map (k := 4#256) hS (by simp) (by simp) hd,
    sload_sstore_map (k := 4#256) hS (by simp) (by simp) hc, World.balance_sstore,
    World.balance_sstore, readMap_sstore (base := 5#256) hS (by simp) hd,
    readMap_sstore (base := 5#256) hS (by simp) hc]
  congr 1
  have hsub : (w.sload t (mappingSlot crypto (Word.ofAddress c) 5#256) - v).toNat =
      (w.sload t (mappingSlot crypto (Word.ofAddress c) 5#256)).toNat - v.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hv)]
  ext a
  simp only [Finsupp.update_apply, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    Finsupp.single_apply]
  by_cases hcd : c = d
  · subst hcd
    rw [World.sload_sstore_self, BitVec.sub_add_cancel]
    by_cases ha : a = c
    · subst ha; simp [readMap_of_mem hc]; omega
    · simp [ha, Ne.symm ha]
  · have hne : balSlot crypto d ≠ balSlot crypto c := fun e =>
      hcd (hS.inj1 5#256 (by simp) 5#256 (by simp) d hd c hc e).1.symm
    rw [World.sload_sstore_ne_key _ _ _ hne]
    have hadd : (w.sload t (mappingSlot crypto (Word.ofAddress d) 5#256) + v).toNat =
        (w.sload t (mappingSlot crypto (Word.ofAddress d) 5#256)).toNat + v.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hov]
    by_cases ha : a = d
    · subst ha; simp [readMap_of_mem hd, hcd, hadd]
    · by_cases hac : a = c
      · subst hac; simp [readMap_of_mem hc, ha, hsub, Ne.symm ha]
      · simp [ha, hac, Ne.symm ha, Ne.symm hac]

set_option linter.unusedSimpArgs false in
/-- **`transfer(dst, v)`**: the checks (and the overflow guard) revert, or the move with its
`Transfer`, no return data. -/
theorem call_transfer (dst : Address) (v : ℕ) :
    CallSpec BNB.runtimeCode bnbAbs M g₀ (.transfer dst v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hdA : dst ∈ Act := haddr dst (by simp [Call.addrs])
  have hcA := hs.caller
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  refine halts_split' (G := Normal g₀ m)
    (fun hG => transfer_high m dst (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1)
    (transfer_low m dst (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  simp only [TransferPost, balSlot] at hrev hok
  have hw0 : word v = 0 ↔ v = 0 := ⟨fun h => by rw [← hwv, h]; rfl, fun h => by subst h; rfl⟩
  by_cases hr : dst = 0 ∨ v = 0 ∨
      (m.world.sload m.frame.msg.currentTarget
        (mappingSlot m.ctx.crypto (Word.ofAddress m.frame.msg.caller) 5#256)).toNat < v ∨
      2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget
        (mappingSlot m.ctx.crypto (Word.ofAddress dst) 5#256)).toNat + v
  · obtain ⟨out, rfl⟩ := hrev (by rw [hwv, hw0]; exact hr)
    by_cases hG : Normal g₀ m
    · left
      have hpre := pre_eq hs hG.2.2
      have hcond : QEDefi.Math.MAX < (pre bnbAbs Act m).bal dst + v ∨ dst = 0 ∨ v = 0 ∨
          (pre bnbAbs Act m).bal m.frame.msg.caller < v := by
        rw [hpre]; simp only [bnbRead, readMap_of_mem hcA, readMap_of_mem hdA]
        rcases hr with h | h | h | h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h))
        · exact .inr (.inr (.inr h))
        · left; simp only [QEDefi.Math.MAX]; omega
      rw [bnb_call_transfer, ite_pos' hcond]
      exact ⟨out, rfl⟩
    · exact .inr ⟨trivial, hG⟩
  left
  simp only [not_or, not_lt] at hr
  obtain ⟨hd0, hv0, hbc, hbd⟩ := hr
  obtain ⟨hv, -, ho, hw, ht, hcr, hl⟩ := hok hd0 (fun h => hv0 (hw0.mp h)) (by rw [hwv]; exact hbc)
    (by rw [hwv]; omega)
  have hpre := pre_eq hs hv
  have hcond : ¬ (QEDefi.Math.MAX < (pre bnbAbs Act m).bal dst + v ∨ dst = 0 ∨ v = 0 ∨
      (pre bnbAbs Act m).bal m.frame.msg.caller < v) := by
    rw [hpre]; simp only [bnbRead, readMap_of_mem hcA, readMap_of_mem hdA]
    rintro (h | h | h | h)
    · simp only [QEDefi.Math.MAX] at h; omega
    · exact hd0 h
    · exact hv0 h
    · omega
  rw [bnb_call_transfer, ite_neg' hcond]
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show bnbRead _ _ _ _ = _
    rw [hw, bnbRead_moveWorld hs.sound hcA hdA (by rw [hwv]; exact hbc) (by rw [hwv]; omega),
      ← hpre, hwv]
  · rw [hw, moveWorld]
    simp only [balSlot]
    exact FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hdA, rfl⟩)))
      (FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hcA, rfl⟩))) frameKeeps_refl')
  · rw [hl]
    simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, QEDefi.ERC20.Spec.BNB.bnbEvents, Spec.eventLog]

end Verified.WeirdERC20.BNB.Spec
