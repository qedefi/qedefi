import Verified.WeirdERC20.BNB.Spec.Transfer
import Verified.WeirdERC20.BNB.Spec.Approve

/-!
# BNB under the spec: `transferFrom`
-/

namespace Verified.WeirdERC20.BNB.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.BNB.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-- The allowance slot of `src` for the caller (`allowance[src][caller]` at slot 7). -/
abbrev allowSlot (crypto : Crypto) (o sp : Address) : Word :=
  mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 7#256

/-- The world after `transferFrom`: the move, then the allowance row lowered (read after the
move). -/
def tfWorld (crypto : Crypto) (w : World) (t c src dst : Address) (v : Word) : World :=
  (moveWorld crypto w t src dst v).sstore t (allowSlot crypto src c)
    ((moveWorld crypto w t src dst v).sload t (allowSlot crypto src c) - v)

/-- `transferFrom(src, dst, v)`'s code-level end: the checks (and the allowance `safeSub` after
the move) revert, or success with `tfWorld`, `true` and the `Transfer` log. -/
def TFPost (m : Machine) (src dst : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (dst = 0 ∨ v = 0 ∨
    (m.world.sload m.frame.msg.currentTarget (mappingSlot m.ctx.crypto (Word.ofAddress src) 5#256)).toNat
      < v.toNat ∨
    2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget
      (mappingSlot m.ctx.crypto (Word.ofAddress dst) 5#256)).toNat + v.toNat ∨
    (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat
      < v.toNat ∨
    ((moveWorld m.ctx.crypto m.world m.frame.msg.currentTarget src dst v).sload
      m.frame.msg.currentTarget (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat < v.toNat →
    ∃ out, o = .revert out) ∧
  (dst ≠ 0 → v ≠ 0 →
    v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (mappingSlot m.ctx.crypto (Word.ofAddress src) 5#256)).toNat →
    (m.world.sload m.frame.msg.currentTarget
      (mappingSlot m.ctx.crypto (Word.ofAddress dst) 5#256)).toNat + v.toNat < 2 ^ 256 →
    v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat →
    v.toNat ≤ ((moveWorld m.ctx.crypto m.world m.frame.msg.currentTarget src dst v).sload
      m.frame.msg.currentTarget (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = tfWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src dst v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push (transferLog m.frame.msg.currentTarget src dst v))

theorem iszero_of_iszero3 {w : Word} (h : w.iszero.iszero.iszero ≠ 0) : w.iszero ≠ 0 := by
  intro h0; exact h (by rw [h0]; decide)

set_option maxHeartbeats 0 in
theorem transferFrom_low (m : Machine) (src dst : Address) (v : Word)
    (hf : Fresh BNB.runtimeCode m)
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
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, harg2, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  all_goals
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    have hd0 := addr_ne_of_word (ne_zero_of_eq_iszero (by with_reducible assumption))
    have hv0 := ne_zero_of_gt (by with_reducible assumption)
    have hbs := le_of_lt_iszero (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 5#256)))
      (by with_reducible assumption)
    have hbd := Verified.Solady.Spec.lt_add_iszero_ne (S := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress dst) ++ Bytes.ofWord 5#256)))
      (by with_reducible assumption)
    have ha := Verified.Solady.Spec.le_of_iszero_gt (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 7#256)))))
      (by with_reducible assumption)
    have ha2 : v.toNat ≤ ((moveWorld m_ctx.crypto m_world m_msg.currentTarget src dst v).sload
        m_msg.currentTarget (allowSlot m_ctx.crypto src m_msg.caller)).toNat := by
      apply Verified.Solady.Spec.le_of_iszero_gt
      apply iszero_of_iszero3
      exact (by with_reducible assumption :
        (v.gt (((m_world.sstore m_msg.currentTarget
          (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 5#256))
          (m_world.sload m_msg.currentTarget
            (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 5#256)) -
              v)).sstore m_msg.currentTarget
          (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress dst) ++ Bytes.ofWord 5#256))
          ((m_world.sstore m_msg.currentTarget
            (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 5#256))
            (m_world.sload m_msg.currentTarget
              (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 5#256)) -
                v)).sload m_msg.currentTarget
            (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress dst) ++ Bytes.ofWord 5#256)) +
              v)).sload m_msg.currentTarget
          (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
            (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++
              Bytes.ofWord 7#256)))))).iszero.iszero.iszero ≠ 0)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun h => ?_, fun _ _ _ _ _ _ =>
      ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩⟩
    · rcases h with h | h | h | h | h | h
      · exact absurd h hd0
      · exact absurd h hv0
      · exact absurd (Nat.lt_of_lt_of_le h hbs) (Nat.lt_irrefl _)
      · exact absurd (Nat.lt_of_lt_of_le hbd h) (Nat.lt_irrefl _)
      · exact absurd (Nat.lt_of_lt_of_le h ha) (Nat.lt_irrefl _)
      · exact absurd (Nat.lt_of_lt_of_le h ha2) (Nat.lt_irrefl _)
    · simp only [outputData]
      apwp_norm []
      rfl
    · logs_simp []
      event_log [v]

set_option maxHeartbeats 0 in
theorem transferFrom_high (m : Machine) (src dst : Address) (v : Word)
    (hf : Fresh BNB.runtimeCode m)
    (hd : Args m.frame.msg.data 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (TFPost m src dst v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  have harg2 := harg 2 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1 harg2
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hd0 : dst = 0
  · subst hd0
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd rfl h⟩
  have h1 := eq_zero_iszero_one (word_ofAddress_ne hd0)
  by_cases hv0 : v = 0
  · subst hv0
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ h => absurd rfl h⟩
  have h2 := gt_zero_iszero2 hv0
  by_cases hbc : v.toNat ≤ (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto src)).toNat
  swap
  · have h3 := lt_iszero_zero (Nat.lt_of_not_le hbc)
    simp only [balSlot, mappingSlot] at h3
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, h1, h2, h3, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ _ h => absurd h hbc⟩
  have h3 := lt_iszero_one hbc
  simp only [balSlot, mappingSlot] at h3
  by_cases hbd : (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto dst)).toNat + v.toNat <
      2 ^ 256
  swap
  · have h4 := Verified.Solady.Spec.lt_add_iszero_zero (Nat.le_of_not_lt hbd)
    simp only [balSlot, mappingSlot] at h4
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, h1, h2, h3, h4,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ _ _ h => absurd h hbd⟩
  have h4 := Verified.Solady.Spec.lt_add_iszero_one hbd
  simp only [balSlot, mappingSlot] at h4
  by_cases ha : v.toNat ≤
      (m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto src m_msg.caller)).toNat
  swap
  · have h5 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le ha)
    simp only [allowSlot, mappingSlot2, mappingSlot] at h5
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, h1, h2, h3, h4, h5,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ _ _ _ h => absurd h ha⟩
  have h5 := Verified.Solady.Spec.iszero_gt_of_le ha
  simp only [allowSlot, mappingSlot2, mappingSlot] at h5
  have h6 := Verified.Solady.Spec.iszero_gt_of_le hbc
  have hX := credit_fits (t := m_msg.currentTarget) hbc hbd
  have h7 := Verified.Solady.Spec.lt_add_iszero_one hX
  have h8 := lt_add_iszero_one' hX
  simp only [balSlot, mappingSlot] at h6 h7 h8
  by_cases ha2 : v.toNat ≤ ((moveWorld m_ctx.crypto m_world m_msg.currentTarget src dst v).sload
      m_msg.currentTarget (allowSlot m_ctx.crypto src m_msg.caller)).toNat
  swap
  · have h9 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le ha2)
    simp only [moveWorld, allowSlot, balSlot, mappingSlot2, mappingSlot] at h9
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ _ _ _ _ h => absurd h ha2⟩
  have h9 := Verified.Solady.Spec.iszero_gt_of_le ha2
  simp only [moveWorld, allowSlot, balSlot, mappingSlot2, mappingSlot] at h9
  pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine ⟨fun h => ?_, fun _ _ _ _ _ _ => ⟨hval, hst, rfl, rfl, rfl, rfl, ?_⟩⟩
  · rcases h with h | h | h | h | h | h
    · exact absurd h hd0
    · exact absurd h hv0
    · exact absurd (Nat.lt_of_lt_of_le h hbc) (Nat.lt_irrefl _)
    · exact absurd (Nat.lt_of_lt_of_le hbd h) (Nat.lt_irrefl _)
    · exact absurd (Nat.lt_of_lt_of_le h ha) (Nat.lt_irrefl _)
    · exact absurd (Nat.lt_of_lt_of_le h ha2) (Nat.lt_irrefl _)
  · logs_simp []
    event_log [v]

/-! ## The obligation -/

set_option linter.unusedSimpArgs false in
theorem bnb_call_transferFrom (s : VState Address) (c src d : Address) (v : ℕ) :
    M.call s c (.transferFrom src d v) =
      if QEDefi.Math.MAX < s.bal d + v ∨ d = 0 ∨ v = 0 ∨ s.bal src < v ∨
          s.allowance src c < v then .halt .revert
      else .ok ({ s with bal := s.bal - Finsupp.single src v + Finsupp.single d v }.setAllowance
        src c (s.allowance src c - v)) (.word true) := by
  simp only [M, QEDefi.ERC20.Spec.BNB.bnbModel_call, QEDefi.ERC20.Spec.BNB.bnbGuard]
  by_cases h1 : QEDefi.Math.MAX < s.bal d + v
  · simp [h1]
  by_cases h2 : d = 0
  · subst h2
    simp [h1, Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk, Variant.bnb,
      Variant.standard, Variant.failKind, Variant.guardOk, Variant.failWith]
  by_cases h3 : v = 0
  · subst h3
    simp [h1, h2, Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk, Variant.bnb,
      Variant.standard, Variant.failKind, Variant.guardOk, Variant.failWith]
  have h2' : ¬ d = 0#160 := h2
  by_cases h4 : s.allowance src c < v
  · simp [h1, h2', h3, h4, Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk,
      Variant.spend, Variant.move, Variant.units, Variant.bnb, Variant.standard, Variant.failKind,
      Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith,
      Infinite.test]
  by_cases h5 : s.bal src < v
  · simp [h1, h2', h3, h4, h5, Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk,
      Variant.spend, Variant.move, Variant.units, Variant.bnb, Variant.standard, Variant.failKind,
      Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith,
      Infinite.test, VState.setAllowance]
  · simp [h1, h2', h3, h4, h5, Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk,
      Variant.spend, Variant.move, Variant.units, Variant.bnb, Variant.standard,
      Variant.feeOverflow, Variant.feeOf, Variant.credit, Variant.retData,
      Infinite.test, VState.setAllowance]

/-- The move leaves an actor's allowance row: it writes two balance rows. -/
theorem sload_moveWorld_allow {crypto : Crypto} {Act : Finset Address} {w : World}
    {t o sp src dst : Address} {v : Word} (hS : bnbSound crypto Act) (ho : o ∈ Act)
    (hsp : sp ∈ Act) (hs : src ∈ Act) (hd : dst ∈ Act) :
    (moveWorld crypto w t src dst v).sload t (allowSlot crypto o sp) =
      w.sload t (allowSlot crypto o sp) := by
  simp only [moveWorld, balSlot, allowSlot]
  rw [World.sload_sstore_ne_key _ _ _ (fun e =>
      hS.disj 5#256 (by simp) 7#256 (by simp) dst hd o ho sp hsp e.symm),
    World.sload_sstore_ne_key _ _ _ (fun e =>
      hS.disj 5#256 (by simp) 7#256 (by simp) src hs o ho sp hsp e.symm)]

set_option linter.unusedSimpArgs false in
/-- **`transferFrom(src, dst, v)`**: the checks (and the overflow guard) revert, or the
allowance is spent and the move done, `true`, with its `Transfer`. -/
theorem call_transferFrom (src dst : Address) (v : ℕ) :
    CallSpec BNB.runtimeCode bnbAbs M g₀ (.transferFrom src dst v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hsA : src ∈ Act := haddr src (by simp [Call.addrs])
  have hdA : dst ∈ Act := haddr dst (by simp [Call.addrs])
  have hcA := hs.caller
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  refine halts_split' (G := Normal g₀ m)
    (fun hG => transferFrom_high m src dst (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1)
    (transferFrom_low m src dst (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  have hmw := sload_moveWorld_allow (w := m.world) (t := m.frame.msg.currentTarget)
    (v := word v) hs.sound hsA hcA hsA hdA
  simp only [TFPost, hmw] at hrev hok
  have hw0 : word v = 0 ↔ v = 0 := ⟨fun h => by rw [← hwv, h]; rfl, fun h => by subst h; rfl⟩
  by_cases hr : dst = 0 ∨ v = 0 ∨
      (m.world.sload m.frame.msg.currentTarget
        (mappingSlot m.ctx.crypto (Word.ofAddress src) 5#256)).toNat < v ∨
      2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget
        (mappingSlot m.ctx.crypto (Word.ofAddress dst) 5#256)).toNat + v ∨
      (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat < v
  · obtain ⟨out, rfl⟩ := hrev (by
      rw [hwv, hw0]
      rcases hr with h | h | h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl h)))
      · exact .inr (.inr (.inr (.inr (.inl h)))))
    by_cases hG : Normal g₀ m
    · left
      have hpre := pre_eq hs hG.2.2
      have hcond : QEDefi.Math.MAX < (pre bnbAbs Act m).bal dst + v ∨ dst = 0 ∨ v = 0 ∨
          (pre bnbAbs Act m).bal src < v ∨
          (pre bnbAbs Act m).allowance src m.frame.msg.caller < v := by
        rw [hpre]; simp only [bnbRead, readMap_of_mem hsA, readMap_of_mem hdA, readMap2, hsA, hcA,
          and_self, ite_true]
        rcases hr with h | h | h | h | h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h))
        · exact .inr (.inr (.inr (.inl h)))
        · left; simp only [QEDefi.Math.MAX]; omega
        · exact .inr (.inr (.inr (.inr h)))
      rw [bnb_call_transferFrom, ite_pos' hcond]
      exact ⟨out, rfl⟩
    · exact .inr ⟨trivial, hG⟩
  left
  simp only [not_or, not_lt] at hr
  obtain ⟨hd0, hv0, hbc, hbd, ha⟩ := hr
  obtain ⟨hv, -, ho, hw, ht, hcr, hl⟩ := hok hd0 (fun h => hv0 (hw0.mp h)) (by rw [hwv]; exact hbc)
    (by rw [hwv]; omega) (by rw [hwv]; exact ha) (by rw [hwv]; exact ha)
  have hpre := pre_eq hs hv
  have hcond : ¬ (QEDefi.Math.MAX < (pre bnbAbs Act m).bal dst + v ∨ dst = 0 ∨ v = 0 ∨
      (pre bnbAbs Act m).bal src < v ∨
      (pre bnbAbs Act m).allowance src m.frame.msg.caller < v) := by
    rw [hpre]; simp only [bnbRead, readMap_of_mem hsA, readMap_of_mem hdA, readMap2, hsA, hcA,
      and_self, ite_true]
    rintro (h | h | h | h | h)
    · simp only [QEDefi.Math.MAX] at h; omega
    · exact hd0 h
    · exact hv0 h
    · omega
    · simp only [allowSlot] at ha; omega
  rw [bnb_call_transferFrom, ite_neg' hcond]
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show bnbRead _ _ _ _ = _
    have hsub : (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto src m.frame.msg.caller) - word v).toNat =
        (m.world.sload m.frame.msg.currentTarget
          (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat - v := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hwv]; exact ha), hwv]
    rw [hw, tfWorld, hmw, bnbRead_sstore_allow hs.sound hsA hcA,
      bnbRead_moveWorld hs.sound hsA hdA (by rw [hwv]; exact hbc) (by rw [hwv]; omega), hsub,
      ← hpre, hwv]
    congr 1
    rw [hpre]
    simp only [bnbRead, readMap2, hsA, hcA, and_self, ite_true]
  · rw [hw, tfWorld, moveWorld]
    simp only [balSlot]
    exact FrameKeeps.sstore' (.inr (.inr (.inr (.inr ⟨_, hsA, _, hcA, rfl⟩))))
      (FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hdA, rfl⟩)))
        (FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hsA, rfl⟩))) frameKeeps_refl'))
  · rw [hl]
    simp [M, QEDefi.ERC20.Spec.BNB.bnbModel, QEDefi.ERC20.Spec.BNB.bnbEvents, Spec.eventLog]

end Verified.WeirdERC20.BNB.Spec
