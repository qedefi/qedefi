import Verified.WeirdERC20.STA.Spec.Transfer
import QEDefi.ERC20.Rep

/-!
# STA under the spec: the `transfer` obligation

The code-level runs (`transfer_high`, `transfer_low`) against the model: `basePercent = 100` and
the credit and burn fitting come from the model's invariant (`Start.wf`).
-/

namespace Verified.WeirdERC20.STA.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.STA.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-! ## The obligation -/

set_option linter.unusedSimpArgs false in
theorem sta_call_transfer (s : VState Address) (c d : Address) (v : ℕ) :
    M.call s c (.transfer d v) =
      if d = 0 ∨ s.bal c < v then .halt .revert
      else if 2 ^ 256 ≤ v + 100 ∨ 2 ^ 256 ≤ (v + 100 - 1) / 100 * 100 * 100 then .halt .invalid
      else .ok { s with bal := s.bal - Finsupp.single c v + Finsupp.single d v -
          Finsupp.single d (cutN v), supply := s.supply - cutN v } (.word true) := by
  simp only [M, QEDefi.ERC20.Spec.STA.staModel, Variant.model_call]
  by_cases h1 : d = 0
  · subst h1
    simp [Variant.call, Variant.step, Variant.transfer, Variant.moveOk, Variant.sta,
      Variant.standard, Variant.failKind, Variant.guardOk, Variant.failWith]
  have h1' : ¬ d = 0#160 := h1
  by_cases h2 : s.bal c < v
  · have h2' : ¬ v ≤ s.bal c := by omega
    simp [h1', h2, h2', Variant.call, Variant.step, Variant.transfer, Variant.moveOk, Variant.move,
      Variant.units, Variant.sta, Variant.standard, Variant.failKind, Variant.guardOk,
      Variant.overflows, Variant.feeOverflow, Variant.failWith]
  have h2' : v ≤ s.bal c := by omega
  by_cases h3 : 2 ^ 256 ≤ v + 100 ∨ 2 ^ 256 ≤ (v + 100 - 1) / 100 * 100 * 100
  · have h3n : 115792089237316195423570985008687907853269984665640564039457584007913129639836 ≤ v ∨ 115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤ (v + 99) / 100 * 100 * 100 := by
      have e : v + 100 - 1 = v + 99 := by omega
      rw [e] at h3; norm_num at h3 ⊢; omega
    have hm : QEDefi.Math.MAX < v + 100 ∨ QEDefi.Math.MAX < (v + 99) / 100 * 100 * 100 := by
      unfold QEDefi.Math.MAX; omega
    simp [h1', h2, h2', h3n, hm, Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      Variant.move, Variant.units, Variant.sta, Variant.standard, Variant.failKind,
      Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith]
  have e : v + 100 - 1 = v + 99 := by omega
  have h3a : ¬ 115792089237316195423570985008687907853269984665640564039457584007913129639836 ≤ v := by rw [e] at h3; norm_num at h3 ⊢; omega
  have h3b : ¬ 115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤ (v + 99) / 100 * 100 * 100 := by
    rw [e] at h3; norm_num at h3 ⊢; omega
  have hmA : ¬ QEDefi.Math.MAX < v + 100 := by unfold QEDefi.Math.MAX; omega
  have hmB : ¬ QEDefi.Math.MAX < (v + 99) / 100 * 100 * 100 := by unfold QEDefi.Math.MAX; omega
  have hfv : cutN v ≤ v := sta_cutN_le v
  have h4 : ¬ v < (v + 99) / 100 * 100 * 100 / 10000 := by
    have := hfv; unfold cutN at this; rw [e] at this; omega
  have hcut : cutN v = (v + 99) / 100 * 100 * 100 / 10000 := by unfold cutN; rw [e]
  rw [ite_neg' h3, hcut]
  by_cases h5 : (v + 99) / 100 * 100 * 100 / 10000 = 0
  · simp [h1', h2, h3a, h3b, hmA, hmB, h4, h5, Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      Variant.move, Variant.units, Variant.sta, Variant.standard, Variant.feeOverflow,
      Variant.feeOf, Variant.credit, Variant.retData]
  · simp [h1', h2, h3a, h3b, hmA, hmB, h4, h5, Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      Variant.move, Variant.units, Variant.sta, Variant.standard, Variant.feeOverflow,
      Variant.feeOf, Variant.credit, Variant.retData]

theorem staRead_sstore_bal {crypto : Crypto} {Act : Finset Address} {w : World} {t a : Address}
    (hS : staSound crypto Act) (ha : a ∈ Act) (x : Word) :
    staRead crypto Act (w.sstore t (balSlot crypto a) x) t =
      { staRead crypto Act w t with bal := (staRead crypto Act w t).bal.update a x.toNat } := by
  simp only [staRead, balSlot]
  rw [BNB.Spec.readMap_sstore hS (by simp) ha, BNB.Spec.readMap2_sstore_map hS (by simp) (by simp) ha]
  simp only [readSlot, BNB.Spec.sload_sstore_map (k := 5#256) (base := 3#256) (x := x) (t := t) (w := w) hS
    (by simp) (by simp) ha, BNB.Spec.sload_sstore_map (k := 6#256) (base := 3#256) (x := x) (t := t) (w := w) hS
    (by simp) (by simp) ha, World.balance_sstore]
  rfl

theorem staRead_sstore_supply {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address}
    (hS : staSound crypto Act) (h6 : w.sload t 6#256 = 100#256) (x : Word) :
    staRead crypto Act (w.sstore t 5#256 x) t =
      { staRead crypto Act w t with supply := x.toNat } := by
  simp only [staRead]
  rw [BNB.Spec.readMap_sstore_fixed hS (by simp) (by simp),
    BNB.Spec.readMap2_sstore_fixed hS (by simp) (by simp)]
  simp only [readSlot, World.sload_sstore_self,
    World.sload_sstore_ne_key _ _ _ (show (6#256 : Word) ≠ 5#256 by decide), h6,
    World.balance_sstore]
  simp

theorem sta_wf_facts {Act : Finset Address} {m : Machine}
    (hs : Start STA.runtimeCode staAbs M Act m) (hv : m.frame.msg.value = 0) :
    m.world.sload m.frame.msg.currentTarget 6#256 = 100#256 ∧
      total (staRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).bal =
        (m.world.sload m.frame.msg.currentTarget 5#256).toNat := by
  have h := hs.wf
  rw [pre_eq hs hv] at h
  simp only [M, QEDefi.ERC20.Spec.STA.staModel, Variant.model_wf, Variant.WF, Variant.sta,
    Variant.standard] at h
  simp only [Bool.false_eq_true, ite_false, reduceCtorEq] at h
  by_cases h6 : readSlot m.world m.frame.msg.currentTarget 6#256 = 100
  · have h6' : m.world.sload m.frame.msg.currentTarget 6#256 = 100#256 := by
      apply BitVec.eq_of_toNat_eq; exact h6
    refine ⟨h6', ?_⟩
    have h1 := h.1
    simp only [staRead, h6, ite_true] at h1
    simp only [total, Finsupp.sum_zero_index, Nat.add_zero] at h1
    exact h1
  · have h2 := h.2
    simp only [staRead, h6, ite_false, QEDefi.Math.MAX] at h2
    omega

theorem sta_word_sub {v : ℕ} (hv : v < 2 ^ 256) : word v - word (cutN v) = word (v - cutN v) := by
  apply BitVec.eq_of_toNat_eq
  have hw : ∀ n, n < 2 ^ 256 → (word n).toNat = n := fun n hn => by
    rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hw _ hv, hw _ (sta_cutN_lt hv)]; exact sta_cutN_le v),
    hw _ hv, hw _ (sta_cutN_lt hv), hw _ (by omega)]

set_option linter.unusedSimpArgs false in
/-- **`transfer(dst, v)`**: the checks revert, an overflow computing `cut(v)` is `INVALID`;
otherwise the move with `cut(v)` burnt, `true`, two `Transfer`s. -/
theorem call_transfer (dst : Address) (v : ℕ) :
    CallSpec STA.runtimeCode staAbs M g₀ (.transfer dst v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hdA : dst ∈ Act := haddr dst (by simp [Call.addrs])
  have hcA := hs.caller
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  refine halts_split' (G := Normal g₀ m)
    (fun hG => transfer_high m dst (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1
      (sta_wf_facts hs hG.2.2).1)
    (transfer_low m dst (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hval0, hrev, hinv, hok⟩
  by_cases hv0 : m.frame.msg.value = 0
  swap
  · obtain ⟨out, rfl⟩ := hval0 hv0
    exact .inr ⟨trivial, fun hG => hv0 hG.2.2⟩
  left
  have hpre := pre_eq hs hv0
  obtain ⟨hbp, htot⟩ := sta_wf_facts hs hv0
  have hbalc := readMap_of_mem (crypto := m.ctx.crypto) hcA m.world m.frame.msg.currentTarget 3#256
  have hbald := readMap_of_mem (crypto := m.ctx.crypto) hdA m.world m.frame.msg.currentTarget 3#256
  have hsc : (pre staAbs Act m).bal m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
    rw [hpre]; exact hbalc
  rw [sta_call_transfer]
  by_cases hr : dst = 0 ∨ (pre staAbs Act m).bal m.frame.msg.caller < v
  · rw [ite_pos' hr]
    exact hrev (by rw [hwv, ← hsc]; exact hr)
  rw [ite_neg' hr]
  simp only [not_or, not_lt] at hr
  obtain ⟨hd0, hbc⟩ := hr
  rw [hsc] at hbc
  by_cases hov : 2 ^ 256 ≤ v + 100 ∨ 2 ^ 256 ≤ (v + 100 - 1) / 100 * 100 * 100
  · rw [ite_pos' hov]
    exact hinv hd0 (by rw [hwv]; exact hbc) hbp (by rw [hwv]; exact hov)
  rw [ite_neg' hov]
  simp only [not_or, not_le] at hov
  obtain ⟨hov1, hov2⟩ := hov
  have hbS := (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).isLt
  have hle : (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat ≤
      (m.world.sload m.frame.msg.currentTarget 5#256).toNat := by
    rw [← htot, ← hbalc]; exact QEDefi.ERC20.Token.le_total _ _
  have hS5 := (m.world.sload m.frame.msg.currentTarget 5#256).isLt
  have hfv := sta_cutN_le v
  have hfit : ((debitWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller
      (word v)).sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat +
      ((word v).toNat - cutN (word v).toNat) < 2 ^ 256 := by
    rw [hwv]
    simp only [debitWorld]
    by_cases hcd : m.frame.msg.caller = dst
    · rw [← hcd, World.sload_sstore_self, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hwv]; exact hbc),
        hwv]
      omega
    · have hne : balSlot m.ctx.crypto dst ≠ balSlot m.ctx.crypto m.frame.msg.caller := fun e =>
        hcd (hs.sound.inj1 3#256 (by simp) 3#256 (by simp) dst hdA _ hcA e).1.symm
      rw [World.sload_sstore_ne_key _ _ _ hne]
      have h2 := QEDefi.ERC20.add_le_total
        (f := (staRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).bal) hcd
      simp only [staRead] at h2 htot
      rw [hbalc, hbald] at h2
      simp only [balSlot] at *
      omega
  have hS2 : (creditWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller dst
      (word v) (word (cutN (word v).toNat))).sload m.frame.msg.currentTarget 5#256 =
      m.world.sload m.frame.msg.currentTarget 5#256 := by
    simp only [creditWorld, debitWorld, balSlot]
    rw [BNB.Spec.sload_sstore_map (k := 5#256) hs.sound (by simp) (by simp) hdA,
      BNB.Spec.sload_sstore_map (k := 5#256) hs.sound (by simp) (by simp) hcA]
  obtain ⟨hv, -, ho, hw, ht, hcr, hl⟩ := hok hd0 (by rw [hwv]; exact hbc) hbp (by rw [hwv]; omega)
    (by rw [hwv]; omega) hfit (by rw [hS2, hwv]; omega)
  have hcw : (word (cutN v)).toNat = cutN v := by
    rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (sta_cutN_lt hv256)]
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show staRead _ _ _ _ = _
    have hc2 : (creditWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller dst
        (word v) (word (cutN (word v).toNat))).sload m.frame.msg.currentTarget 6#256 = 100#256 := by
      simp only [creditWorld, debitWorld, balSlot]
      rw [BNB.Spec.sload_sstore_map (k := 6#256) hs.sound (by simp) (by simp) hdA,
        BNB.Spec.sload_sstore_map (k := 6#256) hs.sound (by simp) (by simp) hcA, hbp]
    rw [hw, staMoveWorld, staRead_sstore_supply hs.sound hc2, hS2, creditWorld,
      staRead_sstore_bal hs.sound hdA, debitWorld, staRead_sstore_bal hs.sound hcA, hpre, hwv]
    have hsupp : (staRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).supply =
        (m.world.sload m.frame.msg.currentTarget 5#256).toNat := by
      simp [staRead, readSlot, hbp]
    have hcwv : (word (cutN v)).toNat = cutN v := hcw
    have hvw : (word v).toNat = v := hwv
    dsimp only
    congr 1
    · ext a
      simp only [Finsupp.update_apply, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
        Pi.sub_apply, Finsupp.single_apply]
      have hsub : (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller) -
          word v).toNat = (m.world.sload m.frame.msg.currentTarget
            (balSlot m.ctx.crypto m.frame.msg.caller)).toNat - v := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hvw]; exact hbc), hvw]
      have hfw : (word v - word (cutN v)).toNat = v - cutN v := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hvw, hcwv]; exact hfv), hvw, hcwv]
      by_cases hcd : m.frame.msg.caller = dst
      · subst hcd
        rw [World.sload_sstore_self]
        have hadd : (word v - word (cutN v) + (m.world.sload m.frame.msg.currentTarget
            (balSlot m.ctx.crypto m.frame.msg.caller) - word v)).toNat =
            (m.world.sload m.frame.msg.currentTarget
              (balSlot m.ctx.crypto m.frame.msg.caller)).toNat - cutN v := by
          rw [BitVec.toNat_add, hfw, hsub, Nat.mod_eq_of_lt (by omega)]; omega
        by_cases ha : a = m.frame.msg.caller
        · subst ha; simp only [staRead, readMap_of_mem hcA, hadd, ite_true]; rw [← hbalc]
          simp only [balSlot] at *; omega
        · simp [ha, Ne.symm ha, staRead]
      · have hne : balSlot m.ctx.crypto dst ≠ balSlot m.ctx.crypto m.frame.msg.caller := fun e =>
          hcd (hs.sound.inj1 3#256 (by simp) 3#256 (by simp) dst hdA _ hcA e).1.symm
        rw [World.sload_sstore_ne_key _ _ _ hne]
        have hfit' := hfit
        simp only [debitWorld] at hfit'
        rw [World.sload_sstore_ne_key _ _ _ hne, hvw] at hfit'
        have hadd : (word v - word (cutN v) + m.world.sload m.frame.msg.currentTarget
            (balSlot m.ctx.crypto dst)).toNat = v - cutN v + (m.world.sload m.frame.msg.currentTarget
              (balSlot m.ctx.crypto dst)).toNat := by
          rw [BitVec.toNat_add, hfw, Nat.mod_eq_of_lt (by omega)]
        by_cases ha : a = dst
        · subst ha
          simp only [staRead, readMap_of_mem hdA, hadd, ite_true, hcd, Ne.symm hcd, ite_false]
          simp only [balSlot] at *; omega
        · by_cases hac : a = m.frame.msg.caller
          · subst hac
            simp only [staRead, readMap_of_mem hcA, hsub, ha, ite_true, ite_false,
              show ¬ dst = m.frame.msg.caller from fun e => ha e.symm]
            simp only [balSlot] at *; omega
          · simp [ha, hac, Ne.symm ha, Ne.symm hac, staRead]
    · rw [hsupp, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hcwv]; omega), hcwv]
  · rw [hw, staMoveWorld, creditWorld, debitWorld]
    exact BNB.Spec.FrameKeeps.sstore' (.inl rfl)
      (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hdA, rfl⟩)))
        (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hcA, rfl⟩))) BNB.Spec.frameKeeps_refl'))
  · rw [hl, hwv, sta_word_sub hv256]
    simp [M, QEDefi.ERC20.Spec.STA.staModel, QEDefi.ERC20.Spec.STA.staEvents, Spec.eventLog,
      Variant.feeOf, Variant.sta, Variant.standard, cutN]
    rfl

end Verified.WeirdERC20.STA.Spec
