import Verified.WeirdERC20.STA.Spec.TransferFrom
import Verified.WeirdERC20.STA.Spec.TransferCall

/-!
# STA under the spec: the `transferFrom` obligation

The code-level runs (`transferFrom_high`, `transferFrom_low`) against the model: `basePercent =
100`, the credit, the burn and the allowance re-read after the move come from the model's
invariant and the actors' distinct rows (`Start.wf`, `Start.sound`).
-/

namespace Verified.WeirdERC20.STA.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.STA.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

set_option linter.unusedSimpArgs false in
theorem sta_call_transferFrom (s : VState Address) (c src d : Address) (v : ℕ) :
    M.call s c (.transferFrom src d v) =
      if d = 0 ∨ s.bal src < v ∨ s.allowance src c < v then .halt .revert
      else if 2 ^ 256 ≤ v + 100 ∨ 2 ^ 256 ≤ (v + 100 - 1) / 100 * 100 * 100 then .halt .invalid
      else .ok (VState.setAllowance
        { s with
          bal := s.bal - Finsupp.single src v + Finsupp.single d v - Finsupp.single d (cutN v)
          supply := s.supply - cutN v }
        src c (s.allowance src c - v)) (.word true) := by
  simp only [M, QEDefi.ERC20.Spec.STA.staModel, Variant.model_call]
  by_cases h1 : d = 0
  · subst h1
    simp [Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk, Variant.sta,
      Variant.standard, Variant.failKind, Variant.guardOk, Variant.failWith]
  have h1' : ¬ d = 0#160 := h1
  by_cases ha : s.allowance src c < v
  · simp [h1', ha, Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk,
      Variant.spend, Variant.move, Variant.units, Variant.sta, Variant.standard, Variant.failKind,
      Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith,
      Infinite.test]
  by_cases h2 : s.bal src < v
  · have h2' : ¬ v ≤ s.bal src := by omega
    simp [h1', h2, h2', ha, Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk,
      Variant.spend, Variant.move, Variant.units, Variant.sta, Variant.standard, Variant.failKind,
      Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith,
      Infinite.test, VState.setAllowance]
  have h2' : v ≤ s.bal src := by omega
  by_cases h3 : 2 ^ 256 ≤ v + 100 ∨ 2 ^ 256 ≤ (v + 100 - 1) / 100 * 100 * 100
  · have h3n : 115792089237316195423570985008687907853269984665640564039457584007913129639836 ≤ v ∨ 115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤ (v + 99) / 100 * 100 * 100 := by
      have e : v + 100 - 1 = v + 99 := by omega
      rw [e] at h3; norm_num at h3 ⊢; omega
    have hm : QEDefi.Math.MAX < v + 100 ∨ QEDefi.Math.MAX < (v + 99) / 100 * 100 * 100 := by
      unfold QEDefi.Math.MAX; omega
    simp [h1', h2, h2', ha, h3n, hm, Variant.call, Variant.step, Variant.transferFrom,
      Variant.moveOk, Variant.spend, Variant.move, Variant.units, Variant.sta, Variant.standard,
      Variant.failKind, Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith,
      Infinite.test, VState.setAllowance]
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
  rw [ite_neg' (by tauto), ite_neg' h3, hcut]
  by_cases h5 : (v + 99) / 100 * 100 * 100 / 10000 = 0
  · simp [h1', h2, ha, h3a, h3b, hmA, hmB, h4, h5, Variant.call, Variant.step,
      Variant.transferFrom, Variant.moveOk, Variant.spend, Variant.move, Variant.units,
      Variant.sta, Variant.standard, Variant.feeOverflow, Variant.feeOf, Variant.credit,
      Variant.retData, Infinite.test, VState.setAllowance]
  · simp [h1', h2, ha, h3a, h3b, hmA, hmB, h4, h5, Variant.call, Variant.step,
      Variant.transferFrom, Variant.moveOk, Variant.spend, Variant.move, Variant.units,
      Variant.sta, Variant.standard, Variant.feeOverflow, Variant.feeOf, Variant.credit,
      Variant.retData, Infinite.test, VState.setAllowance]

set_option linter.unusedSimpArgs false in
/-- **Statera's move through the abstraction**: the debit, the credit of `v − cut(v)` and the
burn, when the source covers `v`, the credit fits and the supply covers the burn. -/
theorem staRead_staMoveWorld {crypto : Crypto} {Act : Finset Address} {w : World}
    {t c d : Address} {v : ℕ} (hS : staSound crypto Act) (hc : c ∈ Act) (hd : d ∈ Act)
    (hv256 : v < 2 ^ 256) (hbp : w.sload t 6#256 = 100#256)
    (hbc : v ≤ (w.sload t (balSlot crypto c)).toNat)
    (hfit : ((debitWorld crypto w t c (word v)).sload t (balSlot crypto d)).toNat +
      (v - cutN v) < 2 ^ 256)
    (hsup : cutN v ≤ (w.sload t 5#256).toNat) :
    staRead crypto Act (staMoveWorld crypto w t c d (word v) (word (cutN v))) t =
      { staRead crypto Act w t with
        bal := (staRead crypto Act w t).bal - Finsupp.single c v + Finsupp.single d v -
          Finsupp.single d (cutN v),
        supply := (staRead crypto Act w t).supply - cutN v } := by
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  have hcw : (word (cutN v)).toNat = cutN v := by
    rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (sta_cutN_lt hv256)]
  have hfv := sta_cutN_le v
  have hbalc := readMap_of_mem (crypto := crypto) hc w t 3#256
  have hbald := readMap_of_mem (crypto := crypto) hd w t 3#256
  have hS2 : (creditWorld crypto w t c d (word v) (word (cutN v))).sload t 5#256 =
      w.sload t 5#256 := by
    simp only [creditWorld, debitWorld, balSlot]
    rw [BNB.Spec.sload_sstore_map (k := 5#256) hS (by simp) (by simp) hd,
      BNB.Spec.sload_sstore_map (k := 5#256) hS (by simp) (by simp) hc]
  have hc2 : (creditWorld crypto w t c d (word v) (word (cutN v))).sload t 6#256 = 100#256 := by
    simp only [creditWorld, debitWorld, balSlot]
    rw [BNB.Spec.sload_sstore_map (k := 6#256) hS (by simp) (by simp) hd,
      BNB.Spec.sload_sstore_map (k := 6#256) hS (by simp) (by simp) hc, hbp]
  have hS5 := (w.sload t 5#256).isLt
  rw [staMoveWorld, staRead_sstore_supply hS hc2, hS2, creditWorld,
    staRead_sstore_bal hS hd, debitWorld, staRead_sstore_bal hS hc]
  have hsupp : (staRead crypto Act w t).supply =
      (w.sload t 5#256).toNat := by
    simp [staRead, readSlot, hbp]
  have hcwv : (word (cutN v)).toNat = cutN v := hcw
  have hvw : (word v).toNat = v := hwv
  dsimp only
  congr 1
  · ext a
    simp only [Finsupp.update_apply, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
      Pi.sub_apply, Finsupp.single_apply]
    have hsub : (w.sload t (balSlot crypto c) -
        word v).toNat = (w.sload t
          (balSlot crypto c)).toNat - v := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hvw]; exact hbc), hvw]
    have hfw : (word v - word (cutN v)).toNat = v - cutN v := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hvw, hcwv]; exact hfv), hvw, hcwv]
    by_cases hcd : c = d
    · subst d
      rw [World.sload_sstore_self]
      have hadd : (word v - word (cutN v) + (w.sload t
          (balSlot crypto c) - word v)).toNat =
          (w.sload t
            (balSlot crypto c)).toNat - cutN v := by
        rw [BitVec.toNat_add, hfw, hsub, Nat.mod_eq_of_lt (by omega)]; omega
      by_cases ha : a = c
      · subst a; simp only [staRead, readMap_of_mem hc, hadd, ite_true]; rw [← hbalc]
        simp only [balSlot] at *; omega
      · simp [ha, Ne.symm ha, staRead]
    · have hne : balSlot crypto d ≠ balSlot crypto c := fun e =>
        hcd (hS.inj1 3#256 (by simp) 3#256 (by simp) d hd _ hc e).1.symm
      rw [World.sload_sstore_ne_key _ _ _ hne]
      have hfit' := hfit
      simp only [debitWorld] at hfit'
      rw [World.sload_sstore_ne_key _ _ _ hne] at hfit'
      have hadd : (word v - word (cutN v) + w.sload t
          (balSlot crypto d)).toNat = v - cutN v + (w.sload t
            (balSlot crypto d)).toNat := by
        rw [BitVec.toNat_add, hfw, Nat.mod_eq_of_lt (by omega)]
      by_cases ha : a = d
      · subst a
        simp only [staRead, readMap_of_mem hd, hadd, ite_true, hcd, Ne.symm hcd, ite_false]
        simp only [balSlot] at *; omega
      · by_cases hac : a = c
        · subst a
          simp only [staRead, readMap_of_mem hc, hsub, ha, ite_true, ite_false,
            show ¬ d = c from fun e => ha e.symm]
          simp only [balSlot] at *; omega
        · simp [ha, hac, Ne.symm ha, Ne.symm hac, staRead]
  · rw [hsupp, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hcwv]; omega), hcwv]

/-- The move leaves an actor's allowance row: it writes two balance rows and the supply. -/
theorem sload_staMoveWorld_allow {crypto : Crypto} {Act : Finset Address} {w : World}
    {t o sp src dst : Address} {v fee : Word} (hS : staSound crypto Act) (ho : o ∈ Act)
    (hsp : sp ∈ Act) (hs : src ∈ Act) (hd : dst ∈ Act) :
    (staMoveWorld crypto w t src dst v fee).sload t (allowSlot crypto o sp) =
      w.sload t (allowSlot crypto o sp) := by
  simp only [staMoveWorld, creditWorld, debitWorld, balSlot, allowSlot]
  rw [World.sload_sstore_ne_key _ _ _ (fun e =>
      hS.fixed2 4#256 (by simp) o ho sp hsp (by rw [e]; simp)),
    World.sload_sstore_ne_key _ _ _ (fun e =>
      hS.disj 3#256 (by simp) 4#256 (by simp) dst hd o ho sp hsp e.symm),
    World.sload_sstore_ne_key _ _ _ (fun e =>
      hS.disj 3#256 (by simp) 4#256 (by simp) src hs o ho sp hsp e.symm)]

set_option linter.unusedSimpArgs false in
/-- **`transferFrom(src, dst, v)`**: the checks revert, an overflow computing `cut(v)` is
`INVALID`; otherwise the allowance spent and the move with `cut(v)` burnt, `true`, two
`Transfer`s. -/
theorem call_transferFrom (src dst : Address) (v : ℕ) :
    CallSpec STA.runtimeCode staAbs M g₀ (.transferFrom src dst v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hsA : src ∈ Act := haddr src (by simp [Call.addrs])
  have hdA : dst ∈ Act := haddr dst (by simp [Call.addrs])
  have hcA := hs.caller
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  have hdeb6 : ∀ x : Word, (debitWorld m.ctx.crypto m.world m.frame.msg.currentTarget src x).sload
      m.frame.msg.currentTarget 6#256 = m.world.sload m.frame.msg.currentTarget 6#256 := fun x => by
    simp only [debitWorld, balSlot]
    exact BNB.Spec.sload_sstore_map (k := 6#256) hs.sound (by simp) (by simp) hsA
  refine halts_split' (G := Normal g₀ m)
    (fun hG => transferFrom_high m src dst (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1
      (by rw [hdeb6]; exact (sta_wf_facts hs hG.2.2).1))
    (transferFrom_low m src dst (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hval0, hrev, hinv, hok⟩
  by_cases hv0 : m.frame.msg.value = 0
  swap
  · obtain ⟨out, rfl⟩ := hval0 hv0
    exact .inr ⟨trivial, fun hG => hv0 hG.2.2⟩
  left
  have hpre := pre_eq hs hv0
  obtain ⟨hbp, htot⟩ := sta_wf_facts hs hv0
  have hbals := readMap_of_mem (crypto := m.ctx.crypto) hsA m.world m.frame.msg.currentTarget 3#256
  have hbald := readMap_of_mem (crypto := m.ctx.crypto) hdA m.world m.frame.msg.currentTarget 3#256
  have hall : (staRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).allowance src
      m.frame.msg.caller = (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat := by
    simp [staRead, readMap2, hsA, hcA]
  have hsc : (pre staAbs Act m).bal src =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat := by
    rw [hpre]; exact hbals
  have hac' : (pre staAbs Act m).allowance src m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat := by
    rw [hpre]; exact hall
  rw [sta_call_transferFrom]
  by_cases hr : dst = 0 ∨ (pre staAbs Act m).bal src < v ∨
      (pre staAbs Act m).allowance src m.frame.msg.caller < v
  · rw [ite_pos' hr]
    exact hrev (by rw [hwv, ← hsc, ← hac']; exact hr)
  rw [ite_neg' hr]
  simp only [not_or, not_lt] at hr
  obtain ⟨hd0, hbc, hac⟩ := hr
  rw [hsc] at hbc
  rw [hac'] at hac
  have hbp1 : (debitWorld m.ctx.crypto m.world m.frame.msg.currentTarget src (word v)).sload
      m.frame.msg.currentTarget 6#256 = 100#256 := by rw [hdeb6]; exact hbp
  by_cases hov : 2 ^ 256 ≤ v + 100 ∨ 2 ^ 256 ≤ (v + 100 - 1) / 100 * 100 * 100
  · rw [ite_pos' hov]
    exact hinv hd0 (by rw [hwv]; exact hbc) (by rw [hwv]; exact hac) hbp1 (by rw [hwv]; exact hov)
  rw [ite_neg' hov]
  simp only [not_or, not_le] at hov
  obtain ⟨hov1, hov2⟩ := hov
  have hbS := (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).isLt
  have hle : (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat ≤
      (m.world.sload m.frame.msg.currentTarget 5#256).toNat := by
    rw [← htot, ← hbals]; exact QEDefi.ERC20.Token.le_total _ _
  have hS5 := (m.world.sload m.frame.msg.currentTarget 5#256).isLt
  have hfv := sta_cutN_le v
  have hfit : ((debitWorld m.ctx.crypto m.world m.frame.msg.currentTarget src
      (word v)).sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat +
      (v - cutN v) < 2 ^ 256 := by
    simp only [debitWorld]
    by_cases hcd : src = dst
    · rw [← hcd, World.sload_sstore_self, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hwv]; exact hbc),
        hwv]
      omega
    · have hne : balSlot m.ctx.crypto dst ≠ balSlot m.ctx.crypto src := fun e =>
        hcd (hs.sound.inj1 3#256 (by simp) 3#256 (by simp) dst hdA _ hsA e).1.symm
      rw [World.sload_sstore_ne_key _ _ _ hne]
      have h2 := QEDefi.ERC20.add_le_total
        (f := (staRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).bal) hcd
      simp only [staRead] at h2 htot
      rw [hbals, hbald] at h2
      simp only [balSlot] at *
      omega
  have hS2 : (creditWorld m.ctx.crypto m.world m.frame.msg.currentTarget src dst
      (word v) (word (cutN (word v).toNat))).sload m.frame.msg.currentTarget 5#256 =
      m.world.sload m.frame.msg.currentTarget 5#256 := by
    simp only [creditWorld, debitWorld, balSlot]
    rw [BNB.Spec.sload_sstore_map (k := 5#256) hs.sound (by simp) (by simp) hdA,
      BNB.Spec.sload_sstore_map (k := 5#256) hs.sound (by simp) (by simp) hsA]
  have hmw := sload_staMoveWorld_allow (w := m.world) (t := m.frame.msg.currentTarget)
    (v := word v) (fee := word (cutN (word v).toNat)) hs.sound hsA hcA hsA hdA
  obtain ⟨hv, -, ho, hw, ht, hcr, hl⟩ := hok hd0 (by rw [hwv]; exact hbc) (by rw [hwv]; exact hac)
    hbp1 (by rw [hwv]; omega) (by rw [hwv]; omega) (by rw [hwv]; exact hfit)
    (by rw [hS2, hwv]; omega) (by rw [hmw, hwv]; exact hac)
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show staRead _ _ _ _ = _
    have hsub : (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto src m.frame.msg.caller) - word v).toNat =
        (staRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).allowance src
          m.frame.msg.caller - v := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hwv]; exact hac), hwv, hall]
    rw [hw, tfWorld, hmw, allowSlot, staRead_sstore_allow hs.sound hsA hcA, hwv,
      staRead_staMoveWorld hs.sound hsA hdA hv256 hbp hbc hfit (by omega), hpre]
    rw [show (m.world.sload m.frame.msg.currentTarget
        (mappingSlot2 m.ctx.crypto (Word.ofAddress src) (Word.ofAddress m.frame.msg.caller) 4#256) -
          word v).toNat = _ from hsub]
  · rw [hw, tfWorld, staMoveWorld, creditWorld, debitWorld]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr ⟨_, hsA, _, hcA, rfl⟩)))
      (BNB.Spec.FrameKeeps.sstore' (.inl rfl)
        (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hdA, rfl⟩)))
          (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hsA, rfl⟩)))
            BNB.Spec.frameKeeps_refl')))
  · rw [hl, hwv, sta_word_sub hv256]
    simp [M, QEDefi.ERC20.Spec.STA.staModel, QEDefi.ERC20.Spec.STA.staEvents, Spec.eventLog,
      Variant.feeOf, Variant.sta, Variant.standard, cutN]
    rfl

end Verified.WeirdERC20.STA.Spec
