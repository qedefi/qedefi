import Verified.WeirdERC20.LEND.Spec.TransferFrom
import Verified.WeirdERC20.LEND.Spec.TransferCall

/-!
# LEND under the spec: the `transferFrom` obligation

`transferFrom_low`/`transferFrom_high` end in `TFPost`; here it is read through the
abstraction. Every allowance is spent, `2²⁵⁶ − 1` included; every failure reverts.
-/

namespace Verified.WeirdERC20.LEND.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.LEND.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open QEDefi.ERC4626

theorem lend_call_transferFrom (s : LEND.State Address) (c src d : Address) (v : ℕ)
    (he : s.enabled = true) :
    M.call s c (.transferFrom src d v) =
      if v ≤ s.allowance src c ∧ v ≤ s.bal src ∧ 0 < v ∧ s.bal d + v ≤ QEDefi.Math.MAX then
        .ok ({ s with bal := s.bal - Finsupp.single src v + Finsupp.single d v }.setAllowance
          src c (s.allowance src c - v)) (.word true)
      else .halt .revert := by
  simp only [M, QEDefi.ERC20.Spec.LEND.model, QEDefi.ERC20.Spec.LEND.call,
    QEDefi.ERC20.Spec.LEND.step, QEDefi.ERC20.Spec.LEND.transferFrom,
    QEDefi.ERC20.Spec.LEND.move, QEDefi.ERC20.Spec.LEND.retData, he, true_and]
  by_cases h1 : v ≤ s.allowance src c
  · by_cases h2 : v ≤ s.bal src ∧ 0 < v ∧ s.bal d + v ≤ QEDefi.Math.MAX
    · simp only [h1, h2, ite_true, and_self, Option.map_some]
    · simp only [h1, h2, ite_true, ite_false, Option.map_none, true_and]
  · simp only [h1, ite_false, false_and]

/-- **`transferFrom`'s move** (credit, then debit) through the abstraction. -/
theorem read_cdWorld {crypto : Crypto} {Act : Finset Address} {w : World} {t c d : Address}
    {v : Word} (hS : abs.Sound crypto Act) (hc : c ∈ Act) (hd : d ∈ Act)
    (hv : v.toNat ≤ (w.sload t (balSlot crypto c)).toNat)
    (hov : (w.sload t (balSlot crypto d)).toNat + v.toNat < 2 ^ 256) :
    read crypto Act (cdWorld crypto w t c d v) t =
      { read crypto Act w t with
        bal := (read crypto Act w t).bal - Finsupp.single c v.toNat +
          Finsupp.single d v.toNat } := by
  change v.toNat ≤ (w.sload t (mappingSlot crypto (Word.ofAddress c) balancesSlot)).toNat at hv
  change (w.sload t (mappingSlot crypto (Word.ofAddress d) balancesSlot)).toNat + v.toNat <
    2 ^ 256 at hov
  simp only [cdWorld, balSlot]
  rw [show (0#256 : Word) = balancesSlot from rfl, read_sstore_bal hS hc, read_sstore_bal hS hd]
  dsimp only
  congr 1
  have hrc : (read crypto Act w t).bal c =
      (w.sload t (mappingSlot crypto (Word.ofAddress c) balancesSlot)).toNat :=
    readMap_of_mem hc _ _ _
  have hrd : (read crypto Act w t).bal d =
      (w.sload t (mappingSlot crypto (Word.ofAddress d) balancesSlot)).toNat :=
    readMap_of_mem hd _ _ _
  have hadd : (w.sload t (mappingSlot crypto (Word.ofAddress d) balancesSlot) + v).toNat =
      (w.sload t (mappingSlot crypto (Word.ofAddress d) balancesSlot)).toNat + v.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hov]
  ext a
  simp only [Finsupp.update_apply, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    Finsupp.single_apply]
  by_cases hcd : c = d
  · subst hcd
    rw [World.sload_sstore_self, BitVec.add_sub_cancel]
    by_cases ha : a = c
    · subst ha; simp [hrc]; omega
    · simp [ha, Ne.symm ha]
  · have hne : mappingSlot crypto (Word.ofAddress c) balancesSlot ≠
        mappingSlot crypto (Word.ofAddress d) balancesSlot := fun e =>
      hcd (hS.inj1 balancesSlot (by simp) balancesSlot (by simp) c hc d hd e).1
    rw [World.sload_sstore_ne_key _ _ _ hne]
    have hsub : (w.sload t (mappingSlot crypto (Word.ofAddress c) balancesSlot) - v).toNat =
        (w.sload t (mappingSlot crypto (Word.ofAddress c) balancesSlot)).toNat - v.toNat := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hv)]
    by_cases ha : a = c
    · subst ha; simp [hrc, hsub, Ne.symm hcd]
    · by_cases had : a = d
      · subst had; simp [hrd, ha, hadd, Ne.symm ha]
      · simp [ha, had, Ne.symm ha, Ne.symm had]

/-- The move leaves an actor's allowance row: it writes two balance rows. -/
theorem sload_cdWorld_allow {crypto : Crypto} {Act : Finset Address} {w : World}
    {t o sp src dst : Address} {v : Word} (hS : abs.Sound crypto Act) (ho : o ∈ Act)
    (hsp : sp ∈ Act) (hs : src ∈ Act) (hd : dst ∈ Act) :
    (cdWorld crypto w t src dst v).sload t (allowSlot crypto o sp) =
      w.sload t (allowSlot crypto o sp) := by
  simp only [cdWorld, balSlot, allowSlot]
  rw [show (0#256 : Word) = balancesSlot from rfl, show (1#256 : Word) = allowedSlot from rfl,
    World.sload_sstore_ne_key _ _ _ (fun e =>
      hS.disj balancesSlot (by simp) allowedSlot (by simp) src hs o ho sp hsp e.symm),
    World.sload_sstore_ne_key _ _ _ (fun e =>
      hS.disj balancesSlot (by simp) allowedSlot (by simp) dst hd o ho sp hsp e.symm)]

/-- **`transferFrom(src, dst, v)`**: a short balance or allowance, a zero value or a wrapping
credit revert; otherwise the move and the allowance spent, `Transfer`, `true`. -/
theorem call_transferFrom (src dst : Address) (v : ℕ) :
    CallSpec LEND.runtimeCode abs M g₀ (.transferFrom src dst v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hsA : src ∈ Act := haddr src (by simp [Call.addrs])
  have hdA : dst ∈ Act := haddr dst (by simp [Call.addrs])
  have hcA := hs.caller
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  have hpre := pre_eq hs
  have hbs : (pre abs Act m).bal src =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat := by
    rw [hpre]; exact readMap_of_mem hsA _ _ _
  have hbd : (pre abs Act m).bal dst =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat := by
    rw [hpre]; exact readMap_of_mem hdA _ _ _
  have hal : (pre abs Act m).allowance src m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat := by
    rw [hpre]; simp [read, readMap2, hsA, hcA, allowedSlot]
  have hmw := sload_cdWorld_allow (w := m.world) (t := m.frame.msg.currentTarget)
    (v := word v) hs.sound hsA hcA hsA hdA
  refine halts_split' (G := Normal g₀ m)
    (fun hG => transferFrom_high m src dst (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1
      (enabled_word hs))
    (transferFrom_low m src dst (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, -, hok⟩
  rw [hwv] at hrev
  rw [hmw, hwv] at hok
  rw [lend_call_transferFrom _ _ _ _ _ (pre_enabled hs), hbs, hbd, hal]
  by_cases hg : v ≤ (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat ∧
      v ≤ (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat ∧ 0 < v ∧
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat + v ≤
        QEDefi.Math.MAX
  · left
    rw [ite_pos' hg]
    obtain ⟨h1, h2, h3, h4⟩ := hg
    have h4' : (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat + v <
        2 ^ 256 := by simp only [QEDefi.Math.MAX] at h4; omega
    obtain ⟨-, -, ho, hw, ht, hcr, hl⟩ := hok h2 h1 h3 h4' h1
    refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
    · show read _ _ _ _ = _
      have hsub : (m.world.sload m.frame.msg.currentTarget
          (allowSlot m.ctx.crypto src m.frame.msg.caller) - word v).toNat =
          (m.world.sload m.frame.msg.currentTarget
            (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat - v := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hwv]; exact h1), hwv]
      rw [hw, tfWorld, hmw]
      simp only [allowSlot]
      rw [show (1#256 : Word) = allowedSlot from rfl, read_sstore_allow hs.sound hsA hcA,
        read_cdWorld hs.sound hsA hdA (by rw [hwv]; exact h2) (by rw [hwv]; exact h4'),
        ← hpre, hwv]
      simp only [allowSlot] at hsub
      rw [show (1#256 : Word) = allowedSlot from rfl] at hsub
      rw [hsub]
    · rw [hw, tfWorld, cdWorld]
      exact BNB.Spec.FrameKeeps.sstore' (allow_mem hsA hcA)
        (BNB.Spec.FrameKeeps.sstore' (bal_mem hsA)
          (BNB.Spec.FrameKeeps.sstore' (bal_mem hdA) BNB.Spec.frameKeeps_refl'))
    · rw [hl]
      simp [M, QEDefi.ERC20.Spec.LEND.model, QEDefi.ERC20.Spec.LEND.events, Spec.eventLog]
  · rw [ite_neg' hg]
    obtain ⟨out, rfl⟩ := hrev (by simp only [QEDefi.Math.MAX] at hg; omega)
    by_cases hG : Normal g₀ m
    · exact .inl ⟨out, rfl⟩
    · exact .inr ⟨trivial, hG⟩

end Verified.WeirdERC20.LEND.Spec
