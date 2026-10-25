import Verified.WeirdERC20.AMPL.Spec.Transfer
import QEDefi.ERC20.Rep

/-!
# AMPL under the spec: the `transfer` obligation

The code-level runs (`transfer_high`, `transfer_low`) against the model. The model's invariant
(`Start.wf`: the actors' gons add up to `TOTAL_GONS < 2²⁵⁶`) makes the credit fit; a gon value
that wraps exceeds every balance, so the code's `mul` check and the model's balance check
agree.
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

set_option linter.unusedSimpArgs false in
theorem ampl_call_transfer (s : VState Address) (c d : Address) (v : ℕ) :
    M.call s c (.transfer d v) =
      if d = 0 ∨ d = s.self ∨ s.bal c < s.scale * v then .halt .revert
      else .ok { s with
        bal := (s.bal - Finsupp.single c (s.scale * v) + Finsupp.single d (s.scale * v)) }
        (.word true) := by
  simp only [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.model_call]
  by_cases h1 : d = 0
  · subst h1
    simp [Variant.call, Variant.step, Variant.transfer, Variant.moveOk, Variant.ampl,
      Variant.standard, Variant.failKind, Variant.guardOk, Variant.failWith]
  have h1' : ¬ d = 0#160 := h1
  by_cases h2 : d = s.self
  · simp [h1', h2, Variant.call, Variant.step, Variant.transfer, Variant.moveOk, Variant.ampl,
      Variant.standard, Variant.failKind, Variant.guardOk, Variant.failWith]
  rw [Nat.mul_comm s.scale v]
  by_cases h3 : s.bal c < v * s.scale
  · simp [h1', h2, h3, Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      Variant.move, Variant.units, Variant.ampl, Variant.standard, Variant.failKind,
      Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith]
  · simp [h1', h2, h3, Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      Variant.move, Variant.units, Variant.ampl, Variant.standard, Variant.feeOverflow,
      Variant.feeOf, Variant.credit, Variant.retData]

theorem amplRead_sstore_bal {crypto : Crypto} {Act : Finset Address} {w : World} {t a : Address}
    (hS : amplSound crypto Act) (ha : a ∈ Act) (x : Word) :
    amplRead crypto Act (w.sstore t (balSlot crypto a) x) t =
      { amplRead crypto Act w t with bal := (amplRead crypto Act w t).bal.update a x.toNat } := by
  simp only [amplRead, balSlot]
  rw [BNB.Spec.readMap_sstore hS (by simp) ha,
    BNB.Spec.readMap_sstore_other (base' := 160#256) hS (by simp) (by simp) (by decide) ha,
    BNB.Spec.readMap2_sstore_map hS (by simp) (by simp) ha]
  simp only [readSlot, BNB.Spec.sload_sstore_map (k := 156#256) (base := 158#256) (x := x) (t := t)
    (w := w) hS (by simp) (by simp) ha, BNB.Spec.sload_sstore_map (k := 157#256) (base := 158#256)
    (x := x) (t := t) (w := w) hS (by simp) (by simp) ha, BNB.Spec.sload_sstore_map (k := 155#256)
    (base := 158#256) (x := x) (t := t) (w := w) hS (by simp) (by simp) ha, World.balance_sstore]

theorem ampl_total_lt {Act : Finset Address} {m : Machine}
    (hs : Start AMPL.runtimeCode amplAbs M Act m) (hv : m.frame.msg.value = 0) :
    total (amplRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).bal < 2 ^ 256 := by
  have h := hs.wf
  rw [pre_eq hs hv] at h
  simp only [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.model_wf, Variant.WF, Variant.ampl,
    Variant.standard, ite_true] at h
  rw [h.1]
  unfold Variant.amplTotalGons QEDefi.Math.MAX
  omega

set_option linter.unusedSimpArgs false in
/-- **`transfer(dst, v)`**: a zero or self recipient or a balance below `v · gonsPerFragment`
reverts; otherwise the move of `v · gonsPerFragment` gons, `true`, `Transfer`. -/
theorem call_transfer (dst : Address) (v : ℕ) :
    CallSpec AMPL.runtimeCode amplAbs M g₀ (.transfer dst v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hdA : dst ∈ Act := haddr dst (by simp [Call.addrs])
  have hcA := hs.caller
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  refine halts_split' (G := Normal g₀ m)
    (fun hG => transfer_high m dst (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1)
    (transfer_low m dst (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hval0, hrev, hok⟩
  by_cases hv0 : m.frame.msg.value = 0
  swap
  · obtain ⟨out, rfl⟩ := hval0 hv0
    exact .inr ⟨trivial, fun hG => hv0 hG.2.2⟩
  left
  have hpre := pre_eq hs hv0
  have htot := ampl_total_lt hs hv0
  have hbalc := readMap_of_mem (crypto := m.ctx.crypto) hcA m.world m.frame.msg.currentTarget 158#256
  have hbald := readMap_of_mem (crypto := m.ctx.crypto) hdA m.world m.frame.msg.currentTarget 158#256
  have hsc : (pre amplAbs Act m).bal m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
    rw [hpre]; exact hbalc
  have hscale : (pre amplAbs Act m).scale =
      (m.world.sload m.frame.msg.currentTarget 157#256).toNat := by
    rw [hpre]; rfl
  have hself : (pre amplAbs Act m).self = m.frame.msg.currentTarget := by rw [hpre]; rfl
  rw [ampl_call_transfer, hscale, hself, hsc]
  by_cases hr : dst = 0 ∨ dst = m.frame.msg.currentTarget ∨
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat <
        (m.world.sload m.frame.msg.currentTarget 157#256).toNat * v
  · rw [ite_pos' hr]
    exact hrev (by rw [hwv]; exact hr)
  rw [ite_neg' hr]
  simp only [not_or, not_lt] at hr
  obtain ⟨hd0, hdt, hbc⟩ := hr
  have hle : (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat < 2 ^ 256 := BitVec.isLt _
  have hgv : (m.world.sload m.frame.msg.currentTarget 157#256 * word v).toNat =
      (m.world.sload m.frame.msg.currentTarget 157#256).toNat * v := by
    rw [BitVec.toNat_mul, hwv, Nat.mod_eq_of_lt (by omega)]
  have hfit : ((debitWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller
      (m.world.sload m.frame.msg.currentTarget 157#256 * word v)).sload m.frame.msg.currentTarget
        (balSlot m.ctx.crypto dst)).toNat +
      (m.world.sload m.frame.msg.currentTarget 157#256).toNat * v < 2 ^ 256 := by
    simp only [debitWorld]
    by_cases hcd : m.frame.msg.caller = dst
    · rw [← hcd, World.sload_sstore_self,
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hgv]; exact hbc), hgv]
      omega
    · have hne : balSlot m.ctx.crypto dst ≠ balSlot m.ctx.crypto m.frame.msg.caller := fun e =>
        hcd (hs.sound.inj1 158#256 (by simp) 158#256 (by simp) dst hdA _ hcA e).1.symm
      rw [World.sload_sstore_ne_key _ _ _ hne]
      have h2 := QEDefi.ERC20.add_le_total
        (f := (amplRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).bal) hcd
      simp only [amplRead] at h2 htot
      rw [hbalc, hbald] at h2
      simp only [balSlot] at *
      omega
  obtain ⟨hv, -, ho, hw, ht, hcr, hl⟩ := hok hd0 hdt (by rw [hwv]; exact hbc)
    (by rw [hwv]; exact hfit)
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show amplRead _ _ _ _ = _
    rw [hw, moveWorld, amplRead_sstore_bal hs.sound hdA, debitWorld,
      amplRead_sstore_bal hs.sound hcA, hpre]
    dsimp only
    congr 1
    ext a
    simp only [Finsupp.update_apply, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
      Pi.sub_apply, Finsupp.single_apply]
    have hsub : (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller) -
        m.world.sload m.frame.msg.currentTarget 157#256 * word v).toNat =
        (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat -
          (m.world.sload m.frame.msg.currentTarget 157#256).toNat * v := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hgv]; exact hbc), hgv]
    by_cases hcd : m.frame.msg.caller = dst
    · subst hcd
      rw [World.sload_sstore_self]
      have hadd : (m.world.sload m.frame.msg.currentTarget 157#256 * word v +
          (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller) -
            m.world.sload m.frame.msg.currentTarget 157#256 * word v)).toNat =
          (m.world.sload m.frame.msg.currentTarget
            (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
        rw [BitVec.add_comm, BitVec.sub_add_cancel]
      by_cases ha : a = m.frame.msg.caller
      · subst ha; simp only [amplRead, readMap_of_mem hcA, hadd, ite_true]; rw [← hbalc]
        simp only [balSlot] at *; omega
      · simp [ha, Ne.symm ha, amplRead]
    · have hne : balSlot m.ctx.crypto dst ≠ balSlot m.ctx.crypto m.frame.msg.caller := fun e =>
        hcd (hs.sound.inj1 158#256 (by simp) 158#256 (by simp) dst hdA _ hcA e).1.symm
      rw [World.sload_sstore_ne_key _ _ _ hne]
      have hfit' := hfit
      simp only [debitWorld] at hfit'
      rw [World.sload_sstore_ne_key _ _ _ hne] at hfit'
      have hadd : (m.world.sload m.frame.msg.currentTarget 157#256 * word v +
          m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat =
          (m.world.sload m.frame.msg.currentTarget 157#256).toNat * v +
            (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat := by
        rw [BitVec.toNat_add, hgv, Nat.mod_eq_of_lt (by omega)]
      by_cases ha : a = dst
      · subst ha
        simp only [amplRead, readMap_of_mem hdA, hadd, ite_true, hcd, Ne.symm hcd, ite_false]
        simp only [balSlot] at *; omega
      · by_cases hac : a = m.frame.msg.caller
        · subst hac
          simp only [amplRead, readMap_of_mem hcA, hsub, ha, ite_true, ite_false,
            show ¬ dst = m.frame.msg.caller from fun e => ha e.symm]
          simp only [balSlot] at *; omega
        · simp [ha, hac, Ne.symm ha, Ne.symm hac, amplRead]
  · rw [hw, moveWorld, debitWorld]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inl ⟨_, hdA, rfl⟩))))
      (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inl ⟨_, hcA, rfl⟩))))
        BNB.Spec.frameKeeps_refl')
  · rw [hl]
    simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, QEDefi.ERC20.Spec.AMPL.amplEvents, Spec.eventLog]

end Verified.WeirdERC20.AMPL.Spec
