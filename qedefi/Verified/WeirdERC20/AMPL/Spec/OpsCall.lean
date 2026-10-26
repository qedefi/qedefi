import Verified.WeirdERC20.AMPL.Spec.Ops

/-!
# AMPL under the spec: the obligation of the other entry points

The code-level runs (`Ops.lean`) against the model's `transferAll`, `transferAllFrom` and
(saturating) `adjustAllowance`. The model's invariant (`Start.wf`) gives `gonsPerFragment > 0`
(the supply is positive and at most `2¹²⁸ − 1`, far below `TOTAL_GONS`) and makes the credit fit;
the actors' distinct rows (`Start.sound`) keep the reads after the allowance write at their
starting values.
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')

set_option linter.unusedSimpArgs false in
theorem ampl_op_transferAll (s : VState Address) (c d : Address) :
    M.op s (.transferAll c d) = if d = 0 ∨ d = s.self then none
      else some { s with
        bal := (s.bal - Finsupp.single c (s.bal c) + Finsupp.single d (s.bal c)) } := by
  by_cases h1 : d = 0
  · subst h1
    simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.stepOp, Variant.transferAll,
      Variant.moveOk, Variant.ampl, Variant.standard]
  · have h1' : ¬ d = 0#160 := h1
    by_cases h2 : d = s.self
    · simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.stepOp, Variant.transferAll,
        Variant.moveOk, Variant.ampl, Variant.standard, h1', h2]
    · simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.stepOp, Variant.transferAll,
        Variant.moveOk, Variant.ampl, Variant.standard, h1', h2]

set_option linter.unusedSimpArgs false in
theorem ampl_op_transferAllFrom (s : VState Address) (c a d : Address) :
    M.op s (.transferAllFrom c a d) =
      if d = 0 ∨ d = s.self ∨ s.allowance a c < s.bal a / s.scale then none
      else some { s.setAllowance a c (s.allowance a c - s.bal a / s.scale) with
        bal := (s.bal - Finsupp.single a (s.bal a) + Finsupp.single d (s.bal a)) } := by
  by_cases h1 : d = 0
  · subst h1
    simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.stepOp, Variant.transferAllFrom,
      Variant.moveOk, Variant.ampl, Variant.standard]
  have h1' : ¬ d = 0#160 := h1
  by_cases h2 : d = s.self
  · simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.stepOp, Variant.transferAllFrom,
      Variant.moveOk, Variant.ampl, Variant.standard, h1', h2]
  by_cases h3 : s.allowance a c < s.bal a / s.scale
  · simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.stepOp, Variant.transferAllFrom,
      Variant.moveOk, Variant.spend, Variant.balanceOf, Variant.ampl, Variant.standard,
      Infinite.test, h1', h2, h3]
  · simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.stepOp, Variant.transferAllFrom,
      Variant.moveOk, Variant.spend, Variant.balanceOf, Variant.ampl, Variant.standard,
      Infinite.test, VState.setAllowance, h1', h2, h3]

set_option linter.unusedSimpArgs false in
theorem ampl_op_inc (s : VState Address) (c sp : Address) (x : ℕ) :
    M.op s (.adjustAllowance c sp true x) =
      if QEDefi.Math.MAX < s.allowance c sp + x then none
      else some (s.setAllowance c sp (s.allowance c sp + x)) := by
  by_cases h : QEDefi.Math.MAX < s.allowance c sp + x
  · simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.stepOp, Variant.adjustAllowance,
      Variant.ampl, Variant.standard, h]
  · simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.stepOp, Variant.adjustAllowance,
      Variant.ampl, Variant.standard, h]

theorem ampl_op_dec (s : VState Address) (c sp : Address) (x : ℕ) :
    M.op s (.adjustAllowance c sp false x) =
      some (s.setAllowance c sp (s.allowance c sp - x)) := by
  simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.stepOp, Variant.adjustAllowance,
    Variant.ampl, Variant.standard]

/-- Under the model's invariant `gonsPerFragment` is positive. -/
theorem ampl_scale_ne {Act : Finset Address} {m : Machine}
    (hs : Start AMPL.runtimeCode amplAbs M Act m) (hv : m.frame.msg.value = 0) :
    m.world.sload m.frame.msg.currentTarget 157#256 ≠ 0 := by
  have h := hs.wf
  rw [pre_eq hs hv] at h
  simp only [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.model_wf, Variant.WF, Variant.ampl,
    Variant.standard, ite_true] at h
  obtain ⟨-, hpos, hmax, hsc⟩ := h
  intro h0
  have hT : (amplRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).supply ≤
      Variant.amplTotalGons :=
    le_trans hmax (by norm_num [Variant.amplTotalGons, QEDefi.Math.MAX])
  have h1 := Nat.div_pos hT hpos
  rw [← hsc] at h1
  have h2 : (amplRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).scale =
      (m.world.sload m.frame.msg.currentTarget 157#256).toNat := rfl
  rw [h2, h0] at h1
  simp at h1

/-- `transferAll` through the abstraction. -/
theorem amplRead_allWorld {crypto : Crypto} {Act : Finset Address} {w : World}
    {t c d : Address} (hS : amplSound crypto Act) (hc : c ∈ Act) (hd : d ∈ Act)
    (hfit : (w.sload t (balSlot crypto c)).toNat +
      ((w.sstore t (balSlot crypto c) 0#256).sload t (balSlot crypto d)).toNat < 2 ^ 256) :
    amplRead crypto Act (allWorld crypto w t c d (w.sload t (balSlot crypto c))) t =
      { amplRead crypto Act w t with
        bal := (amplRead crypto Act w t).bal -
          Finsupp.single c (w.sload t (balSlot crypto c)).toNat +
          Finsupp.single d (w.sload t (balSlot crypto c)).toNat } := by
  have hbalc := readMap_of_mem (crypto := crypto) hc w t 158#256
  rw [allWorld, amplRead_sstore_bal hS hd, amplRead_sstore_bal hS hc]
  dsimp only
  congr 1
  ext b
  simp only [Finsupp.update_apply, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
    Pi.sub_apply, Finsupp.single_apply]
  by_cases hcd : c = d
  · subst d
    rw [World.sload_sstore_self]
    by_cases hb : b = c
    · subst b
      simp only [ite_true, amplRead]
      rw [hbalc]
      simp [balSlot]
    · simp [hb, Ne.symm hb, amplRead]
  · have hne : balSlot crypto d ≠ balSlot crypto c := fun e =>
      hcd (hS.inj1 158#256 (by simp) 158#256 (by simp) d hd _ hc e).1.symm
    rw [World.sload_sstore_ne_key _ _ _ hne] at hfit ⊢
    have hadd : (w.sload t (balSlot crypto c) + w.sload t (balSlot crypto d)).toNat =
        (w.sload t (balSlot crypto c)).toNat + (w.sload t (balSlot crypto d)).toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hfit]
    by_cases hb : b = d
    · subst b
      simp only [ite_true, hcd, Ne.symm hcd, ite_false, hadd, amplRead, readMap_of_mem hd,
        BitVec.toNat_ofNat, Nat.zero_mod]
      simp only [balSlot] at *; omega
    · by_cases hbc : b = c
      · subst b
        simp only [hb, ite_true, ite_false, amplRead, readMap_of_mem hc,
          show ¬ d = c from fun e => hb e.symm, BitVec.toNat_ofNat, Nat.zero_mod]
        rw [← hbalc]; simp only [balSlot] at *; omega
      · simp [hb, hbc, Ne.symm hb, Ne.symm hbc, amplRead]

/-- The credit of `transferAll` fits under the invariant. -/
theorem ampl_all_fit {Act : Finset Address} {m : Machine}
    (hs : Start AMPL.runtimeCode amplAbs M Act m) (hv : m.frame.msg.value = 0)
    {w : World} (hw : ∀ k, (k = 157#256 ∨ ∃ a ∈ Act, k = balSlot m.ctx.crypto a) →
      w.sload m.frame.msg.currentTarget k = m.world.sload m.frame.msg.currentTarget k)
    {c d : Address} (hc : c ∈ Act) (hd : d ∈ Act) :
    (w.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto c)).toNat +
      ((w.sstore m.frame.msg.currentTarget (balSlot m.ctx.crypto c) 0#256).sload
        m.frame.msg.currentTarget (balSlot m.ctx.crypto d)).toNat < 2 ^ 256 := by
  have htot := ampl_total_lt hs hv
  have hbalc := readMap_of_mem (crypto := m.ctx.crypto) hc m.world m.frame.msg.currentTarget 158#256
  have hbald := readMap_of_mem (crypto := m.ctx.crypto) hd m.world m.frame.msg.currentTarget 158#256
  rw [hw _ (.inr ⟨c, hc, rfl⟩)]
  by_cases hcd : c = d
  · subst d
    rw [World.sload_sstore_self]
    have := (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto c)).isLt
    simp; omega
  · have hne : balSlot m.ctx.crypto d ≠ balSlot m.ctx.crypto c := fun e =>
      hcd (hs.sound.inj1 158#256 (by simp) 158#256 (by simp) d hd _ hc e).1.symm
    rw [World.sload_sstore_ne_key _ _ _ hne, hw _ (.inr ⟨d, hd, rfl⟩)]
    have h2 := QEDefi.ERC20.add_le_total
      (f := (amplRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).bal) hcd
    simp only [amplRead] at h2 htot
    rw [hbalc, hbald] at h2
    simp only [balSlot] at *
    omega

theorem op_transferAll (Act : Finset Address) (m : Machine)
    (hs : Start AMPL.runtimeCode amplAbs M Act m) (d : Address) (hdA : d ∈ Act)
    (hval : m.frame.msg.value = 0) (hd : Args m.frame.msg.data 0xa3a7e7f3 [Word.ofAddress d]) :
    Halts m fun mf o =>
      OpMatches amplAbs M Act (.transferAll m.frame.msg.caller d) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  have hS := hs.sound
  have hcA := hs.caller
  have hpre := pre_eq hs hval
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => transferAll_high m d hs.fresh hd hs.size hval hG.2 hG.1)
    (transferAll_low m d hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  have hself : (pre amplAbs Act m).self = m.frame.msg.currentTarget := by rw [hpre]; rfl
  rw [ampl_op_transferAll, hself]
  by_cases hr : d = 0 ∨ d = m.frame.msg.currentTarget
  · rw [ite_pos' hr]
    exact hrev (by rcases hr with h | h; exact .inl h; exact .inr (.inl h))
  rw [ite_neg' hr]
  simp only [not_or] at hr
  obtain ⟨hd0, hdt⟩ := hr
  have hfit := ampl_all_fit hs hval (w := m.world) (fun _ _ => rfl) hcA hdA
  obtain ⟨ho, hw, ht, hcr⟩ := hok hd0 hdt (ampl_scale_ne hs hval) hfit
  refine ⟨ho, ?_, ?_, ht, hcr⟩
  · show amplRead _ _ _ _ = _
    rw [hw, amplRead_allWorld hS hcA hdA hfit, ← hpre]
    have hb : (pre amplAbs Act m).bal m.frame.msg.caller =
        (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
      rw [hpre]; simp [amplRead, hcA]
    rw [hb]
    dsimp only
    rw [hself]
  · rw [hw, allWorld]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inl ⟨_, hdA, rfl⟩))))
      (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inl ⟨_, hcA, rfl⟩))))
        BNB.Spec.frameKeeps_refl')

theorem amplRead_allWorld' {crypto : Crypto} {Act : Finset Address} {w : World}
    {t c d : Address} {g : Word} (hS : amplSound crypto Act) (hc : c ∈ Act) (hd : d ∈ Act)
    (hg : w.sload t (balSlot crypto c) = g)
    (hfit : (w.sload t (balSlot crypto c)).toNat +
      ((w.sstore t (balSlot crypto c) 0#256).sload t (balSlot crypto d)).toNat < 2 ^ 256) :
    amplRead crypto Act (allWorld crypto w t c d g) t =
      { amplRead crypto Act w t with
        bal := (amplRead crypto Act w t).bal - Finsupp.single c g.toNat +
          Finsupp.single d g.toNat } := by
  subst hg
  exact amplRead_allWorld hS hc hd hfit

theorem op_transferAllFrom (Act : Finset Address) (m : Machine)
    (hs : Start AMPL.runtimeCode amplAbs M Act m) (a d : Address) (haA : a ∈ Act) (hdA : d ∈ Act)
    (hval : m.frame.msg.value = 0)
    (hd : Args m.frame.msg.data 0x84d4b410 [Word.ofAddress a, Word.ofAddress d]) :
    Halts m fun mf o =>
      OpMatches amplAbs M Act (.transferAllFrom m.frame.msg.caller a d) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  have hS := hs.sound
  have hcA := hs.caller
  have hpre := pre_eq hs hval
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => transferAllFrom_high m a d hs.fresh hd hs.size hval hG.2 hG.1)
    (transferAllFrom_low m a d hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  set v := Word.div (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a))
    (m.world.sload m.frame.msg.currentTarget 157#256) with hv
  have hGne := ampl_scale_ne hs hval
  have hvn : v.toNat = (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a)).toNat /
      (m.world.sload m.frame.msg.currentTarget 157#256).toNat := by
    rw [hv, Word.div, BitVec.toNat_udiv]
  have hself : (pre amplAbs Act m).self = m.frame.msg.currentTarget := by rw [hpre]; rfl
  have hba : (pre amplAbs Act m).bal a =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a)).toNat := by
    rw [hpre]; simp [amplRead, haA]
  have hscale : (pre amplAbs Act m).scale =
      (m.world.sload m.frame.msg.currentTarget 157#256).toNat := by rw [hpre]; rfl
  have hal : (pre amplAbs Act m).allowance a m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto a m.frame.msg.caller)).toNat := by
    rw [hpre]; simp [amplRead, readMap2, haA, hcA]
  rw [ampl_op_transferAllFrom, hself, hba, hscale, hal, ← hvn]
  by_cases hr : d = 0 ∨ d = m.frame.msg.currentTarget ∨
      (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto a m.frame.msg.caller)).toNat <
        v.toNat
  · rw [ite_pos' hr]
    exact hrev (by
      rcases hr with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inr h)))
  rw [ite_neg' hr]
  simp only [not_or, not_lt] at hr
  obtain ⟨hd0, hdt, hac⟩ := hr
  have hW : ∀ k, (k = 157#256 ∨ ∃ b ∈ Act, k = balSlot m.ctx.crypto b) →
      (allowWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller a v).sload
        m.frame.msg.currentTarget k = m.world.sload m.frame.msg.currentTarget k :=
    fun k hk => sload_allowWorld hS hcA haA hk
  have hfit := ampl_all_fit hs hval hW haA hdA
  rw [hW _ (.inr ⟨a, haA, rfl⟩)] at hfit
  obtain ⟨ho, hw, ht, hcr⟩ := hok hd0 hdt hGne hac hfit
  refine ⟨ho, ?_, ?_, ht, hcr⟩
  · show amplRead _ _ _ _ = _
    have hfit1 := ampl_all_fit hs hval hW haA hdA
    rw [hw, allFromWorld]
    rw [show (m.world.sstore m.frame.msg.currentTarget (allowSlot m.ctx.crypto a m.frame.msg.caller)
        (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto a m.frame.msg.caller) - v)) =
        allowWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller a v from rfl]
    rw [amplRead_allWorld' hS haA hdA (hW _ (.inr ⟨a, haA, rfl⟩)) hfit1]
    rw [allowWorld, allowSlot, amplRead_sstore_allow hS haA hcA, ← hpre]
    have h1 : (m.world.sload m.frame.msg.currentTarget
        (mappingSlot2 m.ctx.crypto (Word.ofAddress a) (Word.ofAddress m.frame.msg.caller) 159#256) -
          v).toNat = (m.world.sload m.frame.msg.currentTarget
            (allowSlot m.ctx.crypto a m.frame.msg.caller)).toNat - v.toNat :=
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hac)
    rw [h1, ← hal, ← hba]
    rfl
  · rw [hw, allFromWorld, allWorld]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inl ⟨_, hdA, rfl⟩))))
      (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inl ⟨_, haA, rfl⟩))))
        (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inr (.inl ⟨_, haA, _, hcA, rfl⟩)))))
          BNB.Spec.frameKeeps_refl'))

theorem op_inc (Act : Finset Address) (m : Machine)
    (hs : Start AMPL.runtimeCode amplAbs M Act m) (sp : Address) (hsA : sp ∈ Act)
    (hval : m.frame.msg.value = 0)
    (hd : Args m.frame.msg.data 0x39509351 [Word.ofAddress sp, argWord m.frame.msg.data 1]) :
    Halts m fun mf o =>
      OpMatches amplAbs M Act (.adjustAllowance m.frame.msg.caller sp true
        (argWord m.frame.msg.data 1).toNat) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  set x := argWord m.frame.msg.data 1
  have hS := hs.sound
  have hcA := hs.caller
  have hpre := pre_eq hs hval
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => inc_high m sp x hs.fresh hd hs.size hval hG.2 hG.1)
    (inc_low m sp x hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  left
  simp only [OpMatches]
  have hal : (pre amplAbs Act m).allowance m.frame.msg.caller sp =
      (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat := by
    rw [hpre]; simp [amplRead, readMap2, hsA, hcA]
  rw [ampl_op_inc, hal]
  by_cases hr : 2 ^ 256 ≤ x.toNat + (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat
  · rw [ite_pos' (by unfold QEDefi.Math.MAX; omega)]
    exact hrev hr
  rw [ite_neg' (by unfold QEDefi.Math.MAX; omega)]
  have hfit := Nat.lt_of_not_le hr
  obtain ⟨ho, hw, ht, hcr⟩ := hok hfit
  refine ⟨ho, ?_, ?_, ht, hcr⟩
  · show amplRead _ _ _ _ = _
    rw [hw, allowSlot, amplRead_sstore_allow hS hcA hsA, ← hpre, BitVec.toNat_add,
      Nat.mod_eq_of_lt hfit, ← allowSlot, ← hal, Nat.add_comm]
  · rw [hw]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inr (.inl ⟨_, hcA, _, hsA, rfl⟩)))))
      BNB.Spec.frameKeeps_refl'

theorem op_dec (Act : Finset Address) (m : Machine)
    (hs : Start AMPL.runtimeCode amplAbs M Act m) (sp : Address) (hsA : sp ∈ Act)
    (hval : m.frame.msg.value = 0)
    (hd : Args m.frame.msg.data 0xa457c2d7 [Word.ofAddress sp, argWord m.frame.msg.data 1]) :
    Halts m fun mf o =>
      OpMatches amplAbs M Act (.adjustAllowance m.frame.msg.caller sp false
        (argWord m.frame.msg.data 1).toNat) m mf o ∨
      (Fails o ∧ ¬ (g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)) := by
  set x := argWord m.frame.msg.data 1
  have hS := hs.sound
  have hcA := hs.caller
  have hpre := pre_eq hs hval
  refine halts_split' (G := g₀ ≤ m.frame.gasLeft ∧ m.frame.msg.isStatic = false)
    (fun hG => dec_high m sp x hs.fresh hd hs.size hval hG.2 hG.1)
    (dec_low m sp x hs.fresh hd hs.size) ?_
  rintro mf o ⟨ho, hlt, hge, ht, hcr⟩
  left
  simp only [OpMatches]
  have hal : (pre amplAbs Act m).allowance m.frame.msg.caller sp =
      (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat := by
    rw [hpre]; simp [amplRead, readMap2, hsA, hcA]
  rw [ampl_op_dec, hal]
  refine ⟨ho, ?_, ?_, ht, hcr⟩
  · show amplRead _ _ _ _ = _
    by_cases h : x.toNat < (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat
    · rw [hlt h, allowSlot, amplRead_sstore_allow hS hcA hsA, ← hpre,
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact Nat.le_of_lt h), ← allowSlot]
    · rw [hge (Nat.le_of_not_lt h), allowSlot, amplRead_sstore_allow hS hcA hsA, ← hpre,
        ← allowSlot]
      have : (m.world.sload m.frame.msg.currentTarget
          (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat - x.toNat = 0 := by omega
      rw [this]; rfl
  · by_cases h : x.toNat < (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat
    · rw [hlt h]
      exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inr (.inl ⟨_, hcA, _, hsA, rfl⟩)))))
        BNB.Spec.frameKeeps_refl'
    · rw [hge (Nat.le_of_not_lt h)]
      exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inr (.inl ⟨_, hcA, _, hsA, rfl⟩)))))
        BNB.Spec.frameKeeps_refl'

theorem ofAddress_toAddress {x : Word} (h : x.toNat < 2 ^ 160) :
    Word.ofAddress x.toAddress = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [Word.ofAddress, Word.toAddress, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

theorem addrArg_word {x : Word} {a : Address} (ha : addrArg x = some a) : Word.ofAddress a = x := by
  unfold addrArg at ha
  split at ha
  · rename_i hlt; cases ha; exact ofAddress_toAddress hlt
  · cases ha

theorem args_a {data : ByteArray} {sel : Nat} {a : Address} (hsel : Abi.selectorOf data = sel)
    (hsz : ¬ data.size < 36) (ha : addrArg (argWord data 0) = some a) :
    Args data sel [Word.ofAddress a] := by
  refine ⟨hsel, by simp; omega, ?_⟩
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0) with rfl
  simp only [List.getElem_cons_zero]; rw [addrArg_word ha]; rfl

theorem args_aw {data : ByteArray} {sel : Nat} {a : Address} (hsel : Abi.selectorOf data = sel)
    (hsz : ¬ data.size < 68) (ha : addrArg (argWord data 0) = some a) :
    Args data sel [Word.ofAddress a, argWord data 1] := by
  refine ⟨hsel, by simp; omega, ?_⟩
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simp only [List.getElem_cons_zero]; rw [addrArg_word ha]; rfl
  · rfl

theorem args_aa {data : ByteArray} {sel : Nat} {a b : Address} (hsel : Abi.selectorOf data = sel)
    (hsz : ¬ data.size < 68) (ha : addrArg (argWord data 0) = some a)
    (hb : addrArg (argWord data 1) = some b) :
    Args data sel [Word.ofAddress a, Word.ofAddress b] := by
  refine ⟨hsel, by simp; omega, ?_⟩
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simp only [List.getElem_cons_zero]; rw [addrArg_word ha]; rfl
  · simp only [List.getElem_cons_succ, List.getElem_cons_zero]; rw [addrArg_word hb]; rfl

/-- **The other entry points**: `transferAll`, `transferAllFrom`, `increaseAllowance`,
`decreaseAllowance`. -/
theorem ops_spec : OpSpec AMPL.runtimeCode amplAbs M g₀ amplOps amplOpAddrs := by
  intro Act m e hs hops haddr
  simp only [amplOps] at hops
  split at hops
  · cases hops
  rename_i hvs
  have hval : m.frame.msg.value = 0 := by
    have : m.frame.msg.value.toNat = 0 := by simp only [not_or] at hvs; omega
    exact BitVec.eq_of_toNat_eq this
  have hsz : ¬ m.frame.msg.data.size < 36 := fun h => hvs (.inr h)
  split at hops
  · rename_i hsel
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => simp [ha] at hops
    | some a =>
      simp only [ha, Option.map_some, Option.some.injEq] at hops
      subst hops
      exact op_transferAll Act m hs a (haddr a (by simp [amplOpAddrs])) hval (args_a hsel hsz ha)
  split at hops
  · cases hops
  rename_i hsz2
  split at hops
  · rename_i _ hsel
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => simp [ha] at hops
    | some a =>
      cases hb : addrArg (argWord m.frame.msg.data 1) with
      | none => simp [ha, hb] at hops
      | some b =>
        simp only [ha, hb, Option.bind_some, Option.map_some, Option.some.injEq] at hops
        subst hops
        exact op_transferAllFrom Act m hs a b (haddr a (by simp [amplOpAddrs]))
          (haddr b (by simp [amplOpAddrs])) hval (args_aa hsel hsz2 ha hb)
  split at hops
  · rename_i _ _ hsel
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => simp [ha] at hops
    | some a =>
      simp only [ha, Option.map_some, Option.some.injEq] at hops
      subst hops
      exact op_inc Act m hs a (haddr a (by simp [amplOpAddrs])) hval (args_aw hsel hsz2 ha)
  split at hops
  · rename_i _ _ _ hsel
    cases ha : addrArg (argWord m.frame.msg.data 0) with
    | none => simp [ha] at hops
    | some a =>
      simp only [ha, Option.map_some, Option.some.injEq] at hops
      subst hops
      exact op_dec Act m hs a (haddr a (by simp [amplOpAddrs])) hval (args_aw hsel hsz2 ha)
  · cases hops

end Verified.WeirdERC20.AMPL.Spec
