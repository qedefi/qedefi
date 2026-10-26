import Verified.WeirdERC20.AMPL.Spec.TransferFrom
import Verified.WeirdERC20.AMPL.Spec.TransferCall

/-!
# AMPL under the spec: the `transferFrom` obligation

The code-level runs (`transferFrom_high`, `transferFrom_low`) against the model's
spend-then-move. The code lowers the allowance first and then reads `gonsPerFragment` and the
balances; the actors' distinct rows (`Start.sound`) keep those reads at their starting values.
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

set_option linter.unusedSimpArgs false in
theorem ampl_call_transferFrom (s : VState Address) (c src d : Address) (v : ℕ) :
    M.call s c (.transferFrom src d v) =
      if d = 0 ∨ d = s.self ∨ s.allowance src c < v ∨ s.bal src < s.scale * v then .halt .revert
      else .ok (VState.setAllowance
        { s with
          bal := (s.bal - Finsupp.single src (s.scale * v) + Finsupp.single d (s.scale * v)) }
        src c (s.allowance src c - v)) (.word true) := by
  simp only [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.model_call]
  by_cases h1 : d = 0
  · subst h1
    simp [Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk, Variant.ampl,
      Variant.standard, Variant.failKind, Variant.guardOk, Variant.failWith]
  have h1' : ¬ d = 0#160 := h1
  by_cases h2 : d = s.self
  · simp [h1', h2, Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk, Variant.ampl,
      Variant.standard, Variant.failKind, Variant.guardOk, Variant.failWith]
  by_cases ha : s.allowance src c < v
  · simp [h1', h2, ha, Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk,
      Variant.spend, Variant.move, Variant.units, Variant.ampl, Variant.standard,
      Variant.failKind, Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith,
      Infinite.test]
  rw [Nat.mul_comm s.scale v]
  by_cases h3 : s.bal src < v * s.scale
  · simp [h1', h2, ha, h3, Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk,
      Variant.spend, Variant.move, Variant.units, Variant.ampl, Variant.standard,
      Variant.failKind, Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith,
      Infinite.test, VState.setAllowance]
  · simp [h1', h2, ha, h3, Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk,
      Variant.spend, Variant.move, Variant.units, Variant.ampl, Variant.standard,
      Variant.feeOverflow, Variant.feeOf, Variant.credit, Variant.retData, Infinite.test,
      VState.setAllowance]

/-- **AMPL's move through the abstraction**: the debit and the credit of `g` gons, when the
source covers `g` and the credit fits. -/
theorem amplRead_moveWorld {crypto : Crypto} {Act : Finset Address} {w : World}
    {t c d : Address} {g : Word} (hS : amplSound crypto Act) (hc : c ∈ Act) (hd : d ∈ Act)
    (hbc : g.toNat ≤ (w.sload t (balSlot crypto c)).toNat)
    (hfit : ((debitWorld crypto w t c g).sload t (balSlot crypto d)).toNat + g.toNat < 2 ^ 256) :
    amplRead crypto Act (moveWorld crypto w t c d g) t =
      { amplRead crypto Act w t with
        bal := (amplRead crypto Act w t).bal - Finsupp.single c g.toNat +
          Finsupp.single d g.toNat } := by
  have hbalc := readMap_of_mem (crypto := crypto) hc w t 158#256
  rw [moveWorld, amplRead_sstore_bal hS hd, debitWorld, amplRead_sstore_bal hS hc]
  dsimp only
  congr 1
  ext a
  simp only [Finsupp.update_apply, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
    Pi.sub_apply, Finsupp.single_apply]
  have hsub : (w.sload t (balSlot crypto c) - g).toNat =
      (w.sload t (balSlot crypto c)).toNat - g.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hbc)
  by_cases hcd : c = d
  · subst d
    rw [World.sload_sstore_self]
    have hadd : (g + (w.sload t (balSlot crypto c) - g)).toNat =
        (w.sload t (balSlot crypto c)).toNat := by
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    by_cases ha : a = c
    · subst a; simp only [amplRead, readMap_of_mem hc, hadd, ite_true]; rw [← hbalc]
      simp only [balSlot] at *; omega
    · simp [ha, Ne.symm ha, amplRead]
  · have hne : balSlot crypto d ≠ balSlot crypto c := fun e =>
      hcd (hS.inj1 158#256 (by simp) 158#256 (by simp) d hd _ hc e).1.symm
    rw [World.sload_sstore_ne_key _ _ _ hne]
    have hfit' := hfit
    simp only [debitWorld] at hfit'
    rw [World.sload_sstore_ne_key _ _ _ hne] at hfit'
    have hadd : (g + w.sload t (balSlot crypto d)).toNat =
        g.toNat + (w.sload t (balSlot crypto d)).toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    by_cases ha : a = d
    · subst a
      simp only [amplRead, readMap_of_mem hd, hadd, ite_true, hcd, Ne.symm hcd, ite_false]
      simp only [balSlot] at *; omega
    · by_cases hac : a = c
      · subst a
        simp only [amplRead, readMap_of_mem hc, hsub, ha, ite_true, ite_false,
          show ¬ d = c from fun e => ha e.symm]
        simp only [balSlot] at *; omega
      · simp [ha, hac, Ne.symm ha, Ne.symm hac, amplRead]

/-- Lowering an actor's allowance row leaves the fixed slots and the balance rows. -/
theorem sload_allowWorld {crypto : Crypto} {Act : Finset Address} {w : World}
    {t c src : Address} {v : Word} (hS : amplSound crypto Act) (hc : c ∈ Act) (hs : src ∈ Act)
    {k : Word} (hk : k = 157#256 ∨ ∃ a ∈ Act, k = balSlot crypto a) :
    (allowWorld crypto w t c src v).sload t k = w.sload t k := by
  simp only [allowWorld, allowSlot]
  apply World.sload_sstore_ne_key
  rcases hk with rfl | ⟨a, ha, rfl⟩
  · exact fun e => hS.fixed2 159#256 (by simp) src hs c hc (by rw [← e]; simp)
  · exact hS.disj 158#256 (by simp) 159#256 (by simp) a ha src hs c hc

set_option linter.unusedSimpArgs false in
/-- **`transferFrom(src, dst, v)`**: a zero or self recipient, an allowance below `v` or a
balance below `v · gonsPerFragment` reverts; otherwise the allowance lowered and the move,
`true`, `Transfer`. -/
theorem call_transferFrom (src dst : Address) (v : ℕ) :
    CallSpec AMPL.runtimeCode amplAbs M g₀ (.transferFrom src dst v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hsA : src ∈ Act := haddr src (by simp [Call.addrs])
  have hdA : dst ∈ Act := haddr dst (by simp [Call.addrs])
  have hcA := hs.caller
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  refine halts_split' (G := Normal g₀ m)
    (fun hG => transferFrom_high m src dst (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1)
    (transferFrom_low m src dst (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hval0, hrev, hok⟩
  by_cases hv0 : m.frame.msg.value = 0
  swap
  · obtain ⟨out, rfl⟩ := hval0 hv0
    exact .inr ⟨trivial, fun hG => hv0 hG.2.2⟩
  left
  have hpre := pre_eq hs hv0
  have htot := ampl_total_lt hs hv0
  have hW157 := sload_allowWorld (w := m.world) (t := m.frame.msg.currentTarget) (v := word v)
    hs.sound hcA hsA (k := 157#256) (.inl rfl)
  have hWs := sload_allowWorld (w := m.world) (t := m.frame.msg.currentTarget) (v := word v)
    hs.sound hcA hsA (k := balSlot m.ctx.crypto src) (.inr ⟨src, hsA, rfl⟩)
  have hWd := sload_allowWorld (w := m.world) (t := m.frame.msg.currentTarget) (v := word v)
    hs.sound hcA hsA (k := balSlot m.ctx.crypto dst) (.inr ⟨dst, hdA, rfl⟩)
  simp only [TFPost, hW157, hWs] at hrev hok
  have hbals := readMap_of_mem (crypto := m.ctx.crypto) hsA m.world m.frame.msg.currentTarget 158#256
  have hbald := readMap_of_mem (crypto := m.ctx.crypto) hdA m.world m.frame.msg.currentTarget 158#256
  have hall : (amplRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).allowance src
      m.frame.msg.caller = (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat := by
    simp [amplRead, readMap2, hsA, hcA]
  have hsc : (pre amplAbs Act m).bal src =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat := by
    rw [hpre]; exact hbals
  have hac' : (pre amplAbs Act m).allowance src m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat := by
    rw [hpre]; exact hall
  have hscale : (pre amplAbs Act m).scale =
      (m.world.sload m.frame.msg.currentTarget 157#256).toNat := by
    rw [hpre]; rfl
  have hself : (pre amplAbs Act m).self = m.frame.msg.currentTarget := by rw [hpre]; rfl
  rw [ampl_call_transferFrom, hscale, hself, hsc, hac']
  by_cases hr : dst = 0 ∨ dst = m.frame.msg.currentTarget ∨
      (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat < v ∨
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat <
        (m.world.sload m.frame.msg.currentTarget 157#256).toNat * v
  · rw [ite_pos' hr]
    exact hrev (by rw [hwv]; exact hr)
  rw [ite_neg' hr]
  simp only [not_or, not_lt] at hr
  obtain ⟨hd0, hdt, hac, hbc⟩ := hr
  have hle : (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto src)).toNat < 2 ^ 256 := BitVec.isLt _
  have hgv : (m.world.sload m.frame.msg.currentTarget 157#256 * word v).toNat =
      (m.world.sload m.frame.msg.currentTarget 157#256).toNat * v := by
    rw [BitVec.toNat_mul, hwv, Nat.mod_eq_of_lt (by omega)]
  have hfit : ((debitWorld m.ctx.crypto
      (allowWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src (word v))
      m.frame.msg.currentTarget src
      (m.world.sload m.frame.msg.currentTarget 157#256 * word v)).sload m.frame.msg.currentTarget
        (balSlot m.ctx.crypto dst)).toNat +
      (m.world.sload m.frame.msg.currentTarget 157#256).toNat * v < 2 ^ 256 := by
    simp only [debitWorld]
    rw [hWs]
    by_cases hcd : src = dst
    · rw [← hcd, World.sload_sstore_self,
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hgv]; exact hbc), hgv]
      omega
    · have hne : balSlot m.ctx.crypto dst ≠ balSlot m.ctx.crypto src := fun e =>
        hcd (hs.sound.inj1 158#256 (by simp) 158#256 (by simp) dst hdA _ hsA e).1.symm
      rw [World.sload_sstore_ne_key _ _ _ hne, hWd]
      have h2 := QEDefi.ERC20.add_le_total
        (f := (amplRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).bal) hcd
      simp only [amplRead] at h2 htot
      rw [hbals, hbald] at h2
      simp only [balSlot] at *
      omega
  obtain ⟨hv, -, ho, hw, ht, hcr, hl⟩ := hok hd0 hdt (by rw [hwv]; exact hac)
    (by rw [hwv]; exact hbc) (by rw [hwv]; exact hfit)
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show amplRead _ _ _ _ = _
    have hsub : (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto src m.frame.msg.caller) - word v).toNat =
        (m.world.sload m.frame.msg.currentTarget
          (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat - v := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hwv]; exact hac), hwv]
    rw [hw, amplRead_moveWorld hs.sound hsA hdA (by rw [hWs, hgv]; exact hbc) (by rw [hgv]; exact hfit),
      allowWorld, allowSlot, amplRead_sstore_allow hs.sound hsA hcA, hpre, hgv]
    rw [show (m.world.sload m.frame.msg.currentTarget
        (mappingSlot2 m.ctx.crypto (Word.ofAddress src) (Word.ofAddress m.frame.msg.caller) 159#256) -
          word v).toNat = _ from hsub]
    simp [VState.setAllowance, hall]
    exact ⟨rfl, rfl⟩
  · rw [hw, moveWorld, debitWorld, allowWorld]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inl ⟨_, hdA, rfl⟩))))
      (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inl ⟨_, hsA, rfl⟩))))
        (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inr (.inl ⟨_, hsA, _, hcA, rfl⟩)))))
          BNB.Spec.frameKeeps_refl'))
  · rw [hl]
    simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, QEDefi.ERC20.Spec.AMPL.amplEvents, Spec.eventLog]

end Verified.WeirdERC20.AMPL.Spec
