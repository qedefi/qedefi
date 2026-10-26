import Verified.WeirdERC20.YAMV2.Spec.TransferHigh

/-!
# YAMv2 under the spec: the `transfer` obligation

The code-level runs (`transfer_high`, `transfer_low`) against the model. The model's invariant
(`Start.wf`: the actors' balances add up to at most the supply, a word) makes the credit fit.
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.YAMV2.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

set_option linter.unusedSimpArgs false in
theorem yam_call_transfer (s : VState Address) (c d : Address) (v : ℕ) :
    M.call s c (.transfer d v) =
      if c = 0 ∨ d = 0 ∨ s.bal c < v then .halt .revert
      else .ok { s with bal := s.bal - Finsupp.single c v + Finsupp.single d v } (.word true) := by
  simp only [M, QEDefi.ERC20.Spec.YAMV2.model]
  by_cases h1 : c = 0
  · subst h1
    simp [Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard, Variant.failKind, Variant.guardOk,
      Variant.failWith]
  have h1' : ¬ c = 0#160 := h1
  by_cases h2 : d = 0
  · subst h2
    simp [h1', Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard, Variant.failKind, Variant.guardOk,
      Variant.failWith]
  have h2' : ¬ d = 0#160 := h2
  by_cases h3 : s.bal c < v
  · simp [h1', h2', h3, Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      Variant.move, Variant.units, QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard,
      Variant.failKind, Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith]
  · simp [h1', h2', h3, Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      Variant.move, Variant.units, QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard,
      Variant.feeOverflow, Variant.feeOf, Variant.credit, Variant.retData]

theorem read_sstore_bal {crypto : Crypto} {Act : Finset Address} {w : World} {t a : Address}
    (hS : abs.Sound crypto Act) (ha : a ∈ Act) (x : Word) :
    read crypto Act (w.sstore t (balSlot crypto a) x) t =
      { read crypto Act w t with bal := (read crypto Act w t).bal.update a x.toNat } := by
  simp only [read, VState.ofToken, balSlot,
    show balancesSlot = 1#256 from rfl, show supplySlot = 3#256 from rfl,
    show allowancesSlot = 2#256 from rfl, show minterSlot = 0#256 from rfl]
  rw [BNB.Spec.readMap_sstore hS (by decide) ha,
    BNB.Spec.readMap2_sstore_map hS (by decide) (by decide) ha]
  simp only [readSlot, BNB.Spec.sload_sstore_map (k := 3#256) (base := 1#256) (x := x) (t := t)
    (w := w) hS (by decide) (by decide) ha, BNB.Spec.sload_sstore_map (k := 0#256)
    (base := 1#256) (x := x) (t := t) (w := w) hS (by decide) (by decide) ha]

/-- Under the model's invariant the actors' balances add up to less than `2²⁵⁶`. -/
theorem yam_total_lt {Act : Finset Address} {m : Machine}
    (hs : Start YAMV2.runtimeCode abs M Act m) (hv : m.frame.msg.value = 0) :
    QEDefi.ERC20.total (read m.ctx.crypto Act m.world m.frame.msg.currentTarget).bal < 2 ^ 256 := by
  have h := hs.wf
  rw [pre_eq hs hv] at h
  obtain ⟨h1, h2⟩ := h
  unfold QEDefi.Math.MAX at h2
  omega

set_option linter.unusedSimpArgs false in
/-- **`transfer(dst, v)`**: a zero sender or recipient or a balance below `v` reverts;
otherwise the move of `v`, `true`, `Transfer`. -/
theorem call_transfer (dst : Address) (v : ℕ) :
    CallSpec YAMV2.runtimeCode abs M g₀ (.transfer dst v) := by
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
  have htot := yam_total_lt hs hv0
  have hbalc := readMap_of_mem (crypto := m.ctx.crypto) hcA m.world m.frame.msg.currentTarget 1#256
  have hbald := readMap_of_mem (crypto := m.ctx.crypto) hdA m.world m.frame.msg.currentTarget 1#256
  have hsc : (pre abs Act m).bal m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
    rw [hpre]; exact hbalc
  rw [yam_call_transfer, hsc]
  by_cases hr : m.frame.msg.caller = 0 ∨ dst = 0 ∨
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat < v
  · rw [ite_pos' hr]
    exact hrev (by rw [hwv]; exact hr)
  rw [ite_neg' hr]
  simp only [not_or, not_lt] at hr
  obtain ⟨hc0, hd0, hbc⟩ := hr
  have hle : (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat < 2 ^ 256 := BitVec.isLt _
  have hfit : ((debitWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller
      (word v)).sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat + v < 2 ^ 256 := by
    simp only [debitWorld]
    by_cases hcd : m.frame.msg.caller = dst
    · rw [← hcd, World.sload_sstore_self,
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hwv]; exact hbc), hwv]
      omega
    · have hne : balSlot m.ctx.crypto dst ≠ balSlot m.ctx.crypto m.frame.msg.caller := fun e =>
        hcd (hs.sound.inj1 1#256 (by decide) 1#256 (by decide) dst hdA _ hcA e).1.symm
      rw [World.sload_sstore_ne_key _ _ _ hne]
      have h2 := QEDefi.ERC20.add_le_total
        (f := (read m.ctx.crypto Act m.world m.frame.msg.currentTarget).bal) hcd
      simp only [read, VState.ofToken, show balancesSlot = 1#256 from rfl] at h2 htot
      rw [hbalc, hbald] at h2
      simp only [balSlot] at *
      omega
  obtain ⟨hv, -, ho, hw, ht, hcr, hl⟩ := hok hc0 hd0 (by rw [hwv]; exact hbc)
    (by rw [hwv]; exact hfit)
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show read _ _ _ _ = _
    rw [hw, moveWorld, read_sstore_bal hs.sound hdA, debitWorld,
      read_sstore_bal hs.sound hcA, hpre]
    dsimp only
    congr 1
    ext a
    simp only [Finsupp.update_apply, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
      Pi.sub_apply, Finsupp.single_apply]
    have hsub : (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller) -
        word v).toNat =
        (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat -
          v := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hwv]; exact hbc), hwv]
    by_cases hcd : m.frame.msg.caller = dst
    · subst hcd
      rw [World.sload_sstore_self]
      have hadd : (word v +
          (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller) -
            word v)).toNat =
          (m.world.sload m.frame.msg.currentTarget
            (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
        rw [BitVec.add_comm, BitVec.sub_add_cancel]
      by_cases ha : a = m.frame.msg.caller
      · subst ha
        simp only [read, VState.ofToken, show balancesSlot = 1#256 from rfl, readMap_of_mem hcA,
          hadd, ite_true]
        rw [← hbalc]
        simp only [balSlot] at *; omega
      · simp [ha, Ne.symm ha, read]
    · have hne : balSlot m.ctx.crypto dst ≠ balSlot m.ctx.crypto m.frame.msg.caller := fun e =>
        hcd (hs.sound.inj1 1#256 (by decide) 1#256 (by decide) dst hdA _ hcA e).1.symm
      rw [World.sload_sstore_ne_key _ _ _ hne]
      have hfit' := hfit
      simp only [debitWorld] at hfit'
      rw [World.sload_sstore_ne_key _ _ _ hne] at hfit'
      have hadd : (word v +
          m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat =
          v + (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat := by
        rw [BitVec.toNat_add, hwv, Nat.mod_eq_of_lt (by omega)]
      by_cases ha : a = dst
      · subst ha
        simp only [read, VState.ofToken, show balancesSlot = 1#256 from rfl, readMap_of_mem hdA,
          hadd, ite_true, hcd, Ne.symm hcd, ite_false]
        simp only [balSlot] at *; omega
      · by_cases hac : a = m.frame.msg.caller
        · subst hac
          simp only [read, VState.ofToken, show balancesSlot = 1#256 from rfl,
            readMap_of_mem hcA, hsub, ha, ite_true, ite_false,
            show ¬ dst = m.frame.msg.caller from fun e => ha e.symm]
          simp only [balSlot] at *; omega
        · simp [ha, hac, Ne.symm ha, Ne.symm hac, read]
  · rw [hw, moveWorld, debitWorld]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hdA, rfl⟩)))
      (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hcA, rfl⟩)))
        BNB.Spec.frameKeeps_refl')
  · rw [hl]
    simp [M, QEDefi.ERC20.Spec.YAMV2.model, QEDefi.ERC20.Spec.YAMV2.events, Spec.eventLog]

end Verified.WeirdERC20.YAMV2.Spec
