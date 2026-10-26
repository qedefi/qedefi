import Verified.WeirdERC20.ZRX.Spec.Transfer

/-!
# ZRX under the spec: the `transfer` obligation

`transfer_low`/`transfer_high` (`Transfer.lean`) end in `TransferPost`; here it is read
through the abstraction: a short balance returns `false` with nothing changed, as the model's
`arithFail := .returnFalse`; otherwise the move. The receiver-overflow branch of the code is
excluded by the model's invariant (`no_wrap`).
-/

namespace Verified.WeirdERC20.ZRX.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.ZRX.Contracts
open Verified.Solady.Spec (LowHalts halts_split eq_zero_of_iszero_ne ite_pos' ite_neg')
open QEDefi.ERC4626

/-! ## The model -/

set_option linter.unusedSimpArgs false in
theorem zrx_call_transfer (s : VState Address) (c d : Address) (v : ℕ) :
    M.call s c (.transfer d v) =
      if s.bal c < v then .ok s (.word false)
      else .ok { s with bal := s.bal - Finsupp.single c v + Finsupp.single d v } (.word true) := by
  by_cases h : s.bal c < v
  · simp [h, M, QEDefi.ERC20.Spec.ZRX.model, Variant.model, Variant.call, Variant.step,
      Variant.transfer, Variant.moveOk, Variant.move, Variant.units,
      QEDefi.ERC20.Spec.ZRX.variant, Variant.standard, Variant.failKind, Variant.guardOk,
      Variant.overflows, Variant.feeOverflow, Variant.failWith]
  · simp [h, M, QEDefi.ERC20.Spec.ZRX.model, Variant.model, Variant.call, Variant.step,
      Variant.transfer, Variant.moveOk, Variant.move, Variant.units,
      QEDefi.ERC20.Spec.ZRX.variant, Variant.standard, Variant.feeOverflow, Variant.feeOf,
      Variant.credit, Variant.retData]

set_option linter.unusedSimpArgs false in
theorem zrx_events_transfer (s : VState Address) (c d : Address) (v : ℕ) :
    M.events s c (.transfer d v) = if s.bal c < v then [] else [.transfer c d v] := by
  by_cases h : s.bal c < v
  · simp [h, M, QEDefi.ERC20.Spec.ZRX.model, Variant.model, QEDefi.ERC20.Spec.ZRX.events,
      Variant.step, Variant.transfer, Variant.moveOk, Variant.move, Variant.units,
      QEDefi.ERC20.Spec.ZRX.variant, Variant.standard]
  · simp [h, M, QEDefi.ERC20.Spec.ZRX.model, Variant.model, QEDefi.ERC20.Spec.ZRX.events,
      Variant.step, Variant.transfer, Variant.moveOk, Variant.move, Variant.units,
      QEDefi.ERC20.Spec.ZRX.variant, Variant.standard, Variant.feeOverflow, Variant.feeOf]

/-- **The credit never wraps** in a state the model admits: `v ≤ bal src` and the balances sum
to at most the supply (distinct accounts), or `2 · supply ≤ MAX` (a self-transfer). -/
theorem no_wrap {s : VState Address} (hw : M.wf s) {src dst : Address} {v : ℕ}
    (hv : v ≤ s.bal src) : s.bal dst + v ≤ QEDefi.Math.MAX := by
  obtain ⟨hsub, h2⟩ := hw
  by_cases he : src = dst
  · subst he
    have := QEDefi.ERC20.Token.le_total s.bal src
    have := hsub.1
    omega
  · exact hsub.credit_le he hv

/-! ## Writes through the abstraction -/

/-- **The move** through the abstraction: the model's move, when covered and not wrapping. -/
theorem read_moveWorld {crypto : Crypto} {Act : Finset Address} {w : World} {t c d : Address}
    {v : Word} (hS : abs.Sound crypto Act) (hc : c ∈ Act) (hd : d ∈ Act)
    (hv : v.toNat ≤ (w.sload t (balSlot crypto c)).toNat)
    (hov : (w.sload t (balSlot crypto d)).toNat + v.toNat < 2 ^ 256) :
    read crypto Act (moveWorld crypto w t c d v) t =
      { read crypto Act w t with
        bal := (read crypto Act w t).bal - Finsupp.single c v.toNat +
          Finsupp.single d v.toNat } := by
  change v.toNat ≤ (w.sload t (mappingSlot crypto (Word.ofAddress c) balancesSlot)).toNat at hv
  change (w.sload t (mappingSlot crypto (Word.ofAddress d) balancesSlot)).toNat + v.toNat <
    2 ^ 256 at hov
  simp only [moveWorld, balSlot, read, VState.ofToken]
  rw [show (0#256 : Word) = balancesSlot from rfl,
    BNB.Spec.readMap2_sstore_map (base2 := allowedSlot) hS (by simp) (by simp) hd,
    BNB.Spec.readMap2_sstore_map (base2 := allowedSlot) hS (by simp) (by simp) hc,
    readSlot, readSlot,
    BNB.Spec.sload_sstore_map (k := supplySlot) hS (by simp [supplySlot]) (by simp) hd,
    BNB.Spec.sload_sstore_map (k := supplySlot) hS (by simp [supplySlot]) (by simp) hc,
    BNB.Spec.readMap_sstore (base := balancesSlot) hS (by simp) hd,
    BNB.Spec.readMap_sstore (base := balancesSlot) hS (by simp) hc]
  congr 1
  have hsub : (w.sload t (mappingSlot crypto (Word.ofAddress c) balancesSlot) - v).toNat =
      (w.sload t (mappingSlot crypto (Word.ofAddress c) balancesSlot)).toNat - v.toNat := by
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
  · have hne : mappingSlot crypto (Word.ofAddress d) balancesSlot ≠
        mappingSlot crypto (Word.ofAddress c) balancesSlot := fun e =>
      hcd (hS.inj1 balancesSlot (by simp) balancesSlot (by simp) d hd c hc e).1.symm
    rw [World.sload_sstore_ne_key _ _ _ hne]
    have hadd : (w.sload t (mappingSlot crypto (Word.ofAddress d) balancesSlot) + v).toNat =
        (w.sload t (mappingSlot crypto (Word.ofAddress d) balancesSlot)).toNat + v.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hov]
    by_cases ha : a = d
    · subst ha; simp [readMap_of_mem hd, hcd, hadd]
    · by_cases hac : a = c
      · subst hac; simp [readMap_of_mem hc, ha, hsub, Ne.symm ha]
      · simp [ha, hac, Ne.symm ha, Ne.symm hac]

/-- The balance row of an actor is in the footprint. -/
theorem bal_mem {crypto : Crypto} {Act : Finset Address} {a : Address} (ha : a ∈ Act) :
    abs.footprint crypto Act (balSlot crypto a) := .inr (.inl ⟨a, ha, rfl⟩)

/-- The allowance row of two actors is in the footprint. -/
theorem allow_mem {crypto : Crypto} {Act : Finset Address} {o sp : Address} (ho : o ∈ Act)
    (hs : sp ∈ Act) : abs.footprint crypto Act (allowSlot crypto o sp) :=
  .inr (.inr ⟨o, ho, sp, hs, rfl⟩)

/-! ## The obligation -/

/-- **`transfer(dst, v)`**: a short balance returns `false` with nothing changed; otherwise the
move with its `Transfer`, `true`. -/
theorem call_transfer (dst : Address) (v : ℕ) :
    CallSpec ZRX.runtimeCode abs M g₀ (.transfer dst v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hdA : dst ∈ Act := haddr dst (by simp [Call.addrs])
  have hcA := hs.caller
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  refine halts_split (G := Normal g₀ m)
    (fun hG => transfer_high m dst (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1)
    (transfer_low m dst (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hv, hok, hno⟩
  have hpre := pre_eq hs hv
  have hbc' : (pre abs Act m).bal m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
    rw [hpre]; simp [read, VState.ofToken, readMap_of_mem hcA, balancesSlot]
  have hbd' : (pre abs Act m).bal dst =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat := by
    rw [hpre]; simp [read, VState.ofToken, readMap_of_mem hdA, balancesSlot]
  rw [hwv] at hok hno
  by_cases hlt : (pre abs Act m).bal m.frame.msg.caller < v
  · obtain ⟨ho, hw, ht, hcr, hl⟩ := hno (.inl (by rw [← hbc']; exact hlt))
    rw [zrx_call_transfer, ite_pos' hlt, zrx_events_transfer, ite_pos' hlt]
    refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
    · show read _ _ _ _ = _
      rw [hw, hpre]
    · rw [hw]; exact BNB.Spec.frameKeeps_refl'
    · rw [hl]; simp
  have hle : v ≤ (pre abs Act m).bal m.frame.msg.caller := Nat.le_of_not_lt hlt
  have hnw := no_wrap hs.wf (dst := dst) hle
  rw [hbc'] at hle
  rw [hbd'] at hnw
  obtain ⟨-, ho, hw, ht, hcr, hl⟩ := hok hle (by simp only [QEDefi.Math.MAX] at hnw; omega)
  rw [zrx_call_transfer, ite_neg' hlt, zrx_events_transfer, ite_neg' hlt]
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show read _ _ _ _ = _
    rw [hw, read_moveWorld hs.sound hcA hdA (by rw [hwv]; exact hle)
      (by rw [hwv]; simp only [QEDefi.Math.MAX] at hnw; omega), ← hpre, hwv]
  · rw [hw, moveWorld]
    exact BNB.Spec.FrameKeeps.sstore' (bal_mem hdA)
      (BNB.Spec.FrameKeeps.sstore' (bal_mem hcA) BNB.Spec.frameKeeps_refl')
  · rw [hl]
    simp [Spec.eventLog]

end Verified.WeirdERC20.ZRX.Spec
