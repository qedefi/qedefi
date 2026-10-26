import Verified.WeirdERC20.ZRX.Spec.TransferFrom

/-!
# ZRX under the spec: the `transferFrom` obligation

`transferFrom_low`/`transferFrom_high` end in `TFPost`; here it is read through the
abstraction: a short balance or allowance returns `false` with nothing changed (the model's
`arithFail := .returnFalse`), an allowance of `2²⁵⁶ − 1` is not spent (`infinite := .eqMax`),
otherwise the move and the spent allowance. The receiver-overflow branch is excluded by the
model's invariant (`no_wrap`).
-/

namespace Verified.WeirdERC20.ZRX.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.ZRX.Contracts
open Verified.Solady.Spec (LowHalts halts_split eq_zero_of_iszero_ne ite_pos' ite_neg')
open QEDefi.ERC4626

/-! ## The model -/

/-- Whether ZRX's `transferFrom` fails (returns `false`). -/
def tfFails (s : VState Address) (c src : Address) (v : ℕ) : Prop :=
  s.bal src < v ∨ (s.allowance src c ≠ QEDefi.Math.MAX ∧ s.allowance src c < v)

instance (s : VState Address) (c src : Address) (v : ℕ) : Decidable (tfFails s c src v) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The state after a successful `transferFrom`. -/
noncomputable def tfState (s : VState Address) (c src d : Address) (v : ℕ) : VState Address :=
  { (if s.allowance src c = QEDefi.Math.MAX then s
      else s.setAllowance src c (s.allowance src c - v)) with
    bal := s.bal - Finsupp.single src v + Finsupp.single d v }

set_option linter.unusedSimpArgs false in
theorem zrx_step_transferFrom (s : VState Address) (c src d : Address) (v : ℕ) :
    (QEDefi.ERC20.Spec.ZRX.variant : Variant Address).step s c (.transferFrom src d v) =
      if tfFails s c src v then none else some (tfState s c src d v) := by
  unfold tfFails tfState
  by_cases h1 : s.allowance src c = QEDefi.Math.MAX
  · by_cases h3 : s.bal src < v
    · simp [h1, h3, Variant.step, Variant.transferFrom, Variant.moveOk, Variant.spend,
        Variant.move, Variant.units, QEDefi.ERC20.Spec.ZRX.variant, Variant.standard,
        Infinite.test]
    · simp [h1, h3, Variant.step, Variant.transferFrom, Variant.moveOk, Variant.spend,
        Variant.move, Variant.units, QEDefi.ERC20.Spec.ZRX.variant, Variant.standard,
        Infinite.test, Variant.feeOverflow, Variant.feeOf, Variant.credit]
  · by_cases h2 : s.allowance src c < v
    · simp [h1, h2, Variant.step, Variant.transferFrom, Variant.moveOk, Variant.spend,
        Variant.move, Variant.units, QEDefi.ERC20.Spec.ZRX.variant, Variant.standard,
        Infinite.test]
    · by_cases h3 : s.bal src < v
      · simp [h1, h2, h3, Variant.step, Variant.transferFrom, Variant.moveOk, Variant.spend,
          Variant.move, Variant.units, QEDefi.ERC20.Spec.ZRX.variant, Variant.standard,
          Infinite.test, VState.setAllowance]
      · simp [h1, h2, h3, Variant.step, Variant.transferFrom, Variant.moveOk, Variant.spend,
          Variant.move, Variant.units, QEDefi.ERC20.Spec.ZRX.variant, Variant.standard,
          Infinite.test, Variant.feeOverflow, Variant.feeOf, Variant.credit, VState.setAllowance]

set_option linter.unusedSimpArgs false in
theorem zrx_call_transferFrom (s : VState Address) (c src d : Address) (v : ℕ) :
    M.call s c (.transferFrom src d v) =
      if tfFails s c src v then .ok s (.word false) else .ok (tfState s c src d v) (.word true) := by
  have h := zrx_step_transferFrom s c src d v
  simp only [M, QEDefi.ERC20.Spec.ZRX.model, Variant.model, Variant.call]
  by_cases hf : tfFails s c src v
  · rw [ite_pos' hf] at h
    rw [h, ite_pos' hf]
    simp [Variant.failKind, Variant.guardOk, Variant.moveOk, Variant.overflows,
      Variant.feeOverflow, QEDefi.ERC20.Spec.ZRX.variant, Variant.standard, Variant.failWith]
  · rw [ite_neg' hf] at h
    rw [h, ite_neg' hf]
    simp [Variant.retData, QEDefi.ERC20.Spec.ZRX.variant, Variant.standard]

theorem zrx_events_transferFrom (s : VState Address) (c src d : Address) (v : ℕ) :
    M.events s c (.transferFrom src d v) =
      if tfFails s c src v then [] else [.transfer src d v] := by
  simp only [M, QEDefi.ERC20.Spec.ZRX.model, Variant.model, QEDefi.ERC20.Spec.ZRX.events,
    zrx_step_transferFrom]
  split <;> simp_all

/-! ## Writes through the abstraction -/

/-- **The credit-then-debit move** through the abstraction: the model's move, when covered and
not wrapping. -/
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
  simp only [cdWorld, balSlot, read, VState.ofToken]
  rw [show (0#256 : Word) = balancesSlot from rfl,
    BNB.Spec.readMap2_sstore_map (base2 := allowedSlot) hS (by simp) (by simp) hc,
    BNB.Spec.readMap2_sstore_map (base2 := allowedSlot) hS (by simp) (by simp) hd,
    readSlot, readSlot,
    BNB.Spec.sload_sstore_map (k := supplySlot) hS (by simp [supplySlot]) (by simp) hc,
    BNB.Spec.sload_sstore_map (k := supplySlot) hS (by simp [supplySlot]) (by simp) hd,
    BNB.Spec.readMap_sstore (base := balancesSlot) hS (by simp) hc,
    BNB.Spec.readMap_sstore (base := balancesSlot) hS (by simp) hd]
  congr 1
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
    · subst ha; simp [readMap_of_mem hc]; omega
    · simp [ha, Ne.symm ha]
  · have hne : mappingSlot crypto (Word.ofAddress c) balancesSlot ≠
        mappingSlot crypto (Word.ofAddress d) balancesSlot := fun e =>
      hcd (hS.inj1 balancesSlot (by simp) balancesSlot (by simp) c hc d hd e).1
    rw [World.sload_sstore_ne_key _ _ _ hne]
    have hsub : (w.sload t (mappingSlot crypto (Word.ofAddress c) balancesSlot) - v).toNat =
        (w.sload t (mappingSlot crypto (Word.ofAddress c) balancesSlot)).toNat - v.toNat := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hv)]
    by_cases ha : a = c
    · subst ha; simp [readMap_of_mem hc, hsub, Ne.symm hcd]
    · by_cases had : a = d
      · subst had; simp [readMap_of_mem hd, ha, hadd, Ne.symm ha]
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

/-! ## The obligation -/

/-- **`transferFrom(src, dst, v)`**: a short balance or allowance returns `false` with nothing
changed; otherwise the move, the allowance spent unless it is `2²⁵⁶ − 1`, `Transfer`, `true`. -/
theorem call_transferFrom (src dst : Address) (v : ℕ) :
    CallSpec ZRX.runtimeCode abs M g₀ (.transferFrom src dst v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hsA : src ∈ Act := haddr src (by simp [Call.addrs])
  have hdA : dst ∈ Act := haddr dst (by simp [Call.addrs])
  have hcA := hs.caller
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  refine halts_split (G := Normal g₀ m)
    (fun hG => transferFrom_high m src dst (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1)
    (transferFrom_low m src dst (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hv, hok, hno⟩
  have hpre := pre_eq hs hv
  have hbs' : (pre abs Act m).bal src =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat := by
    rw [hpre]; simp [read, VState.ofToken, readMap_of_mem hsA, balancesSlot]
  have hbd' : (pre abs Act m).bal dst =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat := by
    rw [hpre]; simp [read, VState.ofToken, readMap_of_mem hdA, balancesSlot]
  have hal' : (pre abs Act m).allowance src m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat := by
    rw [hpre]; simp [read, VState.ofToken, readMap2, hsA, hcA, allowedSlot]
  rw [hwv] at hok hno
  have hal_lt := (m.world.sload m.frame.msg.currentTarget
    (allowSlot m.ctx.crypto src m.frame.msg.caller)).isLt
  by_cases hf : tfFails (pre abs Act m) m.frame.msg.caller src v
  · obtain ⟨ho, hw, ht, hcr, hl⟩ := hno (by
      rcases hf with h | ⟨-, h⟩
      · exact .inl (by rw [← hbs']; exact h)
      · exact .inr (.inl (by rw [← hal']; exact h)))
    rw [zrx_call_transferFrom, ite_pos' hf, zrx_events_transferFrom, ite_pos' hf]
    refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
    · show read _ _ _ _ = _
      rw [hw, hpre]
    · rw [hw]; exact BNB.Spec.frameKeeps_refl'
    · rw [hl]; simp
  have hle : v ≤ (pre abs Act m).bal src := by
    by_contra h; exact hf (.inl (Nat.lt_of_not_le h))
  have hla : v ≤ (pre abs Act m).allowance src m.frame.msg.caller := by
    by_contra h
    by_cases hmx : (pre abs Act m).allowance src m.frame.msg.caller = QEDefi.Math.MAX
    · rw [hmx] at h; simp only [QEDefi.Math.MAX] at h; omega
    · exact hf (.inr ⟨hmx, Nat.lt_of_not_le h⟩)
  have hnw := no_wrap hs.wf (dst := dst) hle
  rw [hbs'] at hle
  rw [hbd'] at hnw
  rw [hal'] at hla
  obtain ⟨-, ho, hw, ht, hcr, hl⟩ := hok hle hla (by simp only [QEDefi.Math.MAX] at hnw; omega)
  rw [zrx_call_transferFrom, ite_neg' hf, zrx_events_transferFrom, ite_neg' hf]
  have hrd := read_cdWorld (w := m.world) (t := m.frame.msg.currentTarget) hs.sound hsA hdA
    (by rw [hwv]; exact hle) (by rw [hwv]; simp only [QEDefi.Math.MAX] at hnw; omega)
  have hmw := sload_cdWorld_allow (w := m.world) (t := m.frame.msg.currentTarget)
    (v := word v) hs.sound hsA hcA hsA hdA
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show read _ _ _ _ = _
    rw [hw]
    unfold tfState
    by_cases hmx : (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat < 2 ^ 256 - 1
    · have hne : (pre abs Act m).allowance src m.frame.msg.caller ≠ QEDefi.Math.MAX := by
        rw [hal']; simp only [QEDefi.Math.MAX]; omega
      rw [ite_pos' hmx, ite_neg' hne, tfWorld, hmw, read_sstore_allow hs.sound hsA hcA, hrd,
        ← hpre, hwv]
      have hsub : (m.world.sload m.frame.msg.currentTarget
          (allowSlot m.ctx.crypto src m.frame.msg.caller) - word v).toNat =
          (m.world.sload m.frame.msg.currentTarget
            (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat - v := by
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hwv]; exact hla), hwv]
      rw [hsub, ← hal']
      rfl
    · have he : (pre abs Act m).allowance src m.frame.msg.caller = QEDefi.Math.MAX := by
        rw [hal']; simp only [QEDefi.Math.MAX]; omega
      rw [ite_neg' hmx, ite_pos' he, hrd, ← hpre, hwv]
  · rw [hw]
    split
    · rw [tfWorld, cdWorld]
      exact BNB.Spec.FrameKeeps.sstore' (allow_mem hsA hcA)
        (BNB.Spec.FrameKeeps.sstore' (bal_mem hsA)
          (BNB.Spec.FrameKeeps.sstore' (bal_mem hdA) BNB.Spec.frameKeeps_refl'))
    · rw [cdWorld]
      exact BNB.Spec.FrameKeeps.sstore' (bal_mem hsA)
        (BNB.Spec.FrameKeeps.sstore' (bal_mem hdA) BNB.Spec.frameKeeps_refl')
  · rw [hl]
    simp [Spec.eventLog]

end Verified.WeirdERC20.ZRX.Spec
