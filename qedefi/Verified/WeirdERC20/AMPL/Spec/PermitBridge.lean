import Verified.WeirdERC20.AMPL.Spec.PermitLow
import Verified.WeirdERC20.AMPL.Spec.Spec

/-!
# AMPL's `permit`: the code's end as the model's `permit`

`ampl_call_permit`: the model's `permit(o, sp, v, live, rec)` succeeds exactly when `live`,
`rec (nonces o) = o` and `nonces o < MAX` (AMPL's `SafeMath` increment; no zero-owner check),
setting the allowance and incrementing the nonce; otherwise it reverts.

`permitOk_iff`: in a `Start` frame with no value and not static, `PermitOk` is the model's
condition for the frame's own `permit` call with `amplRec` (at the depth limit both fail:
`amplRec` is then not the owner). `matches_of_permitDone`: a `PermitOk` frame ending as
`PermitDone` ends as `Matches` says of the model's call.
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC4626 QEDefi.Math Verified.WeirdERC20.AMPL.Contracts
open Verified.WeirdERC20.AMPL.Spec
open QEDefi.ERC20.Spec.AMPL (AState AState.setAllowance liftR AmplOp)
open Verified.Solady.Spec (ite_pos' ite_neg')

/-- The model's state after a successful `permit`. -/
noncomputable def permitState (s : AState Address) (o sp : Address) (v : ℕ) : AState Address :=
  { s with toVState := { s.toVState.setAllowance o sp v with
      nonces := s.nonces.update o ((s.nonces o + 1) % U256) } }

/-- **The model's `permit`** of AMPL. -/
theorem ampl_call_permit (s : AState Address) (c o sp : Address) (v : ℕ) (live : Bool)
    (rec : ℕ → Address) :
    M.call s c (.permit o sp v live rec) =
      if live = true ∧ rec (s.nonces o) = o ∧ s.nonces o < MAX then
        .ok (permitState s o sp v) .empty
      else .halt .revert := by
  simp only [M, QEDefi.ERC20.Spec.AMPL.amplModel, liftR]
  by_cases h : live = true ∧ rec (s.nonces o) = o ∧ s.nonces o < MAX
  · obtain ⟨h1, h2, h3⟩ := h
    rw [ite_pos' ⟨h1, h2, h3⟩]
    have hn : ¬ MAX ≤ s.nonces o := by omega
    simp [Variant.call, Variant.step, Variant.permit, Variant.permitOk, Variant.ampl,
      Variant.standard, h1, h2, hn, Variant.retData, permitState]
  · rw [ite_neg' h]
    have hok : Variant.permitOk Variant.ampl s.toVState o sp v live rec = false := by
      simp only [Variant.permitOk, Variant.ampl, Variant.standard]
      by_cases h1 : live = true <;> by_cases h2 : rec (s.nonces o) = o <;>
        by_cases h3 : s.nonces o < MAX <;> simp_all
    have hr : (Variant.ampl : Variant Address).permitRule = .eip2612 false false := rfl
    have hg : (Variant.ampl : Variant Address).guardFail = .revert := rfl
    simp [Variant.call, Variant.step, Variant.permit, hok, Variant.failKind, Variant.guardOk,
      Variant.failWith, hr, hg]

theorem amplRead_sstore_nonce {crypto : Crypto} {Act : Finset Address} {w : World} {t a : Address}
    (hS : amplSound crypto Act) (ha : a ∈ Act) (x : Word) :
    amplRead crypto Act (w.sstore t (mappingSlot crypto (Word.ofAddress a) 160#256) x) t =
      { amplRead crypto Act w t with
        nonces := (amplRead crypto Act w t).nonces.update a x.toNat } := by
  simp only [amplRead]
  rw [BNB.Spec.readMap_sstore hS (by simp) ha,
    BNB.Spec.readMap_sstore_other (base' := 158#256) hS (by simp) (by simp) (by decide) ha,
    BNB.Spec.readMap2_sstore_map hS (by simp) (by simp) ha]
  simp only [readSlot, Live, BNB.Spec.sload_sstore_map (k := 156#256) (base := 160#256) (x := x)
    (t := t) (w := w) hS (by simp) (by simp) ha, BNB.Spec.sload_sstore_map (k := 157#256)
    (base := 160#256) (x := x) (t := t) (w := w) hS (by simp) (by simp) ha,
    BNB.Spec.sload_sstore_map (k := 155#256) (base := 160#256) (x := x) (t := t) (w := w) hS
    (by simp) (by simp) ha, BNB.Spec.sload_sstore_map (k := 0#256) (base := 160#256) (x := x)
    (t := t) (w := w) hS (by simp) (by simp) ha, BNB.Spec.sload_sstore_map (k := 104#256)
    (base := 160#256) (x := x) (t := t) (w := w) hS (by simp) (by simp) ha, World.balance_sstore]
  congr 1

/-- `live` of the frame's `permit` call. -/
def pLive (m : Machine) : Bool :=
  decide (m.ctx.block.timestamp % 2 ^ 256 ≤ (argWord m.frame.msg.data 3).toNat)

/-- The frame's own `permit` call, with AMPL's recovery. -/
def pCall (m : Machine) : Call Address :=
  .permit (pOwner m.frame.msg.data) (pSpender m.frame.msg.data)
    (argWord m.frame.msg.data 2).toNat (pLive m) (amplRec m)

theorem nonces_pre {Act : Finset Address} {m : Machine}
    (hS : Start AMPL.runtimeCode amplAbs M Act m) (hval : m.frame.msg.value = 0) {a : Address}
    (ha : a ∈ Act) :
    (pre amplAbs Act m).nonces a =
      (m.world.sload m.frame.msg.currentTarget (nonceSlot m.ctx.crypto a)).toNat := by
  rw [pre_eq hS hval]; simp [amplRead, readMap_apply, ha, nonceSlot]

/-- **The model's condition for the frame's `permit` is `PermitOk`**, with no value and not
static. -/
theorem permitOk_iff {Act : Finset Address} {m : Machine}
    (hS : Start AMPL.runtimeCode amplAbs M Act m) (hval : m.frame.msg.value = 0)
    (hst : m.frame.msg.isStatic = false) (ho : pOwner m.frame.msg.data ∈ Act) :
    (pLive m = true ∧ amplRec m ((pre amplAbs Act m).nonces (pOwner m.frame.msg.data)) =
        pOwner m.frame.msg.data ∧
      (pre amplAbs Act m).nonces (pOwner m.frame.msg.data) < MAX) ↔ PermitOk m := by
  rw [nonces_pre hS hval ho]
  have hts : (ofNat m.ctx.block.timestamp).toNat = m.ctx.block.timestamp % 2 ^ 256 := by
    simp [ofNat]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hval, hst, ?_, by rw [hts]; simpa [pLive] using h1, h2, by unfold MAX at h3; omega⟩
    by_contra hd
    unfold amplRec at h2
    rw [ite_pos' (by omega)] at h2
    split at h2 <;> simp_all
  · rintro ⟨-, -, -, h4, h5, h6⟩
    refine ⟨by rw [hts] at h4; simpa [pLive] using h4, h5, by unfold MAX; omega⟩

/-- **A `PermitOk` frame ending as `PermitDone` matches the model.** -/
theorem matches_of_permitDone {Act : Finset Address} {m mf : Machine}
    (hS : Start AMPL.runtimeCode amplAbs M Act m) (hval : m.frame.msg.value = 0)
    (ho : pOwner m.frame.msg.data ∈ Act) (hsp : pSpender m.frame.msg.data ∈ Act)
    (hok : PermitOk m) (hd : PermitDone m mf) :
    Matches amplAbs Act m mf (.success .empty)
      (M.events (pre amplAbs Act m) m.frame.msg.caller (pCall m))
      (M.call (pre amplAbs Act m) m.frame.msg.caller (pCall m)) := by
  have hc := (permitOk_iff hS hval hok.2.1 ho).2 hok
  simp only [pCall]
  rw [ampl_call_permit, ite_pos' hc]
  obtain ⟨hw, ht, hcr, hl⟩ := hd
  refine ⟨rfl, ?_, ?_, ht, hcr, ?_⟩
  · show amplRead _ _ _ _ = _
    rw [hw, allowSlot', amplRead_sstore_allow hS.sound ho hsp, nonceSlot,
      amplRead_sstore_nonce hS.sound ho, pre_eq hS hval]
    simp only [permitState, AState.setAllowance, VState.setAllowance]
    congr 2
    rw [BitVec.toNat_add]
    simp [amplRead, readMap_apply, ho, nonceSlot, U256]
  · rw [hw]
    exact BNB.Spec.FrameKeeps.sstore'
      (.inr (.inr (.inr (.inr (.inl ⟨_, ho, _, hsp, rfl⟩)))))
      (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, ho, rfl⟩))))))
        BNB.Spec.frameKeeps_refl')
  · rw [hl]
    simp [M, QEDefi.ERC20.Spec.AMPL.amplModel, QEDefi.ERC20.Spec.AMPL.amplEvents,
      Spec.eventLog, word]

end Verified.WeirdERC20.AMPL.Spec.Malformed
