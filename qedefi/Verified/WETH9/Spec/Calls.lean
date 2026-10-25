import Verified.WETH9.Spec.Views
import Verified.WETH9.Spec.World
import Verified.WETH9.Spec.ApproveLow

/-!
# WETH9's ERC-20 calls: the model's outcomes and the bridge to `CallSpec`

The model's outcomes for WETH9 (`weth9_call_approve`, `weth9_call_transfer`,
`weth9_call_transferFrom`), the postcondition of `CallSpec` (`CallPost`) and how a `LowOK`
judgement for every gas from `weth9Gas` gives a `CallSpec` frame (`callSpec_halts`), and the
`approve` case (`approve_callPost`).
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.GasMono EvmLogic.Solidity Verified.WETH9.Contracts
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.WETH9 QEDefi.Math

/-- WETH9's model on addresses. -/
noncomputable abbrev W9 : TokenModel (VState Address) Address (Variant.Op Address) := weth9Model

/-! ## The model -/

theorem weth9_call_approve (s : VState Address) (c sp : Address) (v : ℕ) :
    W9.call s c (.approve sp v) = .ok (s.setAllowance c sp v) (.word true) := by
  simp [weth9Model, Variant.call, Variant.step, Variant.approve, Variant.approveOk,
    Variant.retData, Variant.weth9, Variant.standard]

/-- The balances after a move of `v` from `src` to `dst`. -/
noncomputable def moved (s : VState Address) (src dst : Address) (v : ℕ) : VState Address :=
  { s with bal := s.bal - Finsupp.single src v + Finsupp.single dst v }

theorem weth9_call_transfer (s : VState Address) (c dst : Address) (v : ℕ) :
    W9.call s c (.transfer dst v) =
      if s.bal c < v then .halt .revert else .ok (moved s c dst v) (.word true) := by
  by_cases h : s.bal c < v
  · simp [weth9Model, Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      Variant.move, Variant.units, Variant.feeOverflow, Variant.failKind,
      Variant.guardOk, Variant.overflows, Variant.failWith, Variant.weth9, Variant.standard, h]
  · simp [weth9Model, Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      Variant.move, Variant.units, Variant.feeOverflow, Variant.feeOf, Variant.credit,
      Variant.retData, Variant.weth9, Variant.standard, h, moved]

/-! ## The bridge -/

/-- **The postcondition of `CallSpec`** for the call `c` of the frame `m`, actors `Act`. -/
def CallPost (Act : Finset Address) (m : Machine) (c : Call Address) (mf : Machine)
    (o : Outcome) : Prop :=
  Matches weth9Abs Act m mf o (W9.events (pre weth9Abs Act m) m.frame.msg.caller c)
      (W9.call (pre weth9Abs Act m) m.frame.msg.caller c) ∨
    (QEDefi.ERC20.Spec.Fails o ∧ ¬ Normal weth9Gas m)

/-- **A `CallSpec` frame from `LowOK` judgements** for every gas from `weth9Gas`. -/
theorem callSpec_halts {Act : Finset Address} {m : Machine} {c : Call Address}
    (hf : Fresh WETH9.runtimeCode m)
    (h : ∀ g, weth9Gas ≤ g →
      LowOK (CallPost Act m c) (wethM m.ctx m.precompiles m.world m.transient m.originalWorld
        m.createdAccounts m.frame.msg m.frame.sub m.frame.snapshot m.frame.kind m.parents g)) :
    Halts m (CallPost Act m c) :=
  halts_of_low hf (fun hg _ _ hfo => .inr ⟨fails_of_failed hfo, fun h => hg h.1⟩)
    (fun _ _ _ _ _ h => h) h

/-- A revert of a frame with value is a `CallPost`. -/
theorem callPost_value {Act : Finset Address} {m : Machine} {c : Call Address}
    (hv : m.frame.msg.value ≠ 0) (mf : Machine) (out : ByteArray) :
    CallPost Act m c mf (.revert out) :=
  .inr ⟨trivial, fun h => hv h.2.2⟩

/-- A failure of a static frame is a `CallPost`. -/
theorem callPost_static {Act : Finset Address} {m : Machine} {c : Call Address}
    (hs : m.frame.msg.isStatic = true) (mf : Machine) (e : ExceptionalHalt) :
    CallPost Act m c mf (.halt e) :=
  .inr ⟨trivial, fun h => absurd h.2.1 (by rw [hs]; decide)⟩

/-! ## `approve` -/

/-- **`approve(sp, v)`** satisfies `CallSpec`'s postcondition, for every gas. -/
theorem approve_callPost {Act : Finset Address} {m : Machine} {sp : Address} {v : ℕ}
    (hS : Start WETH9.runtimeCode weth9Abs weth9Model Act m)
    (hE : (Call.approve sp v).Encodes m.frame.msg.data) (hsp : sp ∈ Act) :
    Halts m (CallPost Act m (.approve sp v)) := by
  obtain ⟨hv256, hsel, hsize, harg⟩ := hE
  have hc : m.frame.msg.caller ∈ Act := hS.caller
  have hR : ActorRows m.ctx.crypto Act [3] [4] [] := hS.sound
  refine callSpec_halts hS.fresh fun g hg => ?_
  refine approve_low sp (word v) hsel (by simpa using hsize) hS.size
    (by simpa using harg 0 (by simp)) (by simpa using harg 1 (by simp))
    (le_trans (by decide) hg) (fun hv => callPost_value hv)
    (fun _ hs => callPost_static hs) ?_
  intro hv hst mf out hout hw ht hcr hl
  subst hout
  have hw0 := world_eq_snapshot hS hv
  left
  simp only [Matches, weth9Model, Variant.model_call, Variant.model_events]
  rw [show (Variant.weth9 : Variant Address).call = W9.call from rfl, weth9_call_approve]
  refine ⟨by simp [retBytes], ?_, ?_, ht, hcr, ?_⟩
  · rw [hw]
    simp only [pre, weth9Abs, weth9Read, VState.setAllowance, hw0]
    congr 1
    · exact readMap_sstore_allow hR hc hsp _
    · funext p q
      rw [readMap2_sstore_allow hR hc hsp]
      by_cases hp : p = m.frame.msg.caller
      · subst hp
        by_cases hq : q = sp
        · subst hq
          simp only [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256, and_self, ↓reduceIte,
            Function.update_self]
        · simp [hq]
      · simp [hp]
    · simp
  · rw [hw]; exact frameKeeps_sstore (footprint_allow hc hsp) _
  · rw [hl, Array.push_eq_append]
    rfl

end Verified.WETH9.Spec
