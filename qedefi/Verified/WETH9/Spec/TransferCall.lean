import Verified.WETH9.Spec.Calls
import Verified.WETH9.Spec.TransferLow

/-!
# WETH9's `transfer` satisfies `CallSpec`

`transfer_callPost`: on the deployed bytecode, `transfer(dst, v)` by an actor to an actor ends as
`weth9Model` says (through `weth9Abs`), for every gas from `weth9Gas`, or fails below it, with
value or in a static frame. The unchecked credit cannot wrap: the model's invariant (balances
backed by the ether, `Start.wf`) bounds the two balances (`read_move`).
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.GasMono EvmLogic.Solidity Verified.WETH9.Contracts
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.WETH9 QEDefi.Math

theorem toNat_word {v : ℕ} (h : v < 2 ^ 256) : (word v).toNat = v := by
  show (BitVec.ofNat 256 v).toNat = v
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- **`transfer(dst, v)`** satisfies `CallSpec`'s postcondition, for every gas. -/
theorem transfer_callPost {Act : Finset Address} {m : Machine} {dst : Address} {v : ℕ}
    (hS : Start WETH9.runtimeCode weth9Abs weth9Model Act m)
    (hE : (Call.transfer dst v).Encodes m.frame.msg.data) (hd : dst ∈ Act) :
    Halts m (CallPost Act m (.transfer dst v)) := by
  obtain ⟨hv256, hsel, hsize, harg⟩ := hE
  have hc : m.frame.msg.caller ∈ Act := hS.caller
  have hR : ActorRows m.ctx.crypto Act [3] [4] [] := hS.sound
  have hwf := (weth9Model_wf _).1 hS.wf
  have hwv := toNat_word hv256
  refine callSpec_halts hS.fresh fun g hg => ?_
  refine transfer_low dst (word v) _ hsel (by simpa using hsize) hS.size
    (by simpa using harg 0 (by simp)) (by simpa using harg 1 (by simp))
    (le_trans (by decide) hg) rfl ?_ (fun _ hs => callPost_static hs) ?_
  · intro h mf out
    by_cases hv : m.frame.msg.value = 0
    · have hlt := h.resolve_left (not_not.2 hv)
      have hw0 := world_eq_snapshot hS hv
      left
      simp only [Matches, weth9Model, Variant.model_call, Variant.model_events]
      rw [show (Variant.weth9 : Variant Address).call = W9.call from rfl, weth9_call_transfer]
      have : (pre weth9Abs Act m).bal m.frame.msg.caller < v := by
        simp only [pre, weth9Abs, weth9Read, readMap_of_mem hc, ← hw0]
        omega
      simp only [this, ↓reduceIte]
      exact ⟨out, rfl⟩
    · exact callPost_value hv mf out
  · intro hv hst hb mf out hout hw ht hcr hl
    subst hout
    have hw0 := world_eq_snapshot hS hv
    left
    simp only [Matches, weth9Model, Variant.model_call, Variant.model_events]
    rw [show (Variant.weth9 : Variant Address).call = W9.call from rfl, weth9_call_transfer]
    have hnlt : ¬ (pre weth9Abs Act m).bal m.frame.msg.caller < v := by
      simp only [pre, weth9Abs, weth9Read, readMap_of_mem hc, ← hw0]
      omega
    simp only [hnlt, ↓reduceIte]
    refine ⟨by simp [retBytes], ?_, ?_, ht, hcr, ?_⟩
    · rw [hw]
      have hm := read_move (w := m.world) (token := m.frame.msg.currentTarget) hR hc hd hb
        (by simpa only [pre, weth9Abs, hw0] using hwf)
      rw [hwv] at hm
      change weth9Read _ _ _ _ = _
      rw [hm]
      simp only [pre, weth9Abs, hw0]
    · rw [hw]
      exact FrameKeeps.trans (frameKeeps_sstore (footprint_bal hc) _)
        (frameKeeps_sstore (footprint_bal hd) _)
    · rw [hl, Array.push_eq_append]
      rfl

end Verified.WETH9.Spec
