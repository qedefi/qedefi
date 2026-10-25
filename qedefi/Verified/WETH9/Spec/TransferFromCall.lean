import Verified.WETH9.Spec.TransferCall
import Verified.WETH9.Spec.TransferFromLow

/-!
# WETH9's `transferFrom` satisfies `CallSpec`

`transferFrom_callPost`: on the deployed bytecode, `transferFrom(src, dst, v)` by an actor, with
actors `src` and `dst`, ends as `weth9Model` says (through `weth9Abs`), for every gas from
`weth9Gas`, or fails below it, with value or in a static frame. The bytecode checks the balance
before the allowance and the model the other way round; both failures are `REVERT`s, so the
outcomes agree.
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.GasMono EvmLogic.Solidity Verified.WETH9.Contracts
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.WETH9 QEDefi.Math

theorem weth9_call_transferFrom (s : VState Address) (c src dst : Address) (v : ℕ) :
    W9.call s c (.transferFrom src dst v) =
      if src = c ∨ s.allowance src c = MAX then
        (if s.bal src < v then .halt .revert else .ok (moved s src dst v) (.word true))
      else if s.allowance src c < v then .halt .revert
      else if s.bal src < v then .halt .revert
      else .ok (moved (s.setAllowance src c (s.allowance src c - v)) src dst v) (.word true) := by
  simp only [weth9Model, Variant.model_call, Variant.call, Variant.step, Variant.transferFrom,
    Variant.moveOk, Variant.spend, Variant.move, Variant.units, Variant.feeOverflow,
    Variant.feeOf, Variant.credit, Variant.retData, Variant.failKind, Variant.guardOk,
    Variant.overflows, Variant.failWith, Variant.weth9, Variant.standard, Infinite.test]
  by_cases h1 : src = c
  · subst h1; by_cases h2 : s.bal src < v <;> simp [h2, moved]
  · by_cases h2 : s.allowance src c = MAX
    · by_cases h3 : s.bal src < v <;> simp [h1, h2, h3, moved]
    · by_cases h3 : s.allowance src c < v
      · simp [h1, h2, h3]
      · by_cases h4 : s.bal src < v
        · simp [h1, h2, h3, h4, VState.setAllowance]
        · simp [h1, h2, h3, h4, VState.setAllowance, moved]

/-- **Writing `allowance[o][sp]`** is the model's `setAllowance`, for actors `o`, `sp`. -/
theorem read_sstore_allow {crypto : Crypto} {Act : Finset Address} {w : World}
    {token o sp : Address} (hR : ActorRows crypto Act [3] [4] []) (ho : o ∈ Act)
    (hsp : sp ∈ Act) (x : Word) :
    weth9Read crypto Act
        (w.sstore token (mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 4) x) token =
      (weth9Read crypto Act w token).setAllowance o sp x.toNat := by
  simp only [weth9Read, VState.setAllowance]
  congr 1
  · exact readMap_sstore_allow hR ho hsp _
  · funext p q
    rw [readMap2_sstore_allow hR ho hsp]
    by_cases hp : p = o
    · subst hp
      by_cases hq : q = sp
      · subst hq; simp
      · simp [hq]
    · simp [hp]
  · simp

theorem maxWord_iff (x : Word) : x = maxWord ↔ x.toNat = MAX := by
  constructor
  · rintro rfl; rfl
  · intro h; apply BitVec.eq_of_toNat_eq; rw [h]; rfl

/-- **`transferFrom(src, dst, v)`** satisfies `CallSpec`'s postcondition, for every gas. -/
theorem transferFrom_callPost {Act : Finset Address} {m : Machine} {src dst : Address} {v : ℕ}
    (hS : Start WETH9.runtimeCode weth9Abs weth9Model Act m)
    (hE : (Call.transferFrom src dst v).Encodes m.frame.msg.data) (hs : src ∈ Act)
    (hd : dst ∈ Act) :
    Halts m (CallPost Act m (.transferFrom src dst v)) := by
  obtain ⟨hv256, hsel, hsize, harg⟩ := hE
  have hc : m.frame.msg.caller ∈ Act := hS.caller
  have hR : ActorRows m.ctx.crypto Act [3] [4] [] := hS.sound
  have hwf := (weth9Model_wf _).1 hS.wf
  have hwv := toNat_word hv256
  -- the model's view of the two rows, in the frame's world when no value moved
  have hbal : ∀ hv : m.frame.msg.value = 0, (pre weth9Abs Act m).bal src =
      (m.world.sload m.frame.msg.currentTarget (mappingSlot m.ctx.crypto (Word.ofAddress src) 3)).toNat :=
    fun hv => by simp only [pre, weth9Abs, weth9Read, readMap_of_mem hs, world_eq_snapshot hS hv]
  have hall : ∀ hv : m.frame.msg.value = 0,
      (pre weth9Abs Act m).allowance src m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (mappingSlot2 m.ctx.crypto (Word.ofAddress src)
        (Word.ofAddress m.frame.msg.caller) 4)).toNat :=
    fun hv => by simp only [pre, weth9Abs, weth9Read, readMap2, hs, hc, and_self, ↓reduceIte,
      world_eq_snapshot hS hv]
  refine callSpec_halts hS.fresh fun g hg => ?_
  refine transferFrom_low src dst (word v) _ _ hsel (by simpa using hsize) hS.size
    (by simpa using harg 0 (by simp)) (by simpa using harg 1 (by simp))
    (by simpa using harg 2 (by simp)) (le_trans (by decide) hg) rfl rfl ?_
    (fun _ hs => callPost_static hs) ?_ ?_
  · intro h mf out
    by_cases hv : m.frame.msg.value = 0
    · left
      simp only [Matches, weth9Model, Variant.model_call, Variant.model_events]
      rw [show (Variant.weth9 : Variant Address).call = W9.call from rfl, weth9_call_transferFrom]
      rw [hbal hv, hall hv]
      rcases h with h | h | ⟨hsc, hm, hlt⟩
      · exact absurd hv h
      · rw [hwv] at h
        split_ifs <;> exact ⟨out, rfl⟩
      · rw [hwv] at hlt
        have hm' := fun h => hm ((maxWord_iff _).2 h)
        split_ifs with h1 h2 <;> try exact ⟨out, rfl⟩
        rcases h1 with h1 | h1
        · exact absurd h1 hsc
        · exact absurd h1 hm'
    · exact callPost_value hv mf out
  · intro hv hst hb hA mf out hout hw ht hcr hl
    subst hout
    have hw0 := world_eq_snapshot hS hv
    left
    simp only [Matches, weth9Model, Variant.model_call, Variant.model_events]
    rw [show (Variant.weth9 : Variant Address).call = W9.call from rfl, weth9_call_transferFrom]
    have hA' : src = m.frame.msg.caller ∨ (pre weth9Abs Act m).allowance src m.frame.msg.caller
        = MAX := by
      rcases hA with h | h
      · exact .inl h
      · exact .inr (by rw [hall hv]; exact (maxWord_iff _).1 h)
    have hnlt : ¬ (pre weth9Abs Act m).bal src < v := by rw [hbal hv]; omega
    simp only [hA', hnlt, ↓reduceIte]
    refine ⟨by simp [retBytes], ?_, ?_, ht, hcr, ?_⟩
    · rw [hw]
      have hm := read_move (w := m.world) (token := m.frame.msg.currentTarget) hR hs hd hb
        (by simpa only [pre, weth9Abs, hw0] using hwf)
      rw [hwv] at hm
      change weth9Read _ _ _ _ = _
      rw [moveWorld, hm]
      simp only [pre, weth9Abs, hw0]
    · rw [hw]
      exact FrameKeeps.trans (frameKeeps_sstore (footprint_bal hs) _)
        (frameKeeps_sstore (footprint_bal hd) _)
    · rw [hl, Array.push_eq_append]
      rfl
  · intro hv hst hb hsc hm ha mf out hout hw ht hcr hl
    subst hout
    have hw0 := world_eq_snapshot hS hv
    left
    simp only [Matches, weth9Model, Variant.model_call, Variant.model_events]
    rw [show (Variant.weth9 : Variant Address).call = W9.call from rfl, weth9_call_transferFrom]
    have hm' : ¬ (pre weth9Abs Act m).allowance src m.frame.msg.caller = MAX := by
      rw [hall hv]; exact fun h => hm ((maxWord_iff _).2 h)
    have hnlt : ¬ (pre weth9Abs Act m).bal src < v := by rw [hbal hv]; omega
    have hnla : ¬ (pre weth9Abs Act m).allowance src m.frame.msg.caller < v := by
      rw [hall hv]; omega
    simp only [hsc, hm', or_self, hnlt, hnla, ↓reduceIte]
    refine ⟨by simp [retBytes], ?_, ?_, ht, hcr, ?_⟩
    · rw [hw]
      set w' := m.world.sstore m.frame.msg.currentTarget
        (mappingSlot2 m.ctx.crypto (Word.ofAddress src) (Word.ofAddress m.frame.msg.caller) 4)
        (m.world.sload m.frame.msg.currentTarget
          (mappingSlot2 m.ctx.crypto (Word.ofAddress src) (Word.ofAddress m.frame.msg.caller) 4)
          - word v) with hw'
      have hread := read_sstore_allow (w := m.world) (token := m.frame.msg.currentTarget) hR hs
        hc (m.world.sload m.frame.msg.currentTarget
          (mappingSlot2 m.ctx.crypto (Word.ofAddress src) (Word.ofAddress m.frame.msg.caller) 4)
          - word v)
      rw [← hw'] at hread
      have hb' : (word v).toNat ≤
          (w'.sload m.frame.msg.currentTarget (mappingSlot m.ctx.crypto (Word.ofAddress src) 3)).toNat := by
        rw [hw', World.sload_sstore_ne_key _ _ _ (balSlot_ne_allowSlot hR hs hs hc)]
        exact hb
      have hwf' : total (weth9Read m.ctx.crypto Act w' m.frame.msg.currentTarget).bal ≤
          (weth9Read m.ctx.crypto Act w' m.frame.msg.currentTarget).ether := by
        rw [hread]
        simpa only [pre, weth9Abs, hw0, VState.setAllowance] using hwf
      have hm := read_move (w := w') (token := m.frame.msg.currentTarget) hR hs hd hb' hwf'
      rw [hwv] at hm
      change weth9Read _ _ _ _ = _
      rw [moveWorld, hm, hread, QEDefi.Solvency.toNat_sub_of_le ha, hwv, ← hall hv]
      simp only [pre, weth9Abs, hw0]
    · rw [hw]
      exact FrameKeeps.trans (frameKeeps_sstore (footprint_allow hs hc) _)
        (FrameKeeps.trans (frameKeeps_sstore (footprint_bal hs) _)
          (frameKeeps_sstore (footprint_bal hd) _))
    · rw [hl, Array.push_eq_append]
      rfl

end Verified.WETH9.Spec
