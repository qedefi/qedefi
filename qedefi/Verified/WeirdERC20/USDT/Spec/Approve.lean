import Verified.WeirdERC20.USDT.Spec.ApproveRun
import Verified.WeirdERC20.USDT.Spec.Write

/-!
# USDT's `approve` satisfies `CallSpec`

`usdt_approve`: in every frame `Start` admits, at any gas and with any value, an ABI-encoded
`approve(sp, v)` whose spender is an actor ends as `usdtModel` says: it reverts when `v ≠ 0` and
the current allowance is nonzero (the race guard), and otherwise sets `allowed[caller][sp] = v`
(`setAllowance`, through `read_sstore_allow`), returns no data, logs `Approval(caller, sp, v)`
and changes nothing else; with value, in a static frame or below `g₀` it fails.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Verified.WeirdERC20.USDT.Contracts
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math QEDefi.ERC4626

/-- USDT's `approve` in the model: the race guard, else `setAllowance`, no return data. -/
theorem usdt_call_approve (s : VState Address) (c sp : Address) (v : ℕ) :
    M.call s c (.approve sp v) =
      if v ≠ 0 ∧ s.allowance c sp ≠ 0 then .halt .revert
      else .ok (s.setAllowance c sp v) .empty := by
  by_cases h : v ≠ 0 ∧ s.allowance c sp ≠ 0
  · simp only [h, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    simp [M, QEDefi.ERC20.Spec.USDT.usdtModel, Variant.model, Variant.call, Variant.step,
      Variant.approve, Variant.approveOk, Variant.failKind, Variant.guardOk, Variant.usdt,
      Variant.standard, h.1, h.2, Variant.failWith]
  · simp only [h, ↓reduceIte]
    have h' : v = 0 ∨ s.allowance c sp = 0 := by tauto
    rcases h' with h' | h' <;>
    simp [M, QEDefi.ERC20.Spec.USDT.usdtModel, Variant.model, Variant.call, Variant.step,
      Variant.approve, Variant.approveOk, Variant.usdt, Variant.standard, Variant.retData, h']

theorem word_toNat {v : ℕ} (h : v < 2 ^ 256) : (word v).toNat = v := by
  simp only [word, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem word_ne_zero {v : ℕ} (h : v < 2 ^ 256) : word v ≠ 0 ↔ v ≠ 0 := by
  constructor
  · intro hw hv; exact hw (by simp [word, hv])
  · intro hv hw
    have := congrArg BitVec.toNat hw
    rw [word_toNat h] at this
    exact hv this

/-- The model's allowance of two actors at the start of a frame without value: the row in the
frame's world. -/
theorem pre_allowance {Act : Finset Address} {m : Machine}
    (hs : Start USDT.runtimeCode usdtAbs M Act m) (hval : m.frame.msg.value = 0) {o sp : Address}
    (ho : o ∈ Act) (hsp : sp ∈ Act) :
    (pre usdtAbs Act m).allowance o sp =
      (m.world.sload m.frame.msg.currentTarget (allowRow m.ctx.crypto o sp)).toNat := by
  rw [(live_of_start hs).2, world_of_start hs hval]
  simp only [readState, readMap2, ho, hsp, and_self, ↓reduceIte, allowRow]

/-- **`CallSpec` for `approve(sp, v)`.** -/
theorem usdt_approve (sp : Address) (v : ℕ) :
    CallSpec USDT.runtimeCode usdtAbs M g₀ (.approve sp v) := by
  intro Act m hs henc ha
  obtain ⟨hv, hsel, hsize, harg⟩ := henc
  have hsp : sp ∈ Act := ha sp (by simp [Call.addrs])
  have hc : m.frame.msg.caller ∈ Act := hs.caller
  obtain ⟨hlive, hpre⟩ := live_of_start hs
  refine (halts_of_high hs.fresh (Post := ApproveOut sp (word v) m)
    (fun _ _ _ h => approveOut_halt h) (fun _ _ h => h)
    (approve_high m hs.fresh _ sp (word v) (by omega) hsel (by simpa using hsize) hs.size
      (harg 0 (by simp)) (harg 1 (by simp)) (dep_of_start hs))).mono fun mf o _ h => ?_
  rcases h with ⟨hf, hlt⟩ | ⟨hval, hf⟩ | ⟨hst, hf⟩ | ⟨hval, hst, hrev | hok⟩
  · exact .inr ⟨hf, fun h => by unfold Normal at h; omega⟩
  · exact .inr ⟨hf, fun h => hval h.2.2⟩
  · exact .inr ⟨hf, fun h => by rw [h.2.1] at hst; cases hst⟩
  all_goals left
  all_goals have hw := world_of_start hs hval
  all_goals have hcur := pre_allowance hs hval hc hsp
  · obtain ⟨hv0, hne, out, ho⟩ := hrev
    have hc0 : v ≠ 0 ∧ (pre usdtAbs Act m).allowance m.frame.msg.caller sp ≠ 0 := by
      refine ⟨(word_ne_zero hv).1 hv0, ?_⟩
      rw [hcur]; intro h0; exact hne (BitVec.eq_of_toNat_eq (by simpa using h0))
    rw [usdt_call_approve]
    simp only [hc0, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    exact ⟨out, ho⟩
  · obtain ⟨hguard, ho, hwd, htr, hcr, hlog⟩ := hok
    have hc0 : ¬ (v ≠ 0 ∧ (pre usdtAbs Act m).allowance m.frame.msg.caller sp ≠ 0) := by
      rintro ⟨h1, h2⟩
      refine hguard ⟨(word_ne_zero hv).2 h1, fun h0 => h2 ?_⟩
      rw [hcur, h0]; rfl
    rw [usdt_call_approve]
    simp only [hc0, ↓reduceIte]
    have hlive' : Live Act m.world m.frame.msg.currentTarget := hw ▸ hlive
    obtain ⟨-, hread⟩ := read_sstore_allow (token := m.frame.msg.currentTarget) hs.sound hc hsp
      hlive' (word v)
    refine ⟨ho, ?_, ?_, htr, hcr, ?_⟩
    · show read _ _ _ _ = _
      rw [hwd]
      unfold allowRow
      rw [hread, word_toNat hv, read_eq_of_live hlive', hpre, ← hw]
    · rw [hwd]
      exact FrameKeeps.sstore (frameKeeps_refl _ _ _ _) (.inr (.inr (.inl ⟨_, hc, _, hsp, rfl⟩))) _
    · rw [hlog]
      simp [M, QEDefi.ERC20.Spec.USDT.usdtEvents, Spec.eventLog]

end Verified.WeirdERC20.USDT.Spec
