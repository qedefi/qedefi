import Verified.WeirdERC20.LEND.Spec.Transfer
import Verified.WeirdERC20.LEND.Spec.Write

/-!
# LEND under the spec: the `approve` and `transfer` obligations

The runs (`Approve.lean`, `Transfer.lean`) end in `ApprovePost`/`TransferPost`, stated with
transfers enabled; the model's invariant (the final sale state) provides it for the high-gas
run (`enabled_word`). Here the code-level ends are read through the abstraction.
-/

namespace Verified.WeirdERC20.LEND.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.LEND.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open QEDefi.ERC4626

/-! ## The model -/

theorem lend_call_approve (s : LEND.State Address) (c sp : Address) (v : ℕ)
    (he : s.enabled = true) :
    M.call s c (.approve sp v) =
      if v = 0 ∨ s.allowance c sp = 0 then .ok (s.setAllowance c sp v) (.word true)
      else .halt .revert := by
  simp only [M, QEDefi.ERC20.Spec.LEND.model, QEDefi.ERC20.Spec.LEND.call,
    QEDefi.ERC20.Spec.LEND.step, QEDefi.ERC20.Spec.LEND.approve, he, true_and]
  split_ifs <;> rfl

theorem lend_call_transfer (s : LEND.State Address) (c d : Address) (v : ℕ)
    (he : s.enabled = true) :
    M.call s c (.transfer d v) =
      if v ≤ s.bal c ∧ 0 < v ∧ s.bal d + v ≤ QEDefi.Math.MAX then
        .ok { s with bal := s.bal - Finsupp.single c v + Finsupp.single d v } (.word true)
      else .halt .revert := by
  simp only [M, QEDefi.ERC20.Spec.LEND.model, QEDefi.ERC20.Spec.LEND.call,
    QEDefi.ERC20.Spec.LEND.step, QEDefi.ERC20.Spec.LEND.transfer, QEDefi.ERC20.Spec.LEND.move,
    he, ite_true]
  split_ifs <;> rfl

/-- The model state at the start of the frame has transfers enabled (its invariant). -/
theorem pre_enabled {Act : Finset Address} {m : Machine} (hs : Start LEND.runtimeCode abs M Act m) :
    (pre abs Act m).enabled = true := hs.wf.2

/-! ## Writes -/

/-- **`transfer`'s move** through the abstraction: the model's move, when covered and not
wrapping. -/
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
  simp only [moveWorld, balSlot]
  rw [show (0#256 : Word) = balancesSlot from rfl, read_sstore_bal hS hd, read_sstore_bal hS hc]
  dsimp only
  congr 1
  have hrc : (read crypto Act w t).bal c =
      (w.sload t (mappingSlot crypto (Word.ofAddress c) balancesSlot)).toNat :=
    readMap_of_mem hc _ _ _
  have hrd : (read crypto Act w t).bal d =
      (w.sload t (mappingSlot crypto (Word.ofAddress d) balancesSlot)).toNat :=
    readMap_of_mem hd _ _ _
  apply bal_move (by rw [hrc]; exact hv)
  · rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hv), hrc]
  · by_cases hcd : d = c
    · subst hcd
      rw [World.sload_sstore_self, BitVec.toNat_add, BitVec.toNat_sub_of_le
        (by rw [BitVec.le_def]; exact hv), Nat.mod_eq_of_lt (by omega), ite_pos' rfl, hrc]
    · have hne : mappingSlot crypto (Word.ofAddress d) balancesSlot ≠
          mappingSlot crypto (Word.ofAddress c) balancesSlot := fun e =>
        hcd (hS.inj1 balancesSlot (by simp) balancesSlot (by simp) d hd c hc e).1
      rw [World.sload_sstore_ne_key _ _ _ hne, BitVec.toNat_add, Nat.mod_eq_of_lt hov,
        ite_neg' hcd, hrd]

/-- The balance row of an actor is in the footprint. -/
theorem bal_mem {crypto : Crypto} {Act : Finset Address} {a : Address} (ha : a ∈ Act) :
    abs.footprint crypto Act (balSlot crypto a) := .inr (.inl ⟨a, ha, rfl⟩)

/-- The allowance row of two actors is in the footprint. -/
theorem allow_mem {crypto : Crypto} {Act : Finset Address} {o sp : Address} (ho : o ∈ Act)
    (hs : sp ∈ Act) : abs.footprint crypto Act (allowSlot crypto o sp) :=
  .inr (.inr ⟨o, ho, sp, hs, rfl⟩)

/-! ## The obligations -/

/-- **`approve(sp, v)`**: the race guard reverts; otherwise the allowance is set, `true`,
`Approval`. -/
theorem call_approve (sp : Address) (v : ℕ) :
    CallSpec LEND.runtimeCode abs M g₀ (.approve sp v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hsA : sp ∈ Act := haddr sp (by simp [Call.addrs])
  have hcA := hs.caller
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  have hw0 : word v = 0 ↔ v = 0 := ⟨fun h => by rw [← hwv, h]; rfl, fun h => by subst h; rfl⟩
  have hpre := pre_eq hs
  have hal : (pre abs Act m).allowance m.frame.msg.caller sp =
      (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat := by
    rw [hpre]; simp [read, readMap2, hsA, hcA, allowedSlot]
  have hA0 : m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp) = 0 ↔
      (pre abs Act m).allowance m.frame.msg.caller sp = 0 := by
    rw [hal]; exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by simpa using h)⟩
  refine halts_split' (G := Normal g₀ m)
    (fun hG => approve_high m sp (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1
      (enabled_word hs))
    (approve_low m sp (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  rw [lend_call_approve _ _ _ _ (pre_enabled hs)]
  by_cases hg : v = 0 ∨ (pre abs Act m).allowance m.frame.msg.caller sp = 0
  · left
    rw [ite_pos' hg]
    obtain ⟨-, -, ho, hw, ht, hcr, hl⟩ := hok (by
      rcases hg with h | h
      · exact .inl (hw0.2 h)
      · exact .inr (hA0.2 h))
    refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
    · show read _ _ _ _ = _
      rw [hw]
      simp only [allowSlot]
      rw [show (1#256 : Word) = allowedSlot from rfl, read_sstore_allow hs.sound hcA hsA,
        ← hpre, hwv]
    · rw [hw]
      exact BNB.Spec.FrameKeeps.sstore' (allow_mem hcA hsA) BNB.Spec.frameKeeps_refl'
    · rw [hl]
      simp [M, QEDefi.ERC20.Spec.LEND.model, QEDefi.ERC20.Spec.LEND.events, Spec.eventLog]
  · rw [ite_neg' hg]
    simp only [not_or] at hg
    obtain ⟨out, rfl⟩ := hrev (fun h => hg.1 (hw0.1 h)) (fun h => hg.2 (hA0.1 h))
    by_cases hG : Normal g₀ m
    · exact .inl ⟨out, rfl⟩
    · exact .inr ⟨trivial, hG⟩

/-- **`transfer(dst, v)`**: a short balance, a zero value or a wrapping credit revert; otherwise
the move with its `Transfer`, `true`. -/
theorem call_transfer (dst : Address) (v : ℕ) :
    CallSpec LEND.runtimeCode abs M g₀ (.transfer dst v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hdA : dst ∈ Act := haddr dst (by simp [Call.addrs])
  have hcA := hs.caller
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv256]
  have hpre := pre_eq hs
  have hbc : (pre abs Act m).bal m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
    rw [hpre]; exact readMap_of_mem hcA _ _ _
  have hbd : (pre abs Act m).bal dst =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat := by
    rw [hpre]; exact readMap_of_mem hdA _ _ _
  refine halts_split' (G := Normal g₀ m)
    (fun hG => transfer_high m dst (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1
      (enabled_word hs))
    (transfer_low m dst (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  rw [hwv] at hrev hok
  rw [lend_call_transfer _ _ _ _ (pre_enabled hs), hbc, hbd]
  by_cases hg : v ≤ (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat ∧ 0 < v ∧
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat + v ≤
        QEDefi.Math.MAX
  · left
    rw [ite_pos' hg]
    obtain ⟨h1, h2, h3⟩ := hg
    have h3' : (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat + v <
        2 ^ 256 := by simp only [QEDefi.Math.MAX] at h3; omega
    obtain ⟨-, -, ho, hw, ht, hcr, hl⟩ := hok h1 h2 h3'
    refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
    · show read _ _ _ _ = _
      rw [hw, read_moveWorld hs.sound hcA hdA (by rw [hwv]; exact h1) (by rw [hwv]; exact h3'),
        ← hpre, hwv]
    · rw [hw, moveWorld]
      exact BNB.Spec.FrameKeeps.sstore' (bal_mem hdA)
        (BNB.Spec.FrameKeeps.sstore' (bal_mem hcA) BNB.Spec.frameKeeps_refl')
    · rw [hl]
      simp [M, QEDefi.ERC20.Spec.LEND.model, QEDefi.ERC20.Spec.LEND.events, Spec.eventLog]
  · rw [ite_neg' hg]
    obtain ⟨out, rfl⟩ := hrev (by simp only [QEDefi.Math.MAX] at hg; omega)
    by_cases hG : Normal g₀ m
    · exact .inl ⟨out, rfl⟩
    · exact .inr ⟨trivial, hG⟩

end Verified.WeirdERC20.LEND.Spec
