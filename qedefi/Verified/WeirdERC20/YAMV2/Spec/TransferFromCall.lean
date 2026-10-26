import Verified.WeirdERC20.YAMV2.Spec.TransferFromHigh
import Verified.WeirdERC20.YAMV2.Spec.TransferFromLow
import Verified.WeirdERC20.YAMV2.Spec.TransferCall

/-!
# YAMv2 under the spec: the `transferFrom` obligation

The code-level runs (`transferFrom_high`, `transferFrom_low`) against the model: the move as
for `transfer` (`read_moveWorld`), the allowance read after the move is the one before it (the
balance rows and the allowance rows of the actors are distinct), and the allowance written back
through `_approve`, with `Transfer` and `Approval`.
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.YAMV2.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

set_option linter.unusedSimpArgs false in
theorem yam_call_transferFrom (s : VState Address) (c src d : Address) (v : ℕ) :
    M.call s c (.transferFrom src d v) =
      if src = 0 ∨ d = 0 ∨ c = 0 ∨ s.bal src < v ∨ s.allowance src c < v then .halt .revert
      else .ok { s.setAllowance src c (s.allowance src c - v) with
        bal := s.bal - Finsupp.single src v + Finsupp.single d v } (.word true) := by
  simp only [M, QEDefi.ERC20.Spec.YAMV2.model]
  by_cases h1 : src = 0
  · subst h1
    simp [Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk,
      QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard, Variant.failKind, Variant.guardOk,
      Variant.failWith]
  have h1' : ¬ src = 0#160 := h1
  by_cases h2 : d = 0
  · subst h2
    simp [h1', Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk,
      QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard, Variant.failKind, Variant.guardOk,
      Variant.failWith]
  have h2' : ¬ d = 0#160 := h2
  by_cases h4 : s.allowance src c < v
  · simp [h1', h2', h4, Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk,
      Variant.spend, Infinite.test, QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard,
      Variant.failKind, Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith]
  by_cases h3 : c = 0
  · subst h3
    simp [h1', h2', h4, Variant.call, Variant.step, Variant.transferFrom, Variant.moveOk,
      Variant.spend, Infinite.test, QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard,
      Variant.failKind, Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith]
  have h3' : ¬ c = 0#160 := h3
  by_cases h5 : s.bal src < v
  · simp [h1', h2', h3', h4, h5, Variant.call, Variant.step, Variant.transferFrom,
      Variant.moveOk, Variant.spend, Infinite.test, Variant.move, Variant.units,
      VState.setAllowance, QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard, Variant.failKind,
      Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith]
  · simp [h1', h2', h3', h4, h5, Variant.call, Variant.step, Variant.transferFrom,
      Variant.moveOk, Variant.spend, Infinite.test, Variant.move, Variant.units,
      VState.setAllowance, QEDefi.ERC20.Spec.YAMV2.variant, Variant.standard,
      Variant.feeOverflow, Variant.feeOf, Variant.credit, Variant.retData]

/-- Under the supply bound the credit of a move between actors fits a word. -/
theorem yam_fit {crypto : Crypto} {Act : Finset Address} {w : World} {t src dst : Address}
    {v : ℕ} (hS : abs.Sound crypto Act) (hsA : src ∈ Act) (hdA : dst ∈ Act) (hv : v < 2 ^ 256)
    (hbc : v ≤ (w.sload t (balSlot crypto src)).toNat)
    (htot : QEDefi.ERC20.total (read crypto Act w t).bal < 2 ^ 256) :
    ((debitWorld crypto w t src (word v)).sload t (balSlot crypto dst)).toNat + v < 2 ^ 256 := by
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  have hbalc := readMap_of_mem (crypto := crypto) hsA w t 1#256
  have hbald := readMap_of_mem (crypto := crypto) hdA w t 1#256
  simp only [debitWorld]
  by_cases hcd : src = dst
  · rw [← hcd, World.sload_sstore_self,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hwv]; exact hbc), hwv]
    have := BitVec.isLt (w.sload t (balSlot crypto src))
    omega
  · have hne : balSlot crypto dst ≠ balSlot crypto src := fun e =>
      hcd (hS.inj1 1#256 (by decide) 1#256 (by decide) dst hdA _ hsA e).1.symm
    rw [World.sload_sstore_ne_key _ _ _ hne]
    have h2 := QEDefi.ERC20.Spec.YAMV2.add_le_total (f := (read crypto Act w t).bal) hcd
    simp only [read, VState.ofToken, show balancesSlot = 1#256 from rfl] at h2 htot
    rw [hbalc, hbald] at h2
    simp only [balSlot] at *
    omega

set_option linter.unusedSimpArgs false in
/-- **The move as the actors see it**: the debit and the credit of `v` between actors. -/
theorem read_moveWorld {crypto : Crypto} {Act : Finset Address} {w : World} {t src dst : Address}
    {v : ℕ} (hS : abs.Sound crypto Act) (hsA : src ∈ Act) (hdA : dst ∈ Act) (hv : v < 2 ^ 256)
    (hbc : v ≤ (w.sload t (balSlot crypto src)).toNat)
    (hfit : ((debitWorld crypto w t src (word v)).sload t (balSlot crypto dst)).toNat + v <
      2 ^ 256) :
    read crypto Act (moveWorld crypto w t src dst (word v)) t =
      { read crypto Act w t with
        bal := (read crypto Act w t).bal - Finsupp.single src v + Finsupp.single dst v } := by
  have hwv : (word v).toNat = v := by rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  have hbalc := readMap_of_mem (crypto := crypto) hsA w t 1#256
  rw [moveWorld, read_sstore_bal hS hdA, debitWorld, read_sstore_bal hS hsA]
  dsimp only
  congr 1
  ext a
  simp only [Finsupp.update_apply, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
    Pi.sub_apply, Finsupp.single_apply]
  have hsub : (w.sload t (balSlot crypto src) - word v).toNat =
      (w.sload t (balSlot crypto src)).toNat - v := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hwv]; exact hbc), hwv]
  by_cases hcd : src = dst
  · subst hcd
    rw [World.sload_sstore_self]
    have hadd : (word v + (w.sload t (balSlot crypto src) - word v)).toNat =
        (w.sload t (balSlot crypto src)).toNat := by
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    by_cases ha : a = src
    · subst ha
      simp only [read, VState.ofToken, show balancesSlot = 1#256 from rfl, readMap_of_mem hsA,
        hadd, ite_true]
      rw [← hbalc]
      simp only [balSlot] at *; omega
    · simp [ha, Ne.symm ha, read]
  · have hne : balSlot crypto dst ≠ balSlot crypto src := fun e =>
      hcd (hS.inj1 1#256 (by decide) 1#256 (by decide) dst hdA _ hsA e).1.symm
    rw [World.sload_sstore_ne_key _ _ _ hne]
    have hfit' := hfit
    simp only [debitWorld] at hfit'
    rw [World.sload_sstore_ne_key _ _ _ hne] at hfit'
    have hadd : (word v + w.sload t (balSlot crypto dst)).toNat =
        v + (w.sload t (balSlot crypto dst)).toNat := by
      rw [BitVec.toNat_add, hwv, Nat.mod_eq_of_lt (by omega)]
    by_cases ha : a = dst
    · subst ha
      simp only [read, VState.ofToken, show balancesSlot = 1#256 from rfl, readMap_of_mem hdA,
        hadd, ite_true, hcd, Ne.symm hcd, ite_false]
      simp only [balSlot] at *; omega
    · by_cases hac : a = src
      · subst hac
        simp only [read, VState.ofToken, show balancesSlot = 1#256 from rfl,
          readMap_of_mem hsA, hsub, ha, ite_true, ite_false,
          show ¬ dst = a from fun e => ha e.symm]
        simp only [balSlot] at *; omega
      · simp [ha, hac, Ne.symm ha, Ne.symm hac, read]

theorem push_push_eq {α : Type} (a : Array α) (x y : α) : (a.push x).push y = a ++ #[x, y] := by
  cases a; simp

/-- The move leaves the actors' allowance rows. -/
theorem sload_moveWorld_allow {crypto : Crypto} {Act : Finset Address} {w : World}
    {t src dst o sp : Address} {x : Word} (hS : abs.Sound crypto Act) (hsA : src ∈ Act)
    (hdA : dst ∈ Act) (ho : o ∈ Act) (hsp : sp ∈ Act) :
    (moveWorld crypto w t src dst x).sload t (allowSlot crypto o sp) =
      w.sload t (allowSlot crypto o sp) := by
  simp only [moveWorld, debitWorld]
  rw [World.sload_sstore_ne_key _ _ _ (fun e => hS.disj 1#256 (by decide) 2#256 (by decide)
      dst hdA o ho sp hsp e.symm),
    World.sload_sstore_ne_key _ _ _ (fun e => hS.disj 1#256 (by decide) 2#256 (by decide)
      src hsA o ho sp hsp e.symm)]

/-- **`transferFrom(src, dst, v)`**: a zero sender, recipient or caller, or an amount above the
balance or the allowance reverts; otherwise the move, the allowance lowered, `true`, `Transfer`
and `Approval`. -/
theorem call_transferFrom (src dst : Address) (v : ℕ) :
    CallSpec YAMV2.runtimeCode abs M g₀ (.transferFrom src dst v) := by
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
  have htot := yam_total_lt hs hv0
  have hbal : (pre abs Act m).bal src =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat := by
    rw [hpre]; exact readMap_of_mem hsA _ _ _
  have hA' : allowAfter m src dst (word v) =
      m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto src m.frame.msg.caller) :=
    sload_moveWorld_allow hs.sound hsA hdA hsA hcA
  have hall : (pre abs Act m).allowance src m.frame.msg.caller =
      (allowAfter m src dst (word v)).toNat := by
    rw [hA', hpre]
    simp [read, VState.ofToken, readMap2, hsA, hcA, allowancesSlot, allowSlot]
  rw [yam_call_transferFrom, hbal, hall]
  by_cases hr : src = 0 ∨ dst = 0 ∨ m.frame.msg.caller = 0 ∨
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat < v
  · rw [ite_pos' (by rcases hr with h | h | h | h <;> simp [h])]
    exact hrev (by rw [hwv]; exact hr)
  simp only [not_or, not_lt] at hr
  obtain ⟨hs0, hd0, hc0, hbc⟩ := hr
  have hfit := yam_fit hs.sound hsA hdA hv256 hbc htot
  obtain ⟨hrevA, hokA⟩ := hok hs0 hd0 hc0 (by rw [hwv]; exact hbc) (by rw [hwv]; exact hfit)
  by_cases hab : (allowAfter m src dst (word v)).toNat < v
  · rw [ite_pos' (by simp [hab])]
    exact hrevA (by rw [hwv]; exact hab)
  rw [ite_neg' (by simp only [not_or]; exact ⟨hs0, hd0, hc0, Nat.not_lt.2 hbc, hab⟩)]
  have hab' := Nat.le_of_not_lt hab
  obtain ⟨-, -, ho, hw, ht, hcr, hl⟩ := hokA (by rw [hwv]; exact hab')
  have hsubw : (allowAfter m src dst (word v) - word v).toNat =
      (allowAfter m src dst (word v)).toNat - v := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hwv]; exact hab'), hwv]
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show read _ _ _ _ = _
    rw [hw, read_sstore_allow hs.sound hsA hcA,
      read_moveWorld hs.sound hsA hdA hv256 hbc hfit, ← hpre, hsubw]
    rfl
  · rw [hw, moveWorld, debitWorld]
    exact BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inr ⟨_, hsA, _, hcA, rfl⟩)))
      (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hdA, rfl⟩)))
        (BNB.Spec.FrameKeeps.sstore' (.inr (.inr (.inl ⟨_, hsA, rfl⟩)))
          BNB.Spec.frameKeeps_refl'))
  · rw [hl]
    have hwa : word ((allowAfter m src dst (word v)).toNat - v) =
        allowAfter m src dst (word v) - word v := by
      apply BitVec.eq_of_toNat_eq
      rw [word, BitVec.toNat_ofNat, hsubw]
      exact Nat.mod_eq_of_lt (by have := BitVec.isLt (allowAfter m src dst (word v)); omega)
    simp [M, QEDefi.ERC20.Spec.YAMV2.model, QEDefi.ERC20.Spec.YAMV2.events, Spec.eventLog,
      hall, hwa, push_push_eq]

end Verified.WeirdERC20.YAMV2.Spec
