import Verified.WeirdERC20.LEND.Spec.Abs
import Verified.WeirdERC20.BNB.Spec.Write
import Verified.WeirdERC20.BNB.Spec.Fallback
import Verified.Solady.Spec.Views
import EvmLogic.Tactic.StepExt

/-!
# LEND under the spec: shared tools

LEND (solc 0.4.16, unoptimised) is proved like BNB and ZRX: each obligation is a high-gas run
(`pwp_steps`) and an any-gas run (`hwp_steps`) combined by `halts_split`. What is particular to
LEND is the sale state in slot 3: the model's invariant (`WF`, the final state) fixes
`currentState = ICOFinished` (byte 0) and `enableTransfers` (byte 1). The frame's world holds
the same storage as the world before its value moved (`sload_launched`), so the code reads the
final state there too (`enabled_word`, `phase_word`).
-/

namespace Verified.WeirdERC20.LEND.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.LEND.Contracts

code_table LEND.runtimeCode

/-- The LEND model. -/
noncomputable abbrev M : TokenModel (LEND.State Address) Address (LEND.Op Address) :=
  QEDefi.ERC20.Spec.LEND.model

/-- **The frame's storage is the snapshot's**: moving the value into the token changes only its
balance (`Start.value`: the value comes from another account and does not wrap). -/
theorem sload_launched {Act : Finset Address} {m : Machine}
    (hs : Start LEND.runtimeCode abs M Act m) (k : Word) :
    m.world.sload m.frame.msg.currentTarget k =
      m.frame.snapshot.1.sload m.frame.msg.currentTarget k := by
  rw [hs.launched]
  rcases hs.value with hv | ⟨htv, hne, hlt⟩
  · rw [transferValue_zero _ _ hv]
  · by_cases hv : m.frame.msg.value = 0
    · rw [transferValue_zero _ _ hv]
    · simp only [transferValue, htv, hv, ne_eq, not_false_eq_true, Bool.true_and,
        decide_true, ↓reduceIte]
      refine BNB.Spec.bnb_moveEther_dst_storage hne ?_ k
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hlt] at this
      exact hv (BitVec.eq_of_toNat_eq (by simp at this ⊢; omega))

/-- The model state at the start of the frame is read from the frame's world. -/
theorem pre_eq {Act : Finset Address} {m : Machine} (hs : Start LEND.runtimeCode abs M Act m) :
    pre abs Act m = read m.ctx.crypto Act m.world m.frame.msg.currentTarget := by
  have h := sload_launched hs
  show read _ _ _ _ = read _ _ _ _
  simp only [read, readSlot, h]
  rw [readMap_congr (fun k _ => h k), readMap2_congr (fun k _ => h k)]

/-- The final state, read from slot 3: `currentState = 5` (byte 0), `enableTransfers` (byte 1). -/
theorem wf_slot3 {Act : Finset Address} {m : Machine} (hs : Start LEND.runtimeCode abs M Act m) :
    (m.world.sload m.frame.msg.currentTarget stateSlot).toNat % 256 = 5 ∧
      (m.world.sload m.frame.msg.currentTarget stateSlot >>> 8).toNat % 256 ≠ 0 := by
  have hw := hs.wf
  rw [pre_eq hs] at hw
  obtain ⟨h1, h2⟩ := hw
  simp only [read, decide_eq_true_eq] at h1 h2
  exact ⟨h1, h2⟩

/-! ## Branch conditions -/

theorem eq0_of_ne {x : Word} (h : Word.eq x 0#256 ≠ 0) : x = 0 := by
  by_contra hx; exact h (by simp [Word.eq, Word.ofBool]; exact hx)

theorem ne0_of_eq {x : Word} (h : Word.eq x 0#256 = 0) : x ≠ 0 := by
  rintro rfl; exact absurd h (by decide)

theorem eq0_of_ii {x : Word} (h : (Word.eq x 0#256).iszero.iszero ≠ 0) : x = 0 := by
  by_contra hx; exact h (by simp [Word.eq, Word.ofBool, Word.iszero]; exact hx)

theorem ne0_of_ii {x : Word} (h : (Word.eq x 0#256).iszero.iszero = 0) : x ≠ 0 := by
  rintro rfl; exact absurd h (by decide)

theorem eq0_one {x : Word} (h : x = 0) : Word.eq x 0#256 = 1 := by subst h; decide

theorem eq0_zero {x : Word} (h : x ≠ 0) : Word.eq x 0#256 = 0 := by
  simp [Word.eq, Word.ofBool]; exact h

/-- `enableTransfers` as the code reads it (`slot3 / 256 & 0xff`) is set. -/
theorem en_iszero {x : Word} (h : (x >>> 8).toNat % 256 ≠ 0) :
    Word.iszero (255#256 &&& Word.div x 256#256) = 0 := by
  apply iszero_of_ne
  intro h0
  apply h
  have := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_and, Word.div, BitVec.toNat_udiv, BitVec.toNat_ofNat,
    BitVec.toNat_ushiftRight] at this ⊢
  rw [Nat.shiftRight_eq_div_pow]
  rw [show (255 : Nat) % 2 ^ 256 = 2 ^ 8 - 1 by decide, show (256 : Nat) % 2 ^ 256 = 2 ^ 8 by decide,
    Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this

/-- With the frame's world in the final state, `enableTransfers` reads set. -/
theorem enabled_word {Act : Finset Address} {m : Machine} (hs : Start LEND.runtimeCode abs M Act m) :
    Word.iszero (255#256 &&& Word.div (m.world.sload m.frame.msg.currentTarget 3#256) 256#256) = 0 :=
  en_iszero (wf_slot3 hs).2

theorem iszero3_ne {x : Word} (h : x.iszero.iszero.iszero ≠ 0) : x.iszero ≠ 0 := by
  intro h0; exact h (by rw [h0]; decide)

theorem iszero23' {x : Word} (h1 : x.iszero.iszero ≠ 0) (h2 : x.iszero.iszero.iszero ≠ 0) :
    False := by
  have := iszero3_ne h2
  by_cases hx : x = 0
  · subst hx; exact h1 (by decide)
  · exact this (by simp [Word.iszero, Word.ofBool]; exact hx)

/-- `require(balances[to] + v > balances[to])` held: `v ≠ 0` and no wrap. -/
theorem add_gt_of {S v : Word} (h : ((S + v).gt S).iszero.iszero ≠ 0) :
    0 < v.toNat ∧ S.toNat + v.toNat < 2 ^ 256 := by
  have hg : (S + v).gt S ≠ 0 := by
    intro h0; rw [h0] at h; exact h (by decide)
  have hu : BitVec.ult S (S + v) = true := by
    by_contra hu; simp only [Bool.not_eq_true] at hu
    exact hg (by simp [Word.gt, Word.ofBool, hu])
  simp only [BitVec.ult, BitVec.toNat_add, decide_eq_true_eq] at hu
  have := S.isLt; have := v.isLt
  by_cases ho : S.toNat + v.toNat < 2 ^ 256
  · rw [Nat.mod_eq_of_lt ho] at hu; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hu; omega

theorem add_gt_one {S v : Word} (h0 : 0 < v.toNat) (h : S.toNat + v.toNat < 2 ^ 256) :
    (S + v).gt S = 1 := by
  rw [Word.gt_eq_one_iff, BitVec.toNat_add, Nat.mod_eq_of_lt h]; omega

theorem add_gt_zero {S v : Word} (h : v.toNat = 0 ∨ 2 ^ 256 ≤ S.toNat + v.toNat) :
    (S + v).gt S = 0 := by
  have hu : BitVec.ult S (S + v) = false := by
    simp only [BitVec.ult, BitVec.toNat_add, decide_eq_false_iff_not, not_lt]
    have := S.isLt; have := v.isLt
    rcases h with h | h
    · rw [h, Nat.add_zero, Nat.mod_eq_of_lt S.isLt]
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
  simp [Word.gt, Word.ofBool, hu]

end Verified.WeirdERC20.LEND.Spec
