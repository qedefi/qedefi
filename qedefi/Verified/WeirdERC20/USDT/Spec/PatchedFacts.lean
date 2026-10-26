import Verified.WeirdERC20.USDT.Spec.Patched
import Verified.WeirdERC20.USDT.Spec.LowGas

/-!
# `patchedCode` is `USDT.runtimeCode` without its calls

`patchOk : PatchOk USDT.runtimeCode patchedCode patchPcs`, checked by the kernel on single
passes over the two byte lists: the codes differ exactly at `patchPcs` (`sameExcept`), where
the patched code holds `INVALID` and the real code `GAS`/`CALL`; and no instruction of the
patched code reads the gas or the code, nor has a patched byte in its immediate (`insns`).
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLean.Interpreter EvmLogic.GasMono Verified.WeirdERC20.USDT.Contracts

/-- The two byte lists agree except at the positions `R` (counted from `i`). -/
def sameExcept (R : List Nat) : List UInt8 → List UInt8 → Nat → Bool
  | [], [], _ => true
  | a :: as, b :: bs, i => (R.contains i || a == b) && sameExcept R as bs (i + 1)
  | _, _, _ => false

theorem sameExcept_getD {R : List Nat} :
    ∀ {l₁ l₂ : List UInt8} {k : Nat}, sameExcept R l₁ l₂ k = true →
      ∀ i, i + k ∉ R → (l₁[i]?).getD 0 = (l₂[i]?).getD 0 := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ k h i _
    cases l₂ with
    | nil => rfl
    | cons b bs => simp [sameExcept] at h
  | cons a as ih =>
    intro l₂ k h i hi
    cases l₂ with
    | nil => simp [sameExcept] at h
    | cons b bs =>
      simp only [sameExcept, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      cases i with
      | zero =>
        rcases h.1 with h1 | h1
        · exact absurd (List.contains_iff_mem.1 h1) (by simpa using hi)
        · simp [h1]
      | succ i =>
        simp only [List.getElem?_cons_succ]
        exact ih h.2 i (by rwa [show i + (k + 1) = i + 1 + k by omega])

theorem patchedCode_size : patchedCode.size = USDT.runtimeCode.size := by decide +kernel

theorem patchedCode_sameExcept :
    sameExcept patchPcs patchedCode.data.toList USDT.runtimeCode.data.toList 0 = true := by
  decide +kernel

theorem patchedCode_inv :
    patchPcs.all (fun r => Bytes.getD patchedCode r == 0xfe) = true := by decide +kernel

theorem runtimeCode_orig :
    patchPcs.all (fun r =>
      Bytes.getD USDT.runtimeCode r == 0x5a || Bytes.getD USDT.runtimeCode r == 0xf1) = true := by decide +kernel

/-- Each instruction of the patched code reads neither the gas nor the code, and no patched
byte lies in its immediate. -/
def insnOk (R : List Nat) (x : Nat × UInt8 × UInt8) : Bool :=
  goodByte x.2.1 && R.all fun r => !(Nat.blt x.1 r) || Nat.blt (x.1 + immSize x.2.1) r

theorem patchedCode_insns : (insns patchedCode).all (insnOk patchPcs) = true := by
  decide +kernel

/-- **The patched code is USDT without its calls.** -/
theorem patchOk : PatchOk USDT.runtimeCode patchedCode patchPcs where
  size := patchedCode_size
  same i hi := by
    rw [getD_eq_toList, getD_eq_toList]
    exact sameExcept_getD patchedCode_sameExcept i (by simpa using hi)
  inv r hr := by
    have := List.all_eq_true.1 patchedCode_inv r hr
    simpa using this
  orig r hr := by
    have := List.all_eq_true.1 runtimeCode_orig r hr
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with h | h <;> rw [h] <;> decide
  good q hq := by
    have := List.all_eq_true.1 patchedCode_insns (insnInfo patchedCode q)
      (by rw [insns_eq]; exact List.mem_map_of_mem hq)
    simp only [insnOk, insnInfo, Bool.and_eq_true] at this
    exact this.1
  imm q hq r hr hlt := by
    have := List.all_eq_true.1 patchedCode_insns (insnInfo patchedCode q)
      (by rw [insns_eq]; exact List.mem_map_of_mem hq)
    simp only [insnOk, insnInfo, Bool.and_eq_true, List.all_eq_true] at this
    have := this.2 r hr
    simp only [Bool.or_eq_true] at this
    rcases this with h | h
    · rw [Bool.not_eq_true', ← Bool.not_eq_true, Nat.blt_eq] at h; omega
    · rwa [Nat.blt_eq] at h

end Verified.WeirdERC20.USDT.Spec
