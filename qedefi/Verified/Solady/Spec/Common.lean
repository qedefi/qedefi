import Verified.Solady.Spec.Abs
import Verified.Solady.Spec.Rows
import Verified.Solady.Spec.AnyGasTactic
import EvmLogic.Tactic.Patched
import EvmLogic.Solidity.Dispatch

/-!
# Solady `ERC20` under the spec: shared tools

Every obligation of `ERC20Spec` is proved by two symbolic runs of the same frame:

* a **high-gas run** (`pwp_steps`, exact gas: with at least `g₀` gas, no value, not static) that
  ends in the code-level postcondition `P`;
* a **low-gas run** (`hwp_steps`, `Verified.Solady.Spec.AnyGas`: any gas, value, static flag)
  that ends in `P` or fails (`LowHalts m P`).

`halts_split` combines them into "`P`, or a failure outside the exact case", the shape of every
obligation. `P` is then turned into the model's postcondition through the abstraction.
-/

namespace Verified.Solady.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open EvmLean.Interpreter EvmLogic.Tactic Verified.Solady.Contracts Verified.Solady.Spec.AnyGas

set_option hygiene false in
/-- Open a fresh frame (`hf : Fresh code m`) for symbolic execution: destructure `m` and
substitute only the frame's start values. -/
macro "solady_fresh_intro" : tactic => `(tactic| (
  obtain ⟨hc, hj, hpc, hs, hmem, -, -⟩ := hf.frame
  clear hf
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  wp_hide_jump_tables
  subst hs hpc hc hmem))

/-- The frame of `m` ends in `P` or fails, for any gas: every postcondition admitting all
failures and `P` holds at its end. -/
def LowHalts (m : Machine) (P : Machine → Outcome → Prop) : Prop :=
  ∀ H : Machine → Outcome → Prop, FailH H → (∀ mf o, P mf o → H mf o) → Halts m H

/-- **Two runs make an obligation**: the high-gas run when `G` holds, the low-gas run
otherwise. -/
theorem halts_split {m : Machine} {P S : Machine → Outcome → Prop} {G : Prop}
    (hi : G → Halts m P) (lo : LowHalts m P) (hPS : ∀ mf o, P mf o → S mf o) :
    Halts m fun mf o => S mf o ∨ (Fails o ∧ ¬ G) := by
  by_cases hG : G
  · exact (hi hG).mono fun mf o _ h => .inl (hPS mf o h)
  · refine lo _ ⟨fun _ _ => .inr ⟨trivial, hG⟩, fun _ _ => .inr ⟨trivial, hG⟩⟩ ?_
    exact fun mf o h => .inl (hPS mf o h)

/-- `halts_split` when turning `P` into the obligation may need the exact case (a revert the
model only predicts from the state before the value moved). -/
theorem halts_split' {m : Machine} {P S : Machine → Outcome → Prop} {G : Prop}
    (hi : G → Halts m P) (lo : LowHalts m P) (hPS : ∀ mf o, P mf o → S mf o ∨ (Fails o ∧ ¬ G)) :
    Halts m fun mf o => S mf o ∨ (Fails o ∧ ¬ G) := by
  by_cases hG : G
  · exact (hi hG).mono fun mf o _ h => hPS mf o h
  · refine lo _ ⟨fun _ _ => .inr ⟨trivial, hG⟩, fun _ _ => .inr ⟨trivial, hG⟩⟩ ?_
    exact fun mf o h => hPS mf o h

theorem lt_size_four' {n : Nat} (h₁ : 4 ≤ n) (h₂ : n < 2 ^ 256) :
    Word.lt (ofNat n) (BitVec.ofNat 256 4) = 0 := by
  rw [Word.lt_eq_zero_iff]; simp only [ofNat, BitVec.toNat_ofNat]; omega

theorem eq_zero_of_iszero_ne {x : Word} (h : Word.iszero x ≠ 0) : x = 0 := by
  by_contra hx
  exact h (iszero_of_ne hx)

end Verified.Solady.Spec
