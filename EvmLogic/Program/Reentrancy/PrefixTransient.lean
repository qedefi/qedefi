import EvmLogic.Program.Reentrancy.Prefix
import EvmLogic.Step.Transient

/-!
# Prefix rules for transient storage (`TLOAD`, `TSTORE`)

The any-gas prefix calculus of `EvmLogic.Program.Reentrancy.Prefix` for EIP-1153: each rule takes
the instruction when gas, stack and staticness allow, and otherwise absorbs the failure (out of
gas, stack overflow, `TSTORE` in a static frame), which is fine from a `Good` snapshot. `TSTORE`
changes only transient storage, never the world, so it needs no side condition on `Good`; this is
what OpenZeppelin's `ReentrancyGuardTransient` and Uniswap V4's locks execute before a call.
-/

namespace EvmLogic.Program.Reentrancy
open EvmLean EvmLean.Interpreter EvmLogic.Program

variable {Good : World → Prop} {Q : Machine → Prop} {m : Machine}

/-- `TLOAD` (prefix rule). -/
theorem pwp_tload {x : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x5c)
    (hstk : m.frame.stack = x :: rest)
    (hrec : rest.length < 1024 → 100 ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := getTransient m.transient m.frame.msg.currentTarget x :: rest,
        gasLeft := m.frame.gasLeft - 100,
        pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  by_cases hg : 100 ≤ m.frame.gasLeft
  · by_cases hl : rest.length < 1024
    · exact WP.of_step (step_tload hcode hstk hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hl hg)
    · have hl' : Gas.stackLimit ≤ rest.length := Nat.le_of_not_lt hl
      have hg' : ¬ m.frame.gasLeft < Gas.warmAccess := Nat.not_lt.mpr hg
      refine wp_fail_of_error (e := .stackOverflow) hsnap hcode ?_
      rw [decode_tload]
      simp only [exec, pop, push, charge, advance, getFrame, modifyFrame, StateT.run_bind, hstk,
        StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, hg', hl', ite_true,
        ite_false]
      rfl
  · exact WP.halt_of_step (step_tload_oog hcode hstk (Nat.lt_of_not_le hg)) (.refl m)
      (by show Good (frameResult m (.halt _)).2.1; rw [frameResult_halt]; exact hsnap)

/-- `TSTORE` (prefix rule): in a static frame it halts, which `FailOk` absorbs. -/
theorem pwp_tstore {x y : Word} {rest : List Word}
    (hsnap : Good m.frame.snapshot.1) (hcode : m.frame.code[m.frame.pc]? = some 0x5d)
    (hstk : m.frame.stack = x :: y :: rest)
    (hrec : m.frame.msg.isStatic = false → 100 ≤ m.frame.gasLeft →
      WP { m with
        transient := setTransient m.transient m.frame.msg.currentTarget x y
        frame := { m.frame with
          stack := rest,
          gasLeft := m.frame.gasLeft - 100,
          pc := m.frame.pc + 1 } } Q (FailOk Good)) :
    WP m Q (FailOk Good) := by
  have hfail : ∀ {e : ExceptionalHalt}, step m = finishFrame m (.halt e) →
      WP m Q (FailOk Good) := fun h => WP.halt_of_step h (.refl m)
    (by show Good (frameResult m (.halt _)).2.1; rw [frameResult_halt]; exact hsnap)
  by_cases hg : 100 ≤ m.frame.gasLeft
  · cases hs : m.frame.msg.isStatic
    · exact WP.of_step (step_tstore hcode hstk hs hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec hs hg)
    · exact hfail (step_tstore_static hcode hstk hs hg)
  · exact hfail (step_tstore_oog hcode hstk (Nat.lt_of_not_le hg))

end EvmLogic.Program.Reentrancy
