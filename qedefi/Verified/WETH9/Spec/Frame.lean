import Verified.WETH9.Spec.Abs
import Verified.WETH9.Spec.ViewsLow

/-!
# From `LowOK` judgements to the spec's frame statements

`halts_of_low`: a fresh WETH9 frame `m` ends satisfying `P` if, for the gas `g` it has when it has
at least `g₀` (and for `g₀` otherwise), the frame with gas `g` is `LowOK P`, `P` ignores the gas
and parents of the final machine, and every failure satisfies `P` below `g₀`. The frame's own
gas is then either exactly `g` (no failure allowed beyond what `P` admits) or lower, where any
failure is fine.
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.GasMono Verified.WETH9.Contracts

/-- **A fresh WETH9 frame, from its `LowOK` judgements.** -/
theorem halts_of_low {P : Machine → Outcome → Prop} {m : Machine} {g₀ : Nat}
    (hf : Fresh WETH9.runtimeCode m)
    (hfail : ¬ g₀ ≤ m.frame.gasLeft → ∀ mf o, Failed o → P mf o)
    (hbump : ∀ d x ps mf o, P (bump d x ps mf) o → P mf o)
    (h : ∀ g, g₀ ≤ g →
      LowOK P (wethM m.ctx m.precompiles m.world m.transient m.originalWorld m.createdAccounts
        m.frame.msg m.frame.sub m.frame.snapshot m.frame.kind m.parents g)) :
    Halts m P := by
  obtain ⟨msg, k, snap, hfr, hc⟩ := hf
  have key : ∀ d, bump d m.frame.msg.gas m.parents m =
      wethM m.ctx m.precompiles m.world m.transient m.originalWorld m.createdAccounts
        m.frame.msg m.frame.sub m.frame.snapshot m.frame.kind m.parents (m.frame.gasLeft + d) := by
    intro d
    obtain ⟨c, p, w, t, ow, cr, f, par⟩ := m
    simp only at hfr
    subst hfr
    cases msg
    simp only at hc
    subst hc
    simp only [bump, wethM, Frame.init]
  by_cases hg : g₀ ≤ m.frame.gasLeft
  · refine (h _ (by omega) m 0 m.frame.msg.gas m.parents (key 0)).mono fun mf o _ hp => ?_
    rcases hp with ⟨h0, -⟩ | hp
    · omega
    · exact hbump _ _ _ _ _ hp
  · refine (h _ (by omega) m g₀ m.frame.msg.gas m.parents (key g₀)).mono fun mf o _ hp => ?_
    rcases hp with ⟨-, hfo⟩ | hp
    · exact hfail hg mf o hfo
    · exact hbump _ _ _ _ _ hp

/-- A failed outcome is a failure of the spec. -/
theorem fails_of_failed {o : Outcome} (h : Failed o) : QEDefi.ERC20.Spec.Fails o := by
  cases o with
  | success out => exact absurd rfl (h out)
  | revert _ => trivial
  | halt _ => trivial

end Verified.WETH9.Spec
