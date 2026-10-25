import EvmLogic.AbsInt.Code
import EvmLogic.Program.Delegation

/-!
# Code properties of every world of a message call, EIP-7702 authorizations included

`reaches_allWorlds` assumes `ctx.fork < .prague ∨ ctx.tx.authorizations = []`. Without it, the
authorizations run first and install designators (or empty code) at accounts holding empty code
or a designator. `reaches_allWorlds_7702` lifts a `CodeProp` that such an installation keeps.
(`noDesignator` is not one: an authorization creates a designator.)
-/

namespace EvmLogic.AbsInt
open EvmLean EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested

variable {P : World → Prop}

/-- **Every machine a top-level message call of any transaction reaches keeps `AllWorlds`**,
for a code property kept by what an authorization installs (`hdel`): `reaches_allWorlds`
without `ctx.fork < .prague ∨ ctx.tx.authorizations = []`. -/
theorem reaches_allWorlds_7702 (hP : CodeProp P)
    (hdel : ∀ w a c, P w → Delegable (w.code a) → DelegCode c → P (setCode w a c))
    {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message} (hw : P w)
    {m : Machine} (hm : Reaches ctx w tr msg m) : AllWorlds P m := by
  have hw' : P (applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg).1 :=
    applyTopLevelDelegation_induct ctx _ msg P
      (fun w a c h ha hc => hP.congr (code_incrementNonce _ _) (hdel w a c h ha hc)) hw
  obtain ⟨m₀, n, hs, hn⟩ := hm
  refine stepN_allWorlds hP n ?_ hn
  unfold StartsAt at hs
  generalize applyTopLevelDelegation ctx (PrecompileImpl.standard ctx).isPrecompile w msg = d
    at hw' hs
  obtain ⟨w', msg', refund⟩ := d
  dsimp only at hw' hs
  unfold initMachine at hs
  dsimp only at hs
  split at hs
  · cases hs
  split at hs
  · cases hs
  split at hs
  · split at hs
    · cases hs
    · cases hs
      refine ⟨hP.congr ((code_incrementNonce _ _).trans (code_transferValue _ _)) hw', ?_⟩
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; exact hw'
  · split at hs
    · cases hs
    · cases hs
      refine ⟨hP.congr (code_transferValue _ _) hw', ?_⟩
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; exact hw'

end EvmLogic.AbsInt
