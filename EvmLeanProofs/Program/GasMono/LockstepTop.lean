import EvmLeanProofs.Program.GasMono.Lockstep

/-!
# Gas monotonicity: frame summaries for any gas

The form the nested-call simulation consumes (`FrameOk` in `specs/…/NestedSystem.lean` is
`Halts m (fun mf o => ∀ out, o = .success out → P mf.world)` for a property `P` of the world):

**`halts_world_of_mono`**: let `S` be gas-monotone (`MonoFrom S`) and `ml` a frame of a message
call with any gas `g`. For any `G ≥ g`, consider the same frame with gas `G` at the top level
(`topBump G ml`: frame gas and message gas `G`, no parents). If that frame satisfies `S` and
its summary says that every successful end has a world satisfying `P`, then so does every
successful end of `ml` — and `ml` does end (its failures roll back to its snapshot by
`frameResult`, which needs no summary).

The high frame is taken at the top level on purpose: there the end of a frame is
determined by its `Halts` witness (a finished message is absorbing, `exit_of_halts_top`), while
a nested `Halts` witness may describe a later point at which the parent happens to look like a
resumption.
-/

namespace EvmLean.Program.GasMono

open Interpreter Nested

/-- The frame of `m` with gas `G` (frame and message), at the top level. -/
def topBump (G : Nat) (m : Machine) : Machine := bump (G - m.frame.gasLeft) G [] m

/-- Nothing is gas-monotone vacuously: the callee condition of a frame that only calls
precompiles. -/
theorem monoFrom_false : MonoFrom (fun _ => False) := fun _ _ _ _ _ h => h.elim

/-- The top-level bump is related to the frame. -/
theorem bumpOf_topBump (G : Nat) (m : Machine) :
    BumpOf (topBump G m).frame.msg.gas (topBump G m).parents m (topBump G m) :=
  bumpOf_bump _ _ _ _

/-- The top-level results of a successful end of a message call. -/
theorem topLevelResult_frameResult_success {target : Option Address} {mf mf' : Machine}
    {out : ByteArray} {o' : Outcome} {ko ks : Nat} (hk : mf.frame.kind = .call ko ks)
    (hk' : mf'.frame.kind = .call ko ks)
    (h : topLevelResult target (frameResult mf' o').2.1 (frameResult mf' o').2.2
        (frameResult mf' o').1 =
      topLevelResult target (frameResult mf (.success out)).2.1
        (frameResult mf (.success out)).2.2 (frameResult mf (.success out)).1) :
    ∃ out', o' = .success out' ∧ mf'.world = mf.world := by
  rw [frameResult_success_call hk] at h
  cases o' with
  | success out' =>
    rw [frameResult_success_call hk'] at h
    refine ⟨out', rfl, ?_⟩
    have := congrArg MessageResult.world h
    simpa [topLevelResult, ChildResult.success] using this
  | revert out' =>
    have := congrArg MessageResult.reverted h
    simp [topLevelResult, ChildResult.success, frameResult_revert] at this
  | halt e =>
    have := congrArg MessageResult.error h
    simp [topLevelResult, ChildResult.success, frameResult_halt] at this

/-- **A frame summary transfers to any lower gas.** -/
theorem halts_world_of_mono {S : Machine → Prop} (hmono : MonoFrom S) {ml : Machine} {G : Nat}
    {ko ks : Nat} (hk : ml.frame.kind = .call ko ks) (hS : S (topBump G ml))
    {P : World → Prop}
    (h : Halts (topBump G ml) (fun mf o => ∀ out, o = .success out → P mf.world)) :
    Halts ml (fun mf o => ∀ out, o = .success out → P mf.world) := by
  obtain ⟨N, mfh, oh, hex, mf', o', hH, hs', hfin⟩ := exit_of_halts_top rfl h
  have hlow := hmono ml (topBump G ml) N mfh oh hS (bumpOf_topBump G ml) hex
  refine hlow.mono fun mfl ol _ hpost out hol => ?_
  rcases hpost with hf | ⟨rfl, dd, xx, pp, hmf⟩
  · exact absurd hol (hf out)
  · subst hol
    have hfh := hex.finish
    have hph : mfh.parents = [] := hfh.2.parents
    have hp' : mf'.parents = [] := hs'.parents
    have hkh : mfh.frame.kind = .call ko ks := hfh.2.kind.trans hk
    have hk' : mf'.frame.kind = .call ko ks := hs'.kind.trans hk
    rw [finishFrame_of_top _ hp', finishFrame_of_top _ hph, hs'.msg, hfh.2.msg] at hfin
    injection hfin with hfin
    obtain ⟨out', ho', hw⟩ := topLevelResult_frameResult_success hkh hk' hfin
    have := hH out' ho'
    rw [hw, hmf] at this
    exact this

end EvmLean.Program.GasMono
