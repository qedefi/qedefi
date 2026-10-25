import EvmLogic.Tactic.Patched

/-!
# Jump destinations of init code followed by arbitrary arguments

The init code of a creation is the creation code followed by ABI-encoded constructor
arguments. When an argument is symbolic (an address), the `JUMPDEST` scan of the whole code
depends on it: an argument byte `0x5b` is a `JUMPDEST`, a byte `0x60…0x7f` skips what follows.
The scan of the creation code itself does not: `jumpDestList_append` says the destinations of
`l ++ r` are those of `l`, then positions at or past the end of `l`. So every destination of
the creation code is valid in the init code, whatever the arguments
(`mem_jumpDestList_append_left`).

`pjumpdest_disch` is extended to use a hypothesis
`∀ d, d ∈ jumpDestList (base.size + 1) base.data.toList 0 → d < B → isValidJumpDest jd d = true`
(`base` a literal code with a table), for code whose jump table no `JumpDestsAgree` describes.
-/

namespace EvmLogic.Solidity
open EvmLean EvmLean.Interpreter

theorem le_of_mem_jumpDestList : ∀ (f : Nat) (l : List UInt8) (pos d : Nat),
    d ∈ jumpDestList f l pos → pos ≤ d
  | 0, _, _, _, h => by simp [jumpDestList] at h
  | _ + 1, [], _, _, h => by simp [jumpDestList] at h
  | f + 1, b :: bs, pos, d, h => by
    simp only [jumpDestList] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_refl _
      · have := le_of_mem_jumpDestList f bs (pos + 1) d h; omega
    · split at h
      · have := le_of_mem_jumpDestList f _ _ d h; omega
      · have := le_of_mem_jumpDestList f bs (pos + 1) d h; omega

/-- The scan of `l ++ r`: the destinations of `l`, then positions at or past the end of `l`. -/
theorem jumpDestList_append : ∀ (f : Nat) (l r : List UInt8) (pos : Nat),
    ∃ Y, jumpDestList f (l ++ r) pos = jumpDestList f l pos ++ Y ∧ ∀ y ∈ Y, pos + l.length ≤ y
  | 0, _, _, _ => ⟨[], by simp [jumpDestList]⟩
  | f + 1, [], r, pos => ⟨jumpDestList (f + 1) r pos, by simp [jumpDestList],
      fun y hy => by have := le_of_mem_jumpDestList _ _ _ _ hy; simpa using this⟩
  | f + 1, b :: bs, r, pos => by
    simp only [List.cons_append, jumpDestList]
    split
    · obtain ⟨Y, h1, h2⟩ := jumpDestList_append f bs r (pos + 1)
      refine ⟨Y, by rw [h1, List.cons_append], fun y hy => ?_⟩
      have := h2 y hy; simp only [List.length_cons]; omega
    · split
      · by_cases hk : b.toNat - 0x5f ≤ bs.length
        · obtain ⟨Y, h1, h2⟩ := jumpDestList_append f (bs.drop (b.toNat - 0x5f)) r
            (pos + 1 + (b.toNat - 0x5f))
          rw [List.drop_append_of_le_length hk]
          refine ⟨Y, h1, fun y hy => ?_⟩
          have := h2 y hy; simp only [List.length_drop, List.length_cons] at this ⊢; omega
        · have hd : bs.drop (b.toNat - 0x5f) = [] := List.drop_eq_nil_of_le (by omega)
          refine ⟨jumpDestList f ((bs ++ r).drop (b.toNat - 0x5f)) (pos + 1 + (b.toNat - 0x5f)),
            ?_, fun y hy => ?_⟩
          · rw [hd]; cases f <;> simp [jumpDestList]
          · have := le_of_mem_jumpDestList _ _ _ _ hy; simp only [List.length_cons]; omega
      · obtain ⟨Y, h1, h2⟩ := jumpDestList_append f bs r (pos + 1)
        refine ⟨Y, h1, fun y hy => ?_⟩
        have := h2 y hy; simp only [List.length_cons]; omega

/-- A destination of `c ++ a` before the end of `c` is a destination of `c ++ a'`. -/
theorem mem_jumpDestList_append_left {f : Nat} {c a a' : List UInt8} {d : Nat}
    (h : d ∈ jumpDestList f (c ++ a) 0) (hd : d < c.length) : d ∈ jumpDestList f (c ++ a') 0 := by
  obtain ⟨Y, h1, h2⟩ := jumpDestList_append f c a 0
  obtain ⟨Y', h1', -⟩ := jumpDestList_append f c a' 0
  rw [h1] at h
  rw [h1']
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ h
  · have := h2 d h; omega

end EvmLogic.Solidity

namespace EvmLogic.Program
open EvmLean Lean Elab Tactic Meta EvmLean.Interpreter

/-- `pjumpdest_disch` for a jump table described by a hypothesis
`∀ d, d ∈ jumpDestList (base.size + 1) base.data.toList 0 → d < B → isValidJumpDest jd d = true`. -/
elab_rules : tactic
  | `(tactic| pjumpdest_disch) => withMainContext do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let_expr Eq _ lhs _ := t | throwError "pjumpdest_disch: not an equation"
    let_expr isValidJumpDest jd d := lhs | throwError "pjumpdest_disch: not a jump destination"
    let jd ← whnfR jd
    let some _ ← (evalNat (← whnfD d)).run | throwError "pjumpdest_disch: symbolic destination"
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      let .forallE _ _ body _ := ty | continue
      let .forallE _ memTy body2 _ := body | continue
      let .forallE _ _ concl _ := body2 | continue
      let_expr Eq _ clhs _ := concl | continue
      let_expr isValidJumpDest jd' _ := clhs | continue
      unless jd'.hasLooseBVars || (← isDefEq jd' jd) do continue
      let_expr Membership.mem _ _ _ coll _ := memTy | continue
      let_expr Solidity.jumpDestList _ lst _ := coll | continue
      let_expr Array.toList _ arr := lst | continue
      let_expr ByteArray.data base := arr | continue
      let some hmem ← jumpDestMem? base d | continue
      let hlt ← mkDecideProof (← mkAppM ``LT.lt #[d, ← do
        let .forallE _ ltTy _ _ := body2 | throwError "unreachable"
        let_expr LT.lt _ _ _ b := ltTy | throwError "pjumpdest_disch: not a bound"
        pure (b.instantiate1 d)])
      let pf := mkAppN decl.toExpr #[d, hmem, hlt]
      if ← isDefEq (← inferType pf) t then
        g.assign pf
        replaceMainGoal []
        return
    throwError "pjumpdest_disch: no jump-destination hypothesis"

end EvmLogic.Program
