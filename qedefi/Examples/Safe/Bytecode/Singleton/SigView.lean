import Examples.Safe.Bytecode.Singleton.CopyLoop

/-!
# The singleton: the signature checks as views

`checkSignatures` and `checkNSignatures` (both overloads each) run the loop of
`checkNSignatures` (head pc `6820`) over caller-chosen signatures and threshold. As views they
need nothing about the signatures: every request is static (`ecrecover`, `isValidSignature`),
nothing is written. `sigv_loop` proves the frame judgment for every state of the loop head
and of the copy loop inside `checkContractSignature` (head pc `17648`), by coinduction, for
any memory and world.
-/

namespace Examples.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Examples.Safe.Contracts

namespace Dep

variable (D : Dep) {O T : Finset Address} {thr : Nat} {h₀ : Word} {msg : Message}
  {ctx : Context} {w : World} {m : Machine} {s : Word}

/-- The loop states: the head of `checkNSignatures`'s loop (locals `i, s, r, v, currentOwner,
lastOwner`, arguments fixed), or the head of the copy of a contract signature into the
`isValidSignature` calldata. -/
def SigL (msg : Message) (ctx : Context) (rest : List Word) (req sig dh ex ret : Word)
    (x : Machine) : Prop :=
  (∃ i sv rv vv cur last mem w,
    Fr (fix msg ctx) x 6820 (i :: sv :: rv :: vv :: cur :: last :: req :: sig :: dh :: ex :: ret ::
      rest) mem w) ∨
  (∃ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12 v14 v15 v16 v17 v18 v19 i sv rv vv cur last mem w,
    Fr (fix msg ctx) x 17648 (v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 ::
      371636862#256 :: v12 ::
      10019309979067222254582373821846632475949454479833780424560900009889672200192#256 :: v14 ::
      v15 :: v16 :: v17 :: v18 :: v19 :: 6958#256 :: i :: sv :: rv :: vv :: cur :: last :: req ::
      sig :: dh :: ex :: ret :: rest) mem w)

set_option maxHeartbeats 40000000 in
/-- **The signature loop as a view**: from its states, the frame judgment, given the judgment
where the loop returns (`ret`). -/
theorem sigv_loop {rest : List Word} {req sig dh ex ret : Word}
    (hk : ∀ (mem : Memory) (w' : World) (m' : Machine),
      Fr (fix msg ctx) m' ret.toNat rest mem w' →
      D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m') :
    ∀ x, SigL msg ctx rest req sig dh ex ret x →
      D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork x := by
  refine OwnG.coind _ ?_
  rintro x (⟨i, sv, rv, vv, cur, last, mem, w, hF⟩ |
    ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v12, v14, v15, v16, v17, v18, v19, i, sv, rv,
      vv, cur, last, mem, w, hF⟩)
  · refine OwnB.jumpdestStep hF (by own_code) (Own.sstoreOk_of_ne (b := 0x5b) hF (by own_code)
      (by decide)) fun m hF => ?_
    sg_explore [6820, 17648]
    all_goals first
      | exact .leaf (.inl (.inl ⟨_, _, _, _, _, _, _, _, hF⟩))
      | exact .leaf (.inl (.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, hF⟩))
      | exact .leaf (.inr (hk _ _ _ hF))
      | sg_side
  · refine OwnB.jumpdestStep hF (by own_code) (Own.sstoreOk_of_ne (b := 0x5b) hF (by own_code)
      (by decide)) fun m hF => ?_
    sg_explore [6820, 17648]
    all_goals first
      | exact .leaf (.inl (.inl ⟨_, _, _, _, _, _, _, _, hF⟩))
      | exact .leaf (.inl (.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, hF⟩))
      | sg_side

end Dep

end Examples.Safe.Guard
