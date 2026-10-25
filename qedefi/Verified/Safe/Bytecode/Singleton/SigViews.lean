import Verified.Safe.Bytecode.Singleton.SigView

/-!
# The singleton: `checkSignatures`, `checkNSignatures` (views)

Each overload explores to the loop of `checkNSignatures` and concludes with `sigv_loop`.
-/

namespace Verified.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Verified.Safe.Contracts

namespace Dep

variable (D : Dep) {O T : Finset Address} {thr : Nat} {h₀ : Word} {msg : Message}
  {ctx : Context} {w : World} {m : Machine} {s : Word}

set_option maxHeartbeats 40000000 in
theorem sg_checkNSignatures_a (hF : Fr (fix msg ctx) m 1061 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore [6820]
  all_goals
    refine .leaf (D.sigv_loop ?_ _ (.inl ⟨_, _, _, _, _, _, _, _, hF⟩))
  all_goals
    intro mem w' m hF
    simp only [BitVec.reduceToNat] at hF
    sg_explore

set_option maxHeartbeats 40000000 in
theorem sg_checkNSignatures_b (hF : Fr (fix msg ctx) m 756 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore [6820]
  all_goals
    refine .leaf (D.sigv_loop ?_ _ (.inl ⟨_, _, _, _, _, _, _, _, hF⟩))
  all_goals
    intro mem w' m hF
    simp only [BitVec.reduceToNat] at hF
    sg_explore

set_option maxHeartbeats 40000000 in
theorem sg_checkSignatures_a (hF : Fr (fix msg ctx) m 5356 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore [6820]
  all_goals
    refine .leaf (D.sigv_loop ?_ _ (.inl ⟨_, _, _, _, _, _, _, _, hF⟩))
  all_goals
    intro mem w' m hF
    simp only [BitVec.reduceToNat] at hF
    sg_explore

set_option maxHeartbeats 40000000 in
theorem sg_checkSignatures_b (hF : Fr (fix msg ctx) m 3145 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore [6820]
  all_goals
    refine .leaf (D.sigv_loop ?_ _ (.inl ⟨_, _, _, _, _, _, _, _, hF⟩))
  all_goals
    intro mem w' m hF
    simp only [BitVec.reduceToNat] at hF
    sg_explore

end Dep

end Verified.Safe.Guard
