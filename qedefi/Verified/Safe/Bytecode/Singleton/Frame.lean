import Verified.Safe.Bytecode.Singleton.Simple
import Verified.Safe.Bytecode.Singleton.Revert
import Verified.Safe.Bytecode.Singleton.Lists
import Verified.Safe.Bytecode.Singleton.SigViews

/-!
# A singleton frame at the Safe, from its start

The dispatcher (pc `0` to each function's entry), then each function's theorem. `sg_frame`
takes the theorem for `execTransaction` as an argument (`SgExec`), proved in `Exec.lean`.
-/

namespace Verified.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Verified.Safe.Contracts

namespace Dep

variable (D : Dep) {O T : Finset Address} {thr : Nat} {h₀ : Word} {msg : Message}
  {ctx : Context} {w : World} {m : Machine}

/-- The frame judgment from `execTransaction`'s entry (pc `2590`). -/
def SgExec (O T : Finset Address) (thr : Nat) (h₀ : Word) (msg : Message) (ctx : Context) : Prop :=
  ∀ (w : World) (m : Machine) (s : Word), Fr (fix msg ctx) m 2590 [s] mem0 w →
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m

set_option maxHeartbeats 40000000 in
/-- **A singleton frame at the Safe**: from its start, the frame judgment `Jsg`. -/
theorem sg_frame (hC : D.SgCtx O T thr h₀ msg ctx) (hx : D.SgExec O T thr h₀ msg ctx)
    (hF : Fr (fix msg ctx) m 0 [] {} w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore [5313, 5356, 5598, 5721, 4963, 5044, 5189, 5232, 4396, 4455, 4769, 4882, 3548, 3591,
    3823, 4191, 2590, 3034, 3145, 3440, 2181, 2371, 2450, 2531, 1313, 1416, 1519, 1796, 665, 756,
    1061, 476, 561]
  all_goals refine .leaf ?_
  all_goals first
    | exact D.sg_fallback hC hF
    | exact D.sg_receive hC hF
    | exact D.sg_nonce hF
    | exact D.sg_domainSeparator hF
    | exact D.sg_getThreshold hF
    | exact D.sg_approvedHashes hF
    | exact D.sg_signedMessages hF
    | exact D.sg_isOwner hF
    | exact D.sg_isModuleEnabled hF
    | exact D.sg_getTransactionHash hF
    | exact D.sg_approveHash hF
    | exact D.sg_addOwnerWithThreshold hC hF
    | exact D.sg_removeOwner hC hF
    | exact D.sg_swapOwner hC hF
    | exact D.sg_changeThreshold hC hF
    | exact D.sg_enableModule hC hF
    | exact D.sg_disableModule hC hF
    | exact D.sg_setGuard hC hF
    | exact D.sg_setModuleGuard hC hF
    | exact D.sg_setFallbackHandler hC hF
    | exact D.sg_simulateAndRevert hF
    | exact D.sg_execTransactionFromModule hC hF
    | exact D.sg_execTransactionFromModuleReturnData hC hF
    | exact D.sg_setup hC hF
    | exact D.sg_VERSION hF
    | exact D.sg_getStorageAt hF
    | exact D.sg_getOwners hF
    | exact D.sg_getModulesPaginated hF
    | exact D.sg_checkNSignatures_a hF
    | exact D.sg_checkNSignatures_b hF
    | exact D.sg_checkSignatures_a hF
    | exact D.sg_checkSignatures_b hF
    | exact hx _ _ _ hF

end Dep

end Verified.Safe.Guard
