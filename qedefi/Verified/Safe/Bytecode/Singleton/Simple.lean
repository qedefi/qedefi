import Verified.Safe.Bytecode.Singleton.Ctx

/-!
# The singleton: `receive`, the fallback, getters, `approveHash`, `authorized` functions

Each theorem starts at a function's entry (after the dispatcher, with the selector on the stack
and the free memory pointer at `0x80`) and proves the frame judgment `Jsg`.
-/

namespace Verified.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Verified.Safe.Contracts

namespace Dep

variable (D : Dep) {O T : Finset Address} {thr : Nat} {h₀ : Word} {msg : Message}
  {ctx : Context} {w : World} {m : Machine} {s : Word}

set_option maxHeartbeats 4000000 in
/-- **The fallback** (pc `561`): no handler, a successful empty return; otherwise a `CALL` of
the handler, which is not a relay. -/
theorem sg_fallback {st : List Word} (hC : D.SgCtx O T thr h₀ msg ctx)
    (hF : Fr (fix msg ctx) m 561 st mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore
  case call647 =>
    rintro ⟨hG, -⟩ - req ⟨-, ht, -⟩
    refine .inr (.inl ⟨rfl, .inr (.inl ?_)⟩)
    have hh : w.sload D.sf handlerSlot = h₀ := by rw [← hF.world]; exact hG.2.2.handler
    rw [hC.target, ← handlerSlot_eq, hh] at hc613 ht
    rw [ht]
    exact hC.handler.resolve_left hc613
  case doom647 => sg_nodoom

set_option maxHeartbeats 4000000 in
/-- **`receive`** (pc `476`): the `SafeReceived` event, or the fallback. -/
theorem sg_receive {st : List Word} (hC : D.SgCtx O T thr h₀ msg ctx)
    (hF : Fr (fix msg ctx) m 476 st mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore [561]
  exact .leaf (D.sg_fallback hC hF)

/-! ## Getters -/

set_option maxHeartbeats 4000000 in
theorem sg_nonce (hF : Fr (fix msg ctx) m 3548 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore

set_option maxHeartbeats 4000000 in
theorem sg_domainSeparator (hF : Fr (fix msg ctx) m 5313 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore

set_option maxHeartbeats 4000000 in
theorem sg_getThreshold (hF : Fr (fix msg ctx) m 5189 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore

set_option maxHeartbeats 4000000 in
theorem sg_approvedHashes (hF : Fr (fix msg ctx) m 3034 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore

set_option maxHeartbeats 4000000 in
theorem sg_signedMessages (hF : Fr (fix msg ctx) m 2371 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore

set_option maxHeartbeats 4000000 in
theorem sg_isOwner (hF : Fr (fix msg ctx) m 1416 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore

set_option maxHeartbeats 4000000 in
theorem sg_isModuleEnabled (hF : Fr (fix msg ctx) m 1313 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore

set_option maxHeartbeats 4000000 in
theorem sg_getTransactionHash (hF : Fr (fix msg ctx) m 4455 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore

/-! ## `approveHash` -/

set_option maxHeartbeats 4000000 in
/-- **`approveHash`** (pc `4396`): it writes only the sender's approval of the given hash. -/
theorem sg_approveHash (hF : Fr (fix msg ctx) m 4396 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore
  exact .inr ⟨msg.caller, _, rfl⟩

/-! ## `authorized` functions: the frame is no self-call, so they revert -/

set_option maxHeartbeats 4000000 in
theorem sg_addOwnerWithThreshold (hC : D.SgCtx O T thr h₀ msg ctx)
    (hF : Fr (fix msg ctx) m 665 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore using [hC.eq_caller]

set_option maxHeartbeats 4000000 in
theorem sg_removeOwner (hC : D.SgCtx O T thr h₀ msg ctx)
    (hF : Fr (fix msg ctx) m 5598 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore using [hC.eq_caller]

set_option maxHeartbeats 4000000 in
theorem sg_swapOwner (hC : D.SgCtx O T thr h₀ msg ctx)
    (hF : Fr (fix msg ctx) m 5044 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore using [hC.eq_caller]

set_option maxHeartbeats 4000000 in
theorem sg_changeThreshold (hC : D.SgCtx O T thr h₀ msg ctx)
    (hF : Fr (fix msg ctx) m 2531 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore using [hC.eq_caller]

set_option maxHeartbeats 4000000 in
theorem sg_enableModule (hC : D.SgCtx O T thr h₀ msg ctx)
    (hF : Fr (fix msg ctx) m 2450 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore using [hC.eq_caller]

set_option maxHeartbeats 4000000 in
theorem sg_disableModule (hC : D.SgCtx O T thr h₀ msg ctx)
    (hF : Fr (fix msg ctx) m 4769 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore using [hC.eq_caller]

set_option maxHeartbeats 4000000 in
theorem sg_setGuard (hC : D.SgCtx O T thr h₀ msg ctx)
    (hF : Fr (fix msg ctx) m 4963 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore using [hC.eq_caller]

set_option maxHeartbeats 4000000 in
theorem sg_setModuleGuard (hC : D.SgCtx O T thr h₀ msg ctx)
    (hF : Fr (fix msg ctx) m 4882 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore using [hC.eq_caller]

set_option maxHeartbeats 4000000 in
theorem sg_setFallbackHandler (hC : D.SgCtx O T thr h₀ msg ctx)
    (hF : Fr (fix msg ctx) m 5232 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore using [hC.eq_caller]

end Dep

end Verified.Safe.Guard
