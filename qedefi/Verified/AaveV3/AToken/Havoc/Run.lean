import Verified.AaveV3.AToken.Havoc.Words
import EvmLogic.Tactic.PrefixRun

/-!
# Running the AToken in the any-gas prefix calculus

The shape of a function proof: the dispatcher leaves the frame at a function's entry pc with the
selector on the stack and the free-memory pointer set (`entryM`); `BodyOk pc` says that from there
the frame ends in a `Good` world, for any gas, given `CoversA` below a bound of the gas (the
summaries of every dangerous frame the function's calls may reach, at any depth).

`atok_run` drives the function with `apwp_run`; its handler `atok_handle` takes every external
call (`pwp_call_any`: the rewards controller, the Pool, the underlying, any token for
`rescueTokens`), every static call (`pwp_staticcall`: the Pool's index, the ACL, `ecrecover`), every
`LOG` (`pwp_safe_le`) and the end (`pwp_stop`/`pwp_return`). After a call the world is a fresh
`Good` one and the stack is forgotten (`apwp_forget`): the AToken writes nothing after an external
call (checks-effects-interactions, checked here on every path). What is left are the `Good`
obligations for the worlds the function writes before its first call or log: the ledger proofs.
-/

namespace Verified.AaveV3.AToken.Havoc
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
  EvmLogic.Program.Reentrancy EvmLogic.Solidity Verified.AaveV3.Contracts

/-- The memory after solc's `mstore(0x40, 0x80)`. -/
abbrev mem0 : Memory := ({ } : Memory).expand 64 32 |>.storeWord 64 128#256

/-- The machine at a function's entry pc `pc`, as the dispatcher leaves it. -/
abbrev entryM (ctx : Context) (w : World) (tr : TransientStorage) (ow : World)
    (created : AddressSet) (msg : Message) (jd : Array Bool) (pc : Nat) (sel : Word) (g : Nat)
    (sub : Substate) (snap : World × TransientStorage) (ko ks : Nat) (parents : List Frame) :
    Machine :=
  Machine.mk ctx (PrecompileImpl.standard ctx) w tr ow created
    (Frame.mk msg AToken.runtimeCode jd pc [sel] mem0 g .empty sub snap (.call ko ks)) parents

/-- **A function body keeps `Good`**: from its entry `pc`, for any gas below `G`, given the
summaries `CoversA` below `G`, in a non-static frame at a protected account, from a `Good` world
and snapshot. -/
def BodyOk (pc : Nat) : Prop :=
  ∀ (G : Nat) (ctx : Context) (w : World) (tr : TransientStorage) (ow : World)
    (created : AddressSet) (msg : Message) (jd : Array Bool) (sel : Word) (g : Nat)
    (sub : Substate) (snap : World × TransientStorage) (ko ks : Nat) (parents : List Frame),
    SlotsOk ctx.crypto → (∀ g' < G, CoversA Prot (Good ctx.crypto) (Ctx ctx.crypto) g') →
    g ≤ G → Good ctx.crypto snap.1 → Good ctx.crypto w → msg.isStatic = false →
    Prot msg.currentTarget →
    WP (entryM ctx w tr ow created msg jd pc sel g sub snap ko ks parents) (fun _ => False)
      (FailOk (Good ctx.crypto))

set_option hygiene false in
/-- The handler of `apwp_run` for the AToken (see the module docstring). Uses the names `ctx`,
`hK`, `hcov` of the context. -/
macro "atok_handle" : tactic => `(tactic| first
  | (refine pwp_safe_le (b := 0xa1) (p := 3) ‹_› ?_ rfl (by code_fact) (by decide) (by decide) ?_
     on_goal 2 => (intro _ _ _ _ _ _ _; apwp_cont [mask_and_eq, and_mask_eq,
       Word.toAddress_ofAddress, keccak_mappingSlot, EvmLogic.Solidity.eq_self,
       addressMask_and_ofAddress, World.sload_sstore_self, sload54_sstore_user hK,
       sloadUser_sstore54 hK, sload54_sstore_allow hK, sloadUser_sstore_allow hK]))
  | (refine pwp_safe_le (b := 0xa2) (p := 4) ‹_› ?_ rfl (by code_fact) (by decide) (by decide) ?_
     on_goal 2 => (intro _ _ _ _ _ _ _; apwp_cont [mask_and_eq, and_mask_eq,
       Word.toAddress_ofAddress, keccak_mappingSlot, EvmLogic.Solidity.eq_self,
       addressMask_and_ofAddress, World.sload_sstore_self, sload54_sstore_user hK,
       sloadUser_sstore54 hK, sload54_sstore_allow hK, sloadUser_sstore_allow hK]))
  | (refine pwp_safe_le (b := 0xa3) (p := 5) ‹_› ?_ rfl (by code_fact) (by decide) (by decide) ?_
     on_goal 2 => (intro _ _ _ _ _ _ _; apwp_cont [mask_and_eq, and_mask_eq,
       Word.toAddress_ofAddress, keccak_mappingSlot, EvmLogic.Solidity.eq_self,
       addressMask_and_ofAddress, World.sload_sstore_self, sload54_sstore_user hK,
       sloadUser_sstore54 hK, sload54_sstore_allow hK, sloadUser_sstore_allow hK]))
  | (refine pwp_safe_le (b := 0xa4) (p := 6) ‹_› ?_ rfl (by code_fact) (by decide) (by decide) ?_
     on_goal 2 => (intro _ _ _ _ _ _ _; apwp_cont [mask_and_eq, and_mask_eq,
       Word.toAddress_ofAddress, keccak_mappingSlot, EvmLogic.Solidity.eq_self,
       addressMask_and_ofAddress, World.sload_sstore_self, sload54_sstore_user hK,
       sloadUser_sstore54 hK, sload54_sstore_allow hK, sloadUser_sstore_allow hK]))
  | (refine pwp_stop (by code_fact) rfl ?_)
  | (refine pwp_return ‹_› (by code_fact) rfl rfl ?_)
  | (refine pwp_call_any (C := Ctx ctx.crypto) (goodOps_good ctx.crypto) rfl ?_ ?_ ?_
       rfl rfl ?_ ?_ (wp_of_resume ?_)
     on_goal 1 => exact fun g hg => hcov g (Nat.lt_of_lt_of_le hg ‹_›)
     on_goal 1 => assumption
     on_goal 1 => code_fact
     on_goal 2 => exact fun h => absurd rfl h
     on_goal 2 => (intro _ _ _ _ _ _ _ _ _ _; apwp_cont [mask_and_eq, and_mask_eq,
       Word.toAddress_ofAddress, keccak_mappingSlot, EvmLogic.Solidity.eq_self,
       addressMask_and_ofAddress, World.sload_sstore_self, sload54_sstore_user hK,
       sloadUser_sstore54 hK, sload54_sstore_allow hK, sloadUser_sstore_allow hK]; apwp_forget))
  | (refine pwp_staticcall (C := Ctx ctx.crypto) (goodOps_good ctx.crypto) rfl ?_ ?_ ?_
       rfl rfl ?_ (wp_of_resume ?_)
     on_goal 1 => exact fun g hg => hcov g (Nat.lt_of_lt_of_le hg ‹_›)
     on_goal 1 => assumption
     on_goal 1 => code_fact
     on_goal 2 => (intro _ _ _ _ _ _ _ _ _ _; apwp_cont [mask_and_eq, and_mask_eq,
       Word.toAddress_ofAddress, keccak_mappingSlot, EvmLogic.Solidity.eq_self,
       addressMask_and_ofAddress, World.sload_sstore_self, sload54_sstore_user hK,
       sloadUser_sstore54 hK, sload54_sstore_allow hK, sloadUser_sstore_allow hK]; apwp_forget)))

set_option hygiene false in
/-- Run a function body from its entry (see the module docstring); then close the `Good`
obligations of worlds already known to be `Good`. -/
macro "atok_run" : tactic => `(tactic| (
  intro G ctx w tr ow created msg jd sel g sub snap ko ks parents hK hcov hg hsnap hw hst ht
  apwp_run [mask_and_eq, and_mask_eq, Word.toAddress_ofAddress, keccak_mappingSlot,
    EvmLogic.Solidity.eq_self, addressMask_and_ofAddress, World.sload_sstore_self,
    sload54_sstore_user hK, sloadUser_sstore54 hK, sload54_sstore_allow hK,
    sloadUser_sstore_allow hK] using atok_handle
  all_goals try (with_reducible assumption)
  all_goals try dsimp only))

end Verified.AaveV3.AToken.Havoc
