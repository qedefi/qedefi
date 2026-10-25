import Verified.Safe.Bytecode.Singleton.CopyLoop

/-!
# The singleton: views with loops

`VERSION`, `getStorageAt`, `getOwners`, `getModulesPaginated`. Their loops (the storage read
loop, the owners and modules linked lists, the copies of the ABI encoder) are proved by
coinduction (`OwnG.coind`): an invariant of the loop head, no termination argument, any memory
(`getStorageAt` writes past its array when `length * 32` wraps).
-/

namespace Verified.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Verified.Safe.Contracts

namespace Dep

variable (D : Dep) {O T : Finset Address} {thr : Nat} {h₀ : Word} {msg : Message}
  {ctx : Context} {w : World} {m : Machine} {s : Word}

set_option maxHeartbeats 4000000 in
theorem sg_VERSION (hF : Fr (fix msg ctx) m 5721 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore [5779]
  refine .leaf (copyC_5779 (fun i' mem' m hF => ?_) _ _ _ hF)
  sg_explore

set_option maxHeartbeats 4000000 in
/-- The loop of `getStorageAt` (pc `8510`): one `SLOAD` per word, then the ABI encoder's copy. -/
theorem sload_loop {len off : Word} :
    ∀ (i : Word) (mem : Memory) (m : Machine),
      Fr (fix msg ctx) m 8510 [i, 128#256, 96#256, len, off, 2248#256, s] mem w →
      D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  intro i mem m hF
  refine OwnG.coind (fun x => ∃ i mem,
    Fr (fix msg ctx) x 8510 [i, 128#256, 96#256, len, off, 2248#256, s] mem w) ?_ m ⟨i, mem, hF⟩
  rintro x ⟨i, mem, hF⟩
  refine OwnB.jumpdestStep hF (by own_code) (Own.sstoreOk_of_ne (b := 0x5b) hF (by own_code)
    (by decide)) fun m hF => ?_
  sg_explore [8510, 2285]
  · exact .leaf (.inl ⟨_, _, hF⟩)
  · refine .leaf (.inr (copyC_2285 (fun i' mem' m hF => ?_) _ _ _ hF))
    sg_explore

set_option maxHeartbeats 4000000 in
theorem sg_getStorageAt (hF : Fr (fix msg ctx) m 2181 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore [8510]
  all_goals exact .leaf (D.sload_loop _ _ _ hF)

set_option maxHeartbeats 4000000 in
/-- The owners list of `getOwners` (pc `10925`), then the ABI encoder's copy. -/
theorem owners_loop :
    ∀ (cur idx : Word) (mem : Memory) (m : Machine),
      Fr (fix msg ctx) m 10925 [cur, idx, 128#256, 96#256, 3461#256, s] mem w →
      D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  intro cur idx mem m hF
  refine OwnG.coind (fun x => ∃ cur idx mem,
    Fr (fix msg ctx) x 10925 [cur, idx, 128#256, 96#256, 3461#256, s] mem w) ?_ m
    ⟨cur, idx, mem, hF⟩
  rintro x ⟨cur, idx, mem, hF⟩
  refine OwnB.jumpdestStep hF (by own_code) (Own.sstoreOk_of_ne (b := 0x5b) hF (by own_code)
    (by decide)) fun m hF => ?_
  sg_explore [10925, 3501]
  all_goals first
    | exact .leaf (.inl ⟨_, _, _, hF⟩)
    | (refine .leaf (.inr (copyC_3501 (fun i' mem' m hF => ?_) _ _ _ hF)); sg_explore)

set_option maxHeartbeats 4000000 in
theorem sg_getOwners (hF : Fr (fix msg ctx) m 3440 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore [10925]
  all_goals exact .leaf (D.owners_loop _ _ _ _ hF)

set_option maxHeartbeats 4000000 in
/-- The modules list of `getModulesPaginated` (pc `12000`), then the ABI encoder's copy. -/
theorem modules_loop {size start : Word} :
    ∀ (cnt next : Word) (mem : Memory) (m : Machine),
      Fr (fix msg ctx) m 12000 [cnt, next, 128#256, size, start, 4280#256, s] mem w →
      D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  intro cnt next mem m hF
  refine OwnG.coind (fun x => ∃ cnt next mem,
    Fr (fix msg ctx) x 12000 [cnt, next, 128#256, size, start, 4280#256, s] mem w) ?_ m
    ⟨cnt, next, mem, hF⟩
  rintro x ⟨cnt, next, mem, hF⟩
  refine OwnB.jumpdestStep hF (by own_code) (Own.sstoreOk_of_ne (b := 0x5b) hF (by own_code)
    (by decide)) fun m hF => ?_
  sg_explore [12000, 4348]
  all_goals first
    | exact .leaf (.inl ⟨_, _, _, hF⟩)
    | (refine .leaf (.inr (copyC_4348 (fun i' mem' m hF => ?_) _ _ _ hF)); sg_explore)

set_option maxHeartbeats 4000000 in
theorem sg_getModulesPaginated (hF : Fr (fix msg ctx) m 4191 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore [12000]
  all_goals exact .leaf (D.modules_loop _ _ _ _ hF)

end Dep

end Verified.Safe.Guard
