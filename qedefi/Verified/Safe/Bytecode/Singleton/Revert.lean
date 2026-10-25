import Verified.Safe.Bytecode.Singleton.Ctx

/-!
# The singleton: `simulateAndRevert`, `setup`, `execTransactionFromModule`

`simulateAndRevert` reaches the doom point: after its `DELEGATECALL` the frame reverts,
whatever the child did. `setup` reverts because the threshold is set; the module entry points
revert because no module is enabled.
-/

namespace Verified.Safe.Guard

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Program.Nested
open Verified.Safe.Contracts

namespace Dep

variable (D : Dep) {O T : Finset Address} {thr : Nat} {h₀ : Word} {msg : Message}
  {ctx : Context} {w : World} {m : Machine} {s : Word}

set_option maxHeartbeats 4000000 in
/-- **`simulateAndRevert`** (pc `3591`): any code runs by `DELEGATECALL` in the Safe's context
(pc `11184`, the doom point), then the frame reverts. -/
theorem sg_simulateAndRevert (hF : Fr (fix msg ctx) m 3591 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  sg_explore
  case call11184 => exact fun _ hd => absurd hF.pc hd
  case doom11184 =>
    intro _ m res out w' hF
    sg_explore

theorem eq_one_of_caller {a : Address} (h : a = sentinel) :
    (Word.ofAddress a).eq 1#256 = 1#256 := by
  subst h; decide

theorem eq_one_of_ne {a : Address} (h : a ≠ sentinel) : (Word.ofAddress a).eq 1#256 = 0 :=
  eq_ofAddress_of_ne (b := sentinel) h

/-- The module check: the sender is the sentinel, or its slot in `modules` is empty. -/
theorem module_slot {crypto : Crypto} {chainId : Nat} {fork : Fork}
    (hR : D.Rsf crypto chainId O T thr h₀ fork m) (hw : m.world = w) (ht : msg.currentTarget = D.sf)
    {a : Address} (ha : a ≠ sentinel) :
    w.sload msg.currentTarget (crypto.keccak256 (Bytes.ofWord (Word.ofAddress a) ++ Bytes.ofWord 1#256))
      = 0 := by
  rw [← hw, ht]; exact hR.1.2.2.modules a ha

set_option maxHeartbeats 4000000 in
/-- **`execTransactionFromModule`** (pc `1519`): no module is enabled. -/
theorem sg_execTransactionFromModule (hC : D.SgCtx O T thr h₀ msg ctx)
    (hF : Fr (fix msg ctx) m 1519 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  refine OwnG.withR fun hR => ?_
  by_cases hcs : msg.caller = sentinel
  · sg_explore using [eq_one_of_caller hcs]
  · have hmod := D.module_slot hR hF.world hC.target hcs
    sg_explore using [eq_one_of_ne hcs, hmod]

set_option maxHeartbeats 4000000 in
/-- **`execTransactionFromModuleReturnData`** (pc `1796`): no module is enabled. -/
theorem sg_execTransactionFromModuleReturnData (hC : D.SgCtx O T thr h₀ msg ctx)
    (hF : Fr (fix msg ctx) m 1796 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  refine OwnG.withR fun hR => ?_
  by_cases hcs : msg.caller = sentinel
  · sg_explore using [eq_one_of_caller hcs]
  · have hmod := D.module_slot hR hF.world hC.target hcs
    sg_explore using [eq_one_of_ne hcs, hmod]

theorem gt_zero_of_pos {n : Nat} (h0 : 0 < n) (h : n < 2 ^ 256) :
    Word.gt (BitVec.ofNat 256 n) 0#256 = 1#256 := by
  have hu : BitVec.ult 0#256 (BitVec.ofNat 256 n) = true := by
    rw [BitVec.ult]
    exact decide_eq_true (by simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]; simpa using h0)
  simp [Word.gt, Word.ofBool, hu]

set_option maxHeartbeats 40000000 in
/-- **`setup`** (pc `3823`): the threshold is set, so `setupOwners` reverts (after the
`SafeSetup` event). -/
theorem sg_setup (hC : D.SgCtx O T thr h₀ msg ctx) (hF : Fr (fix msg ctx) m 3823 [s] mem0 w) :
    D.Jsg ctx.crypto ctx.block.chainId O T thr h₀ ctx.fork m := by
  refine OwnG.withR fun hR => ?_
  have h4 : w.sload msg.currentTarget 4#256 = BitVec.ofNat 256 thr := by
    rw [← hF.world, hC.target]; exact hR.1.2.2.threshold
  have hpos : 0 < thr := Nat.lt_of_le_of_lt (Nat.zero_le _) hC.card
  sg_explore using [h4, gt_zero_of_pos hpos hC.thr_lt]

end Dep

end Verified.Safe.Guard
