import Examples.Solmate.ERC4626.SharesTransferFrom

/-!
# The vault's `transferFrom`: bytecode, reverts

* `transferFrom_revert_allowance`: a finite allowance below `amount` panics in the checked
  subtraction (`Panic(0x11)`);
* `transferFrom_revert_balance`: otherwise, a balance of `src` (after the allowance update)
  below `amount` panics in the balance subtraction.

Either way the call reverts and the world is unchanged (the allowance write is rolled back).
-/

namespace EvmLeanSpecs.Refinement.Shares

open EvmLean Interpreter Solidity Contracts Dispatch Erc20 Bytes

variable {i : SolmateVault.Immutables} {ctx : Context} {w : World} {tr : TransientStorage}
  {vault caller src dst : Address} {amount : Word} {gas : Nat} {warmAddrs : AddressSet}
  {warmKeys : StorageKeySet}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
/-- **`transferFrom`, insufficient allowance.** -/
theorem transferFrom_revert_allowance (hgas : 100000 ≤ gas)
    (hmax : (view ctx.crypto Layout.solmate w vault).allowance src caller ≠ maxWord)
    (hlt : ((view ctx.crypto Layout.solmate w vault).allowance src caller).toNat < amount.toNat)
    (k : Nat) :
    ∃ r, run (k + 500) (start ctx w tr
        (vaultCall i vault caller (transferFromData src dst amount) gas warmAddrs warmKeys)) =
        .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  have hjd := jumpDestsAgree i
  rw [show k + 500 = (k + 444) + 56 by omega, run_start_transferFrom (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [transferFromData]
  have hmax' : w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4))))) ≠
      maxWord := hmax
  have hlt' : (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
        ofWord (BitVec.ofNat 256 4)))))).toNat < amount.toNat := hlt
  simp only [eq_maxWord_of_ne hmax']
  psol_steps [transferFromData]
  simp only [gt_sub_self_of_lt hlt']
  psol_steps [transferFromData]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [topLevelResult_success]; rfl
  · simp only [topLevelResult_reverted]
  · simp only [topLevelResult_world]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
/-- **`transferFrom`, insufficient balance.** -/
theorem transferFrom_revert_balance (hgas : 100000 ≤ gas)
    (hal : (view ctx.crypto Layout.solmate w vault).allowance src caller = maxWord ∨
      amount.toNat ≤ ((view ctx.crypto Layout.solmate w vault).allowance src caller).toNat)
    (hbal : ((spendWorld ctx.crypto w vault src caller amount).sload vault
      (balanceSlot ctx.crypto Layout.solmate src)).toNat < amount.toNat) (k : Nat) :
    ∃ r, run (k + 500) (start ctx w tr
        (vaultCall i vault caller (transferFromData src dst amount) gas warmAddrs warmKeys)) =
        .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  have hjd := jumpDestsAgree i
  rw [show k + 500 = (k + 444) + 56 by omega, run_start_transferFrom (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [transferFromData]
  by_cases hmax : (view ctx.crypto Layout.solmate w vault).allowance src caller = maxWord
  · have hmax' : w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4))))) =
        maxWord := hmax
    simp only [eq_maxWord_of_eq hmax']
    psol_steps [transferFromData]
    have hbal' : (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
        ofWord (BitVec.ofNat 256 3)))).toNat < amount.toNat := by
      simp only [spendWorld, show w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) =
        maxWord from hmax, ↓reduceIte] at hbal
      exact hbal
    simp only [gt_sub_self_of_lt hbal']
    psol_steps [transferFromData]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [topLevelResult_success]; rfl
    · simp only [topLevelResult_reverted]
    · simp only [topLevelResult_world]
  · have hmax' : w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4))))) ≠
        maxWord := hmax
    have hal' : amount.toNat ≤ (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
          ofWord (BitVec.ofNat 256 4)))))).toNat := hal.resolve_left hmax
    simp only [eq_maxWord_of_ne hmax']
    psol_steps [transferFromData]
    simp only [gt_sub_self_of_le hal']
    psol_steps [transferFromData]
    have hbal' : ((w.sstore vault (ctx.crypto.keccak256
        (ofWord (Word.ofAddress caller) ++ ofWord (ctx.crypto.keccak256
          (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4)))))
        (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
          ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
            ofWord (BitVec.ofNat 256 4))))) - amount)).sload vault
        (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
          ofWord (BitVec.ofNat 256 3)))).toNat < amount.toNat := by
      simp only [spendWorld, show ¬ w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) =
        maxWord from hmax, ↓reduceIte] at hbal
      exact hbal
    simp only [gt_sub_self_of_lt hbal']
    psol_steps [transferFromData]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [topLevelResult_success]; rfl
    · simp only [topLevelResult_reverted]
    · simp only [topLevelResult_world]

end EvmLeanSpecs.Refinement.Shares
