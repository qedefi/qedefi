import Examples.Solmate.ERC4626.SharesCode

/-!
# The vault's `transferFrom`: bytecode, success

`transferFrom(src, dst, amount)` of the compiled vault (`SharesCode.code i`, arbitrary
immutables) called by `caller`: if the allowance `allowance[src][caller]` is
`type(uint256).max` or at least `amount`, and `balanceOf[src]` (after the allowance update)
is at least `amount`, the call returns ABI `true` and the world is
`Erc20.transferFromWorld` (allowance update unless maximal, then the two balance writes).
The reverting cases are in `SharesTransferFromRevert`.
-/

namespace EvmLeanSpecs.Refinement.Shares

open EvmLean Interpreter Solidity Contracts Dispatch Erc20 Bytes

variable {i : SolmateVault.Immutables} {ctx : Context} {w : World} {tr : TransientStorage}
  {vault caller src dst : Address} {amount : Word} {gas : Nat} {warmAddrs : AddressSet}
  {warmKeys : StorageKeySet}

/-- The dispatcher on a `transferFrom` call. -/
theorem run_start_transferFrom (hgas : 230 ≤ gas) (k : Nat) :
    run (k + 56) (start ctx w tr (vaultCall i vault caller (transferFromData src dst amount) gas
      warmAddrs warmKeys)) =
      run k { start ctx w tr (vaultCall i vault caller (transferFromData src dst amount) gas
          warmAddrs warmKeys) with
        frame := { (start ctx w tr (vaultCall i vault caller (transferFromData src dst amount) gas
          warmAddrs warmKeys)).frame with
          pc := 599, stack := [BitVec.ofNat 256 0x23b872dd], memory := initMemory,
          gasLeft := gas - 230 } } :=
  have h := encodeCall_facts 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, amount]
    (by decide) (by simp)
  (reaches_transferFrom i).run_start h.1 h.2.1 h.2.2 hgas k

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
/-- **`transferFrom`, success.** -/
theorem transferFrom_ok (hgas : 100000 ≤ gas)
    (hal : (view ctx.crypto Layout.solmate w vault).allowance src caller = maxWord ∨
      amount.toNat ≤ ((view ctx.crypto Layout.solmate w vault).allowance src caller).toNat)
    (hbal : amount.toNat ≤ ((spendWorld ctx.crypto w vault src caller amount).sload vault
      (balanceSlot ctx.crypto Layout.solmate src)).toNat) (k : Nat) :
    ∃ r, run (k + 500) (start ctx w tr
        (vaultCall i vault caller (transferFromData src dst amount) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = transferFromWorld ctx.crypto w vault caller src dst amount := by
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
    have hbal' : amount.toNat ≤ (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
        ofWord (BitVec.ofNat 256 3)))).toNat := by
      simp only [spendWorld, show w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) =
        maxWord from hmax, ↓reduceIte] at hbal
      exact hbal
    simp only [gt_sub_self_of_le hbal']
    psol_steps [transferFromData]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [topLevelResult_success]; rfl
    · simp only [topLevelResult_output]
      decide +kernel
    · simp only [topLevelResult_world, transferFromWorld, spendWorld,
        show w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) = maxWord from hmax,
        ↓reduceIte]
      rfl
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
    have hbal' : amount.toNat ≤ ((w.sstore vault (ctx.crypto.keccak256
        (ofWord (Word.ofAddress caller) ++ ofWord (ctx.crypto.keccak256
          (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 4)))))
        (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
          ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
            ofWord (BitVec.ofNat 256 4))))) - amount)).sload vault
        (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord (BitVec.ofNat 256 3)))).toNat := by
      simp only [spendWorld, show ¬ w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) =
        maxWord from hmax, ↓reduceIte] at hbal
      exact hbal
    simp only [gt_sub_self_of_le hbal']
    psol_steps [transferFromData]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [topLevelResult_success]; rfl
    · simp only [topLevelResult_output]
      decide +kernel
    · simp only [topLevelResult_world, transferFromWorld, spendWorld,
        show ¬ w.sload vault (allowanceSlot ctx.crypto Layout.solmate src caller) = maxWord from hmax,
        ↓reduceIte]
      rfl

end EvmLeanSpecs.Refinement.Shares
