import Examples.Solmate.ERC4626.SharesCode

/-!
# The vault's `transfer`: bytecode

`transfer(dst, amount)` of the compiled vault (`SharesCode.code i`, arbitrary immutables), from
the start of a top-level call:

* `transfer_ok`: with `amount ≤ balanceOf[caller]`, the call returns ABI `true` and the world
  is `Erc20.transferWorld` (the same two `SSTORE`s as the asset's `transfer`);
* `transfer_revert`: otherwise the checked subtraction panics and the world is unchanged.
-/

namespace EvmLeanSpecs.Refinement.Shares

open EvmLean Interpreter Solidity Contracts Dispatch Erc20 Bytes

variable {i : SolmateVault.Immutables} {ctx : Context} {w : World} {tr : TransientStorage}
  {vault caller dst : Address} {amount : Word} {gas : Nat} {warmAddrs : AddressSet}
  {warmKeys : StorageKeySet}

/-- The dispatcher on a `transfer` call. -/
theorem run_start_transfer (hgas : 208 ≤ gas) (k : Nat) :
    run (k + 51) (start ctx w tr (vaultCall i vault caller (transferData dst amount) gas warmAddrs
      warmKeys)) =
      run k { start ctx w tr (vaultCall i vault caller (transferData dst amount) gas warmAddrs
          warmKeys) with
        frame := { (start ctx w tr (vaultCall i vault caller (transferData dst amount) gas warmAddrs
          warmKeys)).frame with
          pc := 893, stack := [BitVec.ofNat 256 0xa9059cbb], memory := initMemory,
          gasLeft := gas - 208 } } :=
  have h := encodeCall_facts 0xa9059cbb [Word.ofAddress dst, amount] (by decide) (by simp)
  (reaches_transfer i).run_start h.1 h.2.1 h.2.2 hgas k

set_option maxHeartbeats 10000000 in
/-- **`transfer`, success.** -/
theorem transfer_ok (hgas : 100000 ≤ gas)
    (hbal : amount.toNat ≤ ((view ctx.crypto Layout.solmate w vault).balanceOf caller).toNat)
    (k : Nat) :
    ∃ r, run (k + 400) (start ctx w tr
        (vaultCall i vault caller (transferData dst amount) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = transferWorld ctx.crypto w vault caller dst amount := by
  have hjd := jumpDestsAgree i
  have hbal' : amount.toNat ≤
      (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (BitVec.ofNat 256 3)))).toNat := hbal
  rw [show k + 400 = (k + 349) + 51 by omega, run_start_transfer (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [transferData]
  simp only [gt_sub_self_of_le hbal']
  psol_steps [transferData]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp [ChildResult.success]
  · simp only [topLevelResult_output]
    decide +kernel
  · simp only [topLevelResult_world]
    rfl

set_option maxHeartbeats 10000000 in
/-- **`transfer`, insufficient balance**: the checked subtraction panics; the call reverts and
the world is unchanged. -/
theorem transfer_revert (hgas : 100000 ≤ gas)
    (hbal : ((view ctx.crypto Layout.solmate w vault).balanceOf caller).toNat < amount.toNat)
    (k : Nat) :
    ∃ r, run (k + 400) (start ctx w tr
        (vaultCall i vault caller (transferData dst amount) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  have hjd := jumpDestsAgree i
  have hbal' : (w.sload vault (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (BitVec.ofNat 256 3)))).toNat < amount.toNat := hbal
  rw [show k + 400 = (k + 349) + 51 by omega, run_start_transfer (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [transferData]
  simp only [gt_sub_self_of_lt hbal']
  psol_steps [transferData]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp [ChildResult.success]
  · simp
  · simp

end EvmLeanSpecs.Refinement.Shares
