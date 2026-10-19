import EvmLeanSpecs.Refinement.SharesCode

/-!
# The vault's `approve`: bytecode

`approve(spender, amount)` of the compiled vault (`SharesCode.code i`, arbitrary immutables):
the call always succeeds, returns ABI `true`, and the world is `Erc20.approveWorld` (one
`SSTORE` to `allowance[caller][spender]`).
-/

namespace EvmLeanSpecs.Refinement.Shares

open EvmLean Interpreter Solidity Contracts Dispatch Erc20 Bytes

variable {i : SolmateVault.Immutables} {ctx : Context} {w : World} {tr : TransientStorage}
  {vault caller spender : Address} {amount : Word} {gas : Nat} {warmAddrs : AddressSet}
  {warmKeys : StorageKeySet}

/-- The dispatcher on an `approve` call. -/
theorem run_start_approve (hgas : 164 ≤ gas) (k : Nat) :
    run (k + 41) (start ctx w tr (vaultCall i vault caller (approveData spender amount) gas
      warmAddrs warmKeys)) =
      run k { start ctx w tr (vaultCall i vault caller (approveData spender amount) gas warmAddrs
          warmKeys) with
        frame := { (start ctx w tr (vaultCall i vault caller (approveData spender amount) gas
          warmAddrs warmKeys)).frame with
          pc := 536, stack := [BitVec.ofNat 256 0x095ea7b3], memory := initMemory,
          gasLeft := gas - 164 } } :=
  have h := encodeCall_facts 0x095ea7b3 [Word.ofAddress spender, amount] (by decide) (by simp)
  (reaches_approve i).run_start h.1 h.2.1 h.2.2 hgas k

set_option maxHeartbeats 10000000 in
/-- **`approve`**: succeeds, returns `true`, world `approveWorld`. -/
theorem approve_ok (hgas : 100000 ≤ gas) (k : Nat) :
    ∃ r, run (k + 300) (start ctx w tr
        (vaultCall i vault caller (approveData spender amount) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = approveWorld ctx.crypto w vault caller spender amount := by
  have hjd := jumpDestsAgree i
  rw [show k + 300 = (k + 259) + 41 by omega, run_start_approve (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [approveData]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp [ChildResult.success]
  · simp only [topLevelResult_output]
    decide +kernel
  · simp only [topLevelResult_world]
    rfl

end EvmLeanSpecs.Refinement.Shares
