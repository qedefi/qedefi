import Examples.Solmate.ERC4626.SharesCode

/-!
# The vault's share-token views: bytecode

`totalSupply()`, `balanceOf(a)`, `allowance(owner, spender)` and `decimals()` of the compiled
vault (`SharesCode.code i`, arbitrary immutables), from the start of a top-level call by any
caller: each succeeds, returns the ABI encoding of the value read through `Erc20.view`
(resp. the `decimals` immutable, masked to `uint8`), and leaves the world unchanged.
-/

namespace EvmLeanSpecs.Refinement.Shares

open EvmLean Interpreter Solidity Contracts Dispatch Erc20 Bytes

variable {i : SolmateVault.Immutables} {ctx : Context} {w : World} {tr : TransientStorage}
  {vault caller a owner spender : Address} {gas : Nat} {warmAddrs : AddressSet}
  {warmKeys : StorageKeySet}

set_option maxHeartbeats 10000000 in
/-- **`totalSupply()`** returns `totalSupply`. -/
theorem totalSupply_ok (hgas : 10000 ≤ gas) (k : Nat) :
    ∃ r, run (k + 100) (start ctx w tr
        (vaultCall i vault caller totalSupplyData gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧
      r.output = Bytes.ofWord (view ctx.crypto Layout.solmate w vault).totalSupply ∧
      r.world = w := by
  have hjd := jumpDestsAgree i
  have h := encodeCall_facts 0x18160ddd [] (by decide) (by simp)
  rw [show k + 100 = (k + 49) + 51 by omega,
    (reaches_totalSupply i).run_start (data := totalSupplyData) h.1 h.2.1 h.2.2 (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [totalSupplyData]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]; rfl
  · simp only [topLevelResult_world]

set_option maxHeartbeats 10000000 in
/-- **`balanceOf(a)`** returns `balanceOf[a]`. -/
theorem balanceOf_ok (hgas : 10000 ≤ gas) (k : Nat) :
    ∃ r, run (k + 200) (start ctx w tr
        (vaultCall i vault caller (balanceOfData a) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧
      r.output = Bytes.ofWord ((view ctx.crypto Layout.solmate w vault).balanceOf a) ∧
      r.world = w := by
  have hjd := jumpDestsAgree i
  have h := encodeCall_facts 0x70a08231 [Word.ofAddress a] (by decide) (by simp)
  rw [show k + 200 = (k + 150) + 50 by omega,
    (reaches_balanceOf i).run_start (data := balanceOfData a) h.1 h.2.1 h.2.2 (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [balanceOfData]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]; rfl
  · simp only [topLevelResult_world]

set_option maxHeartbeats 10000000 in
/-- **`allowance(owner, spender)`** returns `allowance[owner][spender]`. -/
theorem allowance_ok (hgas : 10000 ≤ gas) (k : Nat) :
    ∃ r, run (k + 200) (start ctx w tr
        (vaultCall i vault caller (allowanceData owner spender) gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧
      r.output = Bytes.ofWord ((view ctx.crypto Layout.solmate w vault).allowance owner spender) ∧
      r.world = w := by
  have hjd := jumpDestsAgree i
  have h := encodeCall_facts 0xdd62ed3e [Word.ofAddress owner, Word.ofAddress spender] (by decide)
    (by simp)
  rw [show k + 200 = (k + 156) + 44 by omega,
    (reaches_allowance i).run_start (data := allowanceData owner spender) h.1 h.2.1 h.2.2 (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [allowanceData]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]; rfl
  · simp only [topLevelResult_world]

set_option maxHeartbeats 10000000 in
/-- **`decimals()`** returns the `decimals` immutable as a `uint8`. -/
theorem decimals_ok (hgas : 10000 ≤ gas) (k : Nat) :
    ∃ r, run (k + 100) (start ctx w tr
        (vaultCall i vault caller decimalsData gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord (i.decimals &&& 255#256) ∧ r.world = w := by
  have hjd := jumpDestsAgree i
  have h := encodeCall_facts 0x313ce567 [] (by decide) (by simp)
  rw [show k + 100 = (k + 59) + 41 by omega,
    (reaches_decimals i).run_start (data := decimalsData) h.1 h.2.1 h.2.2 (by omega)]
  simp only [start, Frame.init, callMsg]
  psol_steps [decimalsData, readBytes_code_decimals]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]
  · simp only [topLevelResult_world]

end EvmLeanSpecs.Refinement.Shares
