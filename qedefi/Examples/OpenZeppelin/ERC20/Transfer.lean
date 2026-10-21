import Examples.OpenZeppelin.ERC20.Basic

/-!
# `OzAsset.transfer` refines the OpenZeppelin ERC-20 model

`transfer(address,uint256)` of OpenZeppelin's `ERC20Mock`: top-level success (`transfer_ok`)
and the three reverts (`ERC20InvalidSender` for a zero caller, `ERC20InvalidReceiver`,
`ERC20InsufficientBalance`), and the refinement `transfer_spec` of `Model.ozTransfer` through
`ERC20.view` with `Layout.oz`. The proof skips the dispatcher (`reaches_transfer`) and runs
`sol_steps`, deciding the two zero-address `JUMPI`s and the balance check by hypotheses.
-/

namespace Examples.OpenZeppelin.ERC20
open EvmLean EvmLogic EvmLogic.Solidity EvmLogic.Tactic EvmLogic.Solidity.ERC20
open EvmLean.Interpreter EvmLogic.Solidity.Dispatch EvmLean.Bytes Examples.OpenZeppelin.Contracts

/-- The selector of `transfer(address,uint256)`. -/
def transferSelector : Nat := 0xa9059cbb

theorem transferSelector_mem :
    ("transfer(address,uint256)", (0xa9059cbb : UInt32)) ∈ OzAsset.selectors := by
  decide

/-- Calldata of `transfer(to, amount)`. -/
def transferCalldata (to : Address) (amount : Word) : ByteArray :=
  Abi.encodeCall transferSelector [Word.ofAddress to, amount]

/-- A top-level call of `transfer(to, amount)` on the token at `token`. -/
abbrev transferCall (token caller to : Address) (amount : Word) (gas : Nat)
    (warmAddrs : AddressSet) (warmKeys : StorageKeySet) : Message :=
  callMsg OzAsset.runtimeCode token caller (transferCalldata to amount) gas warmAddrs warmKeys

theorem selectorOf_transferCalldata (to : Address) (amount : Word) :
    Abi.selectorOf (transferCalldata to amount) = transferSelector := by
  rw [transferCalldata, Abi.selectorOf_encodeCall]; rfl

theorem size_transferCalldata (to : Address) (amount : Word) :
    (transferCalldata to amount).size = 68 := by
  rw [transferCalldata, Abi.size_encodeCall]; rfl

set_option maxHeartbeats 1000000 in
/-- **Dispatch of `transfer`**: selector `a9059cbb` reaches pc 375 in 49 steps for 206 gas. -/
theorem reaches_transfer : Reaches OzAsset.runtimeCode transferSelector 375 49 206 := by
  sol_dispatch

variable {ctx : Context} {w : World} {tr : TransientStorage} {token caller to : Address}
  {amount : Word} {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

theorem run_start_transfer (hgas : 206 ≤ gas) (k : Nat) :
    run (k + 49) (start ctx w tr (transferCall token caller to amount gas warmAddrs warmKeys)) =
      run k { start ctx w tr (transferCall token caller to amount gas warmAddrs warmKeys) with
        frame := { (start ctx w tr
          (transferCall token caller to amount gas warmAddrs warmKeys)).frame with
          pc := 375, stack := [BitVec.ofNat 256 transferSelector], memory := initMemory,
          gasLeft := (start ctx w tr
            (transferCall token caller to amount gas warmAddrs warmKeys)).frame.gasLeft -
            206 } } :=
  reaches_transfer.run_eq (msg := transferCall token caller to amount gas warmAddrs warmKeys)
    rfl rfl rfl (selectorOf_transferCalldata to amount)
    (by rw [show (transferCall token caller to amount gas warmAddrs warmKeys).data =
      transferCalldata to amount from rfl, size_transferCalldata]; decide)
    (by rw [show (transferCall token caller to amount gas warmAddrs warmKeys).data =
      transferCalldata to amount from rfl, size_transferCalldata]; decide)
    hgas k

set_option maxHeartbeats 10000000 in
/-- **`transfer`, success**: nonzero caller and recipient, `amount ≤ balanceOf[caller]`;
returns `true` with `moveWorld`. -/
theorem transfer_ok (hgas : 100000 ≤ gas) (hc : caller ≠ 0) (ht : to ≠ 0)
    (hbal : amount.toNat ≤ ((view ctx.crypto Layout.oz w token).balanceOf caller).toNat)
    (k : Nat) :
    ∃ r, run (k + 400)
        (start ctx w tr (transferCall token caller to amount gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = moveWorld ctx.crypto Layout.oz w token caller to amount := by
  have hbal' : amount.toNat ≤
      (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (BitVec.ofNat 256 0)))).toNat := hbal
  have hc' := ofAddress_ne_zero hc
  have ht' := ofAddress_ne_zero ht
  rw [show k + 400 = (k + 351) + 49 by omega, run_start_transfer (by omega)]
  simp only [start, Frame.init, callMsg, transferSelector]
  sol_steps [transferCalldata]
  simp only [(Word.lt_eq_zero_iff _ _).2 hbal']
  sol_steps [transferCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]
    kernel_decide
  · simp only [topLevelResult_world]
    rfl

set_option maxHeartbeats 10000000 in
/-- **`transfer` from the zero address** reverts (`ERC20InvalidSender(0)`); world unchanged. -/
theorem transfer_revert_sender (hgas : 100000 ≤ gas) (hc : caller = 0) (k : Nat) :
    ∃ r, run (k + 400)
        (start ctx w tr (transferCall token caller to amount gas warmAddrs warmKeys)) = .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  subst hc
  rw [show k + 400 = (k + 351) + 49 by omega, run_start_transfer (by omega)]
  simp only [start, Frame.init, callMsg, transferSelector]
  sol_steps [transferCalldata, ofAddress_zero]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp
  · simp

set_option maxHeartbeats 10000000 in
/-- **`transfer` to the zero address** reverts (`ERC20InvalidReceiver(0)`); world unchanged. -/
theorem transfer_revert_receiver (hgas : 100000 ≤ gas) (hc : caller ≠ 0) (ht : to = 0)
    (k : Nat) :
    ∃ r, run (k + 400)
        (start ctx w tr (transferCall token caller to amount gas warmAddrs warmKeys)) = .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  subst ht
  have hc' := ofAddress_ne_zero hc
  rw [show k + 400 = (k + 351) + 49 by omega, run_start_transfer (by omega)]
  simp only [start, Frame.init, callMsg, transferSelector]
  sol_steps [transferCalldata, ofAddress_zero]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp
  · simp

set_option maxHeartbeats 10000000 in
/-- **`transfer`, insufficient balance**: reverts (`ERC20InsufficientBalance`); world
unchanged. -/
theorem transfer_revert_balance (hgas : 100000 ≤ gas) (hc : caller ≠ 0) (ht : to ≠ 0)
    (hbal : ((view ctx.crypto Layout.oz w token).balanceOf caller).toNat < amount.toNat)
    (k : Nat) :
    ∃ r, run (k + 400)
        (start ctx w tr (transferCall token caller to amount gas warmAddrs warmKeys)) = .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  have hbal' : (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (BitVec.ofNat 256 0)))).toNat < amount.toNat := hbal
  have hc' := ofAddress_ne_zero hc
  have ht' := ofAddress_ne_zero ht
  rw [show k + 400 = (k + 351) + 49 by omega, run_start_transfer (by omega)]
  simp only [start, Frame.init, callMsg, transferSelector]
  sol_steps [transferCalldata]
  simp only [(Word.lt_eq_one_iff _ _).2 hbal']
  sol_steps [transferCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp
  · simp

/-! ## The refinement theorem -/

set_option maxHeartbeats 1000000 in
/-- **`transfer` refines `Model.ozTransfer`** for a top-level call (no EIP-7702 authorizations
or before Prague, gas ≥ 100000, fuel ≥ 400), assuming `BalanceSlotOk` for `caller` and `to`:
on `some s'` it returns `true` with `s'`'s supply, balances and the allowances in unwritten
slots, other accounts untouched; on `none` it reverts with the world unchanged. -/
theorem transfer_spec (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 100000 ≤ gas)
    (hc : BalanceSlotOk ctx.crypto Layout.oz caller)
    (ht : BalanceSlotOk ctx.crypto Layout.oz to) (fuel : Nat) (hfuel : 400 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (transferCall token caller to amount gas warmAddrs warmKeys) = .ok r ∧
      match Model.ozTransfer (view ctx.crypto Layout.oz w token) caller to amount with
      | some s' =>
        r.success = true ∧ r.output = Bytes.ofWord 1 ∧
        (view ctx.crypto Layout.oz r.world token).totalSupply = s'.totalSupply ∧
        (view ctx.crypto Layout.oz r.world token).balanceOf = s'.balanceOf ∧
        (∀ o s, allowanceSlot ctx.crypto Layout.oz o s ≠ balanceSlot ctx.crypto Layout.oz caller →
          allowanceSlot ctx.crypto Layout.oz o s ≠ balanceSlot ctx.crypto Layout.oz to →
          (view ctx.crypto Layout.oz r.world token).allowance o s = s'.allowance o s) ∧
        (∀ b k, b ≠ token → r.world.sload b k = w.sload b k)
      | none => r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 400 := ⟨fuel - 400, by omega⟩
  rw [transferCall, processMessageCall_callMsg hdeleg delegatedAddress?_runtimeCode hpre]
  split
  · rename_i s' hm
    unfold Model.ozTransfer at hm
    split at hm
    · cases hm
    rename_i hc0
    split at hm
    · cases hm
    rename_i ht0
    have hbal : amount.toNat ≤ ((view ctx.crypto Layout.oz w token).balanceOf caller).toNat := by
      unfold Model.transfer at hm
      split at hm
      · assumption
      · cases hm
    obtain ⟨r, hr, hs, ho, hw⟩ := transfer_ok (tr := tr) (warmAddrs := warmAddrs)
      (warmKeys := warmKeys) hgas hc0 ht0 hbal k
    obtain ⟨h1, h2, h3, h4⟩ := view_moveWorld hc ht hm
    refine ⟨r, hr, hs, ho, ?_, ?_, ?_, ?_⟩ <;> rw [hw]
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · rename_i hm
    unfold Model.ozTransfer at hm
    by_cases hc0 : caller = 0
    · exact transfer_revert_sender hgas hc0 k
    by_cases ht0 : to = 0
    · exact transfer_revert_receiver hgas hc0 ht0 k
    simp only [hc0, ht0, ↓reduceIte] at hm
    have hbal : ((view ctx.crypto Layout.oz w token).balanceOf caller).toNat < amount.toNat := by
      unfold Model.transfer at hm
      split at hm
      · cases hm
      · omega
    exact transfer_revert_balance hgas hc0 ht0 hbal k

end Examples.OpenZeppelin.ERC20
