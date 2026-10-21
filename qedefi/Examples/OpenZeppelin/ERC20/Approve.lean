import Examples.OpenZeppelin.ERC20.Basic

/-!
# `OzAsset.approve` refines the OpenZeppelin ERC-20 model

`approve(address,uint256)` of OpenZeppelin's `ERC20Mock`: top-level success (`approve_ok`), the
zero-address reverts (`ERC20InvalidApprover` for a zero caller, `ERC20InvalidSpender`), and
the refinement `approve_spec` of `Model.ozApprove` through `ERC20.view` with `Layout.oz`.
-/

namespace Examples.OpenZeppelin.ERC20
open EvmLean EvmLogic EvmLogic.Solidity EvmLogic.Tactic EvmLogic.Solidity.ERC20
open EvmLean.Interpreter EvmLogic.Solidity.Dispatch EvmLean.Bytes Examples.OpenZeppelin.Contracts

/-- The selector of `approve(address,uint256)`. -/
def approveSelector : Nat := 0x095ea7b3

theorem approveSelector_mem :
    ("approve(address,uint256)", (0x095ea7b3 : UInt32)) ∈ OzAsset.selectors := by
  decide

/-- Calldata of `approve(spender, amount)`. -/
def approveCalldata (spender : Address) (amount : Word) : ByteArray :=
  Abi.encodeCall approveSelector [Word.ofAddress spender, amount]

/-- A top-level call of `approve(spender, amount)` on the token at `token`. -/
abbrev approveCall (token caller spender : Address) (amount : Word) (gas : Nat)
    (warmAddrs : AddressSet) (warmKeys : StorageKeySet) : Message :=
  callMsg OzAsset.runtimeCode token caller (approveCalldata spender amount) gas warmAddrs
    warmKeys

theorem selectorOf_approveCalldata (spender : Address) (amount : Word) :
    Abi.selectorOf (approveCalldata spender amount) = approveSelector := by
  rw [approveCalldata, Abi.selectorOf_encodeCall]; rfl

theorem size_approveCalldata (spender : Address) (amount : Word) :
    (approveCalldata spender amount).size = 68 := by
  rw [approveCalldata, Abi.size_encodeCall]; rfl

set_option maxHeartbeats 1000000 in
/-- **Dispatch of `approve`**: selector `095ea7b3` reaches pc 200 in 35 steps for 141 gas. -/
theorem reaches_approve : Reaches OzAsset.runtimeCode approveSelector 200 35 141 := by
  sol_dispatch

variable {ctx : Context} {w : World} {tr : TransientStorage} {token caller spender : Address}
  {amount : Word} {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

theorem run_start_approve (hgas : 141 ≤ gas) (k : Nat) :
    run (k + 35) (start ctx w tr (approveCall token caller spender amount gas warmAddrs warmKeys)) =
      run k { start ctx w tr (approveCall token caller spender amount gas warmAddrs warmKeys) with
        frame := { (start ctx w tr
          (approveCall token caller spender amount gas warmAddrs warmKeys)).frame with
          pc := 200, stack := [BitVec.ofNat 256 approveSelector], memory := initMemory,
          gasLeft := (start ctx w tr
            (approveCall token caller spender amount gas warmAddrs warmKeys)).frame.gasLeft -
            141 } } :=
  reaches_approve.run_eq (msg := approveCall token caller spender amount gas warmAddrs warmKeys)
    rfl rfl rfl (selectorOf_approveCalldata spender amount)
    (by rw [show (approveCall token caller spender amount gas warmAddrs warmKeys).data =
      approveCalldata spender amount from rfl, size_approveCalldata]; decide)
    (by rw [show (approveCall token caller spender amount gas warmAddrs warmKeys).data =
      approveCalldata spender amount from rfl, size_approveCalldata]; decide)
    hgas k

set_option maxHeartbeats 10000000 in
/-- **`approve`, success**: nonzero caller and spender; returns `true` with
`allowanceWorld`. -/
theorem approve_ok (hgas : 100000 ≤ gas) (hc : caller ≠ 0) (hs : spender ≠ 0) (k : Nat) :
    ∃ r, run (k + 400)
        (start ctx w tr (approveCall token caller spender amount gas warmAddrs warmKeys)) =
          .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = allowanceWorld ctx.crypto Layout.oz w token caller spender amount := by
  have hc' := ofAddress_ne_zero hc
  have hs' := ofAddress_ne_zero hs
  rw [show k + 400 = (k + 365) + 35 by omega, run_start_approve (by omega)]
  simp only [start, Frame.init, callMsg, approveSelector]
  sol_steps [approveCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]
    kernel_decide
  · simp only [topLevelResult_world]
    rfl

set_option maxHeartbeats 10000000 in
/-- **`approve` from the zero address** reverts (`ERC20InvalidApprover(0)`); world
unchanged. -/
theorem approve_revert_approver (hgas : 100000 ≤ gas) (hc : caller = 0) (k : Nat) :
    ∃ r, run (k + 400)
        (start ctx w tr (approveCall token caller spender amount gas warmAddrs warmKeys)) =
          .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  subst hc
  rw [show k + 400 = (k + 365) + 35 by omega, run_start_approve (by omega)]
  simp only [start, Frame.init, callMsg, approveSelector]
  sol_steps [approveCalldata, ofAddress_zero]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp
  · simp

set_option maxHeartbeats 10000000 in
/-- **`approve` of the zero address** reverts (`ERC20InvalidSpender(0)`); world unchanged. -/
theorem approve_revert_spender (hgas : 100000 ≤ gas) (hc : caller ≠ 0) (hs : spender = 0)
    (k : Nat) :
    ∃ r, run (k + 400)
        (start ctx w tr (approveCall token caller spender amount gas warmAddrs warmKeys)) =
          .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  subst hs
  have hc' := ofAddress_ne_zero hc
  rw [show k + 400 = (k + 365) + 35 by omega, run_start_approve (by omega)]
  simp only [start, Frame.init, callMsg, approveSelector]
  sol_steps [approveCalldata, ofAddress_zero]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp
  · simp

/-! ## The refinement theorem -/

set_option maxHeartbeats 1000000 in
/-- **`approve` refines `Model.ozApprove`** for a top-level call (no EIP-7702 authorizations
or before Prague, gas ≥ 100000, fuel ≥ 400), assuming `AllowanceSlotOk` for the written entry:
on `some s'` it returns `true` with `s'`'s supply and balances, the written allowance and those
in other slots, other accounts untouched; on `none` it reverts with the world unchanged. -/
theorem approve_spec (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 100000 ≤ gas)
    (ha : AllowanceSlotOk ctx.crypto Layout.oz caller spender) (fuel : Nat) (hfuel : 400 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (approveCall token caller spender amount gas warmAddrs warmKeys) = .ok r ∧
      match Model.ozApprove (view ctx.crypto Layout.oz w token) caller spender amount with
      | some s' =>
        r.success = true ∧ r.output = Bytes.ofWord 1 ∧
        (view ctx.crypto Layout.oz r.world token).totalSupply = s'.totalSupply ∧
        (view ctx.crypto Layout.oz r.world token).balanceOf = s'.balanceOf ∧
        (∀ o sp, (o = caller ∧ sp = spender) ∨
            allowanceSlot ctx.crypto Layout.oz o sp ≠
              allowanceSlot ctx.crypto Layout.oz caller spender →
          (view ctx.crypto Layout.oz r.world token).allowance o sp = s'.allowance o sp) ∧
        (∀ b k, b ≠ token → r.world.sload b k = w.sload b k)
      | none => r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 400 := ⟨fuel - 400, by omega⟩
  rw [approveCall, processMessageCall_callMsg hdeleg delegatedAddress?_runtimeCode hpre]
  split
  · rename_i s' hm
    unfold Model.ozApprove at hm
    split at hm
    · cases hm
    rename_i hc0
    split at hm
    · cases hm
    rename_i hs0
    cases hm
    obtain ⟨r, hr, hs, ho, hw⟩ := approve_ok (ctx := ctx) (w := w) (tr := tr) (token := token)
      (amount := amount) (warmAddrs := warmAddrs) (warmKeys := warmKeys) hgas hc0 hs0 k
    obtain ⟨h1, h2, h3, h4⟩ := view_allowanceWorld (w := w) (token := token) (amount := amount) ha
    refine ⟨r, hr, hs, ho, ?_, ?_, ?_, ?_⟩ <;> rw [hw]
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · rename_i hm
    unfold Model.ozApprove at hm
    by_cases hc0 : caller = 0
    · exact approve_revert_approver hgas hc0 k
    by_cases hs0 : spender = 0
    · exact approve_revert_spender hgas hc0 hs0 k
    simp only [hc0, hs0, ↓reduceIte, reduceCtorEq] at hm

end Examples.OpenZeppelin.ERC20
