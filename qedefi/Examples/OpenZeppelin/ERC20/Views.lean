import Examples.OpenZeppelin.ERC20.Basic

/-!
# `OzAsset`'s view functions

`totalSupply()`, `balanceOf(a)`, `allowance(o, s)` and `decimals()` of OpenZeppelin's
`ERC20Mock` for a top-level call: each returns the ABI word of the corresponding field of
`ERC20.view` with `Layout.oz` (`decimals` is 18) and leaves the world unchanged.
-/

namespace Examples.OpenZeppelin.ERC20
open EvmLean EvmLogic EvmLogic.Solidity EvmLogic.Tactic EvmLogic.Solidity.ERC20
open EvmLean.Interpreter EvmLogic.Solidity.Dispatch EvmLean.Bytes Examples.OpenZeppelin.Contracts

variable {ctx : Context} {w : World} {tr : TransientStorage} {token caller : Address}
  {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

/-! ## `totalSupply()` -/

/-- The selector of `totalSupply()`. -/
def totalSupplySelector : Nat := 0x18160ddd

theorem totalSupplySelector_mem : ("totalSupply()", (0x18160ddd : UInt32)) ∈ OzAsset.selectors := by
  decide

/-- Calldata of `totalSupply()`. -/
def totalSupplyCalldata : ByteArray := Abi.encodeCall totalSupplySelector []

set_option maxHeartbeats 1000000 in
/-- **Dispatch of `totalSupply`**: selector `18160ddd` reaches pc 235 in 40 steps for 163 gas. -/
theorem reaches_totalSupply : Reaches OzAsset.runtimeCode totalSupplySelector 235 40 163 := by
  sol_dispatch

set_option maxHeartbeats 10000000 in
/-- **`totalSupply()`** returns the supply word; world unchanged. -/
theorem totalSupply_spec (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 10000 ≤ gas) (fuel : Nat)
    (hfuel : 200 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (callMsg OzAsset.runtimeCode token caller totalSupplyCalldata gas warmAddrs warmKeys) =
          .ok r ∧
      r.success = true ∧
      r.output = Bytes.ofWord (view ctx.crypto Layout.oz w token).totalSupply ∧ r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = (k + 160) + 40 := ⟨fuel - 200, by omega⟩
  rw [processMessageCall_callMsg hdeleg delegatedAddress?_runtimeCode hpre,
    reaches_totalSupply.run_eq rfl rfl rfl
      (by simp only [callMsg, totalSupplyCalldata, Abi.selectorOf_encodeCall]; rfl)
      (by simp only [callMsg, totalSupplyCalldata, Abi.size_encodeCall]; decide)
      (by simp only [callMsg, totalSupplyCalldata, Abi.size_encodeCall]; decide)
      (by simp only [callMsg]; omega)]
  simp only [start, Frame.init, callMsg, totalSupplySelector]
  sol_steps [totalSupplyCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]
    rfl
  · simp only [topLevelResult_world]

/-! ## `balanceOf(a)` -/

/-- The selector of `balanceOf(address)`. -/
def balanceOfSelector : Nat := 0x70a08231

theorem balanceOfSelector_mem : ("balanceOf(address)", (0x70a08231 : UInt32)) ∈ OzAsset.selectors := by
  decide

/-- Calldata of `balanceOf(a)`. -/
def balanceOfCalldata (a : Address) : ByteArray :=
  Abi.encodeCall balanceOfSelector [Word.ofAddress a]

set_option maxHeartbeats 1000000 in
/-- **Dispatch of `balanceOf`**: selector `70a08231` reaches pc 308 in 34 steps for 140 gas. -/
theorem reaches_balanceOf : Reaches OzAsset.runtimeCode balanceOfSelector 308 34 140 := by
  sol_dispatch

set_option maxHeartbeats 10000000 in
/-- **`balanceOf(a)`** returns `a`'s balance word; world unchanged. -/
theorem balanceOf_spec (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 10000 ≤ gas) (a : Address)
    (fuel : Nat) (hfuel : 200 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (callMsg OzAsset.runtimeCode token caller (balanceOfCalldata a) gas warmAddrs warmKeys) =
          .ok r ∧
      r.success = true ∧
      r.output = Bytes.ofWord ((view ctx.crypto Layout.oz w token).balanceOf a) ∧
      r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = (k + 166) + 34 := ⟨fuel - 200, by omega⟩
  rw [processMessageCall_callMsg hdeleg delegatedAddress?_runtimeCode hpre,
    reaches_balanceOf.run_eq rfl rfl rfl
      (by simp only [callMsg, balanceOfCalldata, Abi.selectorOf_encodeCall]; rfl)
      (by simp only [callMsg, balanceOfCalldata, Abi.size_encodeCall]; simp)
      (by simp only [callMsg, balanceOfCalldata, Abi.size_encodeCall]; simp)
      (by simp only [callMsg]; omega)]
  simp only [start, Frame.init, callMsg, balanceOfSelector]
  sol_steps [balanceOfCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]
    rfl
  · simp only [topLevelResult_world]

/-! ## `allowance(o, s)` -/

/-- The selector of `allowance(address,address)`. -/
def allowanceSelector : Nat := 0xdd62ed3e

theorem allowanceSelector_mem :
    ("allowance(address,address)", (0xdd62ed3e : UInt32)) ∈ OzAsset.selectors := by
  decide

/-- Calldata of `allowance(o, s)`. -/
def allowanceCalldata (o s : Address) : ByteArray :=
  Abi.encodeCall allowanceSelector [Word.ofAddress o, Word.ofAddress s]

set_option maxHeartbeats 1000000 in
/-- **Dispatch of `allowance`**: selector `dd62ed3e` reaches pc 394 in 54 steps for 228 gas. -/
theorem reaches_allowance : Reaches OzAsset.runtimeCode allowanceSelector 394 54 228 := by
  sol_dispatch

set_option maxHeartbeats 10000000 in
/-- **`allowance(o, s)`** returns the allowance word; world unchanged. -/
theorem allowance_spec (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 10000 ≤ gas) (o s : Address)
    (fuel : Nat) (hfuel : 200 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (callMsg OzAsset.runtimeCode token caller (allowanceCalldata o s) gas warmAddrs warmKeys) =
          .ok r ∧
      r.success = true ∧
      r.output = Bytes.ofWord ((view ctx.crypto Layout.oz w token).allowance o s) ∧
      r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = (k + 146) + 54 := ⟨fuel - 200, by omega⟩
  rw [processMessageCall_callMsg hdeleg delegatedAddress?_runtimeCode hpre,
    reaches_allowance.run_eq rfl rfl rfl
      (by simp only [callMsg, allowanceCalldata, Abi.selectorOf_encodeCall]; rfl)
      (by simp only [callMsg, allowanceCalldata, Abi.size_encodeCall]; simp)
      (by simp only [callMsg, allowanceCalldata, Abi.size_encodeCall]; simp)
      (by simp only [callMsg]; omega)]
  simp only [start, Frame.init, callMsg, allowanceSelector]
  sol_steps [allowanceCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]
    rfl
  · simp only [topLevelResult_world]

/-! ## `decimals()` -/

/-- The selector of `decimals()`. -/
def decimalsSelector : Nat := 0x313ce567

theorem decimalsSelector_mem : ("decimals()", (0x313ce567 : UInt32)) ∈ OzAsset.selectors := by
  decide

/-- Calldata of `decimals()`. -/
def decimalsCalldata : ByteArray := Abi.encodeCall decimalsSelector []

set_option maxHeartbeats 1000000 in
/-- **Dispatch of `decimals`**: selector `313ce567` reaches pc 272 in 50 steps for 207 gas. -/
theorem reaches_decimals : Reaches OzAsset.runtimeCode decimalsSelector 272 50 207 := by
  sol_dispatch

set_option maxHeartbeats 10000000 in
/-- **`decimals()`** returns 18; world unchanged. -/
theorem decimals_spec (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 10000 ≤ gas) (fuel : Nat)
    (hfuel : 200 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (callMsg OzAsset.runtimeCode token caller decimalsCalldata gas warmAddrs warmKeys) =
          .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 18 ∧ r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = (k + 150) + 50 := ⟨fuel - 200, by omega⟩
  rw [processMessageCall_callMsg hdeleg delegatedAddress?_runtimeCode hpre,
    reaches_decimals.run_eq rfl rfl rfl
      (by simp only [callMsg, decimalsCalldata, Abi.selectorOf_encodeCall]; rfl)
      (by simp only [callMsg, decimalsCalldata, Abi.size_encodeCall]; decide)
      (by simp only [callMsg, decimalsCalldata, Abi.size_encodeCall]; decide)
      (by simp only [callMsg]; omega)]
  simp only [start, Frame.init, callMsg, decimalsSelector]
  sol_steps [decimalsCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]
  · simp only [topLevelResult_world]

end Examples.OpenZeppelin.ERC20
