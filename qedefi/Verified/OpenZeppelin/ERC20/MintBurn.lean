import Verified.OpenZeppelin.ERC20.Basic

/-!
# `OzAsset.mint` and `OzAsset.burn` refine the OpenZeppelin ERC-20 model

`ERC20Mock.mint`/`burn` (public, unrestricted `_mint`/`_burn`): top-level success, the
zero-address reverts (`ERC20InvalidReceiver`, `ERC20InvalidSender`), the supply overflow
(`Panic(0x11)`) and the insufficient balance, and the refinements `mint_spec`/`burn_spec` of
`Model.ozMint`/`Model.ozBurn` through `ERC20.view` with `Layout.oz`. Writing the supply slot
needs `SupplySlotOk` besides `BalanceSlotOk` for the written balance.
-/

section

namespace Verified.OpenZeppelin.ERC20
open EvmLean EvmLogic EvmLogic.Solidity EvmLogic.Tactic EvmLogic.Solidity.ERC20
open EvmLean.Interpreter EvmLogic.Solidity.Dispatch EvmLean.Bytes Verified.OpenZeppelin.Contracts

/-- The selector of `mint(address,uint256)`. -/
def mintSelector : Nat := 0x40c10f19

theorem mintSelector_mem :
    ("mint(address,uint256)", (0x40c10f19 : UInt32)) ∈ OzAsset.selectors := by
  decide

/-- Calldata of `mint(dst, amount)`. -/
def mintCalldata (dst : Address) (amount : Word) : ByteArray :=
  Abi.encodeCall mintSelector [Word.ofAddress dst, amount]

/-- A top-level call of `mint(dst, amount)` on the token at `token`. -/
abbrev mintCall (token caller dst : Address) (amount : Word) (gas : Nat)
    (warmAddrs : AddressSet) (warmKeys : StorageKeySet) : Message :=
  callMsg OzAsset.runtimeCode token caller (mintCalldata dst amount) gas warmAddrs warmKeys

theorem selectorOf_mintCalldata (dst : Address) (amount : Word) :
    Abi.selectorOf (mintCalldata dst amount) = mintSelector := by
  rw [mintCalldata, Abi.selectorOf_encodeCall]; rfl

theorem size_mintCalldata (dst : Address) (amount : Word) :
    (mintCalldata dst amount).size = 68 := by
  rw [mintCalldata, Abi.size_encodeCall]; rfl

set_option maxHeartbeats 1000000 in
/-- **Dispatch of `mint`**: selector `40c10f19` reaches pc 287 in 29 steps for 118 gas. -/
theorem reaches_mint : Reaches OzAsset.runtimeCode mintSelector 287 29 118 := by
  sol_dispatch

variable {ctx : Context} {w : World} {tr : TransientStorage} {token caller dst : Address}
  {amount : Word} {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

theorem run_start_mint (hgas : 118 ≤ gas) (k : Nat) :
    run (k + 29) (start ctx w tr (mintCall token caller dst amount gas warmAddrs warmKeys)) =
      run k { start ctx w tr (mintCall token caller dst amount gas warmAddrs warmKeys) with
        frame := { (start ctx w tr
          (mintCall token caller dst amount gas warmAddrs warmKeys)).frame with
          pc := 287, stack := [BitVec.ofNat 256 mintSelector], memory := initMemory,
          gasLeft := (start ctx w tr
            (mintCall token caller dst amount gas warmAddrs warmKeys)).frame.gasLeft -
            118 } } :=
  reaches_mint.run_eq (msg := mintCall token caller dst amount gas warmAddrs warmKeys)
    rfl rfl rfl (selectorOf_mintCalldata dst amount)
    (by rw [show (mintCall token caller dst amount gas warmAddrs warmKeys).data =
      mintCalldata dst amount from rfl, size_mintCalldata]; decide)
    (by rw [show (mintCall token caller dst amount gas warmAddrs warmKeys).data =
      mintCalldata dst amount from rfl, size_mintCalldata]; decide)
    hgas k

set_option maxHeartbeats 10000000 in
/-- **`mint`, success**: nonzero recipient, `totalSupply + amount` does not overflow; returns
nothing with `mintWorld`. -/
theorem mint_ok (hgas : 100000 ≤ gas) (hd : dst ≠ 0)
    (hov : (view ctx.crypto Layout.oz w token).totalSupply.toNat + amount.toNat < 2 ^ 256)
    (k : Nat) :
    ∃ r, run (k + 400)
        (start ctx w tr (mintCall token caller dst amount gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = .empty ∧
      r.world = mintWorld ctx.crypto Layout.oz w token dst amount := by
  have hov' : (w.sload token (BitVec.ofNat 256 2)).toNat + amount.toNat < 2 ^ 256 := hov
  have hd' := ofAddress_ne_zero hd
  rw [show k + 400 = (k + 371) + 29 by omega, run_start_mint (by omega)]
  simp only [start, Frame.init, callMsg, mintSelector]
  sol_steps [mintCalldata]
  simp only [gt_add_self_eq_zero hov']
  sol_steps [mintCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]
  · simp only [topLevelResult_world]
    rfl

set_option maxHeartbeats 10000000 in
/-- **`mint` to the zero address** reverts (`ERC20InvalidReceiver(0)`); world unchanged. -/
theorem mint_revert_receiver (hgas : 100000 ≤ gas) (hd : dst = 0) (k : Nat) :
    ∃ r, run (k + 400)
        (start ctx w tr (mintCall token caller dst amount gas warmAddrs warmKeys)) = .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  subst hd
  rw [show k + 400 = (k + 371) + 29 by omega, run_start_mint (by omega)]
  simp only [start, Frame.init, callMsg, mintSelector]
  sol_steps [mintCalldata, ofAddress_zero]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp
  · simp

set_option maxHeartbeats 10000000 in
/-- **`mint`, supply overflow**: the checked addition panics; world unchanged. -/
theorem mint_revert_overflow (hgas : 100000 ≤ gas) (hd : dst ≠ 0)
    (hov : 2 ^ 256 ≤ (view ctx.crypto Layout.oz w token).totalSupply.toNat + amount.toNat)
    (k : Nat) :
    ∃ r, run (k + 400)
        (start ctx w tr (mintCall token caller dst amount gas warmAddrs warmKeys)) = .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  have hov' : 2 ^ 256 ≤ (w.sload token (BitVec.ofNat 256 2)).toNat + amount.toNat := hov
  have hd' := ofAddress_ne_zero hd
  rw [show k + 400 = (k + 371) + 29 by omega, run_start_mint (by omega)]
  simp only [start, Frame.init, callMsg, mintSelector]
  sol_steps [mintCalldata]
  simp only [gt_add_self_eq_one hov']
  sol_steps [mintCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp
  · simp

set_option maxHeartbeats 1000000 in
/-- **`mint` refines `Model.ozMint`** for a top-level call by any caller (no EIP-7702
authorizations or before Prague, gas ≥ 100000, fuel ≥ 400), assuming `BalanceSlotOk` for `dst`
and `SupplySlotOk`: on `some s'` it succeeds with `s'`'s supply, balances and the allowances in
unwritten slots, other accounts untouched; on `none` it reverts with the world unchanged. -/
theorem mint_spec (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 100000 ≤ gas)
    (hdo : BalanceSlotOk ctx.crypto Layout.oz dst) (hk : SupplySlotOk ctx.crypto Layout.oz)
    (fuel : Nat) (hfuel : 400 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (mintCall token caller dst amount gas warmAddrs warmKeys) = .ok r ∧
      match Model.ozMint (view ctx.crypto Layout.oz w token) dst amount with
      | some s' =>
        r.success = true ∧ r.output = .empty ∧
        (view ctx.crypto Layout.oz r.world token).totalSupply = s'.totalSupply ∧
        (view ctx.crypto Layout.oz r.world token).balanceOf = s'.balanceOf ∧
        (∀ o sp, allowanceSlot ctx.crypto Layout.oz o sp ≠ Layout.oz.totalSupply →
          allowanceSlot ctx.crypto Layout.oz o sp ≠ balanceSlot ctx.crypto Layout.oz dst →
          (view ctx.crypto Layout.oz r.world token).allowance o sp = s'.allowance o sp) ∧
        (∀ b k, b ≠ token → r.world.sload b k = w.sload b k)
      | none => r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 400 := ⟨fuel - 400, by omega⟩
  rw [mintCall, processMessageCall_callMsg hdeleg delegatedAddress?_runtimeCode hpre]
  split
  · rename_i s' hm
    have hm' := hm
    unfold Model.ozMint at hm'
    split at hm'
    · cases hm'
    rename_i hd0
    split at hm'
    · rename_i hov
      obtain ⟨r, hr, hs, ho, hw⟩ := mint_ok (tr := tr) (caller := caller) (warmAddrs := warmAddrs)
        (warmKeys := warmKeys) hgas hd0 hov k
      obtain ⟨h1, h2, h3, h4⟩ := view_mintWorld hdo hk hm
      refine ⟨r, hr, hs, ho, ?_, ?_, ?_, ?_⟩ <;> rw [hw]
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    · cases hm'
  · rename_i hm
    unfold Model.ozMint at hm
    by_cases hd0 : dst = 0
    · exact mint_revert_receiver hgas hd0 k
    simp only [hd0, ↓reduceIte] at hm
    split at hm
    · cases hm
    · exact mint_revert_overflow hgas hd0 (by omega) k

end Verified.OpenZeppelin.ERC20

end

section

namespace Verified.OpenZeppelin.ERC20
open EvmLean EvmLogic EvmLogic.Solidity EvmLogic.Tactic EvmLogic.Solidity.ERC20
open EvmLean.Interpreter EvmLogic.Solidity.Dispatch EvmLean.Bytes Verified.OpenZeppelin.Contracts

/-- The selector of `burn(address,uint256)`. -/
def burnSelector : Nat := 0x9dc29fac

theorem burnSelector_mem :
    ("burn(address,uint256)", (0x9dc29fac : UInt32)) ∈ OzAsset.selectors := by
  decide

/-- Calldata of `burn(src, amount)`. -/
def burnCalldata (src : Address) (amount : Word) : ByteArray :=
  Abi.encodeCall burnSelector [Word.ofAddress src, amount]

/-- A top-level call of `burn(src, amount)` on the token at `token`. -/
abbrev burnCall (token caller src : Address) (amount : Word) (gas : Nat)
    (warmAddrs : AddressSet) (warmKeys : StorageKeySet) : Message :=
  callMsg OzAsset.runtimeCode token caller (burnCalldata src amount) gas warmAddrs warmKeys

theorem selectorOf_burnCalldata (src : Address) (amount : Word) :
    Abi.selectorOf (burnCalldata src amount) = burnSelector := by
  rw [burnCalldata, Abi.selectorOf_encodeCall]; rfl

theorem size_burnCalldata (src : Address) (amount : Word) :
    (burnCalldata src amount).size = 68 := by
  rw [burnCalldata, Abi.size_encodeCall]; rfl

set_option maxHeartbeats 1000000 in
/-- **Dispatch of `burn`**: selector `9dc29fac` reaches pc 356 in 44 steps for 184 gas. -/
theorem reaches_burn : Reaches OzAsset.runtimeCode burnSelector 356 44 184 := by
  sol_dispatch

variable {ctx : Context} {w : World} {tr : TransientStorage} {token caller src : Address}
  {amount : Word} {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

theorem run_start_burn (hgas : 184 ≤ gas) (k : Nat) :
    run (k + 44) (start ctx w tr (burnCall token caller src amount gas warmAddrs warmKeys)) =
      run k { start ctx w tr (burnCall token caller src amount gas warmAddrs warmKeys) with
        frame := { (start ctx w tr
          (burnCall token caller src amount gas warmAddrs warmKeys)).frame with
          pc := 356, stack := [BitVec.ofNat 256 burnSelector], memory := initMemory,
          gasLeft := (start ctx w tr
            (burnCall token caller src amount gas warmAddrs warmKeys)).frame.gasLeft -
            184 } } :=
  reaches_burn.run_eq (msg := burnCall token caller src amount gas warmAddrs warmKeys)
    rfl rfl rfl (selectorOf_burnCalldata src amount)
    (by rw [show (burnCall token caller src amount gas warmAddrs warmKeys).data =
      burnCalldata src amount from rfl, size_burnCalldata]; decide)
    (by rw [show (burnCall token caller src amount gas warmAddrs warmKeys).data =
      burnCalldata src amount from rfl, size_burnCalldata]; decide)
    hgas k

set_option maxHeartbeats 10000000 in
/-- **`burn`, success**: nonzero `src`, `amount ≤ balanceOf[src]`; returns nothing with
`burnWorld`. -/
theorem burn_ok (hgas : 100000 ≤ gas) (hs : src ≠ 0)
    (hbal : amount.toNat ≤ ((view ctx.crypto Layout.oz w token).balanceOf src).toNat)
    (k : Nat) :
    ∃ r, run (k + 400)
        (start ctx w tr (burnCall token caller src amount gas warmAddrs warmKeys)) = .ok r ∧
      r.success = true ∧ r.output = .empty ∧
      r.world = burnWorld ctx.crypto Layout.oz w token src amount := by
  have hbal' : amount.toNat ≤
      (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
        ofWord (BitVec.ofNat 256 0)))).toNat := hbal
  have hs' := ofAddress_ne_zero hs
  rw [show k + 400 = (k + 356) + 44 by omega, run_start_burn (by omega)]
  simp only [start, Frame.init, callMsg, burnSelector]
  sol_steps [burnCalldata]
  simp only [(Word.lt_eq_zero_iff _ _).2 hbal']
  sol_steps [burnCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]
  · simp only [topLevelResult_world]
    rfl

set_option maxHeartbeats 10000000 in
/-- **`burn` from the zero address** reverts (`ERC20InvalidSender(0)`); world unchanged. -/
theorem burn_revert_sender (hgas : 100000 ≤ gas) (hs : src = 0) (k : Nat) :
    ∃ r, run (k + 400)
        (start ctx w tr (burnCall token caller src amount gas warmAddrs warmKeys)) = .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  subst hs
  rw [show k + 400 = (k + 356) + 44 by omega, run_start_burn (by omega)]
  simp only [start, Frame.init, callMsg, burnSelector]
  sol_steps [burnCalldata, ofAddress_zero]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp
  · simp

set_option maxHeartbeats 10000000 in
/-- **`burn`, insufficient balance**: reverts (`ERC20InsufficientBalance`); world unchanged. -/
theorem burn_revert_balance (hgas : 100000 ≤ gas) (hs : src ≠ 0)
    (hbal : ((view ctx.crypto Layout.oz w token).balanceOf src).toNat < amount.toNat)
    (k : Nat) :
    ∃ r, run (k + 400)
        (start ctx w tr (burnCall token caller src amount gas warmAddrs warmKeys)) = .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  have hbal' : (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
      ofWord (BitVec.ofNat 256 0)))).toNat < amount.toNat := hbal
  have hs' := ofAddress_ne_zero hs
  rw [show k + 400 = (k + 356) + 44 by omega, run_start_burn (by omega)]
  simp only [start, Frame.init, callMsg, burnSelector]
  sol_steps [burnCalldata]
  simp only [(Word.lt_eq_one_iff _ _).2 hbal']
  sol_steps [burnCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp
  · simp

set_option maxHeartbeats 1000000 in
/-- **`burn` refines `Model.ozBurn`** for a top-level call by any caller (no EIP-7702
authorizations or before Prague, gas ≥ 100000, fuel ≥ 400), assuming `BalanceSlotOk` for `src`
and `SupplySlotOk`: on `some s'` it succeeds with `s'`'s supply, balances and the allowances in
unwritten slots, other accounts untouched; on `none` it reverts with the world unchanged. -/
theorem burn_spec (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 100000 ≤ gas)
    (hso : BalanceSlotOk ctx.crypto Layout.oz src) (hk : SupplySlotOk ctx.crypto Layout.oz)
    (fuel : Nat) (hfuel : 400 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (burnCall token caller src amount gas warmAddrs warmKeys) = .ok r ∧
      match Model.ozBurn (view ctx.crypto Layout.oz w token) src amount with
      | some s' =>
        r.success = true ∧ r.output = .empty ∧
        (view ctx.crypto Layout.oz r.world token).totalSupply = s'.totalSupply ∧
        (view ctx.crypto Layout.oz r.world token).balanceOf = s'.balanceOf ∧
        (∀ o sp, allowanceSlot ctx.crypto Layout.oz o sp ≠ Layout.oz.totalSupply →
          allowanceSlot ctx.crypto Layout.oz o sp ≠ balanceSlot ctx.crypto Layout.oz src →
          (view ctx.crypto Layout.oz r.world token).allowance o sp = s'.allowance o sp) ∧
        (∀ b k, b ≠ token → r.world.sload b k = w.sload b k)
      | none => r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 400 := ⟨fuel - 400, by omega⟩
  rw [burnCall, processMessageCall_callMsg hdeleg delegatedAddress?_runtimeCode hpre]
  split
  · rename_i s' hm
    have hm' := hm
    unfold Model.ozBurn at hm'
    split at hm'
    · cases hm'
    rename_i hs0
    split at hm'
    · rename_i hbal
      obtain ⟨r, hr, hs, ho, hw⟩ := burn_ok (tr := tr) (caller := caller) (warmAddrs := warmAddrs)
        (warmKeys := warmKeys) hgas hs0 hbal k
      obtain ⟨h1, h2, h3, h4⟩ := view_burnWorld hso hk hm
      refine ⟨r, hr, hs, ho, ?_, ?_, ?_, ?_⟩ <;> rw [hw]
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    · cases hm'
  · rename_i hm
    unfold Model.ozBurn at hm
    by_cases hs0 : src = 0
    · exact burn_revert_sender hgas hs0 k
    simp only [hs0, ↓reduceIte] at hm
    split at hm
    · cases hm
    · exact burn_revert_balance hgas hs0 (by omega) k

end Verified.OpenZeppelin.ERC20

end
