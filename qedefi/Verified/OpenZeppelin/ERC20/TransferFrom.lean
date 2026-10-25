import Verified.OpenZeppelin.ERC20.Basic

/-!
# `OzAsset.transferFrom` refines the OpenZeppelin ERC-20 model

`transferFrom(address,address,uint256)` of OpenZeppelin's `ERC20Mock`, from `caller` (the
spender): `_spendAllowance(src, caller, amount)` then `_transfer(src, dst, amount)`. On an
infinite allowance (`type(uint256).max`) the spend does nothing (`transferFrom_ok_max`,
`transferFrom_revert_max`); otherwise it is a checked subtraction written back by `_approve`,
whose zero-address checks apply (`transferFrom_ok`, `transferFrom_revert`). The refinement
`transferFrom_spec` of `Model.ozTransferFrom` goes through `ERC20.view` with `Layout.oz`.
-/

namespace Verified.OpenZeppelin.ERC20
open EvmLean EvmLogic EvmLogic.Solidity EvmLogic.Tactic EvmLogic.Solidity.ERC20
open EvmLean.Interpreter EvmLogic.Solidity.Dispatch EvmLean.Bytes Verified.OpenZeppelin.Contracts

/-- The selector of `transferFrom(address,address,uint256)`. -/
def transferFromSelector : Nat := 0x23b872dd

theorem transferFromSelector_mem :
    ("transferFrom(address,address,uint256)", (0x23b872dd : UInt32)) ∈ OzAsset.selectors := by
  decide

/-- Calldata of `transferFrom(src, dst, amount)`. -/
def transferFromCalldata (src dst : Address) (amount : Word) : ByteArray :=
  Abi.encodeCall transferFromSelector [Word.ofAddress src, Word.ofAddress dst, amount]

/-- A top-level call of `transferFrom(src, dst, amount)` on the token at `token`. -/
abbrev transferFromCall (token caller src dst : Address) (amount : Word) (gas : Nat)
    (warmAddrs : AddressSet) (warmKeys : StorageKeySet) : Message :=
  callMsg OzAsset.runtimeCode token caller (transferFromCalldata src dst amount) gas warmAddrs
    warmKeys

theorem selectorOf_transferFromCalldata (src dst : Address) (amount : Word) :
    Abi.selectorOf (transferFromCalldata src dst amount) = transferFromSelector := by
  rw [transferFromCalldata, Abi.selectorOf_encodeCall]; rfl

theorem size_transferFromCalldata (src dst : Address) (amount : Word) :
    (transferFromCalldata src dst amount).size = 100 := by
  rw [transferFromCalldata, Abi.size_encodeCall]; rfl

set_option maxHeartbeats 1000000 in
/-- **Dispatch of `transferFrom`**: selector `23b872dd` reaches pc 253 in 45 steps for 185
gas. -/
theorem reaches_transferFrom : Reaches OzAsset.runtimeCode transferFromSelector 253 45 185 := by
  sol_dispatch

variable {ctx : Context} {w : World} {tr : TransientStorage} {token caller src dst : Address}
  {amount : Word} {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

theorem run_start_transferFrom (hgas : 185 ≤ gas) (k : Nat) :
    run (k + 45)
        (start ctx w tr (transferFromCall token caller src dst amount gas warmAddrs warmKeys)) =
      run k { start ctx w tr (transferFromCall token caller src dst amount gas warmAddrs warmKeys)
        with frame := { (start ctx w tr
          (transferFromCall token caller src dst amount gas warmAddrs warmKeys)).frame with
          pc := 253, stack := [BitVec.ofNat 256 transferFromSelector], memory := initMemory,
          gasLeft := (start ctx w tr
            (transferFromCall token caller src dst amount gas warmAddrs warmKeys)).frame.gasLeft -
            185 } } :=
  reaches_transferFrom.run_eq
    (msg := transferFromCall token caller src dst amount gas warmAddrs warmKeys)
    rfl rfl rfl (selectorOf_transferFromCalldata src dst amount)
    (by rw [show (transferFromCall token caller src dst amount gas warmAddrs warmKeys).data =
      transferFromCalldata src dst amount from rfl, size_transferFromCalldata]; decide)
    (by rw [show (transferFromCall token caller src dst amount gas warmAddrs warmKeys).data =
      transferFromCalldata src dst amount from rfl, size_transferFromCalldata]; decide)
    hgas k

/-! ## Infinite allowance -/

set_option maxHeartbeats 10000000 in
/-- **`transferFrom`, infinite allowance, success**: nonzero `src` and `dst`,
`amount ≤ balanceOf[src]`; returns `true` with `ozTransferFromWorld` (the allowance is not
written). -/
theorem transferFrom_ok_max (hgas : 100000 ≤ gas)
    (hmax : (view ctx.crypto Layout.oz w token).allowance src caller = maxWord)
    (hs : src ≠ 0) (hd : dst ≠ 0)
    (hbal : amount.toNat ≤ ((view ctx.crypto Layout.oz w token).balanceOf src).toNat)
    (k : Nat) :
    ∃ r, run (k + 600)
        (start ctx w tr (transferFromCall token caller src dst amount gas warmAddrs warmKeys)) =
          .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = ozTransferFromWorld ctx.crypto Layout.oz w token caller src dst amount := by
  have hmax' : w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord 1#256)))) = maxWord :=
    hmax
  have hbal' : amount.toNat ≤
      (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
        ofWord (BitVec.ofNat 256 0)))).toNat := hbal
  have hs' := ofAddress_ne_zero hs
  have hd' := ofAddress_ne_zero hd
  rw [show k + 600 = (k + 555) + 45 by omega, run_start_transferFrom (by omega)]
  simp only [start, Frame.init, callMsg, transferFromSelector]
  sol_steps [transferFromCalldata]
  simp only [lt_maxWord_of_eq hmax']
  sol_steps [transferFromCalldata]
  simp only [(Word.lt_eq_zero_iff _ _).2 hbal']
  sol_steps [transferFromCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]
    kernel_decide
  · simp only [topLevelResult_world, ozTransferFromWorld, ozSpendWorld]
    split
    · rfl
    · rename_i h; exact absurd hmax h

set_option maxHeartbeats 10000000 in
/-- **`transferFrom`, infinite allowance, revert**: when `_transfer(src, dst, amount)` fails
(`ERC20InvalidSender`, `ERC20InvalidReceiver`, `ERC20InsufficientBalance`); world unchanged. -/
theorem transferFrom_revert_max (hgas : 100000 ≤ gas)
    (hmax : (view ctx.crypto Layout.oz w token).allowance src caller = maxWord)
    (hm : Model.ozTransfer (view ctx.crypto Layout.oz w token) src dst amount = none)
    (k : Nat) :
    ∃ r, run (k + 600)
        (start ctx w tr (transferFromCall token caller src dst amount gas warmAddrs warmKeys)) =
          .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  have hmax' : w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord 1#256)))) = maxWord :=
    hmax
  unfold Model.ozTransfer at hm
  rw [show k + 600 = (k + 555) + 45 by omega, run_start_transferFrom (by omega)]
  simp only [start, Frame.init, callMsg, transferFromSelector]
  by_cases hs : src = 0
  · subst hs
    have hmax0 : w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress 0#160) ++ ofWord 1#256)))) =
          maxWord := hmax'
    sol_steps [transferFromCalldata]
    simp only [lt_maxWord_of_eq hmax0]
    sol_steps [transferFromCalldata]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · rw [topLevelResult_success]; rfl
    · simp
    · simp
  have hs' := ofAddress_ne_zero hs
  by_cases hd : dst = 0
  · subst hd
    sol_steps [transferFromCalldata]
    simp only [lt_maxWord_of_eq hmax']
    sol_steps [transferFromCalldata]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · rw [topLevelResult_success]; rfl
    · simp
    · simp
  have hd' := ofAddress_ne_zero hd
  simp only [hs, hd, ↓reduceIte] at hm
  have hbal : ((view ctx.crypto Layout.oz w token).balanceOf src).toNat < amount.toNat := by
    unfold Model.transfer at hm
    split at hm
    · cases hm
    · omega
  have hbal' : (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++
      ofWord (BitVec.ofNat 256 0)))).toNat < amount.toNat := hbal
  sol_steps [transferFromCalldata]
  simp only [lt_maxWord_of_eq hmax']
  sol_steps [transferFromCalldata]
  simp only [(Word.lt_eq_one_iff _ _).2 hbal']
  sol_steps [transferFromCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp
  · simp

/-! ## Finite allowance -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
/-- **`transferFrom`, finite allowance, success**: `amount ≤ allowance[src][caller]`, nonzero
`src`, `caller`, `dst`, `amount ≤ balanceOf[src]`; returns `true` with `ozTransferFromWorld`.
`AllowanceSlotOk` makes the balance read after the allowance write the original one. -/
theorem transferFrom_ok (hgas : 100000 ≤ gas)
    (ha : AllowanceSlotOk ctx.crypto Layout.oz src caller)
    (hmax : (view ctx.crypto Layout.oz w token).allowance src caller ≠ maxWord)
    (hle : amount.toNat ≤ ((view ctx.crypto Layout.oz w token).allowance src caller).toNat)
    (hs : src ≠ 0) (hc : caller ≠ 0) (hd : dst ≠ 0)
    (hbal : amount.toNat ≤ ((view ctx.crypto Layout.oz w token).balanceOf src).toNat)
    (k : Nat) :
    ∃ r, run (k + 600)
        (start ctx w tr (transferFromCall token caller src dst amount gas warmAddrs warmKeys)) =
          .ok r ∧
      r.success = true ∧ r.output = Bytes.ofWord 1 ∧
      r.world = ozTransferFromWorld ctx.crypto Layout.oz w token caller src dst amount := by
  have hmax' : w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord 1#256)))) ≠ maxWord :=
    hmax
  have hle' : amount.toNat ≤ (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord 1#256))))).toNat := hle
  have hbal₁ : amount.toNat ≤
      ((allowanceWorld ctx.crypto Layout.oz w token src caller
        (w.sload token (allowanceSlot ctx.crypto Layout.oz src caller) - amount)).sload token
          (balanceSlot ctx.crypto Layout.oz src)).toNat := by
    rw [allowanceWorld, World.sload_sstore_ne_key _ _ _ (balanceSlot_ne_allowanceSlot ha src)]
    exact hbal
  have hbal' : amount.toNat ≤
      ((w.sstore token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
          ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord 1#256))))
        (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
          ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord 1#256)))) -
            amount)).sload token
        (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord 0#256))).toNat := hbal₁
  have hs' := ofAddress_ne_zero hs
  have hc' := ofAddress_ne_zero hc
  have hd' := ofAddress_ne_zero hd
  rw [show k + 600 = (k + 555) + 45 by omega, run_start_transferFrom (by omega)]
  simp only [start, Frame.init, callMsg, transferFromSelector]
  sol_steps [transferFromCalldata]
  simp only [lt_maxWord_of_ne hmax']
  sol_steps [transferFromCalldata]
  simp only [(Word.lt_eq_zero_iff _ _).2 hle']
  sol_steps [transferFromCalldata]
  simp only [(Word.lt_eq_zero_iff _ _).2 hbal']
  sol_steps [transferFromCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp only [topLevelResult_output]
    kernel_decide
  · simp only [topLevelResult_world, ozTransferFromWorld, ozSpendWorld]
    split
    · rename_i h; exact absurd h hmax
    · rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
/-- **`transferFrom`, finite allowance, revert**: when the spend fails
(`ERC20InsufficientAllowance`, `ERC20InvalidApprover`, `ERC20InvalidSpender`) or the transfer
does (`ERC20InvalidReceiver`, `ERC20InsufficientBalance`); world unchanged. -/
theorem transferFrom_revert (hgas : 100000 ≤ gas)
    (ha : AllowanceSlotOk ctx.crypto Layout.oz src caller)
    (hmax : (view ctx.crypto Layout.oz w token).allowance src caller ≠ maxWord)
    (hm : Model.ozTransferFrom (view ctx.crypto Layout.oz w token) caller src dst amount = none)
    (k : Nat) :
    ∃ r, run (k + 600)
        (start ctx w tr (transferFromCall token caller src dst amount gas warmAddrs warmKeys)) =
          .ok r ∧
      r.success = false ∧ r.reverted = true ∧ r.world = w := by
  have hmax' : w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord 1#256)))) ≠ maxWord :=
    hmax
  unfold Model.ozTransferFrom Model.ozSpend at hm
  simp only [hmax, ↓reduceIte] at hm
  rw [show k + 600 = (k + 555) + 45 by omega, run_start_transferFrom (by omega)]
  simp only [start, Frame.init, callMsg, transferFromSelector]
  rcases Nat.lt_or_ge ((view ctx.crypto Layout.oz w token).allowance src caller).toNat
    amount.toNat with hlt | hle
  · have hlt' : (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord 1#256))))).toNat <
          amount.toNat := hlt
    sol_steps [transferFromCalldata]
    simp only [lt_maxWord_of_ne hmax']
    sol_steps [transferFromCalldata]
    simp only [(Word.lt_eq_one_iff _ _).2 hlt']
    sol_steps [transferFromCalldata]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · rw [topLevelResult_success]; rfl
    · simp
    · simp
  have hle' : amount.toNat ≤ (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
      ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord 1#256))))).toNat := hle
  simp only [show amount.toNat ≤ ((view ctx.crypto Layout.oz w token).allowance src caller).toNat
    from hle, ↓reduceIte, Model.ozApprove] at hm
  by_cases hs : src = 0
  · subst hs
    have hmax0 : w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress 0#160) ++ ofWord 1#256)))) ≠
          maxWord := hmax'
    have hle0 : amount.toNat ≤ (w.sload token (ctx.crypto.keccak256
        (ofWord (Word.ofAddress caller) ++ ofWord (ctx.crypto.keccak256
          (ofWord (Word.ofAddress 0#160) ++ ofWord 1#256))))).toNat := hle'
    sol_steps [transferFromCalldata]
    simp only [lt_maxWord_of_ne hmax0]
    sol_steps [transferFromCalldata]
    simp only [(Word.lt_eq_zero_iff _ _).2 hle0]
    sol_steps [transferFromCalldata]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · rw [topLevelResult_success]; rfl
    · simp
    · simp
  have hs' := ofAddress_ne_zero hs
  by_cases hc : caller = 0
  · subst hc
    have hmax0 : w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress 0#160) ++
        ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord 1#256)))) ≠
          maxWord := hmax'
    have hle0 : amount.toNat ≤ (w.sload token (ctx.crypto.keccak256
        (ofWord (Word.ofAddress 0#160) ++ ofWord (ctx.crypto.keccak256
          (ofWord (Word.ofAddress src) ++ ofWord 1#256))))).toNat := hle'
    sol_steps [transferFromCalldata]
    simp only [lt_maxWord_of_ne hmax0]
    sol_steps [transferFromCalldata]
    simp only [(Word.lt_eq_zero_iff _ _).2 hle0]
    sol_steps [transferFromCalldata]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · rw [topLevelResult_success]; rfl
    · simp
    · simp
  have hc' := ofAddress_ne_zero hc
  simp only [hs, hc, ↓reduceIte, Option.bind_some, Model.ozTransfer] at hm
  by_cases hd : dst = 0
  · subst hd
    sol_steps [transferFromCalldata]
    simp only [lt_maxWord_of_ne hmax']
    sol_steps [transferFromCalldata]
    simp only [(Word.lt_eq_zero_iff _ _).2 hle']
    sol_steps [transferFromCalldata]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · rw [topLevelResult_success]; rfl
    · simp
    · simp
  have hd' := ofAddress_ne_zero hd
  simp only [hd, ↓reduceIte] at hm
  have hbal : ((view ctx.crypto Layout.oz w token).balanceOf src).toNat < amount.toNat := by
    unfold Model.transfer at hm
    split at hm
    · cases hm
    · rename_i h
      simpa only [Model.approve, State.setAllowance, Nat.not_le] using h
  have hbal₁ : ((allowanceWorld ctx.crypto Layout.oz w token src caller
      (w.sload token (allowanceSlot ctx.crypto Layout.oz src caller) - amount)).sload token
        (balanceSlot ctx.crypto Layout.oz src)).toNat < amount.toNat := by
    rw [allowanceWorld, World.sload_sstore_ne_key _ _ _ (balanceSlot_ne_allowanceSlot ha src)]
    exact hbal
  have hbal' : ((w.sstore token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
          ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord 1#256))))
        (w.sload token (ctx.crypto.keccak256 (ofWord (Word.ofAddress caller) ++
          ofWord (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord 1#256)))) -
            amount)).sload token
        (ctx.crypto.keccak256 (ofWord (Word.ofAddress src) ++ ofWord 0#256))).toNat <
          amount.toNat := hbal₁
  sol_steps [transferFromCalldata]
  simp only [lt_maxWord_of_ne hmax']
  sol_steps [transferFromCalldata]
  simp only [(Word.lt_eq_zero_iff _ _).2 hle']
  sol_steps [transferFromCalldata]
  simp only [(Word.lt_eq_one_iff _ _).2 hbal']
  sol_steps [transferFromCalldata]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [topLevelResult_success]; rfl
  · simp
  · simp

/-! ## The refinement theorem -/

set_option maxHeartbeats 1000000 in
/-- **`transferFrom` refines `Model.ozTransferFrom`** for a top-level call from the spender
`caller` (no EIP-7702 authorizations or before Prague, gas ≥ 100000, fuel ≥ 600), assuming
`BalanceSlotOk` for `src`, `dst` and `AllowanceSlotOk` for `allowance[src][caller]`: on
`some s'` it returns `true` with `s'`'s supply, balances and the allowances in unwritten
slots, other accounts untouched; on `none` it reverts with the world unchanged. -/
theorem transferFrom_spec (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 100000 ≤ gas)
    (hso : BalanceSlotOk ctx.crypto Layout.oz src) (hdo : BalanceSlotOk ctx.crypto Layout.oz dst)
    (ha : AllowanceSlotOk ctx.crypto Layout.oz src caller) (fuel : Nat) (hfuel : 600 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (transferFromCall token caller src dst amount gas warmAddrs warmKeys) = .ok r ∧
      match Model.ozTransferFrom (view ctx.crypto Layout.oz w token) caller src dst amount with
      | some s' =>
        r.success = true ∧ r.output = Bytes.ofWord 1 ∧
        (view ctx.crypto Layout.oz r.world token).totalSupply = s'.totalSupply ∧
        (view ctx.crypto Layout.oz r.world token).balanceOf = s'.balanceOf ∧
        (∀ o sp, allowanceSlot ctx.crypto Layout.oz o sp ≠ balanceSlot ctx.crypto Layout.oz src →
          allowanceSlot ctx.crypto Layout.oz o sp ≠ balanceSlot ctx.crypto Layout.oz dst →
          (o = src ∧ sp = caller) ∨
            allowanceSlot ctx.crypto Layout.oz o sp ≠
              allowanceSlot ctx.crypto Layout.oz src caller →
          (view ctx.crypto Layout.oz r.world token).allowance o sp = s'.allowance o sp) ∧
        (∀ b k, b ≠ token → r.world.sload b k = w.sload b k)
      | none => r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 600 := ⟨fuel - 600, by omega⟩
  rw [transferFromCall, processMessageCall_callMsg hdeleg delegatedAddress?_runtimeCode hpre]
  split
  · rename_i s' hm
    obtain ⟨h1, h2, h3, h4⟩ := view_ozTransferFromWorld hso hdo ha hm
    have hm' := hm
    unfold Model.ozTransferFrom at hm'
    obtain ⟨s₁, hs₁, ht⟩ := Option.bind_eq_some_iff.1 hm'
    have hb₁ : s₁.balanceOf = (view ctx.crypto Layout.oz w token).balanceOf := by
      unfold Model.ozSpend at hs₁
      split at hs₁
      · cases hs₁; rfl
      split at hs₁
      · unfold Model.ozApprove at hs₁
        split at hs₁
        · cases hs₁
        split at hs₁
        · cases hs₁
        cases hs₁; rfl
      · cases hs₁
    unfold Model.ozTransfer at ht
    split at ht
    · cases ht
    rename_i hs0
    split at ht
    · cases ht
    rename_i hd0
    have hbal : amount.toNat ≤ ((view ctx.crypto Layout.oz w token).balanceOf src).toNat := by
      unfold Model.transfer at ht
      split at ht
      · rename_i h; rw [hb₁] at h; exact h
      · cases ht
    obtain ⟨r, hr, hsu, ho, hw⟩ : ∃ r, run (k + 600) (start ctx w tr
        (transferFromCall token caller src dst amount gas warmAddrs warmKeys)) = .ok r ∧
        r.success = true ∧ r.output = Bytes.ofWord 1 ∧
        r.world = ozTransferFromWorld ctx.crypto Layout.oz w token caller src dst amount := by
      by_cases hmax : (view ctx.crypto Layout.oz w token).allowance src caller = maxWord
      · exact transferFrom_ok_max hgas hmax hs0 hd0 hbal k
      · unfold Model.ozSpend at hs₁
        simp only [hmax, ↓reduceIte] at hs₁
        split at hs₁
        · rename_i hle
          unfold Model.ozApprove at hs₁
          split at hs₁
          · cases hs₁
          split at hs₁
          · cases hs₁
          rename_i hc0
          exact transferFrom_ok hgas ha hmax hle hs0 hc0 hd0 hbal k
        · cases hs₁
    refine ⟨r, hr, hsu, ho, ?_, ?_, ?_, ?_⟩ <;> rw [hw]
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · rename_i hm
    by_cases hmax : (view ctx.crypto Layout.oz w token).allowance src caller = maxWord
    · refine transferFrom_revert_max hgas hmax ?_ k
      unfold Model.ozTransferFrom Model.ozSpend at hm
      simpa only [hmax, ↓reduceIte, Option.bind_some] using hm
    · exact transferFrom_revert hgas ha hmax hm k

end Verified.OpenZeppelin.ERC20
