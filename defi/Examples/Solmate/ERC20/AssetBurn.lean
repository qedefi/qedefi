import Examples.Solmate.ERC20.MintBurn

/-!
# The asset's `burn`

`MockERC20.burn(from, amount)` is public and unrestricted (anyone can burn anyone's tokens; in
the model this is the vault's "loss" when `from` is the vault): it runs Solmate's `_burn`,

```solidity
balanceOf[from] -= amount;                   // checked
unchecked { totalSupply -= amount; }
emit Transfer(from, address(0), amount);
```

and returns nothing. For the deployed asset (any immutables), in any non-static fresh frame:

* `burn_halts_ok`: if `from`'s balance covers `amount`, the call succeeds with empty output and
  the world `burnWorld` (the two `SSTORE`s in the code's order);
* `burn_halts_revert`: otherwise the checked subtraction panics;
* `assetBurn_refines`: against `Token.burn` of the represented ledger.

Hypotheses as for `mint` (`AssetMint.lean`): no balance slot is the `totalSupply` slot 2
(`KeccakAvoids crypto (AddressKeyed [3]) [2]`), `BalanceSlotOk` of `from`, and `Token.WF`
(the unchecked subtraction from the supply does not wrap).
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault Shares

/-! ## The world -/

/-- The world after a successful `burn(src, amount)`: `balanceOf[src] -= amount`, then
`totalSupply -= amount` (reading the updated storage), in the order the code does it. -/
def burnWorld (crypto : Crypto) (w : World) (token src : Address) (amount : Word) : World :=
  let ss := Erc20.balanceSlot crypto Erc20.Layout.solmate src
  let w₁ := w.sstore token ss (w.sload token ss - amount)
  w₁.sstore token 2#256 (w₁.sload token 2#256 - amount)

/-- `burn` writes only the balance slot of `src` and the `totalSupply` slot. -/
theorem sload_burnWorld {crypto : Crypto} {w : World} {token src b : Address} {amount k : Word}
    (h : b ≠ token ∨ (k ≠ 2#256 ∧ k ≠ Erc20.balanceSlot crypto Erc20.Layout.solmate src)) :
    (burnWorld crypto w token src amount).sload b k = w.sload b k := by
  simp only [burnWorld]
  rw [sload_sstore_frame (by rcases h with h | h; exact .inl h; exact .inr h.1),
    sload_sstore_frame (by rcases h with h | h; exact .inl h; exact .inr h.2)]

/-- `burn` changes no code. -/
theorem code_burnWorld (crypto : Crypto) (w : World) (token src : Address) (amount : Word)
    (b : Address) : (burnWorld crypto w token src amount).code b = w.code b := by
  simp [burnWorld]

/-- What a successful `burn(src, amount)` of the asset ends with: empty output, the world
`burnWorld`, transient storage and created accounts unchanged, at most 55000 gas used. -/
def BurnOk (src : Address) (amount : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success .empty ∧
  mf.world = burnWorld m.ctx.crypto m.world m.frame.msg.currentTarget src amount ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 55000

/-! ## Bytecode -/

set_option maxHeartbeats 0 in
/-- **`burn(src, amount)` of the asset, success**, in any non-static frame: when `src`'s
balance covers `amount`. -/
theorem burn_halts_ok {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false) {src : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate src)).toNat) :
    Halts m (BurnOk src amount m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [balanceSlot_solmate] at hbal
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_sub_self_of_le hbal, iszero_zero]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  pwp_codecopy
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine WP.halt_of_step (step_stop ?_) (by same_frame) ⟨rfl, ?_, rfl, rfl, ?_⟩
  · pcode_fact
  · simp only [burnWorld, balanceSlot_solmate]
  · evm_gas

set_option maxHeartbeats 0 in
/-- **`burn(src, amount)` of the asset, insufficient balance**, in any frame: the checked
subtraction panics (`Panic(0x11)`). -/
theorem burn_halts_revert {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) {src : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 10000 ≤ m.frame.gasLeft)
    (hbal : (m.world.sload m.frame.msg.currentTarget
      (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate src)).toNat < amount.toNat) :
    Halts m (Reverts 10000 m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [balanceSlot_solmate] at hbal
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [gt_sub_self_of_lt hbal, iszero_one]
  pwp_steps
  refine ⟨⟨_, rfl⟩, ?_⟩
  dsimp only [outputMachine]
  evm_gas

/-! ## Against the model -/

/-- The allowance predicate of a `burn`'s result: entries whose slot is neither written slot
(the same shape as for `mint`). -/
abbrev BurnAllowances (crypto : Crypto) (src : Address) : Address → Address → Prop :=
  MintAllowances crypto src

/-- **`burnWorld` represents `Token.burn`**: on a well-formed ledger, when the model's `burn`
succeeds, the storage view after the two writes represents its result (allowances on
`BurnAllowances`). -/
theorem repOn_burnWorld {crypto : Crypto} {w : World} {token src : Address} {amount : Word}
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256])
    (hs : Erc20.BalanceSlotOk crypto Erc20.Layout.solmate src)
    {t t' : Token Address} (hr : Rep (Erc20.view crypto Erc20.Layout.solmate w token) t)
    (hw : t.WF) (ht : t.burn src amount.toNat = some t') :
    RepOn (BurnAllowances crypto src)
      (Erc20.view crypto Erc20.Layout.solmate (burnWorld crypto w token src amount) token) t' := by
  obtain ⟨hv, rfl⟩ := Token.burn_eq_some.1 ht
  have hs2 := balanceSlot_ne_two hk src
  have hts : (w.sload token 2#256).toNat = t.totalSupply := hr.totalSupply
  have hbal : (w.sload token (Erc20.balanceSlot crypto Erc20.Layout.solmate src)).toNat =
      t.balanceOf src := hr.balanceOf src
  have hle := Token.balanceOf_le_totalSupply hw src
  refine ⟨?_, fun a => ?_, fun o sp hp => ?_⟩
  · -- the total supply
    show ((burnWorld crypto w token src amount).sload token 2#256).toNat = _
    simp only [burnWorld]
    rw [World.sload_sstore_self, World.sload_sstore_ne_key _ _ _ (fun e => hs2 e.symm),
      BitVec.toNat_sub_of_le (BitVec.le_def.2 (by rw [hts]; omega)), hts]
  · -- the balances
    show ((burnWorld crypto w token src amount).sload token
      (Erc20.balanceSlot crypto Erc20.Layout.solmate a)).toNat = _
    dsimp only
    rw [Token.sub_single_apply]
    by_cases ha : src = a
    · subst ha
      simp only [burnWorld, ↓reduceIte]
      rw [World.sload_sstore_ne_key _ _ _ hs2, World.sload_sstore_self,
        BitVec.toNat_sub_of_le (BitVec.le_def.2 (by rw [hbal]; exact hv)), hbal]
    · simp only [ha, ↓reduceIte]
      rw [sload_burnWorld (.inr ⟨balanceSlot_ne_two hk a,
        Erc20.balanceSlot_ne hs (Ne.symm ha)⟩)]
      exact hr.balanceOf a
  · -- the allowances off the written slots
    show ((burnWorld crypto w token src amount).sload token
      (Erc20.allowanceSlot crypto Erc20.Layout.solmate o sp)).toNat = _
    rw [sload_burnWorld (.inr hp)]
    exact hr.allowance o sp trivial

/-- **`burn(src, amount)` of the asset refines `Token.burn`**, in any non-static frame:
success with the model's ledger, or a revert. -/
theorem assetBurn_refines {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {src : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hk : KeccakAvoids m.ctx.crypto (AddressKeyed [3#256]) [2#256])
    (hs : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate src)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    match t.burn src amount.toNat with
    | some t' => Halts m (fun mf o => BurnOk src amount m mf o ∧
        RepOn (BurnAllowances m.ctx.crypto src)
          (Erc20.view m.ctx.crypto Erc20.Layout.solmate mf.world m.frame.msg.currentTarget) t')
    | none => Halts m (Reverts 10000 m) := by
  have hbal : (m.world.sload m.frame.msg.currentTarget
      (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate src)).toNat = t.balanceOf src :=
    hr.balanceOf src
  split
  · rename_i t' hT
    have hv := (Token.burn_eq_some.1 hT).1
    have hrep := repOn_burnWorld hk hs hr hw hT
    refine (burn_halts_ok m hf hval hstatic hd hsz hg (by rw [hbal]; exact hv)).mono
      fun mf o _ hok => ⟨hok, ?_⟩
    rw [hok.2.1]
    exact hrep
  · rename_i hT
    have hlt : t.balanceOf src < amount.toNat := by
      unfold Token.burn at hT
      split at hT
      · assumption
      · cases hT
    exact burn_halts_revert m hf hval hd hsz (by omega) (by rw [hbal]; exact hlt)

end EvmLeanSpecs.Refinement
