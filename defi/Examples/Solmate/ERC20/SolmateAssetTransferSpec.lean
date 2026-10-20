import Examples.Solmate.ERC20.Transfer

/-!
# `SolmateAsset.transfer`: the refinement theorem

`transfer_spec` lifts `transfer_ok` / `transfer_revert` (bytecode level) through the ERC-20
storage abstraction: a top-level call of `transfer(to, amount)` on the deployed asset
behaves as `Erc20.Model.transfer` on `Erc20.view` of the world.
-/

namespace EvmLean.Solidity.Examples.SolmateAssetTransfer

open Interpreter Erc20 Contracts

variable {ctx : Context} {w : World} {tr : TransientStorage} {token caller to : Address}
  {amount : Word} {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

set_option maxHeartbeats 1000000 in
/-- **`transfer` refines `Model.transfer`** on the deployed `SolmateAsset` bytecode, for every
`Crypto`, context without EIP-7702 authorizations (or before Prague), world, transient
storage, caller, recipient (possibly the caller), amount, gas ≥ 100 000, warm sets and fuel
≥ 300, assuming only that the balance slots of `caller` and `to` do not collide with other
balance/allowance-row slots or with `totalSupply` (`BalanceSlotOk`):

* if the model succeeds with `s'`, the call succeeds, returns `true`, and the abstract
  `totalSupply` and `balanceOf` after the call are those of `s'`; allowances whose slots are
  not the written slots equal those of `s'` (that is, are unchanged); no other account's
  storage changes;
* if the model reverts (insufficient balance), the call reverts and the world is unchanged. -/
theorem transfer_spec (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork token = false) (hgas : 100000 ≤ gas)
    (hc : BalanceSlotOk ctx.crypto Layout.solmate caller)
    (ht : BalanceSlotOk ctx.crypto Layout.solmate to) (fuel : Nat) (hfuel : 300 ≤ fuel) :
    ∃ r, processMessageCall fuel ctx w tr
        (transferCall token caller to amount gas warmAddrs warmKeys) = .ok r ∧
      match Model.transfer (view ctx.crypto Layout.solmate w token) caller to amount with
      | some s' =>
        r.success = true ∧ r.output = Bytes.ofWord 1 ∧
        (view ctx.crypto Layout.solmate r.world token).totalSupply = s'.totalSupply ∧
        (view ctx.crypto Layout.solmate r.world token).balanceOf = s'.balanceOf ∧
        (∀ o s, allowanceSlot ctx.crypto Layout.solmate o s ≠
            balanceSlot ctx.crypto Layout.solmate caller →
          allowanceSlot ctx.crypto Layout.solmate o s ≠ balanceSlot ctx.crypto Layout.solmate to →
          (view ctx.crypto Layout.solmate r.world token).allowance o s = s'.allowance o s) ∧
        (∀ b k, b ≠ token → r.world.sload b k = w.sload b k)
      | none => r.success = false ∧ r.reverted = true ∧ r.world = w := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 300 := ⟨fuel - 300, by omega⟩
  rw [transferCall, processMessageCall_callMsg hdeleg delegatedAddress?_runtimeCode hpre]
  split
  · rename_i s' hm
    have hbal : amount.toNat ≤ ((view ctx.crypto Layout.solmate w token).balanceOf caller).toNat := by
      unfold Model.transfer at hm
      split at hm
      · assumption
      · cases hm
    obtain ⟨r, hr, hs, ho, hw⟩ := transfer_ok (tr := tr) (to := to) (warmAddrs := warmAddrs)
      (warmKeys := warmKeys) hgas hbal k
    obtain ⟨h1, h2, h3, h4⟩ := view_transferWorld hc ht hm
    refine ⟨r, hr, hs, ho, ?_, ?_, ?_, ?_⟩ <;> rw [hw]
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · rename_i hm
    have hbal : ((view ctx.crypto Layout.solmate w token).balanceOf caller).toNat < amount.toNat := by
      unfold Model.transfer at hm
      split at hm
      · cases hm
      · omega
    exact transfer_revert hgas hbal k

end EvmLean.Solidity.Examples.SolmateAssetTransfer
