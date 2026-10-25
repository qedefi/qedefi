import Verified.OpenZeppelin.ERC20.Spec.Token
import Verified.OpenZeppelin.ERC20.Basic
import QEDefi.ERC20.Spec.Invariant

/-!
# OpenZeppelin's `ERC20Mock`: the supply is the sum of the balances, after any transactions

`oz_supply_eq_sum` (the open challenge *OzAssetSupplySum*): for the deployed `ERC20Mock` at
`a`, `totalSupply` equals the sum of the actors' `balanceOf` after any sequence of successful
transactions, when it did before, provided every token frame the transactions reach touches
only actors (`TxTouch`; the spec is exact for actors' calls). It is `Invariant.variant_conserved`
for `Variant.oz` applied to `oz_erc20Spec`.
-/

namespace Verified.OpenZeppelin.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Solidity EvmLogic.Solidity.ERC20 EvmLogic.Tx
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.Oz QEDefi.ERC20.Spec.Invariant
open Verified.OpenZeppelin.Contracts

theorem ozAbs_etherFree : EtherFree ozAbs ozModel :=
  etherFree_of_read fun crypto Act w w' t hk => ozRead_congr crypto Act w w' t hk

theorem total_readMap (crypto : Crypto) (Act : Finset Address) (w : World) (a : Address)
    (base : Word) :
    total (readMap crypto Act w a base) =
      ∑ b ∈ Act, (w.sload a (mappingSlot crypto (Word.ofAddress b) base)).toNat := by
  unfold total readMap
  rw [Finsupp.onFinset_sum _ (fun _ => rfl)]
  exact Finset.sum_congr rfl fun b hb => by simp [hb]

/-- **OzAssetSupplySum: `totalSupply = Σ balanceOf` after any transactions.** For the deployed
OpenZeppelin `ERC20Mock` at `a` and a finite set of actors `Act` whose storage rows are distinct
(`ozSound`): if the actors' balances add up to `totalSupply` in `w` (the actors hold every
token), they do after any sequence of successful transactions using `crypto` whose token frames
touch only actors. -/
theorem oz_supply_eq_sum {crypto : Crypto} {Act : Finset Address} {a : Address} {w w' : World}
    (hsound : ozSound crypto Act)
    (hw : TokInv OzAsset.runtimeCode ozAbs ozModel crypto Act a w)
    (h : TxSteps (TxTouch OzAsset.runtimeCode ozAbs ozModel ozSel ozOps ozOpAddrs none crypto
      Act a) w w') :
    ∑ b ∈ Act, (w'.sload a (balanceSlot crypto Layout.oz b)).toNat =
      (w'.sload a Layout.oz.totalSupply).toNat := by
  have := variant_conserved (V := Variant.oz) (ev := ozEvents) Variant.oz_sane rfl rfl
    oz_erc20Spec (fun _ h => by cases h) ozAbs_etherFree hsound
    (by rw [OzAsset.size_runtimeCode]; decide) delegatedAddress?_runtimeCode hw h
  simp only [ozAbs_read, ozRead, total_readMap] at this
  simpa [total, readSlot, balanceSlot] using this

end Verified.OpenZeppelin.ERC20.Spec
