import EvmLeanSpecs.Vault.Solmate
import EvmLeanSpecs.Refinement.VaultViewsMax
import EvmLeanSpecs.Refinement.AssetTransferFrom
import EvmLeanProofs.Solidity.Call

/-!
# The bridge: deployed bytecode ↔ the Solmate vault model

* `Deployed w vault asset`: the world holds the compiled `MockERC4626` at `vault` and the
  compiled `MockERC20` at `asset`, and `asset` is the address baked into the vault's code (the
  `asset` immutable of `SolmateVault.runtimeCode`, i.e. `assetAddr`).
* `abs crypto w vault asset : Vault.Solmate.State Address`: the model state read from
  storage through the Solidity layout (`Erc20.Layout.solmate`: `totalSupply` at 2,
  `balanceOf` at 3, `allowance` at 4; `MockERC4626`'s hook counters at 6 and 7). Balances are
  read pointwise (`balanceOf a = sload(keccak(a ‖ 3))`); since `Address` is finite this is a
  finitely supported map without any assumption. No hypothesis on Keccak is needed to *read*:
  whatever `crypto` is, `abs` is exactly what the bytecode reads.
* `*_refines`: every view of the compiled vault, run in **any** frame (top level or called
  from another contract, any `Crypto`, any world in which the asset is deployed), returns the
  model's value when the model returns `some v` and reverts when it returns `none`
  (`ViewPost`); `*_call`: the same for a top-level transaction (`processMessageCall`).
* The asset's callee summaries (`balanceOf_halts`, `transfer_halts_*`, `transferFrom_halts_*`)
  are related to the model's `Token` operations by `tokenView_transferWorld` /
  `tokenView_transferFromWorld`, under the pointwise freshness hypotheses
  `Erc20.BalanceSlotOk` of the touched balance slots (as in the solidity package).

Collision hypotheses are needed only for *writes*: a write to one slot must not change what
`abs` reads at another key. Such statements are pointwise (`KeccakFresh` of the written
slot against all address-keyed rows), never global injectivity, which is false for every
`Crypto`; see `EvmLeanProofs/Solidity/Keccak.lean` and `README.md`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLean.Solidity.Examples.SolmateAssetTransfer (transferWorld)
open Vault

/-! ## Deployment -/

/-- The canonical asset address is not a precompile in any fork. -/
theorem assetAddr_not_precompile (fork : Fork) : Precompile.isPrecompile fork assetAddr = false := by
  cases fork <;> decide

/-- The vault and its asset are deployed in `w`: the exact compiled runtime code of
`MockERC4626` at `vault` and of `MockERC20` at `asset`, where `asset` is the address the
vault's code was deployed with (its `asset` immutable), and `vault` is not a precompile. Neither
code is an EIP-7702 delegation designator (`delegatedAddress?_vault`, `…_asset`), and the asset
address is no precompile (`assetAddr_not_precompile`). -/
structure Deployed (w : World) (vault asset : Address) : Prop where
  /-- The vault's runtime code. -/
  vaultCode : w.code vault = SolmateVault.runtimeCode
  /-- The vault's `asset` immutable is `asset`. -/
  asset_eq : asset = assetAddr
  /-- The asset's runtime code. -/
  assetCode : w.code asset = SolmateAsset.runtimeCode
  /-- The vault is not a precompile. -/
  vaultNotPrecompile : ∀ fork, Precompile.isPrecompile fork vault = false

/-- The vault's code is not a delegation designator. -/
theorem delegatedAddress?_vault : delegatedAddress? SolmateVault.runtimeCode = none :=
  delegatedAddress?_of_size (by rw [SolmateVault.size_runtimeCode]; decide)

/-- The asset's code is not a delegation designator. -/
theorem delegatedAddress?_asset : delegatedAddress? SolmateAsset.runtimeCode = none :=
  delegatedAddress?_of_size (by rw [SolmateAsset.size_runtimeCode]; decide)

/-! ## The abstraction -/

/-- The ERC-20 ledger of the Solmate token at `token`, read from storage. -/
noncomputable def tokenView (crypto : Crypto) (w : World) (token : Address) : Token Address where
  balanceOf := Finsupp.equivFunOnFinite.symm fun a =>
    (w.sload token (Erc20.balanceSlot crypto Erc20.Layout.solmate a)).toNat
  totalSupply := (w.sload token Erc20.Layout.solmate.totalSupply).toNat
  allowance o s := (w.sload token (Erc20.allowanceSlot crypto Erc20.Layout.solmate o s)).toNat

/-- **The abstraction function**: the Solmate vault model state of the vault at `vault` over
the asset at `asset`, read from the world. -/
noncomputable def abs (crypto : Crypto) (w : World) (vault asset : Address) :
    Solmate.State Address where
  self := vault
  asset := tokenView crypto w asset
  shares := tokenView crypto w vault
  afterDepositCount := (w.sload vault 7).toNat
  beforeWithdrawCount := (w.sload vault 6).toNat

@[simp] theorem tokenView_balanceOf (crypto : Crypto) (w : World) (token a : Address) :
    (tokenView crypto w token).balanceOf a =
      (w.sload token (Erc20.balanceSlot crypto Erc20.Layout.solmate a)).toNat := by
  simp [tokenView]

@[simp] theorem tokenView_totalSupply (crypto : Crypto) (w : World) (token : Address) :
    (tokenView crypto w token).totalSupply = (w.sload token 2#256).toNat := rfl

@[simp] theorem tokenView_allowance (crypto : Crypto) (w : World) (token o s : Address) :
    (tokenView crypto w token).allowance o s =
      (w.sload token (Erc20.allowanceSlot crypto Erc20.Layout.solmate o s)).toNat := rfl

/-- `totalSupply` of the model is slot 2 of the vault. -/
theorem abs_totalSupply (crypto : Crypto) (w : World) (vault asset : Address) :
    (abs crypto w vault asset).totalSupply = (w.sload vault 2#256).toNat := rfl

/-- `totalAssets()` of the model is the vault's balance slot in the asset. -/
theorem abs_totalAssets (crypto : Crypto) (w : World) (vault asset : Address) :
    (abs crypto w vault asset).totalAssets =
      (w.sload asset (Erc20.balanceSlot crypto Erc20.Layout.solmate vault)).toNat := by
  simp [abs, Solmate.State.totalAssets]

/-! ## The arithmetic mirrors are the specification's -/

theorem mulDivDownN_eq : mulDivDownN = Vault.mulDivDown := rfl

theorem mulDivUpN_eq : mulDivUpN = Vault.mulDivUp := rfl

/-- The vault-side state of a frame running the vault: its world, crypto and address. -/
noncomputable abbrev absOf (m : Machine) : Solmate.State Address :=
  abs m.ctx.crypto m.world m.frame.msg.currentTarget assetAddr

theorem absOf_totalSupply (m : Machine) : (absOf m).totalSupply = (supplyOf m).toNat := rfl

theorem absOf_totalAssets (m : Machine) : (absOf m).totalAssets = (assetsOf m).toNat := by
  rw [abs_totalAssets]; rfl

theorem absOf_convertToShares (m : Machine) (x : ℕ) :
    (absOf m).convertToShares x = convertToSharesN (supplyOf m).toNat (assetsOf m).toNat x := by
  rw [Solmate.State.convertToShares, absOf_totalSupply,
    absOf_totalAssets]; rfl

theorem absOf_convertToAssets (m : Machine) (x : ℕ) :
    (absOf m).convertToAssets x = convertToAssetsN (supplyOf m).toNat (assetsOf m).toNat x := by
  rw [Solmate.State.convertToAssets, absOf_totalSupply, absOf_totalAssets]; rfl

theorem absOf_previewMint (m : Machine) (x : ℕ) :
    (absOf m).previewMint x = previewMintN (supplyOf m).toNat (assetsOf m).toNat x := by
  rw [Solmate.State.previewMint, absOf_totalSupply, absOf_totalAssets]; rfl

theorem absOf_previewWithdraw (m : Machine) (x : ℕ) :
    (absOf m).previewWithdraw x = previewWithdrawN (supplyOf m).toNat (assetsOf m).toNat x := by
  rw [Solmate.State.previewWithdraw, absOf_totalSupply, absOf_totalAssets]; rfl

theorem absOf_sharesOf (m : Machine) (a : Address) :
    (absOf m).shares.balanceOf a = (sharesOf m a).toNat := by
  simp [absOf, abs, sharesOf]

end EvmLeanSpecs.Refinement
