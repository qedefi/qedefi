import Defi.Math.Arith
import Defi.ERC20.Token
import Defi.ERC4626.Solmate
import Defi.ERC4626.SolmateProps
import Defi.ERC4626.Oz
import Defi.ERC4626.OzProps
import Defi.ERC4626.Inflation
import Defi.ERC4626.Witnesses
import Defi.ERC4626.MoreProps
import Defi.ERC4626.Events
import EvmLean
import Examples.Solmate.ERC4626.Views
import Examples.Solmate.ERC20.TransferFrom
import EvmLogic.Solidity.Call
import Defi.ERC20.Rep

/-!
# Bridge to evm-lean

This file checks that the specification package can import both Mathlib (through the
vault model) and the evm-lean semantics (by path dependency on the parent package), and
fixes the actor type used by the refinement proofs: EVM addresses.
-/

section

namespace Examples.Solmate.ERC4626

/-- The Solmate vault model over EVM addresses, as used by the refinement proofs. -/
abbrev SolmateVaultState := Defi.ERC4626.Solmate.State EvmLean.Address

end Examples.Solmate.ERC4626

end

section

/-!
## The bridge: deployed bytecode ↔ the Solmate vault model

* `Deployed w vault asset`: the world holds the compiled `MockERC4626` at `vault`, deployed
  with any immutables `i` whose `asset` is `asset` (`SolmateVault.runtimeCodeWith i`; e.g.
  `runtimeCodeFor keccak chainId asset vault`), and the compiled `MockERC20` at `asset` (any
  immutables); neither is a precompile.
* `abs crypto w vault asset : Vault.Solmate.State Address`: the model state read from
  storage through the Solidity layout (`Erc20.view`, then `toToken`) (`Erc20.Layout.solmate`: `totalSupply` at 2,
  `balanceOf` at 3, `allowance` at 4; `MockERC4626`'s hook counters at 6 and 7). Balances are
  read pointwise (`balanceOf a = sload(keccak(a ‖ 3))`); since `Address` is finite this is a
  finitely supported map without any assumption. No hypothesis on Keccak is needed to *read*:
  whatever `crypto` is, `abs` is exactly what the bytecode reads.
* `*_refines`: every view of the compiled vault, run in **any** frame (top level or called
  from another contract, any `Crypto`, any world in which the asset is deployed), returns the
  model's value when the model returns `some v` and reverts when it returns `none`
  (`ViewPost`); `*_call`: the same for a top-level transaction (`processMessageCall`).
* The relational form `Refines crypto w vault asset s` (the share and asset storage
  represent `s.shares` and `s.asset` in the sense of `Shares.Rep`) is equivalent to
  `s = abs crypto w vault asset` (`refines_iff`); after writes, where allowances are only
  known pointwise, the weaker `Shares.RepOn P` is what the asset summaries give
  (`Examples.Solmate.ERC20.Spec`).

Collision hypotheses are needed only for *writes*: a write to one slot must not change what
`abs` reads at another key. Such statements are pointwise (`KeccakFresh` of the written
slot against all address-keyed rows), never global injectivity, which is false for every
`Crypto`; see `EvmLogic/Solidity/Keccak.lean` and `README.md`.
-/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic Examples.Solmate.Contracts
open EvmLogic.Solidity.ERC20 (transferWorld)
open Defi.ERC4626 Defi.Math Defi.ERC20

/-! ## Deployment -/

/-- The vault and its asset are deployed in `w`: the vault's compiled runtime code at `vault`,
deployed with immutables whose `asset` is `asset` (any chain id, domain separator, decimals),
and the asset's compiled runtime code (any immutables) at `asset`; neither address is a
precompile. Neither code is an EIP-7702 delegation designator
(`Shares.delegatedAddress?_code`, `delegatedAddress?_assetCode`). -/
structure Deployed (w : World) (vault asset : Address) : Prop where
  /-- The vault's runtime code, with `asset` as its `asset` immutable. -/
  vaultCode : ∃ i : SolmateVault.Immutables, i.asset = asset ∧
    w.code vault = SolmateVault.runtimeCodeWith i
  /-- The asset's runtime code. -/
  assetCode : ∃ ia : SolmateAsset.Immutables, w.code asset = SolmateAsset.runtimeCodeWith ia
  /-- The vault is not a precompile. -/
  vaultNotPrecompile : ∀ fork, Precompile.isPrecompile fork vault = false
  /-- The asset is not a precompile. -/
  assetNotPrecompile : ∀ fork, Precompile.isPrecompile fork asset = false

/-- The canonical deployment (`contracts/README.md`) is an instance, for every world holding
the canonical codes at the canonical addresses. -/
theorem deployed_canonical {w : World}
    (hv : w.code SolmateVault.address = SolmateVault.runtimeCode)
    (ha : w.code SolmateVault.deployment.asset = SolmateAsset.runtimeCode) :
    Deployed w SolmateVault.address SolmateVault.deployment.asset where
  vaultCode := ⟨SolmateVault.deployment, rfl, hv.trans SolmateVault.runtimeCodeWith_deployment.symm⟩
  assetCode := ⟨SolmateAsset.deployment, ha.trans SolmateAsset.runtimeCodeWith_deployment.symm⟩
  vaultNotPrecompile fork := by cases fork <;> decide
  assetNotPrecompile fork := by cases fork <;> decide

/-! ## The abstraction -/

/-- The `ℕ`-valued ledger of a word-valued ERC-20 state (`toNat` of every field; balances as a
finitely supported map, `Address` being finite). -/
noncomputable def toToken (s : ERC20.State) : Token Address where
  balanceOf := Finsupp.equivFunOnFinite.symm fun a => (s.balanceOf a).toNat
  totalSupply := s.totalSupply.toNat
  allowance o sp := (s.allowance o sp).toNat

/-- A word-valued state represents its `toToken`. -/
theorem rep_toToken (s : ERC20.State) : Defi.ERC20.Rep s (toToken s) :=
  ⟨rfl, fun a => by simp [toToken], fun _ _ _ => rfl⟩

/-- The ledger a word-valued state represents is `toToken` of it. -/
theorem toToken_eq_of_rep {s : ERC20.State} {t : Token Address} (h : Defi.ERC20.Rep s t) :
    toToken s = t := by
  obtain ⟨b, ts, al⟩ := t
  obtain ⟨h1, h2, h3⟩ := h
  simp only [toToken] at *
  congr
  · ext a; simpa using h2 a
  · funext o sp; exact h3 o sp trivial

/-- The ERC-20 ledger of the Solmate token at `token`, read from storage. -/
noncomputable def tokenView (crypto : Crypto) (w : World) (token : Address) : Token Address :=
  toToken (ERC20.view crypto ERC20.Layout.solmate w token)

/-- **The abstraction function**: the Solmate vault model state of the vault at `vault` over
the asset at `asset`, read from the world. -/
noncomputable def abs (crypto : Crypto) (w : World) (vault asset : Address) :
    Solmate.State Address where
  self := vault
  asset := tokenView crypto w asset
  shares := tokenView crypto w vault
  afterDepositCount := (w.sload vault 7).toNat
  beforeWithdrawCount := (w.sload vault 6).toNat

/-- **The refinement relation** in `Shares.Rep` form: the share and asset storage represent the
model's ledgers, and the hook counters are the model's. -/
structure Refines (crypto : Crypto) (w : World) (vault asset : Address)
    (s : Solmate.State Address) : Prop where
  /-- The vault's address. -/
  self : s.self = vault
  /-- The share ledger. -/
  shares : Defi.ERC20.Rep (ERC20.view crypto ERC20.Layout.solmate w vault) s.shares
  /-- The asset ledger. -/
  asset : Defi.ERC20.Rep (ERC20.view crypto ERC20.Layout.solmate w asset) s.asset
  /-- `afterDepositHookCalledCounter` (slot 7). -/
  afterDeposit : (w.sload vault 7).toNat = s.afterDepositCount
  /-- `beforeWithdrawHookCalledCounter` (slot 6). -/
  beforeWithdraw : (w.sload vault 6).toNat = s.beforeWithdrawCount

/-- `Refines` determines the model state: it is `abs`. -/
theorem refines_iff {crypto : Crypto} {w : World} {vault asset : Address}
    {s : Solmate.State Address} : Refines crypto w vault asset s ↔ s = abs crypto w vault asset := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨self, a, sh, c1, c2⟩ := s
    simp only at h1 h4 h5
    simp only [abs, tokenView, toToken_eq_of_rep h2, toToken_eq_of_rep h3, h1, h4, h5]
  · rintro rfl
    exact ⟨rfl, rep_toToken _, rep_toToken _, rfl, rfl⟩

@[simp] theorem tokenView_balanceOf (crypto : Crypto) (w : World) (token a : Address) :
    (tokenView crypto w token).balanceOf a =
      (w.sload token (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat := by
  simp [tokenView, toToken, ERC20.view]

@[simp] theorem tokenView_totalSupply (crypto : Crypto) (w : World) (token : Address) :
    (tokenView crypto w token).totalSupply = (w.sload token 2#256).toNat := rfl

@[simp] theorem tokenView_allowance (crypto : Crypto) (w : World) (token o s : Address) :
    (tokenView crypto w token).allowance o s =
      (w.sload token (ERC20.allowanceSlot crypto ERC20.Layout.solmate o s)).toNat := rfl

/-- `totalSupply` of the model is slot 2 of the vault. -/
theorem abs_totalSupply (crypto : Crypto) (w : World) (vault asset : Address) :
    (abs crypto w vault asset).totalSupply = (w.sload vault 2#256).toNat := rfl

/-- `totalAssets()` of the model is the vault's balance slot in the asset. -/
theorem abs_totalAssets (crypto : Crypto) (w : World) (vault asset : Address) :
    (abs crypto w vault asset).totalAssets =
      (w.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate vault)).toNat := by
  simp [abs, Solmate.State.totalAssets]

/-! ## The arithmetic mirrors are the specification's -/

/-- The bytecode-side mirror of `mulDivDown` is the specification's. -/
theorem mulDivDownN_eq : mulDivDownN = Defi.Math.mulDivDown := rfl

/-- The bytecode-side mirror of `mulDivUp` is the specification's. -/
theorem mulDivUpN_eq : mulDivUpN = Defi.Math.mulDivUp := rfl

/-- The model state seen by a frame running the vault over `asset`: its world, crypto and
address. -/
noncomputable abbrev absOf (asset : Address) (m : Machine) : Solmate.State Address :=
  abs m.ctx.crypto m.world m.frame.msg.currentTarget asset

theorem absOf_totalSupply (asset : Address) (m : Machine) : (absOf asset m).totalSupply = (supplyOf m).toNat := rfl

theorem absOf_totalAssets (asset : Address) (m : Machine) : (absOf asset m).totalAssets = (assetsOf asset m).toNat := by
  rw [abs_totalAssets]; rfl

theorem absOf_convertToShares (asset : Address) (m : Machine) (x : ℕ) :
    (absOf asset m).convertToShares x = convertToSharesN (supplyOf m).toNat (assetsOf asset m).toNat x := by
  rw [Solmate.State.convertToShares, absOf_totalSupply,
    absOf_totalAssets]; rfl

theorem absOf_convertToAssets (asset : Address) (m : Machine) (x : ℕ) :
    (absOf asset m).convertToAssets x = convertToAssetsN (supplyOf m).toNat (assetsOf asset m).toNat x := by
  rw [Solmate.State.convertToAssets, absOf_totalSupply, absOf_totalAssets]; rfl

theorem absOf_previewMint (asset : Address) (m : Machine) (x : ℕ) :
    (absOf asset m).previewMint x = previewMintN (supplyOf m).toNat (assetsOf asset m).toNat x := by
  rw [Solmate.State.previewMint, absOf_totalSupply, absOf_totalAssets]; rfl

theorem absOf_previewWithdraw (asset : Address) (m : Machine) (x : ℕ) :
    (absOf asset m).previewWithdraw x = previewWithdrawN (supplyOf m).toNat (assetsOf asset m).toNat x := by
  rw [Solmate.State.previewWithdraw, absOf_totalSupply, absOf_totalAssets]; rfl

theorem absOf_sharesOf (asset : Address) (m : Machine) (a : Address) :
    (absOf asset m).shares.balanceOf a = (sharesOf m a).toNat := by
  simp [absOf, abs, sharesOf]

end Examples.Solmate.ERC4626

end
