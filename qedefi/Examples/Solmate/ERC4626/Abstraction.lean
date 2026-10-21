import QEDefi.Math.Arith
import QEDefi.ERC20.Token
import QEDefi.ERC4626.Solmate
import QEDefi.ERC4626.SolmateProps
import QEDefi.ERC4626.Oz
import QEDefi.ERC4626.OzProps
import QEDefi.ERC4626.Inflation
import QEDefi.ERC4626.Witnesses
import QEDefi.ERC4626.MoreProps
import QEDefi.ERC4626.Events
import EvmLean
import Examples.Solmate.ERC4626.Views
import EvmLogic.Solidity.Call
import QEDefi.ERC20.Rep

/-!
# Abstraction: deployed bytecode ↔ the Solmate vault model

`Deployed` (the compiled vault and asset at two addresses), the abstraction function `abs`
(the model state read from storage through the Solidity layout) and the relation `Refines`,
with `refines_iff : Refines … s ↔ s = abs …`. Reading needs no Keccak hypothesis; see
`docs/erc4626/details.md` §1.
-/

section

namespace Examples.Solmate.ERC4626

/-- The Solmate vault model over EVM addresses, as used by the refinement proofs. -/
abbrev SolmateVaultState := QEDefi.ERC4626.Solmate.State EvmLean.Address

end Examples.Solmate.ERC4626

end

section


namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 QEDefi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open EvmLogic.Solidity.ERC20 (transferWorld)
open QEDefi.Math QEDefi.ERC20

/-! ## Deployment -/

/-- The vault's compiled code at `vault` (any immutables whose `asset` is `asset`) and the
asset's compiled code (any immutables) at `asset`; neither address is a precompile. -/
structure Deployed (w : World) (vault asset : Address) : Prop where
  vaultCode : ∃ i : SolmateVault.Immutables, i.asset = asset ∧
    w.code vault = SolmateVault.runtimeCodeWith i
  assetCode : ∃ ia : SolmateAsset.Immutables, w.code asset = SolmateAsset.runtimeCodeWith ia
  vaultNotPrecompile : ∀ fork, Precompile.isPrecompile fork vault = false
  assetNotPrecompile : ∀ fork, Precompile.isPrecompile fork asset = false

theorem deployed_canonical {w : World}
    (hv : w.code SolmateVault.address = SolmateVault.runtimeCode)
    (ha : w.code SolmateVault.deployment.asset = SolmateAsset.runtimeCode) :
    Deployed w SolmateVault.address SolmateVault.deployment.asset where
  vaultCode := ⟨SolmateVault.deployment, rfl, hv.trans SolmateVault.runtimeCodeWith_deployment.symm⟩
  assetCode := ⟨SolmateAsset.deployment, ha.trans SolmateAsset.runtimeCodeWith_deployment.symm⟩
  vaultNotPrecompile fork := by cases fork <;> decide
  assetNotPrecompile fork := by cases fork <;> decide

/-! ## The abstraction -/

/-- The `ℕ`-valued ledger of a word-valued ERC-20 state (`toNat` of every field). -/
noncomputable def toToken (s : ERC20.State) : Token Address where
  balanceOf := Finsupp.equivFunOnFinite.symm fun a => (s.balanceOf a).toNat
  totalSupply := s.totalSupply.toNat
  allowance o sp := (s.allowance o sp).toNat

theorem rep_toToken (s : ERC20.State) : QEDefi.ERC20.Rep s (toToken s) :=
  ⟨rfl, fun a => by simp [toToken], fun _ _ _ => rfl⟩

theorem toToken_eq_of_rep {s : ERC20.State} {t : Token Address} (h : QEDefi.ERC20.Rep s t) :
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

/-- **The refinement relation**: the share and asset storage represent the model's ledgers
(`QEDefi.ERC20.Rep`), and the hook counters are the model's. -/
structure Refines (crypto : Crypto) (w : World) (vault asset : Address)
    (s : Solmate.State Address) : Prop where
  self : s.self = vault
  shares : QEDefi.ERC20.Rep (ERC20.view crypto ERC20.Layout.solmate w vault) s.shares
  asset : QEDefi.ERC20.Rep (ERC20.view crypto ERC20.Layout.solmate w asset) s.asset
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

theorem abs_totalSupply (crypto : Crypto) (w : World) (vault asset : Address) :
    (abs crypto w vault asset).totalSupply = (w.sload vault 2#256).toNat := rfl

theorem abs_totalAssets (crypto : Crypto) (w : World) (vault asset : Address) :
    (abs crypto w vault asset).totalAssets =
      (w.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate vault)).toNat := by
  simp [abs, Solmate.State.totalAssets]

/-! ## The arithmetic mirrors are the specification's -/

theorem mulDivDownN_eq : mulDivDownN = QEDefi.Math.mulDivDown := rfl

theorem mulDivUpN_eq : mulDivUpN = QEDefi.Math.mulDivUp := rfl

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
