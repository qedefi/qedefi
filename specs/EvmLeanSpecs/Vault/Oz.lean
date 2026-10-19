module

public import EvmLeanSpecs.Vault.Token

/-!
# The OpenZeppelin ERC-4626 vault, as an abstract state machine

Mirrors OpenZeppelin Contracts v5 `token/ERC20/extensions/ERC4626.sol` (vendored v5.7.0)
with `totalAssets() = asset.balanceOf(address(this))` and a decimals offset `δ`
(`_decimalsOffset()`; the pinned `OzVault` uses `δ = 0`), over an OpenZeppelin `ERC20Mock`
asset. `δ` is a parameter of every function: the vault has `10^δ` *virtual shares* and
one *virtual asset*:

```
_convertToShares(a, r) = a.mulDiv(totalSupply() + 10 ** δ, totalAssets() + 1, r)
_convertToAssets(n, r) = n.mulDiv(totalAssets() + 1, totalSupply() + 10 ** δ, r)
```

Reverts are modelled exactly: checked `+` in both conversions, `Math.mulDiv`'s
division-by-zero / overflow panics and its checked rounding increment, the
`ERC4626ExceededMax*` checks, and every OpenZeppelin `ERC20` revert (zero addresses,
insufficient balance or allowance, supply overflow). As for Solmate, events, gas and
reentrancy are out of scope and the vault never calls itself. `A` needs a `0`
(`address(0)`).
-/

@[expose] public noncomputable section

namespace EvmLeanSpecs.Vault.Oz

open Token

/-- Storage of a deployed OpenZeppelin ERC-4626 vault together with its asset. -/
structure State (A : Type) where
  /-- `address(this)` of the vault. -/
  self : A
  /-- Storage of the asset token (`ERC20Mock`). -/
  asset : Token A
  /-- Storage of the vault's share token. -/
  shares : Token A

variable {A : Type} [DecidableEq A] [Zero A]

namespace State

variable (δ : ℕ) (s : State A)

/-- `totalAssets() = asset.balanceOf(address(this))`. -/
def totalAssets : ℕ := s.asset.balanceOf s.self

/-- `totalSupply()` of shares. -/
def totalSupply : ℕ := s.shares.totalSupply

/-- `_convertToShares(assets, rounding)`; `up = true` is `Rounding.Ceil`. -/
def toShares (assets : ℕ) (up : Bool) : Option ℕ :=
  (checkedAdd s.totalSupply (10 ^ δ)).bind fun sv =>
  (checkedAdd s.totalAssets 1).bind fun tv =>
  ozMulDiv assets sv tv up

/-- `_convertToAssets(shares, rounding)`; `up = true` is `Rounding.Ceil`. -/
def toAssets (shares : ℕ) (up : Bool) : Option ℕ :=
  (checkedAdd s.totalAssets 1).bind fun tv =>
  (checkedAdd s.totalSupply (10 ^ δ)).bind fun sv =>
  ozMulDiv shares tv sv up

/-- `convertToShares(assets)` (floor). -/
def convertToShares (assets : ℕ) : Option ℕ := s.toShares δ assets false

/-- `convertToAssets(shares)` (floor). -/
def convertToAssets (shares : ℕ) : Option ℕ := s.toAssets δ shares false

/-- `previewDeposit(assets)` (floor). -/
def previewDeposit (assets : ℕ) : Option ℕ := s.toShares δ assets false

/-- `previewMint(shares)` (ceil). -/
def previewMint (shares : ℕ) : Option ℕ := s.toAssets δ shares true

/-- `previewWithdraw(assets)` (ceil). -/
def previewWithdraw (assets : ℕ) : Option ℕ := s.toShares δ assets true

/-- `previewRedeem(shares)` (floor). -/
def previewRedeem (shares : ℕ) : Option ℕ := s.toAssets δ shares false

/-- `maxWithdraw(owner) = previewRedeem(balanceOf(owner))`. -/
def maxWithdraw (owner : A) : Option ℕ := s.previewRedeem δ (s.shares.balanceOf owner)

/-- `maxRedeem(owner) = balanceOf(owner)`. -/
def maxRedeem (owner : A) : ℕ := s.shares.balanceOf owner

end State

/-- `maxDeposit(_) = maxMint(_) = type(uint256).max`. -/
def maxDeposit (_s : State A) (_receiver : A) : ℕ := MAX

/-- `deposit(assets, receiver)` called by `caller`. Returns the shares minted (possibly 0). -/
def deposit (δ : ℕ) (s : State A) (caller : A) (assets : ℕ) (receiver : A) :
    Option (State A × ℕ) :=
  if MAX < assets then none else                                   -- ERC4626ExceededMaxDeposit
  (s.previewDeposit δ assets).bind fun shares =>
  (s.asset.ozTransferFrom s.self caller s.self assets).bind fun asset =>  -- _transferIn
  (s.shares.ozMint receiver shares).map fun sh =>                  -- _mint
  ({ s with asset := asset, shares := sh }, shares)

/-- `mint(shares, receiver)` called by `caller`. Returns the assets pulled in. -/
def mint (δ : ℕ) (s : State A) (caller : A) (shares : ℕ) (receiver : A) :
    Option (State A × ℕ) :=
  if MAX < shares then none else                                   -- ERC4626ExceededMaxMint
  (s.previewMint δ shares).bind fun assets =>
  (s.asset.ozTransferFrom s.self caller s.self assets).bind fun asset =>
  (s.shares.ozMint receiver shares).map fun sh =>
  ({ s with asset := asset, shares := sh }, assets)

/-- `if (caller != owner) _spendAllowance(owner, caller, shares);` -/
def spendIfNotOwner (t : Token A) (caller owner : A) (shares : ℕ) : Option (Token A) :=
  if caller ≠ owner then t.ozSpend owner caller shares else some t

/-- `withdraw(assets, receiver, owner)` called by `caller`. Returns the shares burned. -/
def withdraw (δ : ℕ) (s : State A) (caller : A) (assets : ℕ) (receiver owner : A) :
    Option (State A × ℕ) :=
  (s.maxWithdraw δ owner).bind fun maxAssets =>
  if maxAssets < assets then none else                             -- ERC4626ExceededMaxWithdraw
  (s.previewWithdraw δ assets).bind fun shares =>
  (spendIfNotOwner s.shares caller owner shares).bind fun sh1 =>
  (sh1.ozBurn owner shares).bind fun sh2 =>                        -- _burn
  (s.asset.ozTransfer s.self receiver assets).map fun asset =>     -- _transferOut
  ({ s with asset := asset, shares := sh2 }, shares)

/-- `redeem(shares, receiver, owner)` called by `caller`. Returns the assets paid out. -/
def redeem (δ : ℕ) (s : State A) (caller : A) (shares : ℕ) (receiver owner : A) :
    Option (State A × ℕ) :=
  if s.maxRedeem owner < shares then none else                     -- ERC4626ExceededMaxRedeem
  (s.previewRedeem δ shares).bind fun assets =>
  (spendIfNotOwner s.shares caller owner shares).bind fun sh1 =>
  (sh1.ozBurn owner shares).bind fun sh2 =>
  (s.asset.ozTransfer s.self receiver assets).map fun asset =>
  ({ s with asset := asset, shares := sh2 }, assets)

/-- External state-changing calls on the vault and on the asset (`ERC20Mock`). -/
inductive Op (A : Type) where
  /-- `vault.deposit(assets, receiver)` from `caller`. -/
  | deposit (caller : A) (assets : ℕ) (receiver : A)
  /-- `vault.mint(shares, receiver)` from `caller`. -/
  | mint (caller : A) (shares : ℕ) (receiver : A)
  /-- `vault.withdraw(assets, receiver, owner)` from `caller`. -/
  | withdraw (caller : A) (assets : ℕ) (receiver owner : A)
  /-- `vault.redeem(shares, receiver, owner)` from `caller`. -/
  | redeem (caller : A) (shares : ℕ) (receiver owner : A)
  /-- `vault.transfer(to, amount)` from `caller`. -/
  | transfer (caller dst : A) (amount : ℕ)
  /-- `vault.transferFrom(src, dst, amount)` from `caller`. -/
  | transferFrom (caller src dst : A) (amount : ℕ)
  /-- `vault.approve(spender, amount)` from `caller`. -/
  | approve (caller spender : A) (amount : ℕ)
  /-- `asset.transfer(to, amount)` from `caller` (a donation when `dst = self`). -/
  | assetTransfer (caller dst : A) (amount : ℕ)
  /-- `asset.transferFrom(src, dst, amount)` from `caller`. -/
  | assetTransferFrom (caller src dst : A) (amount : ℕ)
  /-- `asset.approve(spender, amount)` from `caller`. -/
  | assetApprove (caller spender : A) (amount : ℕ)
  /-- `ERC20Mock.mint(to, amount)` (yield when `dst = self`). -/
  | assetMint (dst : A) (amount : ℕ)
  /-- `ERC20Mock.burn(from, amount)` (a loss when `src = self`). -/
  | assetBurn (src : A) (amount : ℕ)

/-- One external call; `none` = revert. -/
def step (δ : ℕ) (s : State A) : Op A → Option (State A)
  | .deposit c a r => (deposit δ s c a r).map Prod.fst
  | .mint c n r => (mint δ s c n r).map Prod.fst
  | .withdraw c a r o => (withdraw δ s c a r o).map Prod.fst
  | .redeem c n r o => (redeem δ s c n r o).map Prod.fst
  | .transfer c d v => (s.shares.ozTransfer c d v).map fun t => { s with shares := t }
  | .transferFrom c src d v =>
      (s.shares.ozTransferFrom c src d v).map fun t => { s with shares := t }
  | .approve c sp v => (s.shares.ozApprove c sp v).map fun t => { s with shares := t }
  | .assetTransfer c d v => (s.asset.ozTransfer c d v).map fun t => { s with asset := t }
  | .assetTransferFrom c src d v =>
      (s.asset.ozTransferFrom c src d v).map fun t => { s with asset := t }
  | .assetApprove c sp v => (s.asset.ozApprove c sp v).map fun t => { s with asset := t }
  | .assetMint d v => (s.asset.ozMint d v).map fun t => { s with asset := t }
  | .assetBurn src v => (s.asset.ozBurn src v).map fun t => { s with asset := t }

/-- A sequence of transactions; a reverted one leaves the state unchanged. -/
def exec (δ : ℕ) (s : State A) : List (Op A) → State A
  | [] => s
  | op :: ops => exec δ ((step δ s op).getD s) ops

/-- The model's global invariant: both ledgers are well formed. -/
def Inv (s : State A) : Prop := s.asset.WF ∧ s.shares.WF

end EvmLeanSpecs.Vault.Oz
