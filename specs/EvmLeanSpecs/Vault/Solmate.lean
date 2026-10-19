module

public import EvmLeanSpecs.Vault.Token

/-!
# The Solmate ERC-4626 vault, as an abstract state machine

Mirrors `transmissions11/solmate` `src/tokens/ERC4626.sol` instantiated as
`src/test/utils/mocks/MockERC4626.sol` (`totalAssets() = asset.balanceOf(address(this))`,
hook counters), over a Solmate `MockERC20` asset — the pinned verification target
(`contracts/src/Targets.sol`).

State (`State A`, `A` = addresses):

* `self` — the vault's own address;
* `asset` — the storage of the asset token (`MockERC20`);
* `shares` — the vault's own ERC-20 storage (balances, `totalSupply`, allowances);
* `afterDepositCount`, `beforeWithdrawCount` — `MockERC4626`'s hook counters.

Every external function is a partial function `State A → Option (State A × ℕ)`; `none`
means the transaction reverts (and so leaves the state unchanged). Each one follows the
Solidity source statement by statement, including every place where it can revert:
`mulDivDown`/`mulDivUp` (zero denominator, 256-bit product overflow), `ZERO_SHARES` /
`ZERO_ASSETS`, checked balance and allowance subtractions in both tokens, the checked
`totalSupply += shares` in `_mint`, and the checked hook-counter increments. Unchecked
Solidity arithmetic is `ℕ` arithmetic, sound under `Inv` (see `Token.WF`).

Out of scope: `permit` (EIP-2612; its storage effect is an `approve` by the owner, which
`Op.approve` covers), events, gas, and reentrancy (the asset is `MockERC20`, which makes no
calls). The vault never calls itself, so theorems about value flows assume
`caller ≠ self`.
-/

@[expose] public noncomputable section

namespace EvmLeanSpecs.Vault.Solmate

open Token

/-- Storage of a deployed Solmate `MockERC4626` together with its `MockERC20` asset. -/
structure State (A : Type) where
  /-- `address(this)` of the vault. -/
  self : A
  /-- Storage of the asset token. -/
  asset : Token A
  /-- Storage of the vault's share token. -/
  shares : Token A
  /-- `MockERC4626.afterDepositHookCalledCounter`. -/
  afterDepositCount : ℕ
  /-- `MockERC4626.beforeWithdrawHookCalledCounter`. -/
  beforeWithdrawCount : ℕ

variable {A : Type} [DecidableEq A]

namespace State

variable (s : State A)

/-- `totalAssets() = asset.balanceOf(address(this))`. -/
def totalAssets : ℕ := s.asset.balanceOf s.self

/-- `totalSupply` of shares. -/
def totalSupply : ℕ := s.shares.totalSupply

/-- `convertToShares(assets)`: `supply == 0 ? assets : assets.mulDivDown(supply, totalAssets())`. -/
def convertToShares (assets : ℕ) : Option ℕ :=
  if s.totalSupply = 0 then some assets else mulDivDown assets s.totalSupply s.totalAssets

/-- `convertToAssets(shares)`: `supply == 0 ? shares : shares.mulDivDown(totalAssets(), supply)`. -/
def convertToAssets (shares : ℕ) : Option ℕ :=
  if s.totalSupply = 0 then some shares else mulDivDown shares s.totalAssets s.totalSupply

/-- `previewDeposit(assets) = convertToShares(assets)`. -/
def previewDeposit (assets : ℕ) : Option ℕ := s.convertToShares assets

/-- `previewMint(shares)`: `supply == 0 ? shares : shares.mulDivUp(totalAssets(), supply)`. -/
def previewMint (shares : ℕ) : Option ℕ :=
  if s.totalSupply = 0 then some shares else mulDivUp shares s.totalAssets s.totalSupply

/-- `previewWithdraw(assets)`: `supply == 0 ? assets : assets.mulDivUp(supply, totalAssets())`. -/
def previewWithdraw (assets : ℕ) : Option ℕ :=
  if s.totalSupply = 0 then some assets else mulDivUp assets s.totalSupply s.totalAssets

/-- `previewRedeem(shares) = convertToAssets(shares)`. -/
def previewRedeem (shares : ℕ) : Option ℕ := s.convertToAssets shares

/-- `maxDeposit(_) = type(uint256).max`. -/
def maxDeposit (_receiver : A) : ℕ := MAX

/-- `maxMint(_) = type(uint256).max`. -/
def maxMint (_receiver : A) : ℕ := MAX

/-- `maxWithdraw(owner) = convertToAssets(balanceOf[owner])`. -/
def maxWithdraw (owner : A) : Option ℕ := s.convertToAssets (s.shares.balanceOf owner)

/-- `maxRedeem(owner) = balanceOf[owner]`. -/
def maxRedeem (owner : A) : ℕ := s.shares.balanceOf owner

end State

/-- A checked `counter++` (reverts at `type(uint256).max`). -/
def bump (c : ℕ) : Option ℕ := checkedAdd c 1

/-- `deposit(assets, receiver)` called by `caller`. Returns the shares minted. -/
def deposit (s : State A) (caller : A) (assets : ℕ) (receiver : A) : Option (State A × ℕ) :=
  (s.previewDeposit assets).bind fun shares =>
  if shares = 0 then none else                                    -- "ZERO_SHARES"
  (s.asset.transferFrom s.self caller s.self assets).bind fun asset =>  -- safeTransferFrom
  (s.shares.mint receiver shares).bind fun sh =>                   -- _mint
  (bump s.afterDepositCount).map fun c =>                          -- afterDeposit
  ({ s with asset := asset, shares := sh, afterDepositCount := c }, shares)

/-- `mint(shares, receiver)` called by `caller`. Returns the assets pulled in. -/
def mint (s : State A) (caller : A) (shares : ℕ) (receiver : A) : Option (State A × ℕ) :=
  (s.previewMint shares).bind fun assets =>
  (s.asset.transferFrom s.self caller s.self assets).bind fun asset =>
  (s.shares.mint receiver shares).bind fun sh =>
  (bump s.afterDepositCount).map fun c =>
  ({ s with asset := asset, shares := sh, afterDepositCount := c }, assets)

/-- The allowance step of `withdraw`/`redeem`: only when `msg.sender != owner`. -/
def spendIfNotOwner (t : Token A) (caller owner : A) (shares : ℕ) : Option (Token A) :=
  if caller ≠ owner then t.spend owner caller shares else some t

/-- `withdraw(assets, receiver, owner)` called by `caller`. Returns the shares burned. -/
def withdraw (s : State A) (caller : A) (assets : ℕ) (receiver owner : A) :
    Option (State A × ℕ) :=
  (s.previewWithdraw assets).bind fun shares =>
  (spendIfNotOwner s.shares caller owner shares).bind fun sh1 =>
  (bump s.beforeWithdrawCount).bind fun c =>                       -- beforeWithdraw
  (sh1.burn owner shares).bind fun sh2 =>                          -- _burn
  (s.asset.transfer s.self receiver assets).map fun asset =>       -- safeTransfer
  ({ s with asset := asset, shares := sh2, beforeWithdrawCount := c }, shares)

/-- `redeem(shares, receiver, owner)` called by `caller`. Returns the assets paid out. -/
def redeem (s : State A) (caller : A) (shares : ℕ) (receiver owner : A) :
    Option (State A × ℕ) :=
  (spendIfNotOwner s.shares caller owner shares).bind fun sh1 =>
  (s.previewRedeem shares).bind fun assets =>
  if assets = 0 then none else                                     -- "ZERO_ASSETS"
  (bump s.beforeWithdrawCount).bind fun c =>
  (sh1.burn owner shares).bind fun sh2 =>
  (s.asset.transfer s.self receiver assets).map fun asset =>
  ({ s with asset := asset, shares := sh2, beforeWithdrawCount := c }, assets)

/-- External calls that change state: the vault's ERC-4626 and ERC-20 entry points, and the
asset's (`MockERC20`) entry points, which model donations (`assetTransfer` to the vault),
yield (`assetMint` to the vault) and losses (`assetBurn` from the vault). -/
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
  /-- `MockERC20.mint(to, amount)` (yield when `dst = self`). -/
  | assetMint (dst : A) (amount : ℕ)
  /-- `MockERC20.burn(from, amount)` (a loss when `src = self`). -/
  | assetBurn (src : A) (amount : ℕ)

/-- One external call; `none` = revert. -/
def step (s : State A) : Op A → Option (State A)
  | .deposit c a r => (deposit s c a r).map Prod.fst
  | .mint c n r => (mint s c n r).map Prod.fst
  | .withdraw c a r o => (withdraw s c a r o).map Prod.fst
  | .redeem c n r o => (redeem s c n r o).map Prod.fst
  | .transfer c d v => (s.shares.transfer c d v).map fun t => { s with shares := t }
  | .transferFrom c src d v =>
      (s.shares.transferFrom c src d v).map fun t => { s with shares := t }
  | .approve c sp v => some { s with shares := s.shares.approve c sp v }
  | .assetTransfer c d v => (s.asset.transfer c d v).map fun t => { s with asset := t }
  | .assetTransferFrom c src d v =>
      (s.asset.transferFrom c src d v).map fun t => { s with asset := t }
  | .assetApprove c sp v => some { s with asset := s.asset.approve c sp v }
  | .assetMint d v => (s.asset.mint d v).map fun t => { s with asset := t }
  | .assetBurn src v => (s.asset.burn src v).map fun t => { s with asset := t }

/-- A sequence of transactions; a reverted one leaves the state unchanged. -/
def exec (s : State A) : List (Op A) → State A
  | [] => s
  | op :: ops => exec ((step s op).getD s) ops

/-- The model's global invariant: both ledgers are well formed. -/
def Inv (s : State A) : Prop := s.asset.WF ∧ s.shares.WF

end EvmLeanSpecs.Vault.Solmate
