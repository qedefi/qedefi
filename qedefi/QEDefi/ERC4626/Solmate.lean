module

public import QEDefi.ERC20.Token

/-!
# The Solmate ERC-4626 vault, as an abstract state machine

Solmate `ERC4626` + `MockERC4626` (`totalAssets() = asset.balanceOf(this)`, hook counters)
over a `MockERC20` asset. Each entry point is `State A → Option (State A × ℕ)` (`none` =
revert), following the source statement by statement including every revert. `permit`,
events, gas and reentrancy are out of scope; value-flow theorems assume `caller ≠ self`.
-/

section

@[expose] public noncomputable section

namespace QEDefi.ERC4626.Solmate
open QEDefi.Math QEDefi.ERC20 QEDefi.ERC20.Token

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
def maxDeposit (_s : State A) (_receiver : A) : ℕ := MAX

/-- `maxMint(_) = type(uint256).max`. -/
def maxMint (_s : State A) (_receiver : A) : ℕ := MAX

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
  (s.asset.transferFrom s.self caller s.self assets).bind fun asset =>
  (s.shares.mint receiver shares).bind fun sh =>
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
  (sh1.burn owner shares).bind fun sh2 =>
  (s.asset.transfer s.self receiver assets).map fun asset =>
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

/-- State-changing external calls: the vault's entry points and the asset's, which model
donations, yield (`assetMint`) and losses (`assetBurn`). -/
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

end QEDefi.ERC4626.Solmate
end

end

section

/-!
## Effects of the Solmate vault operations

What each successful entry point returned and how the two ledgers changed.
-/

@[expose] public section

namespace QEDefi.ERC4626.Solmate
open QEDefi.Math QEDefi.ERC20 QEDefi.ERC20.Token Finsupp

variable {A : Type} [DecidableEq A]

/-! ## Views -/

theorem convertToShares_eq_some {s : State A} {a n : ℕ} :
    s.convertToShares a = some n ↔
      (s.totalSupply = 0 ∧ n = a) ∨
      (s.totalSupply ≠ 0 ∧ s.totalAssets ≠ 0 ∧ a * s.totalSupply ≤ MAX ∧
        n = a * s.totalSupply / s.totalAssets) := by
  unfold State.convertToShares
  split_ifs with h
  · simp [h, eq_comm]
  · rw [mulDivDown_eq_some]; simp [h]

theorem convertToAssets_eq_some {s : State A} {n a : ℕ} :
    s.convertToAssets n = some a ↔
      (s.totalSupply = 0 ∧ a = n) ∨
      (s.totalSupply ≠ 0 ∧ n * s.totalAssets ≤ MAX ∧ a = n * s.totalAssets / s.totalSupply) := by
  unfold State.convertToAssets
  split_ifs with h
  · simp [h, eq_comm]
  · rw [mulDivDown_eq_some]; simp [h]

theorem previewMint_eq_some {s : State A} {n a : ℕ} :
    s.previewMint n = some a ↔
      (s.totalSupply = 0 ∧ a = n) ∨
      (s.totalSupply ≠ 0 ∧ n * s.totalAssets ≤ MAX ∧
        a = ceilDiv (n * s.totalAssets) s.totalSupply) := by
  unfold State.previewMint
  split_ifs with h
  · simp [h, eq_comm]
  · rw [mulDivUp_eq_some]; simp [h]

theorem previewWithdraw_eq_some {s : State A} {a n : ℕ} :
    s.previewWithdraw a = some n ↔
      (s.totalSupply = 0 ∧ n = a) ∨
      (s.totalSupply ≠ 0 ∧ s.totalAssets ≠ 0 ∧ a * s.totalSupply ≤ MAX ∧
        n = ceilDiv (a * s.totalSupply) s.totalAssets) := by
  unfold State.previewWithdraw
  split_ifs with h
  · simp [h, eq_comm]
  · rw [mulDivUp_eq_some]; simp [h]

/-! ## Entry points -/

theorem spendIfNotOwner_eq_some {t t' : Token A} {c o : A} {n : ℕ}
    (h : spendIfNotOwner t c o n = some t') :
    t'.balanceOf = t.balanceOf ∧ t'.totalSupply = t.totalSupply := by
  unfold spendIfNotOwner at h
  split_ifs at h
  · exact spend_eq_some h
  · cases h; exact ⟨rfl, rfl⟩

theorem deposit_eq_some {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit s c a r = some (s', n)) :
    s.previewDeposit a = some n ∧ n ≠ 0 ∧ a ≤ s.asset.balanceOf c ∧
      s.totalSupply + n ≤ MAX ∧ s'.self = s.self ∧
      s'.asset.balanceOf = s.asset.balanceOf - single c a + single s.self a ∧
      s'.asset.totalSupply = s.asset.totalSupply ∧
      s'.shares.balanceOf = s.shares.balanceOf + single r n ∧
      s'.totalSupply = s.totalSupply + n := by
  unfold deposit at h
  obtain ⟨n', hp, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h with hz
  obtain ⟨asset, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh, hm, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  obtain ⟨hv, hb, hs⟩ := transferFrom_eq_some ha
  obtain ⟨hmx, rfl⟩ := mint_eq_some.1 hm
  exact ⟨hp, hz, hv, hmx, rfl, hb, hs, rfl, rfl⟩

theorem mint_eq_some' {s s' : State A} {c r : A} {n a : ℕ}
    (h : mint s c n r = some (s', a)) :
    s.previewMint n = some a ∧ a ≤ s.asset.balanceOf c ∧
      s.totalSupply + n ≤ MAX ∧ s'.self = s.self ∧
      s'.asset.balanceOf = s.asset.balanceOf - single c a + single s.self a ∧
      s'.asset.totalSupply = s.asset.totalSupply ∧
      s'.shares.balanceOf = s.shares.balanceOf + single r n ∧
      s'.totalSupply = s.totalSupply + n := by
  unfold mint at h
  obtain ⟨a', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh, hm, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  obtain ⟨hv, hb, hs⟩ := transferFrom_eq_some ha
  obtain ⟨hmx, rfl⟩ := mint_eq_some.1 hm
  exact ⟨hp, hv, hmx, rfl, hb, hs, rfl, rfl⟩

theorem withdraw_eq_some {s s' : State A} {c r o : A} {a n : ℕ}
    (h : withdraw s c a r o = some (s', n)) :
    s.previewWithdraw a = some n ∧ n ≤ s.shares.balanceOf o ∧ a ≤ s.totalAssets ∧
      s'.self = s.self ∧
      s'.asset.balanceOf = s.asset.balanceOf - single s.self a + single r a ∧
      s'.asset.totalSupply = s.asset.totalSupply ∧
      s'.shares.balanceOf = s.shares.balanceOf - single o n ∧
      s'.totalSupply = s.totalSupply - n := by
  unfold withdraw at h
  obtain ⟨n', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, hb2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ht, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  obtain ⟨e1, e2⟩ := spendIfNotOwner_eq_some hs1
  obtain ⟨hn, rfl⟩ := burn_eq_some.1 hb2
  obtain ⟨ha, rfl⟩ := transfer_eq_some.1 ht
  exact ⟨hp, e1 ▸ hn, ha, rfl, rfl, rfl, by simp [e1], by simp [State.totalSupply, e2]⟩

theorem redeem_eq_some {s s' : State A} {c r o : A} {n a : ℕ}
    (h : redeem s c n r o = some (s', a)) :
    s.previewRedeem n = some a ∧ a ≠ 0 ∧ n ≤ s.shares.balanceOf o ∧ a ≤ s.totalAssets ∧
      s'.self = s.self ∧
      s'.asset.balanceOf = s.asset.balanceOf - single s.self a + single r a ∧
      s'.asset.totalSupply = s.asset.totalSupply ∧
      s'.shares.balanceOf = s.shares.balanceOf - single o n ∧
      s'.totalSupply = s.totalSupply - n := by
  unfold redeem at h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a', hp, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h with hz
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, hb2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ht, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  obtain ⟨e1, e2⟩ := spendIfNotOwner_eq_some hs1
  obtain ⟨hn, rfl⟩ := burn_eq_some.1 hb2
  obtain ⟨ha, rfl⟩ := transfer_eq_some.1 ht
  exact ⟨hp, hz, e1 ▸ hn, ha, rfl, rfl, rfl, by simp [e1], by simp [State.totalSupply, e2]⟩

/-! ## Total assets after the asset moves -/

theorem totalAssets_in {s s' : State A} {c : A} {a : ℕ} (hc : c ≠ s.self)
    (hself : s'.self = s.self)
    (hb : s'.asset.balanceOf = s.asset.balanceOf - single c a + single s.self a) :
    s'.totalAssets = s.totalAssets + a := by
  simp only [State.totalAssets, hself, hb, move_apply_dst _ _ hc]

theorem totalAssets_out {s s' : State A} {r : A} {a : ℕ} (hr : r ≠ s.self)
    (hself : s'.self = s.self)
    (hb : s'.asset.balanceOf = s.asset.balanceOf - single s.self a + single r a) :
    s'.totalAssets = s.totalAssets - a := by
  simp only [State.totalAssets, hself, hb, move_apply_src _ _ (Ne.symm hr)]

theorem totalAssets_out_self {s s' : State A} {a : ℕ} (ha : a ≤ s.totalAssets)
    (hself : s'.self = s.self)
    (hb : s'.asset.balanceOf = s.asset.balanceOf - single s.self a + single s.self a) :
    s'.totalAssets = s.totalAssets := by
  simp only [State.totalAssets, hself, hb, move_self ha]

/-! ## The invariant -/

theorem Inv_deposit {s s' : State A} {c r : A} {a n : ℕ} (hi : Inv s)
    (h : deposit s c a r = some (s', n)) : Inv s' := by
  unfold deposit at h
  obtain ⟨n', -, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h
  obtain ⟨asset, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh, hm, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨WF_transferFrom hi.1 ha, WF_mint hi.2 hm⟩

theorem Inv_mint {s s' : State A} {c r : A} {n a : ℕ} (hi : Inv s)
    (h : mint s c n r = some (s', a)) : Inv s' := by
  unfold mint at h
  obtain ⟨a', -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh, hm, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨WF_transferFrom hi.1 ha, WF_mint hi.2 hm⟩

theorem WF_spendIfNotOwner {t t' : Token A} {c o : A} {n : ℕ} (hw : t.WF)
    (h : spendIfNotOwner t c o n = some t') : t'.WF := by
  unfold spendIfNotOwner at h
  split_ifs at h
  · exact WF_spend hw h
  · cases h; exact hw

theorem Inv_withdraw {s s' : State A} {c r o : A} {a n : ℕ} (hi : Inv s)
    (h : withdraw s c a r o = some (s', n)) : Inv s' := by
  unfold withdraw at h
  obtain ⟨n', -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, hb2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ht, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨WF_transfer hi.1 ht, WF_burn (WF_spendIfNotOwner hi.2 hs1) hb2⟩

theorem Inv_redeem {s s' : State A} {c r o : A} {n a : ℕ} (hi : Inv s)
    (h : redeem s c n r o = some (s', a)) : Inv s' := by
  unfold redeem at h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a', -, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, hb2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ht, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨WF_transfer hi.1 ht, WF_burn (WF_spendIfNotOwner hi.2 hs1) hb2⟩

theorem Inv_step {s s' : State A} {op : Op A} (hi : Inv s) (h : step s op = some s') :
    Inv s' := by
  cases op with
  | deposit c a r =>
    obtain ⟨⟨s1, n⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact Inv_deposit hi h1
  | mint c n r =>
    obtain ⟨⟨s1, a⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact Inv_mint hi h1
  | withdraw c a r o =>
    obtain ⟨⟨s1, n⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact Inv_withdraw hi h1
  | redeem c n r o =>
    obtain ⟨⟨s1, a⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact Inv_redeem hi h1
  | transfer c d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨hi.1, WF_transfer hi.2 h1⟩
  | transferFrom c src d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨hi.1, WF_transferFrom hi.2 h1⟩
  | approve c sp v =>
    cases h; exact ⟨hi.1, WF_approve hi.2 _ _ _⟩
  | assetTransfer c d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨WF_transfer hi.1 h1, hi.2⟩
  | assetTransferFrom c src d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨WF_transferFrom hi.1 h1, hi.2⟩
  | assetApprove c sp v =>
    cases h; exact ⟨WF_approve hi.1 _ _ _, hi.2⟩
  | assetMint d v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨WF_mint hi.1 h1, hi.2⟩
  | assetBurn src v =>
    obtain ⟨t, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨WF_burn hi.1 h1, hi.2⟩

/-- Any sequence of calls, by any callers with any arguments, preserves `Inv`. -/
theorem Inv_exec {s : State A} (hi : Inv s) (ops : List (Op A)) : Inv (exec s ops) := by
  induction ops generalizing s with
  | nil => exact hi
  | cons op ops ih =>
    apply ih
    cases h : step s op with
    | none => exact hi
    | some s' => exact Inv_step hi h

/-- In every reachable state `totalSupply = Σ balanceOf`, for shares and asset. -/
theorem totalSupply_eq_sum_exec {s : State A} (hi : Inv s) (ops : List (Op A)) :
    (exec s ops).totalSupply = total (exec s ops).shares.balanceOf ∧
      (exec s ops).asset.totalSupply = total (exec s ops).asset.balanceOf :=
  ⟨((Inv_exec hi ops).2.1).symm, ((Inv_exec hi ops).1.1).symm⟩

theorem self_step {s s' : State A} {op : Op A} (h : step s op = some s') : s'.self = s.self := by
  cases op with
  | deposit c a r =>
    obtain ⟨⟨s1, n⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact (deposit_eq_some h1).2.2.2.2.1
  | mint c n r =>
    obtain ⟨⟨s1, a⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact (mint_eq_some' h1).2.2.2.1
  | withdraw c a r o =>
    obtain ⟨⟨s1, n⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h; exact (withdraw_eq_some h1).2.2.2.1
  | redeem c n r o =>
    obtain ⟨⟨s1, a⟩, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    exact (redeem_eq_some h1).2.2.2.2.1
  | transfer | transferFrom | assetTransfer | assetTransferFrom | assetMint | assetBurn =>
    obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.1 h; rfl
  | approve | assetApprove => cases h; rfl

end QEDefi.ERC4626.Solmate
end

end
