module

public import Defi.ERC4626.SolmateProps
public import Defi.ERC4626.OzProps
public import Defi.ERC20.VariantProps

/-!
# The vaults over an arbitrary asset

The Solmate and OpenZeppelin vault models (`Solmate.lean`, `Oz.lean`) fix their asset to a
`Token`. Here both are generalised to any `Asset σ A`: a state type `σ` with the balance view
and the two calls a vault makes (`transferFrom(caller → vault)` on deposit/mint,
`transfer(vault → receiver)` on withdraw/redeem). `GSolmate` and `GOz` are the vault models
statement by statement with the asset calls replaced; `GSolmate.deposit_solmate` … show that
over `Asset.solmate` (`Token`'s operations) they are the existing models, `GOz.deposit_oz` …
likewise over `Asset.oz`.

`Asset.variant V` is a token `Variant` called through `SafeTransferLib`/`SafeERC20`
(`Result.safe`), which is what both vaults use. The vault theorems below need only
`Asset.ExactOn`: pulling `v` into the vault raises its balance by exactly `v`, sending `v` out
lowers it by exactly `v`. `variant_exactOn` proves it for every variant whose fee is zero in
the current state, for every return and failure convention, rebasing tokens included.

Proved here for any asset: the share ledger stays well formed (`Inv_step`), solvency
(`solvent`); for an exact asset: no dilution (`deposit_price_mono` … for Solmate while
`S > 0`, unconditionally for OpenZeppelin).
-/

@[expose] public noncomputable section

namespace Defi.ERC4626
open Defi.Math Defi.ERC20 Defi.ERC20.Token Finsupp

/-- What a vault needs from its asset: the balance view and the two calls it makes. -/
structure Asset (σ A : Type) where
  /-- `asset.balanceOf(a)`. -/
  balanceOf : σ → A → ℕ
  /-- `asset.transfer(dst, v)` by `caller` (the vault paying out); `none` = the vault reverts. -/
  transfer : σ → A → A → ℕ → Option σ
  /-- `asset.transferFrom(src, dst, v)` by `caller` (the vault pulling a deposit). -/
  transferFrom : σ → A → A → A → ℕ → Option σ

namespace Asset

variable {σ A : Type} [DecidableEq A]

/-- Solmate `MockERC20` (the `Token` operations). -/
def solmate : Asset (Token A) A :=
  ⟨fun t a => t.balanceOf a, Token.transfer, Token.transferFrom⟩

/-- OpenZeppelin `ERC20Mock` (the `Token.oz*` operations). -/
def oz [Zero A] : Asset (Token A) A :=
  ⟨fun t a => t.balanceOf a, Token.ozTransfer, Token.ozTransferFrom⟩

/-- A token `Variant`, called through `SafeTransferLib`/`SafeERC20`. -/
def variant [Zero A] (V : Variant A) : Asset (VState A) A :=
  ⟨V.balanceOf, fun s c d v => (V.call s c (.transfer d v)).safe,
    fun s c src d v => (V.call s c (.transferFrom src d v)).safe⟩

/-- Exact accounting at the vault `self`, in states satisfying `P`: a pull of `v` from
`c ≠ self` raises `self`'s balance by exactly `v`; a push of `v` needs `v` and lowers the
balance by exactly `v` (leaves it when sent to `self`). -/
structure ExactOn (M : Asset σ A) (P : σ → Prop) (vault : A) : Prop where
  /-- Pulls are exact. -/
  pull : ∀ {s s' : σ} {c : A} {v : ℕ}, P s → c ≠ vault →
    M.transferFrom s vault c vault v = some s' → M.balanceOf s' vault = M.balanceOf s vault + v
  /-- Pushes are exact. -/
  push : ∀ {s s' : σ} {r : A} {v : ℕ}, P s → M.transfer s vault r v = some s' →
    v ≤ M.balanceOf s vault ∧
      M.balanceOf s' vault = if r = vault then M.balanceOf s vault else M.balanceOf s vault - v

theorem solmate_exactOn (self : A) : (solmate : Asset (Token A) A).ExactOn (fun _ => True) self where
  pull := by
    intro s s' c v _ hc h
    obtain ⟨-, hb, -⟩ := Token.transferFrom_eq_some h
    show s'.balanceOf self = s.balanceOf self + v
    rw [hb, move_apply_dst _ _ hc]
  push := by
    intro s s' r v _ h
    obtain ⟨hv, rfl⟩ := Token.transfer_eq_some.1 h
    refine ⟨hv, ?_⟩
    show (s.balanceOf - single self v + single r v) self = _
    split_ifs with hr
    · subst hr; rw [move_self hv]; rfl
    · rw [move_apply_src _ _ (Ne.symm hr)]; rfl

theorem oz_exactOn [Zero A] (self : A) : (oz : Asset (Token A) A).ExactOn (fun _ => True) self where
  pull := by
    intro s s' c v _ hc h
    obtain ⟨-, hb, -⟩ := Token.ozTransferFrom_eq_some h
    show s'.balanceOf self = s.balanceOf self + v
    rw [hb, move_apply_dst _ _ hc]
  push := by
    intro s s' r v _ h
    obtain ⟨-, -, hv, hb, -⟩ := Token.ozTransfer_eq_some h
    refine ⟨hv, ?_⟩
    show s'.balanceOf self = _
    rw [hb]
    split_ifs with hr
    · subst hr; rw [move_self hv]; rfl
    · rw [move_apply_src _ _ (Ne.symm hr)]; rfl

/-- The states in which a variant transfers exactly: no fee on any value, and a positive
scale if it rebases. -/
def NoFee [Zero A] (V : Variant A) (s : VState A) : Prop :=
  (∀ v, V.feeOf s v = 0) ∧ (V.rebasing = true → 0 < s.scale)

theorem feeOf_congr [Zero A] (V : Variant A) {s s' : VState A} (h1 : s'.feeBps = s.feeBps)
    (h2 : s'.feeMax = s.feeMax) (v : ℕ) : V.feeOf s' v = V.feeOf s v := by
  unfold Variant.feeOf; rw [h1, h2]

theorem balanceOf_congr [Zero A] (V : Variant A) {s s' : VState A} (h1 : s'.bal = s.bal)
    (h2 : s'.scale = s.scale) (a : A) : V.balanceOf s' a = V.balanceOf s a := by
  unfold Variant.balanceOf; rw [h1, h2]

/-- **Exact accounting of every fee-free variant**, whatever its return-data and failure
conventions (USDT returning nothing and failing with `INVALID`, BNB, …) and including
rebasing tokens: through `SafeTransferLib` the vault sees exactly the `Token` balance moves. -/
theorem variant_exactOn [Zero A] (V : Variant A) (self : A) :
    (variant V).ExactOn (NoFee V) self where
  pull := by
    intro s s' c v hP hc h
    simp only [variant, Variant.safe_call, Variant.step] at h
    obtain ⟨s1, h1, h2⟩ := V.transferFrom_eq_some h
    obtain ⟨e1, -, e3, -, -, -, e7, e8, -⟩ := V.spend_eq_some h1
    have hf : V.feeOf s1 v = 0 := by rw [feeOf_congr V e7 e8]; exact hP.1 v
    have hk : V.rebasing = true → 0 < s1.scale := fun hr => e3 ▸ hP.2 hr
    obtain ⟨-, -, -, hdst, -, -⟩ := V.move_balanceOf hf hk h2
    show V.balanceOf s' self = V.balanceOf s self + v
    rw [hdst hc, balanceOf_congr V e1 e3]
  push := by
    intro s s' r v hP h
    simp only [variant, Variant.safe_call, Variant.step, Variant.transfer] at h
    split_ifs at h
    obtain ⟨hv, -, hsrc, -, -, hsame⟩ := V.move_balanceOf (hP.1 v) hP.2 h
    refine ⟨hv, ?_⟩
    show V.balanceOf s' self = _
    split_ifs with hr
    · exact hsame hr.symm
    · exact hsrc (Ne.symm hr)

theorem variant_transferFrom [Zero A] (V : Variant A) (s : VState A) (c src d : A) (v : ℕ) :
    (variant V).transferFrom s c src d v = V.transferFrom s c src d v := by
  simp [variant, Variant.safe_call, Variant.step]

theorem variant_transfer [Zero A] (V : Variant A) (s : VState A) (c d : A) (v : ℕ) :
    (variant V).transfer s c d v = V.transfer s c d v := by
  simp [variant, Variant.safe_call, Variant.step]

end Asset

theorem _root_.Option.map_ite_none {α β : Type} {c : Prop} [Decidable c] (f : α → β)
    (x : Option α) : (if c then none else x).map f = if c then none else x.map f := by
  split <;> rfl

/-! ## The Solmate vault over an arbitrary asset -/

namespace GSolmate

/-- Storage of a Solmate `MockERC4626` over an asset with state type `σ`. -/
structure State (σ A : Type) where
  /-- `address(this)` of the vault. -/
  self : A
  /-- The asset's state. -/
  asset : σ
  /-- The vault's share token. -/
  shares : Token A
  /-- `afterDepositHookCalledCounter`. -/
  afterDepositCount : ℕ
  /-- `beforeWithdrawHookCalledCounter`. -/
  beforeWithdrawCount : ℕ

variable {σ A : Type} [DecidableEq A] (M : Asset σ A)

/-- `totalAssets() = asset.balanceOf(address(this))`. -/
def totalAssets (s : State σ A) : ℕ := M.balanceOf s.asset s.self

/-- `totalSupply` of shares. -/
def totalSupply (s : State σ A) : ℕ := s.shares.totalSupply

/-- `convertToShares(assets)`. -/
def convertToShares (s : State σ A) (assets : ℕ) : Option ℕ :=
  if totalSupply s = 0 then some assets else mulDivDown assets (totalSupply s) (totalAssets M s)

/-- `convertToAssets(shares)`. -/
def convertToAssets (s : State σ A) (shares : ℕ) : Option ℕ :=
  if totalSupply s = 0 then some shares else mulDivDown shares (totalAssets M s) (totalSupply s)

/-- `previewMint(shares)`. -/
def previewMint (s : State σ A) (shares : ℕ) : Option ℕ :=
  if totalSupply s = 0 then some shares else mulDivUp shares (totalAssets M s) (totalSupply s)

/-- `previewWithdraw(assets)`. -/
def previewWithdraw (s : State σ A) (assets : ℕ) : Option ℕ :=
  if totalSupply s = 0 then some assets else mulDivUp assets (totalSupply s) (totalAssets M s)

/-- `deposit(assets, receiver)` called by `caller`. -/
def deposit (s : State σ A) (caller : A) (assets : ℕ) (receiver : A) :
    Option (State σ A × ℕ) :=
  (convertToShares M s assets).bind fun shares =>
  if shares = 0 then none else
  (M.transferFrom s.asset s.self caller s.self assets).bind fun asset =>
  (s.shares.mint receiver shares).bind fun sh =>
  (Solmate.bump s.afterDepositCount).map fun c =>
  ({ s with asset := asset, shares := sh, afterDepositCount := c }, shares)

/-- `mint(shares, receiver)` called by `caller`. -/
def mint (s : State σ A) (caller : A) (shares : ℕ) (receiver : A) : Option (State σ A × ℕ) :=
  (previewMint M s shares).bind fun assets =>
  (M.transferFrom s.asset s.self caller s.self assets).bind fun asset =>
  (s.shares.mint receiver shares).bind fun sh =>
  (Solmate.bump s.afterDepositCount).map fun c =>
  ({ s with asset := asset, shares := sh, afterDepositCount := c }, assets)

/-- `withdraw(assets, receiver, owner)` called by `caller`. -/
def withdraw (s : State σ A) (caller : A) (assets : ℕ) (receiver owner : A) :
    Option (State σ A × ℕ) :=
  (previewWithdraw M s assets).bind fun shares =>
  (Solmate.spendIfNotOwner s.shares caller owner shares).bind fun sh1 =>
  (Solmate.bump s.beforeWithdrawCount).bind fun c =>
  (sh1.burn owner shares).bind fun sh2 =>
  (M.transfer s.asset s.self receiver assets).map fun asset =>
  ({ s with asset := asset, shares := sh2, beforeWithdrawCount := c }, shares)

/-- `redeem(shares, receiver, owner)` called by `caller`. -/
def redeem (s : State σ A) (caller : A) (shares : ℕ) (receiver owner : A) :
    Option (State σ A × ℕ) :=
  (Solmate.spendIfNotOwner s.shares caller owner shares).bind fun sh1 =>
  (convertToAssets M s shares).bind fun assets =>
  if assets = 0 then none else
  (Solmate.bump s.beforeWithdrawCount).bind fun c =>
  (sh1.burn owner shares).bind fun sh2 =>
  (M.transfer s.asset s.self receiver assets).map fun asset =>
  ({ s with asset := asset, shares := sh2, beforeWithdrawCount := c }, assets)

/-- The share ledger is well formed. -/
def Inv (s : State σ A) : Prop := s.shares.WF

/-! ### Over `Token`, this is the Solmate model -/

/-- A Solmate model state as a generic one. -/
def ofSolmate (s : Solmate.State A) : State (Token A) A :=
  ⟨s.self, s.asset, s.shares, s.afterDepositCount, s.beforeWithdrawCount⟩

theorem totalAssets_solmate (s : Solmate.State A) :
    totalAssets Asset.solmate (ofSolmate s) = s.totalAssets := rfl

theorem deposit_solmate (s : Solmate.State A) (c : A) (a : ℕ) (r : A) :
    deposit Asset.solmate (ofSolmate s) c a r =
      (Solmate.deposit s c a r).map fun p => (ofSolmate p.1, p.2) := by
  simp only [deposit, Solmate.deposit, Solmate.State.previewDeposit, convertToShares,
    Solmate.State.convertToShares, Option.map_bind, Function.comp_def, Option.map_ite_none, Option.map_map]
  rfl

theorem mint_solmate (s : Solmate.State A) (c : A) (n : ℕ) (r : A) :
    mint Asset.solmate (ofSolmate s) c n r =
      (Solmate.mint s c n r).map fun p => (ofSolmate p.1, p.2) := by
  simp only [mint, Solmate.mint, previewMint, Solmate.State.previewMint, Option.map_bind,
    Function.comp_def, Option.map_map]
  rfl

theorem withdraw_solmate (s : Solmate.State A) (c : A) (a : ℕ) (r o : A) :
    withdraw Asset.solmate (ofSolmate s) c a r o =
      (Solmate.withdraw s c a r o).map fun p => (ofSolmate p.1, p.2) := by
  simp only [withdraw, Solmate.withdraw, previewWithdraw, Solmate.State.previewWithdraw,
    Option.map_bind, Function.comp_def, Option.map_map]
  rfl

theorem redeem_solmate (s : Solmate.State A) (c : A) (n : ℕ) (r o : A) :
    redeem Asset.solmate (ofSolmate s) c n r o =
      (Solmate.redeem s c n r o).map fun p => (ofSolmate p.1, p.2) := by
  simp only [redeem, Solmate.redeem, convertToAssets, Solmate.State.previewRedeem,
    Solmate.State.convertToAssets, Option.map_bind, Function.comp_def, Option.map_ite_none, Option.map_map]
  rfl

/-! ### Effects -/

variable {M}

theorem deposit_eq_some {s s' : State σ A} {c r : A} {a n : ℕ}
    (h : deposit M s c a r = some (s', n)) :
    convertToShares M s a = some n ∧ n ≠ 0 ∧
      M.transferFrom s.asset s.self c s.self a = some s'.asset ∧ s'.self = s.self ∧
      s.shares.mint r n = some s'.shares := by
  unfold deposit at h
  obtain ⟨n', hp, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h with hz
  obtain ⟨asset, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh, hm, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨hp, hz, ha, rfl, hm⟩

theorem mint_eq_some {s s' : State σ A} {c r : A} {n a : ℕ}
    (h : mint M s c n r = some (s', a)) :
    previewMint M s n = some a ∧ M.transferFrom s.asset s.self c s.self a = some s'.asset ∧
      s'.self = s.self ∧ s.shares.mint r n = some s'.shares := by
  unfold mint at h
  obtain ⟨a', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh, hm, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨hp, ha, rfl, hm⟩

theorem withdraw_eq_some {s s' : State σ A} {c r o : A} {a n : ℕ}
    (h : withdraw M s c a r o = some (s', n)) :
    previewWithdraw M s a = some n ∧ M.transfer s.asset s.self r a = some s'.asset ∧
      s'.self = s.self ∧ ∃ sh1, Solmate.spendIfNotOwner s.shares c o n = some sh1 ∧
        sh1.burn o n = some s'.shares := by
  unfold withdraw at h
  obtain ⟨n', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, hb2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ht, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨hp, ht, rfl, sh1, hs1, hb2⟩

theorem redeem_eq_some {s s' : State σ A} {c r o : A} {n a : ℕ}
    (h : redeem M s c n r o = some (s', a)) :
    convertToAssets M s n = some a ∧ a ≠ 0 ∧ M.transfer s.asset s.self r a = some s'.asset ∧
      s'.self = s.self ∧ ∃ sh1, Solmate.spendIfNotOwner s.shares c o n = some sh1 ∧
        sh1.burn o n = some s'.shares := by
  unfold redeem at h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a', hp, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h with hz
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, hb2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ht, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨hp, hz, ht, rfl, sh1, hs1, hb2⟩

/-- `withdraw`/`redeem` burn `n` shares of the owner: `n ≤ balance`, supply drops by `n`. -/
theorem burn_shares {t t' t'' : Token A} {c o : A} {n : ℕ}
    (h1 : Solmate.spendIfNotOwner t c o n = some t') (h2 : t'.burn o n = some t'') :
    n ≤ t.balanceOf o ∧ t''.totalSupply = t.totalSupply - n := by
  obtain ⟨e1, e2⟩ := Solmate.spendIfNotOwner_eq_some h1
  obtain ⟨hn, rfl⟩ := Token.burn_eq_some.1 h2
  exact ⟨e1 ▸ hn, by simp [e2]⟩

/-! ### The share ledger and solvency, for any asset -/

theorem Inv_deposit {s s' : State σ A} {c r : A} {a n : ℕ} (hi : Inv s)
    (h : deposit M s c a r = some (s', n)) : Inv s' :=
  WF_mint hi (deposit_eq_some h).2.2.2.2

theorem Inv_mint {s s' : State σ A} {c r : A} {n a : ℕ} (hi : Inv s)
    (h : mint M s c n r = some (s', a)) : Inv s' :=
  WF_mint hi (mint_eq_some h).2.2.2

theorem Inv_withdraw {s s' : State σ A} {c r o : A} {a n : ℕ} (hi : Inv s)
    (h : withdraw M s c a r o = some (s', n)) : Inv s' := by
  obtain ⟨-, -, -, sh1, h1, h2⟩ := withdraw_eq_some h
  exact WF_burn (Solmate.WF_spendIfNotOwner hi h1) h2

theorem Inv_redeem {s s' : State σ A} {c r o : A} {n a : ℕ} (hi : Inv s)
    (h : redeem M s c n r o = some (s', a)) : Inv s' := by
  obtain ⟨-, -, -, -, sh1, h1, h2⟩ := redeem_eq_some h
  exact WF_burn (Solmate.WF_spendIfNotOwner hi h1) h2

/-- **Solvency, for any asset.** `Σₓ ⌊balanceOf[x]·T/S⌋ ≤ T` whenever the share ledger is
well formed (`T` is whatever the asset reports for the vault). -/
theorem solvent (s : State σ A) (hi : Inv s) :
    (s.shares.balanceOf.sum fun _ b => b * totalAssets M s / totalSupply s) ≤ totalAssets M s := by
  have hsum : total s.shares.balanceOf = totalSupply s := hi.1
  by_cases hS : totalSupply s = 0
  · simp [hS]
  · have hpos := Nat.pos_of_ne_zero hS
    unfold Finsupp.sum
    rw [← Nat.mul_le_mul_right_iff hpos]
    calc (∑ x ∈ s.shares.balanceOf.support,
            s.shares.balanceOf x * totalAssets M s / totalSupply s) * totalSupply s
        = ∑ x ∈ s.shares.balanceOf.support,
            s.shares.balanceOf x * totalAssets M s / totalSupply s * totalSupply s :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ x ∈ s.shares.balanceOf.support, s.shares.balanceOf x * totalAssets M s :=
          Finset.sum_le_sum fun _ _ => Nat.div_mul_le_self _ _
      _ = total s.shares.balanceOf * totalAssets M s := by
          unfold total Finsupp.sum; rw [Finset.sum_mul]
      _ = totalAssets M s * totalSupply s := by rw [hsum, Nat.mul_comm]

/-! ### Rounding -/

theorem deposit_rounding {s s' : State σ A} {c r : A} {a n : ℕ}
    (h : deposit M s c a r = some (s', n)) (hS : totalSupply s ≠ 0) :
    n * totalAssets M s ≤ a * totalSupply s ∧ a * totalSupply s < (n + 1) * totalAssets M s := by
  have hp := (deposit_eq_some h).1
  unfold convertToShares at hp
  simp only [hS, ↓reduceIte, mulDivDown_eq_some] at hp
  obtain ⟨hT, -, rfl⟩ := hp
  exact ⟨Nat.div_mul_le_self _ _, lt_div_add_one_mul _ _ (Nat.pos_of_ne_zero hT)⟩

theorem mint_rounding {s s' : State σ A} {c r : A} {n a : ℕ}
    (h : mint M s c n r = some (s', a)) (hS : totalSupply s ≠ 0) :
    n * totalAssets M s ≤ a * totalSupply s := by
  have hp := (mint_eq_some h).1
  unfold previewMint at hp
  simp only [hS, ↓reduceIte, mulDivUp_eq_some] at hp
  obtain ⟨-, -, rfl⟩ := hp
  exact le_ceilDiv_mul _ _ (Nat.pos_of_ne_zero hS)

theorem withdraw_rounding {s s' : State σ A} {c r o : A} {a n : ℕ}
    (h : withdraw M s c a r o = some (s', n)) (hS : totalSupply s ≠ 0) :
    a * totalSupply s ≤ n * totalAssets M s := by
  have hp := (withdraw_eq_some h).1
  unfold previewWithdraw at hp
  simp only [hS, ↓reduceIte, mulDivUp_eq_some] at hp
  obtain ⟨hT, -, rfl⟩ := hp
  exact le_ceilDiv_mul _ _ (Nat.pos_of_ne_zero hT)

theorem redeem_rounding {s s' : State σ A} {c r o : A} {n a : ℕ}
    (h : redeem M s c n r o = some (s', a)) (hS : totalSupply s ≠ 0) :
    a * totalSupply s ≤ n * totalAssets M s := by
  have hp := (redeem_eq_some h).1
  unfold convertToAssets at hp
  simp only [hS, ↓reduceIte, mulDivDown_eq_some] at hp
  obtain ⟨-, -, rfl⟩ := hp
  exact Nat.div_mul_le_self _ _

/-! ### No dilution, for an exact asset -/

variable {P : σ → Prop}

/-- A deposit never lowers assets per share (`T·S' ≤ T'·S`) when the asset is exact. -/
theorem deposit_price_mono {s s' : State σ A} {c r : A} {a n : ℕ} (hM : M.ExactOn P s.self)
    (hP : P s.asset) (h : deposit M s c a r = some (s', n)) (hc : c ≠ s.self)
    (hS : totalSupply s ≠ 0) :
    totalAssets M s * totalSupply s' ≤ totalAssets M s' * totalSupply s := by
  obtain ⟨-, -, ha, hself, hm⟩ := deposit_eq_some h
  have hT : totalAssets M s' = totalAssets M s + a := by
    unfold totalAssets; rw [hself]; exact hM.pull hP hc ha
  have hS' : totalSupply s' = totalSupply s + n := by
    obtain ⟨-, e⟩ := Token.mint_eq_some.1 hm; unfold totalSupply; rw [e]
  have := (deposit_rounding h hS).1
  rw [hT, hS']; nlinarith

theorem mint_price_mono {s s' : State σ A} {c r : A} {n a : ℕ} (hM : M.ExactOn P s.self)
    (hP : P s.asset) (h : mint M s c n r = some (s', a)) (hc : c ≠ s.self)
    (hS : totalSupply s ≠ 0) :
    totalAssets M s * totalSupply s' ≤ totalAssets M s' * totalSupply s := by
  obtain ⟨-, ha, hself, hm⟩ := mint_eq_some h
  have hT : totalAssets M s' = totalAssets M s + a := by
    unfold totalAssets; rw [hself]; exact hM.pull hP hc ha
  have hS' : totalSupply s' = totalSupply s + n := by
    obtain ⟨-, e⟩ := Token.mint_eq_some.1 hm; unfold totalSupply; rw [e]
  have := mint_rounding h hS
  rw [hT, hS']; nlinarith

theorem out_price_mono {T T' S S' a n : ℕ} (hS' : S' = S - n) (hnS : n ≤ S) (ha : a ≤ T)
    (hT : T' = T ∨ T' = T - a) (hr : a * S ≤ n * T) : T * S' ≤ T' * S := by
  rw [hS']
  rcases hT with rfl | rfl
  · exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  · obtain ⟨T₁, rfl⟩ := Nat.exists_eq_add_of_le ha
    obtain ⟨S₁, rfl⟩ := Nat.exists_eq_add_of_le hnS
    simp only [Nat.add_sub_cancel_left]
    nlinarith

theorem withdraw_price_mono {s s' : State σ A} {c r o : A} {a n : ℕ} (hM : M.ExactOn P s.self)
    (hP : P s.asset) (hi : Inv s) (h : withdraw M s c a r o = some (s', n))
    (hS : totalSupply s ≠ 0) :
    totalAssets M s * totalSupply s' ≤ totalAssets M s' * totalSupply s := by
  obtain ⟨-, ht, hself, sh1, h1, h2⟩ := withdraw_eq_some h
  obtain ⟨hn, hsS⟩ := burn_shares h1 h2
  obtain ⟨ha, hb⟩ := hM.push hP ht
  refine out_price_mono (a := a) (n := n) hsS (hn.trans (balanceOf_le_totalSupply hi o)) ha ?_
    (withdraw_rounding h hS)
  unfold totalAssets; rw [hself, hb]
  split_ifs <;> simp

theorem redeem_price_mono {s s' : State σ A} {c r o : A} {n a : ℕ} (hM : M.ExactOn P s.self)
    (hP : P s.asset) (hi : Inv s) (h : redeem M s c n r o = some (s', a))
    (hS : totalSupply s ≠ 0) :
    totalAssets M s * totalSupply s' ≤ totalAssets M s' * totalSupply s := by
  obtain ⟨-, -, ht, hself, sh1, h1, h2⟩ := redeem_eq_some h
  obtain ⟨hn, hsS⟩ := burn_shares h1 h2
  obtain ⟨ha, hb⟩ := hM.push hP ht
  refine out_price_mono (a := a) (n := n) hsS (hn.trans (balanceOf_le_totalSupply hi o)) ha ?_
    (redeem_rounding h hS)
  unfold totalAssets; rw [hself, hb]
  split_ifs <;> simp

end GSolmate

/-! ## The OpenZeppelin vault over an arbitrary asset -/

namespace GOz

/-- Storage of an OpenZeppelin ERC-4626 vault over an asset with state type `σ`. -/
structure State (σ A : Type) where
  /-- `address(this)` of the vault. -/
  self : A
  /-- The asset's state. -/
  asset : σ
  /-- The vault's share token. -/
  shares : Token A

variable {σ A : Type} [DecidableEq A] [Zero A] (M : Asset σ A) (δ : ℕ)

/-- `totalAssets() = asset.balanceOf(address(this))`. -/
def totalAssets (s : State σ A) : ℕ := M.balanceOf s.asset s.self

/-- `totalSupply()` of shares. -/
def totalSupply (s : State σ A) : ℕ := s.shares.totalSupply

/-- Virtual supply `Ŝ = totalSupply + 10^δ`. -/
def vS (s : State σ A) : ℕ := totalSupply s + 10 ^ δ

/-- Virtual assets `T̂ = totalAssets + 1`. -/
def vT (s : State σ A) : ℕ := totalAssets M s + 1

/-- `_convertToShares(assets, rounding)`. -/
def toShares (s : State σ A) (assets : ℕ) (up : Bool) : Option ℕ :=
  (checkedAdd (totalSupply s) (10 ^ δ)).bind fun sv =>
  (checkedAdd (totalAssets M s) 1).bind fun tv =>
  ozMulDiv assets sv tv up

/-- `_convertToAssets(shares, rounding)`. -/
def toAssets (s : State σ A) (shares : ℕ) (up : Bool) : Option ℕ :=
  (checkedAdd (totalAssets M s) 1).bind fun tv =>
  (checkedAdd (totalSupply s) (10 ^ δ)).bind fun sv =>
  ozMulDiv shares tv sv up

/-- `deposit(assets, receiver)` called by `caller`. -/
def deposit (s : State σ A) (caller : A) (assets : ℕ) (receiver : A) :
    Option (State σ A × ℕ) :=
  if MAX < assets then none else
  (toShares M δ s assets false).bind fun shares =>
  (M.transferFrom s.asset s.self caller s.self assets).bind fun asset =>
  (s.shares.ozMint receiver shares).map fun sh =>
  ({ s with asset := asset, shares := sh }, shares)

/-- `mint(shares, receiver)` called by `caller`. -/
def mint (s : State σ A) (caller : A) (shares : ℕ) (receiver : A) : Option (State σ A × ℕ) :=
  if MAX < shares then none else
  (toAssets M δ s shares true).bind fun assets =>
  (M.transferFrom s.asset s.self caller s.self assets).bind fun asset =>
  (s.shares.ozMint receiver shares).map fun sh =>
  ({ s with asset := asset, shares := sh }, assets)

/-- `withdraw(assets, receiver, owner)` called by `caller`. -/
def withdraw (s : State σ A) (caller : A) (assets : ℕ) (receiver owner : A) :
    Option (State σ A × ℕ) :=
  (toAssets M δ s (s.shares.balanceOf owner) false).bind fun maxAssets =>
  if maxAssets < assets then none else
  (toShares M δ s assets true).bind fun shares =>
  (Oz.spendIfNotOwner s.shares caller owner shares).bind fun sh1 =>
  (sh1.ozBurn owner shares).bind fun sh2 =>
  (M.transfer s.asset s.self receiver assets).map fun asset =>
  ({ s with asset := asset, shares := sh2 }, shares)

/-- `redeem(shares, receiver, owner)` called by `caller`. -/
def redeem (s : State σ A) (caller : A) (shares : ℕ) (receiver owner : A) :
    Option (State σ A × ℕ) :=
  if s.shares.balanceOf owner < shares then none else
  (toAssets M δ s shares false).bind fun assets =>
  (Oz.spendIfNotOwner s.shares caller owner shares).bind fun sh1 =>
  (sh1.ozBurn owner shares).bind fun sh2 =>
  (M.transfer s.asset s.self receiver assets).map fun asset =>
  ({ s with asset := asset, shares := sh2 }, assets)

/-- The share ledger is well formed. -/
def Inv (s : State σ A) : Prop := s.shares.WF

/-! ### Over `Token`, this is the OpenZeppelin model -/

/-- An OpenZeppelin model state as a generic one. -/
def ofOz (s : Oz.State A) : State (Token A) A := ⟨s.self, s.asset, s.shares⟩

theorem deposit_oz (s : Oz.State A) (c : A) (a : ℕ) (r : A) :
    deposit Asset.oz δ (ofOz s) c a r = (Oz.deposit δ s c a r).map fun p => (ofOz p.1, p.2) := by
  simp only [deposit, Oz.deposit, Oz.State.previewDeposit, Oz.State.toShares, toShares,
    Option.map_bind, Function.comp_def, Option.map_ite_none, Option.map_map]
  rfl

theorem mint_oz (s : Oz.State A) (c : A) (n : ℕ) (r : A) :
    mint Asset.oz δ (ofOz s) c n r = (Oz.mint δ s c n r).map fun p => (ofOz p.1, p.2) := by
  simp only [mint, Oz.mint, Oz.State.previewMint, Oz.State.toAssets, toAssets,
    Option.map_bind, Function.comp_def, Option.map_ite_none, Option.map_map]
  rfl

theorem withdraw_oz (s : Oz.State A) (c : A) (a : ℕ) (r o : A) :
    withdraw Asset.oz δ (ofOz s) c a r o =
      (Oz.withdraw δ s c a r o).map fun p => (ofOz p.1, p.2) := by
  simp only [withdraw, Oz.withdraw, Oz.State.maxWithdraw, Oz.State.previewRedeem,
    Oz.State.previewWithdraw, Oz.State.toShares, Oz.State.toAssets, toShares, toAssets,
    Option.map_bind, Function.comp_def, Option.map_ite_none, Option.map_map]
  rfl

theorem redeem_oz (s : Oz.State A) (c : A) (n : ℕ) (r o : A) :
    redeem Asset.oz δ (ofOz s) c n r o =
      (Oz.redeem δ s c n r o).map fun p => (ofOz p.1, p.2) := by
  unfold redeem Oz.redeem
  by_cases h : s.shares.balanceOf o < n
  · simp [Oz.State.maxRedeem, ofOz, h]
  · simp only [Oz.State.maxRedeem, ofOz, h, ↓reduceIte, Oz.State.previewRedeem,
      Oz.State.toAssets, toAssets, Option.map_bind, Function.comp_def, Option.map_map]
    rfl

/-! ### Effects -/

variable {M δ}

theorem toShares_eq_some {s : State σ A} {a n : ℕ} {up : Bool} :
    toShares M δ s a up = some n ↔
      vS δ s ≤ MAX ∧ vT M s ≤ MAX ∧ n ≤ MAX ∧
        n = (if up then ceilDiv (a * vS δ s) (vT M s) else a * vS δ s / vT M s) := by
  unfold toShares vS vT checkedAdd
  by_cases h1 : MAX < totalSupply s + 10 ^ δ
  · simp only [h1, ↓reduceIte, Option.bind_none, reduceCtorEq, false_iff, not_and]
    omega
  by_cases h2 : MAX < totalAssets M s + 1
  · simp only [h1, h2, ↓reduceIte, Option.bind_some, Option.bind_none, reduceCtorEq,
      false_iff, not_and]
    omega
  simp only [h1, h2, ↓reduceIte, Option.bind_some, ozMulDiv_eq_some]
  constructor
  · rintro ⟨-, h3, h4⟩; exact ⟨by omega, by omega, h3, h4⟩
  · rintro ⟨-, -, h3, h4⟩; exact ⟨by omega, h3, h4⟩

theorem toAssets_eq_some {s : State σ A} {n a : ℕ} {up : Bool} :
    toAssets M δ s n up = some a ↔
      vT M s ≤ MAX ∧ vS δ s ≤ MAX ∧ a ≤ MAX ∧
        a = (if up then ceilDiv (n * vT M s) (vS δ s) else n * vT M s / vS δ s) := by
  unfold toAssets vS vT checkedAdd
  by_cases h1 : MAX < totalAssets M s + 1
  · simp only [h1, ↓reduceIte, Option.bind_none, reduceCtorEq, false_iff, not_and]
    omega
  by_cases h2 : MAX < totalSupply s + 10 ^ δ
  · simp only [h1, h2, ↓reduceIte, Option.bind_some, Option.bind_none, reduceCtorEq,
      false_iff, not_and]
    omega
  simp only [h1, h2, ↓reduceIte, Option.bind_some, ozMulDiv_eq_some]
  constructor
  · rintro ⟨-, h3, h4⟩; exact ⟨by omega, by omega, h3, h4⟩
  · rintro ⟨-, -, h3, h4⟩; exact ⟨by positivity, h3, h4⟩

theorem vS_pos (s : State σ A) : 0 < vS δ s := by unfold vS; positivity

theorem deposit_eq_some {s s' : State σ A} {c r : A} {a n : ℕ}
    (h : deposit M δ s c a r = some (s', n)) :
    toShares M δ s a false = some n ∧ M.transferFrom s.asset s.self c s.self a = some s'.asset ∧
      s'.self = s.self ∧ s.shares.ozMint r n = some s'.shares := by
  unfold deposit at h
  split_ifs at h
  obtain ⟨n', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh, hm, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨hp, ha, rfl, hm⟩

theorem mint_eq_some {s s' : State σ A} {c r : A} {n a : ℕ}
    (h : mint M δ s c n r = some (s', a)) :
    toAssets M δ s n true = some a ∧ M.transferFrom s.asset s.self c s.self a = some s'.asset ∧
      s'.self = s.self ∧ s.shares.ozMint r n = some s'.shares := by
  unfold mint at h
  split_ifs at h
  obtain ⟨a', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh, hm, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨hp, ha, rfl, hm⟩

theorem withdraw_eq_some {s s' : State σ A} {c r o : A} {a n : ℕ}
    (h : withdraw M δ s c a r o = some (s', n)) :
    toShares M δ s a true = some n ∧ M.transfer s.asset s.self r a = some s'.asset ∧
      s'.self = s.self ∧ ∃ sh1, Oz.spendIfNotOwner s.shares c o n = some sh1 ∧
        sh1.ozBurn o n = some s'.shares := by
  unfold withdraw at h
  obtain ⟨m, -, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h
  obtain ⟨n', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, hb2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ht, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨hp, ht, rfl, sh1, hs1, hb2⟩

theorem redeem_eq_some {s s' : State σ A} {c r o : A} {n a : ℕ}
    (h : redeem M δ s c n r o = some (s', a)) :
    toAssets M δ s n false = some a ∧ M.transfer s.asset s.self r a = some s'.asset ∧
      s'.self = s.self ∧ ∃ sh1, Oz.spendIfNotOwner s.shares c o n = some sh1 ∧
        sh1.ozBurn o n = some s'.shares := by
  unfold redeem at h
  split_ifs at h
  obtain ⟨a', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, hb2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, ht, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact ⟨hp, ht, rfl, sh1, hs1, hb2⟩

theorem burn_shares {t t' t'' : Token A} {c o : A} {n : ℕ}
    (h1 : Oz.spendIfNotOwner t c o n = some t') (h2 : t'.ozBurn o n = some t'') :
    n ≤ t.balanceOf o ∧ t''.totalSupply = t.totalSupply - n := by
  obtain ⟨e1, e2⟩ := Oz.spendIfNotOwner_eq_some h1
  obtain ⟨-, hn, -, hs⟩ := ozBurn_eq_some h2
  exact ⟨e1 ▸ hn, by rw [hs, e2]⟩

/-! ### The share ledger and solvency, for any asset -/

theorem Inv_deposit {s s' : State σ A} {c r : A} {a n : ℕ} (hi : Inv s)
    (h : deposit M δ s c a r = some (s', n)) : Inv s' :=
  WF_ozMint hi (deposit_eq_some h).2.2.2

theorem Inv_mint {s s' : State σ A} {c r : A} {n a : ℕ} (hi : Inv s)
    (h : mint M δ s c n r = some (s', a)) : Inv s' :=
  WF_ozMint hi (mint_eq_some h).2.2.2

theorem Inv_withdraw {s s' : State σ A} {c r o : A} {a n : ℕ} (hi : Inv s)
    (h : withdraw M δ s c a r o = some (s', n)) : Inv s' := by
  obtain ⟨-, -, -, sh1, h1, h2⟩ := withdraw_eq_some h
  exact WF_ozBurn (Oz.WF_spendIfNotOwner hi h1) h2

theorem Inv_redeem {s s' : State σ A} {c r o : A} {n a : ℕ} (hi : Inv s)
    (h : redeem M δ s c n r o = some (s', a)) : Inv s' := by
  obtain ⟨-, -, -, sh1, h1, h2⟩ := redeem_eq_some h
  exact WF_ozBurn (Oz.WF_spendIfNotOwner hi h1) h2

/-- **Solvency, for any asset.** `Σₓ ⌊balanceOf[x]·T̂/Ŝ⌋ ≤ T`. -/
theorem solvent (s : State σ A) (hi : Inv s) :
    (s.shares.balanceOf.sum fun _ b => b * vT M s / vS δ s) ≤ totalAssets M s := by
  have hsum : total s.shares.balanceOf = totalSupply s := hi.1
  have hpos := vS_pos (σ := σ) (δ := δ) s
  have hk : 0 < 10 ^ δ := by positivity
  unfold Finsupp.sum
  have key : (∑ x ∈ s.shares.balanceOf.support, s.shares.balanceOf x * vT M s / vS δ s) * vS δ s
      ≤ totalSupply s * vT M s := by
    calc (∑ x ∈ s.shares.balanceOf.support, s.shares.balanceOf x * vT M s / vS δ s) * vS δ s
        = ∑ x ∈ s.shares.balanceOf.support, s.shares.balanceOf x * vT M s / vS δ s * vS δ s :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ x ∈ s.shares.balanceOf.support, s.shares.balanceOf x * vT M s :=
          Finset.sum_le_sum fun _ _ => Nat.div_mul_le_self _ _
      _ = total s.shares.balanceOf * vT M s := by unfold total Finsupp.sum; rw [Finset.sum_mul]
      _ = totalSupply s * vT M s := by rw [hsum]
  have hlt : totalSupply s * vT M s < vT M s * vS δ s := by
    rw [Nat.mul_comm]
    exact Nat.mul_lt_mul_of_pos_left (by unfold vS; omega) (by unfold vT; omega)
  exact Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt key hlt))

/-! ### No dilution, unconditionally, for an exact asset -/

variable {P : σ → Prop}

theorem deposit_price_mono {s s' : State σ A} {c r : A} {a n : ℕ} (hM : M.ExactOn P s.self)
    (hP : P s.asset) (h : deposit M δ s c a r = some (s', n)) (hc : c ≠ s.self) :
    vT M s * vS δ s' ≤ vT M s' * vS δ s := by
  obtain ⟨hp, ha, hself, hm⟩ := deposit_eq_some h
  have hT : vT M s' = vT M s + a := by
    unfold vT totalAssets; rw [hself, hM.pull hP hc ha]; omega
  have hS' : vS δ s' = vS δ s + n := by
    obtain ⟨-, -, -, e⟩ := ozMint_eq_some hm; unfold vS totalSupply; rw [e]; omega
  obtain ⟨-, -, -, rfl⟩ := toShares_eq_some.1 hp
  have : a * vS δ s / vT M s * vT M s ≤ a * vS δ s := Nat.div_mul_le_self _ _
  simp only [Bool.false_eq_true, ↓reduceIte] at hS' ⊢
  rw [hT, hS']; nlinarith

theorem mint_price_mono {s s' : State σ A} {c r : A} {n a : ℕ} (hM : M.ExactOn P s.self)
    (hP : P s.asset) (h : mint M δ s c n r = some (s', a)) (hc : c ≠ s.self) :
    vT M s * vS δ s' ≤ vT M s' * vS δ s := by
  obtain ⟨hp, ha, hself, hm⟩ := mint_eq_some h
  have hT : vT M s' = vT M s + a := by
    unfold vT totalAssets; rw [hself, hM.pull hP hc ha]; omega
  have hS' : vS δ s' = vS δ s + n := by
    obtain ⟨-, -, -, e⟩ := ozMint_eq_some hm; unfold vS totalSupply; rw [e]; omega
  obtain ⟨-, -, -, rfl⟩ := toAssets_eq_some.1 hp
  have : n * vT M s ≤ ceilDiv (n * vT M s) (vS δ s) * vS δ s := le_ceilDiv_mul _ _ (vS_pos s)
  simp only [↓reduceIte] at hT
  rw [hT, hS']; nlinarith

theorem out_price_mono {T T' S S' a n : ℕ} (hS' : S + n = S') (hT : T = T' ∨ T = a + T')
    (hr : a * S' ≤ n * T) : T * S ≤ T' * S' := by
  rcases hT with rfl | rfl
  · rw [← hS']; exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  · rw [← hS'] at hr ⊢; nlinarith

theorem withdraw_price_mono {s s' : State σ A} {c r o : A} {a n : ℕ} (hM : M.ExactOn P s.self)
    (hP : P s.asset) (hi : Inv s) (h : withdraw M δ s c a r o = some (s', n)) :
    vT M s * vS δ s' ≤ vT M s' * vS δ s := by
  obtain ⟨hp, ht, hself, sh1, h1, h2⟩ := withdraw_eq_some h
  obtain ⟨hn, hsS⟩ := burn_shares h1 h2
  have hnS := hn.trans (balanceOf_le_totalSupply hi o)
  obtain ⟨ha, hb⟩ := hM.push hP ht
  obtain ⟨-, -, -, hn'⟩ := toShares_eq_some.1 hp
  simp only [↓reduceIte] at hn'
  have hr : a * vS δ s ≤ n * vT M s := by rw [hn']; exact le_ceilDiv_mul _ _ (by unfold vT; omega)
  refine out_price_mono (a := a) (n := n) (S' := vS δ s) ?_ ?_ hr
  · unfold vS totalSupply; rw [hsS]; omega
  · unfold vT totalAssets; rw [hself, hb]
    split_ifs
    · left; rfl
    · right; omega

theorem redeem_price_mono {s s' : State σ A} {c r o : A} {n a : ℕ} (hM : M.ExactOn P s.self)
    (hP : P s.asset) (hi : Inv s) (h : redeem M δ s c n r o = some (s', a)) :
    vT M s * vS δ s' ≤ vT M s' * vS δ s := by
  obtain ⟨hp, ht, hself, sh1, h1, h2⟩ := redeem_eq_some h
  obtain ⟨hn, hsS⟩ := burn_shares h1 h2
  have hnS := hn.trans (balanceOf_le_totalSupply hi o)
  obtain ⟨ha, hb⟩ := hM.push hP ht
  obtain ⟨-, -, -, ha'⟩ := toAssets_eq_some.1 hp
  simp only [Bool.false_eq_true, ↓reduceIte] at ha'
  have hr : a * vS δ s ≤ n * vT M s := by rw [ha']; exact Nat.div_mul_le_self _ _
  refine out_price_mono (a := a) (n := n) (S' := vS δ s) ?_ ?_ hr
  · unfold vS totalSupply; rw [hsS]; omega
  · unfold vT totalAssets; rw [hself, hb]
    split_ifs
    · left; rfl
    · right; omega

end GOz

end Defi.ERC4626
