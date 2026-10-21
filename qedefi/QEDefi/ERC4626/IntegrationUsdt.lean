module

public import QEDefi.ERC4626.Integration
public import QEDefi.ERC20.VariantExtras

/-!
# Vaults over USDT: fee switch, blacklist, pause (model level)

The Solmate and OpenZeppelin vaults over `Asset.variant usdt` (USDT through
`SafeTransferLib`/`SafeERC20`) with USDT's administrative switches.

* **(a) Fee on.** With `basisPointsRate > 0` USDT's fee is
  `min(v · bps / 10000, maximumFee)` (`usdt_feeOf`), paid to the owner. The fee-on-transfer
  breakage applies (`usdt_fee_deposit_price_drop`, `usdt_oz_fee_deposit_price_drop`); witness at
  the largest parameters `setParams` allows (`bps = 19`, `maximumFee = 1·10⁶` = 1 USDT with
  `mx = 1`, reached from the zero-fee state, `usdtFee_reachable`), where the cap binds
  (`usdt_fee_witness`): alice deposits 1,000 USDT (10⁹ units) for 10⁹ shares, the vault
  receives 999·10⁶; bob deposits as much for 1,001,001,001 shares; alice's shares drop from
  999,000,000 to 998,500,250 units and redeeming them pays her 997,500,250 (the owner collects
  three capped fees).
* **(b) Blacklist.** USDT checks only the sender of `transfer` and the `from` of
  `transferFrom`. Hence: a blacklisted vault makes every `withdraw`/`redeem` revert, on both
  vaults (`blacklisted_vault_withdraw`, `_redeem`, `_oz_withdraw`, `_oz_redeem`), while deposits are unaffected — a deposit into a
  blacklisted vault is exactly the deposit into the same vault unlisted
  (`deposit_setBl`: only the caller's flag matters), so funds keep flowing into a
  vault they cannot leave; `destroyBlackFunds(vault)` then sets `totalAssets` to `0` with the
  shares outstanding (`destroyBlackFunds_vault`). A blacklisted user cannot `deposit`/`mint`
  (`blacklisted_caller_deposit`, `_mint`, `_oz_deposit`, `_oz_mint`), but can still `withdraw`/`redeem` shares acquired before
  — to any receiver: the vault is a blacklist bypass (`blacklist_bypass_witness`); witness of
  the locked deposits: `blacklisted_vault_witness`.
* **(c) Pause.** For any pausable variant, while paused every `deposit`, `mint`, `withdraw`
  and `redeem` reverts on both vaults (`paused_solmate`, `paused_oz`), and the views (`totalAssets`,
  `convertToShares`, `convertToAssets`, `previewMint`, `previewWithdraw`, OZ `toShares`/
  `toAssets`) are those of the unpaused state (`paused_views`, `oz_paused_views`).
-/

@[expose] public noncomputable section

namespace QEDefi.ERC4626.Integration
open QEDefi.Math QEDefi.ERC20 QEDefi.ERC20.Variant Finsupp

variable {σ A : Type} [DecidableEq A] [Zero A]

/-! ## Transfers that cannot succeed -/

theorem variant_transfer_none {V : Variant A} {s : VState A} {c : A}
    (h : ∀ d v, V.moveOk s c d v = false) (d : A) (v : ℕ) :
    (Asset.variant V).transfer s c d v = none := by
  rw [Asset.variant_transfer]; simp [Variant.transfer, h]

theorem variant_transferFrom_none {V : Variant A} {s : VState A} {src : A}
    (h : ∀ d v, V.moveOk s src d v = false) (c d : A) (v : ℕ) :
    (Asset.variant V).transferFrom s c src d v = none := by
  rw [Asset.variant_transferFrom]; simp [Variant.transferFrom, h]

omit [Zero A] in
theorem solmate_withdraw_none {M : Asset σ A} {s : GSolmate.State σ A}
    (h : ∀ r a, M.transfer s.asset s.self r a = none) (c : A) (a : ℕ) (r o : A) :
    GSolmate.withdraw M s c a r o = none := by
  cases hw : GSolmate.withdraw M s c a r o with
  | none => rfl
  | some p =>
    obtain ⟨-, ht, -⟩ := GSolmate.withdraw_eq_some (n := p.2) (s' := p.1) (by rw [hw])
    rw [h] at ht; cases ht

omit [Zero A] in
theorem solmate_redeem_none {M : Asset σ A} {s : GSolmate.State σ A}
    (h : ∀ r a, M.transfer s.asset s.self r a = none) (c : A) (n : ℕ) (r o : A) :
    GSolmate.redeem M s c n r o = none := by
  cases hw : GSolmate.redeem M s c n r o with
  | none => rfl
  | some p =>
    obtain ⟨-, -, ht, -⟩ := GSolmate.redeem_eq_some (a := p.2) (s' := p.1) (by rw [hw])
    rw [h] at ht; cases ht

omit [Zero A] in
theorem solmate_deposit_none {M : Asset σ A} {s : GSolmate.State σ A} {c : A}
    (h : ∀ a, M.transferFrom s.asset s.self c s.self a = none) (a : ℕ) (r : A) :
    GSolmate.deposit M s c a r = none := by
  cases hw : GSolmate.deposit M s c a r with
  | none => rfl
  | some p =>
    obtain ⟨-, -, ht, -⟩ := GSolmate.deposit_eq_some (n := p.2) (s' := p.1) (by rw [hw])
    rw [h] at ht; cases ht

omit [Zero A] in
theorem solmate_mint_none {M : Asset σ A} {s : GSolmate.State σ A} {c : A}
    (h : ∀ a, M.transferFrom s.asset s.self c s.self a = none) (n : ℕ) (r : A) :
    GSolmate.mint M s c n r = none := by
  cases hw : GSolmate.mint M s c n r with
  | none => rfl
  | some p =>
    obtain ⟨-, ht, -⟩ := GSolmate.mint_eq_some (a := p.2) (s' := p.1) (by rw [hw])
    rw [h] at ht; cases ht

theorem oz_withdraw_none {M : Asset σ A} {δ : ℕ} {s : GOz.State σ A}
    (h : ∀ r a, M.transfer s.asset s.self r a = none) (c : A) (a : ℕ) (r o : A) :
    GOz.withdraw M δ s c a r o = none := by
  cases hw : GOz.withdraw M δ s c a r o with
  | none => rfl
  | some p =>
    obtain ⟨-, ht, -⟩ := GOz.withdraw_eq_some (n := p.2) (s' := p.1) (by rw [hw])
    rw [h] at ht; cases ht

theorem oz_redeem_none {M : Asset σ A} {δ : ℕ} {s : GOz.State σ A}
    (h : ∀ r a, M.transfer s.asset s.self r a = none) (c : A) (n : ℕ) (r o : A) :
    GOz.redeem M δ s c n r o = none := by
  cases hw : GOz.redeem M δ s c n r o with
  | none => rfl
  | some p =>
    obtain ⟨-, ht, -⟩ := GOz.redeem_eq_some (a := p.2) (s' := p.1) (by rw [hw])
    rw [h] at ht; cases ht

theorem oz_deposit_none {M : Asset σ A} {δ : ℕ} {s : GOz.State σ A} {c : A}
    (h : ∀ a, M.transferFrom s.asset s.self c s.self a = none) (a : ℕ) (r : A) :
    GOz.deposit M δ s c a r = none := by
  cases hw : GOz.deposit M δ s c a r with
  | none => rfl
  | some p =>
    obtain ⟨-, ht, -⟩ := GOz.deposit_eq_some (n := p.2) (s' := p.1) (by rw [hw])
    rw [h] at ht; cases ht

theorem oz_mint_none {M : Asset σ A} {δ : ℕ} {s : GOz.State σ A} {c : A}
    (h : ∀ a, M.transferFrom s.asset s.self c s.self a = none) (n : ℕ) (r : A) :
    GOz.mint M δ s c n r = none := by
  cases hw : GOz.mint M δ s c n r with
  | none => rfl
  | some p =>
    obtain ⟨-, ht, -⟩ := GOz.mint_eq_some (a := p.2) (s' := p.1) (by rw [hw])
    rw [h] at ht; cases ht

/-! ## (a) USDT with the fee switched on -/

/-- **Fee-on-transfer breakage with USDT's capped fee (Solmate vault).** If the fee
`min(a · bps / 10000, maximumFee)` is worth at least one share, a deposit strictly lowers the
assets per share of the existing holders (the vault is not USDT's owner). -/
theorem usdt_fee_deposit_price_drop {s s' : GSolmate.State (VState A) A} {c r : A} {a n : ℕ}
    (hadm : s.self ≠ s.asset.admin)
    (h : GSolmate.deposit (Asset.variant usdt) s c a r = some (s', n)) (hc : c ≠ s.self)
    (hS : GSolmate.totalSupply s ≠ 0)
    (hf : GSolmate.totalAssets (Asset.variant usdt) s ≤
      min (a * s.asset.feeBps / 10000) s.asset.feeMax * GSolmate.totalSupply s) :
    GSolmate.totalAssets (Asset.variant usdt) s' * GSolmate.totalSupply s <
      GSolmate.totalAssets (Asset.variant usdt) s * GSolmate.totalSupply s' :=
  fee_deposit_price_drop rfl (fun _ => hadm) h hc hS (by rwa [usdt_feeOf])

/-- The same for the OpenZeppelin vault (virtual totals `T̂ = T + 1`, `Ŝ = S + 10^δ`). -/
theorem usdt_oz_fee_deposit_price_drop {δ : ℕ} {s s' : GOz.State (VState A) A} {c r : A}
    {a n : ℕ} (hadm : s.self ≠ s.asset.admin)
    (h : GOz.deposit (Asset.variant usdt) δ s c a r = some (s', n)) (hc : c ≠ s.self)
    (hf : GOz.vT (Asset.variant usdt) s ≤
      min (a * s.asset.feeBps / 10000) s.asset.feeMax * GOz.vS δ s) :
    GOz.vT (Asset.variant usdt) s' * GOz.vS δ s < GOz.vT (Asset.variant usdt) s * GOz.vS δ s' :=
  oz_fee_deposit_price_drop rfl (fun _ => hadm) h hc (by rwa [usdt_feeOf])

/-- USDT's storage with the fee off: alice (`1`) and bob (`2`) hold 1,000 USDT (`10⁹` units)
each and approved the vault (`10`) without limit; the owner is `0`. -/
def usdtAsset0 : VState ℕ where
  self := 20
  bal := single 1 (10 ^ 9) + single 2 (10 ^ 9)
  supply := 2 * 10 ^ 9
  allowance := fun _ sp => if sp = 10 then MAX else 0
  scale := 1
  admin := 0
  paused := false
  blacklisted := fun _ => false
  feeBps := 0
  feeMax := 0
  ether := 0
  frozen := 0
  nonces := 0

/-- The same with the largest fee `setParams` permits for `maximumFee = 1` USDT: `bps = 19`. -/
def usdtFeeAsset : VState ℕ := { usdtAsset0 with feeBps := 19, feeMax := 10 ^ 6 }

/-- The fee-on state is reached by the owner's `setParams(19, 1)`. -/
theorem usdtFee_reachable : (usdt : Variant ℕ).setParams usdtAsset0 0 19 1 = some usdtFeeAsset := by
  simp [setParams, usdt, standard, usdtAsset0, usdtFeeAsset]

/-- An empty Solmate vault at `10` over the USDT state `a`. -/
def usdtVault (a : VState ℕ) : GSolmate.State (VState ℕ) ℕ := ⟨10, a, ⟨0, 0, fun _ _ => 0⟩, 0, 0⟩

/-- **USDT fee breakage, concretely (cap binding).** Alice deposits `10⁹` (shares `10⁹`; fee
capped at `10⁶`, the vault receives `999·10⁶`); bob deposits `10⁹` for `⌊10¹⁸/(999·10⁶)⌋ =
1,001,001,001` shares (vault `1,998·10⁶`). Alice's shares, worth `999,000,000` before, are
worth `998,500,250`; she redeems them for that and receives `997,500,250`; the owner holds the
three fees. -/
theorem usdt_fee_witness :
    ((GSolmate.deposit (Asset.variant usdt) (usdtVault usdtFeeAsset) 1 (10 ^ 9) 1).bind fun p1 =>
      (GSolmate.deposit (Asset.variant usdt) p1.1 2 (10 ^ 9) 2).bind fun p2 =>
      (GSolmate.redeem (Asset.variant usdt) p2.1 1 (10 ^ 9) 1 1).map fun p3 =>
        (p1.2, GSolmate.totalAssets (Asset.variant usdt) p1.1,
         p2.2, GSolmate.totalAssets (Asset.variant usdt) p2.1, GSolmate.totalSupply p2.1,
         GSolmate.convertToAssets (Asset.variant usdt) p2.1 (10 ^ 9),
         p3.2, p3.1.asset.bal 1, p3.1.asset.bal 0)) =
      some (10 ^ 9, 999000000, 1001001001, 1998000000, 2001001001, some 998500250, 998500250,
        997500250, 3000000) := by
  simp [GSolmate.deposit, GSolmate.redeem, GSolmate.convertToShares, GSolmate.convertToAssets,
    GSolmate.totalAssets, GSolmate.totalSupply, usdtVault, usdtFeeAsset, usdtAsset0,
    Asset.variant, safe_call, step, Variant.transferFrom, Variant.transfer, moveOk, spend, move,
    credit, units, feeOf, feeOverflow, balanceOf, usdt, standard, Infinite.test,
    VState.setAllowance, Token.mint, Token.burn, Solmate.spendIfNotOwner, Solmate.bump,
    checkedAdd, mulDivDown, Finsupp.add_apply, MAX]

/-! ## (b) Blacklist -/

theorem usdt_moveOk_blacklisted {s : VState A} {src : A} (h : s.blacklisted src = true)
    (d : A) (v : ℕ) : (usdt : Variant A).moveOk s src d v = false := by
  simp [usdt_moveOk, h]

/-- **A blacklisted vault cannot pay out**: every Solmate `withdraw` reverts. -/
theorem blacklisted_vault_withdraw {s : GSolmate.State (VState A) A}
    (h : s.asset.blacklisted s.self = true) (c : A) (a : ℕ) (r o : A) :
    GSolmate.withdraw (Asset.variant usdt) s c a r o = none :=
  solmate_withdraw_none (variant_transfer_none (usdt_moveOk_blacklisted h)) c a r o

theorem blacklisted_vault_redeem {s : GSolmate.State (VState A) A}
    (h : s.asset.blacklisted s.self = true) (c : A) (n : ℕ) (r o : A) :
    GSolmate.redeem (Asset.variant usdt) s c n r o = none :=
  solmate_redeem_none (variant_transfer_none (usdt_moveOk_blacklisted h)) c n r o

theorem blacklisted_vault_oz_withdraw {δ : ℕ} {s : GOz.State (VState A) A}
    (h : s.asset.blacklisted s.self = true) (c : A) (a : ℕ) (r o : A) :
    GOz.withdraw (Asset.variant usdt) δ s c a r o = none :=
  oz_withdraw_none (variant_transfer_none (usdt_moveOk_blacklisted h)) c a r o

theorem blacklisted_vault_oz_redeem {δ : ℕ} {s : GOz.State (VState A) A}
    (h : s.asset.blacklisted s.self = true) (c : A) (n : ℕ) (r o : A) :
    GOz.redeem (Asset.variant usdt) δ s c n r o = none :=
  oz_redeem_none (variant_transfer_none (usdt_moveOk_blacklisted h)) c n r o

/-- **A blacklisted caller cannot deposit or mint** (USDT checks `from` in `transferFrom`). -/
theorem blacklisted_caller_deposit {s : GSolmate.State (VState A) A} {c : A}
    (h : s.asset.blacklisted c = true) (a : ℕ) (r : A) :
    GSolmate.deposit (Asset.variant usdt) s c a r = none :=
  solmate_deposit_none (fun a => variant_transferFrom_none (usdt_moveOk_blacklisted h) _ _ a) a r

theorem blacklisted_caller_mint {s : GSolmate.State (VState A) A} {c : A}
    (h : s.asset.blacklisted c = true) (n : ℕ) (r : A) :
    GSolmate.mint (Asset.variant usdt) s c n r = none :=
  solmate_mint_none (fun a => variant_transferFrom_none (usdt_moveOk_blacklisted h) _ _ a) n r

theorem blacklisted_caller_oz_deposit {δ : ℕ} {s : GOz.State (VState A) A} {c : A}
    (h : s.asset.blacklisted c = true) (a : ℕ) (r : A) :
    GOz.deposit (Asset.variant usdt) δ s c a r = none :=
  oz_deposit_none (fun a => variant_transferFrom_none (usdt_moveOk_blacklisted h) _ _ a) a r

theorem blacklisted_caller_oz_mint {δ : ℕ} {s : GOz.State (VState A) A} {c : A}
    (h : s.asset.blacklisted c = true) (n : ℕ) (r : A) :
    GOz.mint (Asset.variant usdt) δ s c n r = none :=
  oz_mint_none (fun a => variant_transferFrom_none (usdt_moveOk_blacklisted h) _ _ a) n r

/-- The asset state with blacklist `b`. -/
def setBl (s : VState A) (b : A → Bool) : VState A := { s with blacklisted := b }

theorem spend_setBl (V : Variant A) (s : VState A) (b : A → Bool) (o sp : A) (v : ℕ) :
    V.spend (setBl s b) o sp v = (V.spend s o sp v).map (setBl · b) := by
  unfold spend
  by_cases h1 : (V.selfSpendFree && decide (o = sp)) = true
  · simp [h1]
  by_cases h2 : V.permit2 = some sp
  · simp [h1, h2]
  by_cases h3 : V.infinite.test (s.allowance o sp) = true
  · simp [h1, h2, h3, setBl]
  by_cases h4 : s.allowance o sp < v
  · simp [h1, h2, h3, h4, setBl]
  by_cases h5 : (V.spendViaApprove && (decide (o = 0) || decide (sp = 0))) = true
  · simp [h1, h2, h3, h4, h5, setBl]
  · simp only [h1, h2, h3, h4, h5, setBl, Bool.false_eq_true, ↓reduceIte, Option.map_some]
    rfl

omit [DecidableEq A] [Zero A] in
theorem credit_setBl (V : Variant A) (s : VState A) (b : A → Bool) (src dst : A) (v : ℕ) :
    V.credit (setBl s b) src dst v = setBl (V.credit s src dst v) b := by
  have hf : ∀ x, V.feeOf (setBl s b) x = V.feeOf s x := fun _ => rfl
  have hu : ∀ x, V.units (setBl s b) x = V.units s x := fun _ => rfl
  unfold credit
  simp only [hf, hu]
  by_cases h : V.feeOf s v = 0
  · simp only [h, ↓reduceIte]; rfl
  · simp only [h, ↓reduceIte]; cases V.feeSink <;> rfl

omit [DecidableEq A] [Zero A] in
theorem move_setBl (V : Variant A) (s : VState A) (b : A → Bool) (src dst : A) (v : ℕ) :
    V.move (setBl s b) src dst v = (V.move s src dst v).map (setBl · b) := by
  have hf : ∀ x, V.feeOf (setBl s b) x = V.feeOf s x := fun _ => rfl
  have hu : ∀ x, V.units (setBl s b) x = V.units s x := fun _ => rfl
  have ho : V.feeOverflow (setBl s b) v = V.feeOverflow s v := rfl
  have hb : (setBl s b).bal = s.bal := rfl
  unfold move
  simp only [hf, hu, ho, hb, credit_setBl]
  by_cases h1 : s.bal src < V.units s v
  · simp [h1]
  by_cases h2 : V.feeOverflow s v = true
  · simp [h1, h2]
  by_cases h3 : v < V.feeOf s v
  · simp [h1, h2, h3]
  · simp [h1, h2, h3]

/-- USDT's `transferFrom` reads the blacklist only at `from`. -/
theorem usdt_transferFrom_setBl (s : VState A) {b : A → Bool} {c src d : A} (v : ℕ)
    (hb : b src = s.blacklisted src) :
    (usdt : Variant A).transferFrom (setBl s b) c src d v =
      ((usdt : Variant A).transferFrom s c src d v).map (setBl · b) := by
  have hm : (usdt : Variant A).moveOk (setBl s b) src d v = (usdt : Variant A).moveOk s src d v := by
    simp only [usdt_moveOk, setBl, hb]
  unfold Variant.transferFrom
  rw [hm, spend_setBl]
  split_ifs
  · cases (usdt : Variant A).spend s src c v with
    | none => rfl
    | some t => simp only [Option.map_some, Option.bind_some, move_setBl]
  · rfl

/-- **A deposit does not see the vault's (or anyone else's) blacklisting, only the caller's**:
in a state where the blacklist differs from `s`'s anywhere but at the caller, the deposit has
the same outcome. Funds keep entering a blacklisted vault. -/
theorem deposit_setBl (s : GSolmate.State (VState A) A) {c : A} {b : A → Bool}
    (hb : b c = s.asset.blacklisted c) (a : ℕ) (r : A) :
    GSolmate.deposit (Asset.variant usdt) { s with asset := setBl s.asset b } c a r =
      (GSolmate.deposit (Asset.variant usdt) s c a r).map
        fun p => ({ p.1 with asset := setBl p.1.asset b }, p.2) := by
  have hT : GSolmate.convertToShares (Asset.variant usdt) { s with asset := setBl s.asset b } a =
      GSolmate.convertToShares (Asset.variant usdt) s a := rfl
  unfold GSolmate.deposit
  rw [hT]
  cases GSolmate.convertToShares (Asset.variant usdt) s a with
  | none => rfl
  | some n =>
    simp only [Option.bind_some]
    split_ifs
    · rfl
    · simp only [Asset.variant_transferFrom] at *
      rw [usdt_transferFrom_setBl _ _ hb]
      cases (usdt : Variant A).transferFrom s.asset s.self c s.self a with
      | none => rfl
      | some t =>
        simp only [Option.map_some, Option.bind_some]
        cases s.shares.mint r n with
        | none => rfl
        | some sh =>
          simp only [Option.bind_some]
          cases Solmate.bump s.afterDepositCount with
          | none => rfl
          | some k => rfl

/-- **`destroyBlackFunds` on the vault** sets `totalAssets` to `0`; the shares stay
outstanding (worth nothing). -/
theorem destroyBlackFunds_vault {s : GSolmate.State (VState A) A} {a' : VState A} {c : A}
    (h : (usdt : Variant A).destroyBlackFunds s.asset c s.self = some a') :
    GSolmate.totalAssets (Asset.variant usdt) { s with asset := a' } = 0 ∧
      GSolmate.totalSupply { s with asset := a' } = GSolmate.totalSupply s := by
  unfold Variant.destroyBlackFunds at h
  split_ifs at h
  cases h
  refine ⟨?_, rfl⟩
  simp [GSolmate.totalAssets, Asset.variant, balanceOf, usdt, standard]

/-- **Blacklist bypass through the vault.** Alice deposits `100`, is then blacklisted: her own
`transfer` fails, but she redeems her `100` shares to bob, who receives the `100`. -/
theorem blacklist_bypass_witness :
    ((GSolmate.deposit (Asset.variant usdt) (usdtVault usdtAsset0) 1 100 1).bind fun p1 =>
      ((usdt : Variant ℕ).setBlacklisted p1.1.asset 0 1 true).bind fun a1 =>
      (GSolmate.redeem (Asset.variant usdt) { p1.1 with asset := a1 } 1 100 2 1).map fun p2 =>
        (p1.2, ((usdt : Variant ℕ).transfer a1 1 2 100).isSome, p2.2, p2.1.asset.bal 2)) =
      some (100, false, 100, 10 ^ 9 + 100) := by
  simp [GSolmate.deposit, GSolmate.redeem, GSolmate.convertToShares, GSolmate.convertToAssets,
    GSolmate.totalAssets, GSolmate.totalSupply, usdtVault, usdtAsset0, Asset.variant, safe_call,
    step, Variant.transferFrom, Variant.transfer, moveOk, spend, move, credit, units, feeOf,
    feeOverflow, balanceOf, setBlacklisted, usdt, standard, Infinite.test, VState.setAllowance,
    Token.mint, Token.burn, Solmate.spendIfNotOwner, Solmate.bump, checkedAdd, mulDivDown,
    Finsupp.add_apply, Function.update, MAX]

/-- **A blacklisted vault keeps accepting deposits it cannot repay.** The owner blacklists the
vault; alice's deposit of `100` succeeds (`100` shares), her redeem reverts, and
`destroyBlackFunds(vault)` leaves her shares worth `0`. -/
theorem blacklisted_vault_witness :
    (((usdt : Variant ℕ).setBlacklisted usdtAsset0 0 10 true).bind fun a0 =>
      (GSolmate.deposit (Asset.variant usdt) (usdtVault a0) 1 100 1).bind fun p1 =>
      ((usdt : Variant ℕ).destroyBlackFunds p1.1.asset 0 10).map fun a2 =>
        (p1.2, (GSolmate.redeem (Asset.variant usdt) p1.1 1 100 1 1).isSome,
         GSolmate.totalAssets (Asset.variant usdt) { p1.1 with asset := a2 },
         GSolmate.convertToAssets (Asset.variant usdt) { p1.1 with asset := a2 } 100)) =
      some (100, false, 0, some 0) := by
  simp [GSolmate.deposit, GSolmate.redeem, GSolmate.convertToShares, GSolmate.convertToAssets,
    GSolmate.totalAssets, GSolmate.totalSupply, usdtVault, usdtAsset0, Asset.variant, safe_call,
    step, Variant.transferFrom, Variant.transfer, moveOk, spend, move, credit, units, feeOf,
    feeOverflow, balanceOf, setBlacklisted, Variant.destroyBlackFunds, usdt, standard,
    Infinite.test, VState.setAllowance, Token.mint, Token.burn, Solmate.spendIfNotOwner,
    Solmate.bump, checkedAdd, mulDivDown, Finsupp.add_apply, Function.update, MAX]

/-! ## (c) Pause -/

theorem moveOk_paused {V : Variant A} (hp : V.pausable = true) {s : VState A}
    (h : s.paused = true) (src d : A) (v : ℕ) : V.moveOk s src d v = false := by
  simp [moveOk, hp, h]

/-- **While paused, every Solmate vault operation reverts** (for any pausable variant). -/
theorem paused_solmate {V : Variant A} (hp : V.pausable = true)
    {s : GSolmate.State (VState A) A} (h : s.asset.paused = true) (c r o : A) (x : ℕ) :
    GSolmate.deposit (Asset.variant V) s c x r = none ∧
      GSolmate.mint (Asset.variant V) s c x r = none ∧
      GSolmate.withdraw (Asset.variant V) s c x r o = none ∧
      GSolmate.redeem (Asset.variant V) s c x r o = none :=
  ⟨solmate_deposit_none (fun a => variant_transferFrom_none (moveOk_paused hp h c) _ _ a) x r,
    solmate_mint_none (fun a => variant_transferFrom_none (moveOk_paused hp h c) _ _ a) x r,
    solmate_withdraw_none (variant_transfer_none (moveOk_paused hp h s.self)) c x r o,
    solmate_redeem_none (variant_transfer_none (moveOk_paused hp h s.self)) c x r o⟩

/-- The same for the OpenZeppelin vault. -/
theorem paused_oz {V : Variant A} (hp : V.pausable = true) {δ : ℕ}
    {s : GOz.State (VState A) A} (h : s.asset.paused = true) (c r o : A) (x : ℕ) :
    GOz.deposit (Asset.variant V) δ s c x r = none ∧
      GOz.mint (Asset.variant V) δ s c x r = none ∧
      GOz.withdraw (Asset.variant V) δ s c x r o = none ∧
      GOz.redeem (Asset.variant V) δ s c x r o = none :=
  ⟨oz_deposit_none (fun a => variant_transferFrom_none (moveOk_paused hp h c) _ _ a) x r,
    oz_mint_none (fun a => variant_transferFrom_none (moveOk_paused hp h c) _ _ a) x r,
    oz_withdraw_none (variant_transfer_none (moveOk_paused hp h s.self)) c x r o,
    oz_redeem_none (variant_transfer_none (moveOk_paused hp h s.self)) c x r o⟩

/-- **The views do not see the pause** (nor the blacklist): `totalAssets` and the conversions
are those of the same state with any other `paused` flag and blacklist. -/
theorem paused_views (V : Variant A) (s : GSolmate.State (VState A) A) (p : Bool)
    (b : A → Bool) :
    let s' : GSolmate.State (VState A) A := { s with asset := { s.asset with paused := p, blacklisted := b } }
    GSolmate.totalAssets (Asset.variant V) s' = GSolmate.totalAssets (Asset.variant V) s ∧
      ∀ x, GSolmate.convertToShares (Asset.variant V) s' x =
          GSolmate.convertToShares (Asset.variant V) s x ∧
        GSolmate.convertToAssets (Asset.variant V) s' x =
          GSolmate.convertToAssets (Asset.variant V) s x ∧
        GSolmate.previewMint (Asset.variant V) s' x = GSolmate.previewMint (Asset.variant V) s x ∧
        GSolmate.previewWithdraw (Asset.variant V) s' x =
          GSolmate.previewWithdraw (Asset.variant V) s x :=
  ⟨rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The same for the OpenZeppelin vault's conversions (both roundings). -/
theorem oz_paused_views (V : Variant A) (δ : ℕ) (s : GOz.State (VState A) A) (p : Bool)
    (b : A → Bool) :
    let s' : GOz.State (VState A) A := { s with asset := { s.asset with paused := p, blacklisted := b } }
    GOz.totalAssets (Asset.variant V) s' = GOz.totalAssets (Asset.variant V) s ∧
      ∀ x up, GOz.toShares (Asset.variant V) δ s' x up = GOz.toShares (Asset.variant V) δ s x up ∧
        GOz.toAssets (Asset.variant V) δ s' x up = GOz.toAssets (Asset.variant V) δ s x up :=
  ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩

end QEDefi.ERC4626.Integration
