module

public import QEDefi.ERC4626.AssetVariants

/-!
# Vaults over non-standard assets (model level)

The Solmate and OpenZeppelin vault models over an asset `Variant` called through
`SafeTransferLib`/`SafeERC20` (`Asset.variant`), and what changes.

* **(a) Return conventions do not matter, balance accounting does.** Both ledgers stay well
  formed for every `Sane` variant, fees and rebasing included (`solmate_vinv_deposit` …).
  Solvency holds for any asset. No dilution (`T·S' ≤ T'·S`, OZ with virtual totals) holds for
  every variant in a fee-free state, whatever its return-data and failure conventions: USDT
  with `basisPointsRate = 0` (returns nothing, fails with `INVALID`), BNB (returns nothing from
  `transfer`), AMPL between rebases (`noFee_solmate_deposit_price_mono` …, `usdt_noFee`,
  `bnb_noFee`, `ampl_noFee`). A vault that ABI-decodes a `bool` instead reverts on every USDT
  deposit (`naive_usdt_deposit_eq_none`); one that ignores the return data mints free shares
  against a token that returns `false` (`unchecked_returnFalse_deposit`).
* **(b) Fee on transfer breaks the share price.** A deposit of `a` with fee `f` credits shares
  for `a` while the vault receives `a − f` (`fee_deposit_totalAssets`); exactly
  `T·S' + ρ = T'·S + f·S` with the rounding remainder `ρ < T` (`fee_deposit_dilution`), so the
  price strictly drops as soon as the fee is worth a share (`fee_deposit_price_drop`; OZ:
  `oz_fee_deposit_price_drop`), and a withdrawal delivers `a − f` (`fee_withdraw_receiver`).
  Witness on STA (`sta_solmate_witness`): two deposits of 100 leave the first depositor's 100
  shares worth 98 and she redeems 97 tokens; the second depositor's fee is socialised onto her.
  A negative AMPL rebase lowers `totalAssets` with no vault call (`negative_rebase_totalAssets_le`;
  a positive one raises it and accrues to every holder, `positive_rebase_accrues`); witness
  (`ampl_rebase_witness`): after halving the supply the depositor's 100 shares are worth 50 and
  withdrawing the previewed 100 reverts; after doubling they are worth 200.
* **(c) USDT approve race guard.** `approve(x)` then `approve(y)` with `x, y ≠ 0` reverts
  (`usdt_reapprove_reverts`); after a spender pulls `x'` of an allowance `x < MAX`, the next
  nonzero `approve` succeeds iff `x' = x` (`usdt_reapprove_after_pull`).
-/

@[expose] public noncomputable section

namespace QEDefi.ERC4626.Integration
open QEDefi.Math QEDefi.ERC20 QEDefi.ERC20.Variant Finsupp

variable {A : Type} [DecidableEq A] [Zero A]

/-! ## (a) Ledgers and price for fee-free variants -/

/-- Both ledgers of a Solmate vault over a variant are well formed. -/
def VInv (V : Variant A) (s : GSolmate.State (VState A) A) : Prop := V.WF s.asset ∧ s.shares.WF

theorem solmate_vinv_deposit {V : Variant A} {s s' : GSolmate.State (VState A) A} {c r : A}
    {a n : ℕ} (hV : V.Sane) (hi : VInv V s)
    (h : GSolmate.deposit (Asset.variant V) s c a r = some (s', n)) : VInv V s' := by
  obtain ⟨-, -, ha, -, -⟩ := GSolmate.deposit_eq_some h
  rw [Asset.variant_transferFrom] at ha
  exact ⟨V.WF_transferFrom hV hi.1 ha, GSolmate.Inv_deposit hi.2 h⟩

theorem solmate_vinv_mint {V : Variant A} {s s' : GSolmate.State (VState A) A} {c r : A}
    {n a : ℕ} (hV : V.Sane) (hi : VInv V s)
    (h : GSolmate.mint (Asset.variant V) s c n r = some (s', a)) : VInv V s' := by
  obtain ⟨-, ha, -, -⟩ := GSolmate.mint_eq_some h
  rw [Asset.variant_transferFrom] at ha
  exact ⟨V.WF_transferFrom hV hi.1 ha, GSolmate.Inv_mint hi.2 h⟩

theorem solmate_vinv_withdraw {V : Variant A} {s s' : GSolmate.State (VState A) A} {c r o : A}
    {a n : ℕ} (hV : V.Sane) (hi : VInv V s)
    (h : GSolmate.withdraw (Asset.variant V) s c a r o = some (s', n)) : VInv V s' := by
  obtain ⟨-, ht, -, -⟩ := GSolmate.withdraw_eq_some h
  rw [Asset.variant_transfer] at ht
  exact ⟨V.WF_transfer hV hi.1 ht, GSolmate.Inv_withdraw hi.2 h⟩

theorem solmate_vinv_redeem {V : Variant A} {s s' : GSolmate.State (VState A) A} {c r o : A}
    {n a : ℕ} (hV : V.Sane) (hi : VInv V s)
    (h : GSolmate.redeem (Asset.variant V) s c n r o = some (s', a)) : VInv V s' := by
  obtain ⟨-, -, ht, -, -⟩ := GSolmate.redeem_eq_some h
  rw [Asset.variant_transfer] at ht
  exact ⟨V.WF_transfer hV hi.1 ht, GSolmate.Inv_redeem hi.2 h⟩

/-- USDT is fee-free in every state with `basisPointsRate = 0` (the mainnet setting). -/
theorem usdt_noFee {s : VState A} (h : s.feeBps = 0) : Asset.NoFee usdt s :=
  ⟨fun v => by simp [feeOf, usdt, h], by simp [usdt, standard]⟩

/-- BNB is fee-free in every state. -/
theorem bnb_noFee (s : VState A) : Asset.NoFee bnb s :=
  ⟨fun _ => by simp [feeOf, bnb, standard], by simp [bnb, standard]⟩

/-- AMPL transfers are exact in every well-formed state (between rebases). -/
theorem ampl_noFee {s : VState A} (hw : (ampl : Variant A).WF s) : Asset.NoFee ampl s := by
  refine ⟨fun _ => by simp [feeOf, ampl, standard], fun hr => ?_⟩
  have hV := ampl_sane (A := A)
  unfold WF at hw; simp only [hr, ↓reduceIte] at hw
  obtain ⟨-, hpos, hcap, hsc⟩ := hw
  obtain ⟨-, hsq⟩ := hV.rebasing_cap hr
  rw [hsc]
  apply Nat.div_pos _ hpos
  calc s.supply ≤ s.supply * s.supply := Nat.le_mul_self _
    _ ≤ (ampl : Variant A).maxSupply ^ 2 := by rw [sq]; exact Nat.mul_le_mul hcap hcap
    _ ≤ _ := hsq

/-- **No dilution over any fee-free variant (Solmate deposit)**, whatever its return and failure
conventions. -/
theorem noFee_solmate_deposit_price_mono {V : Variant A} {s s' : GSolmate.State (VState A) A}
    {c r : A} {a n : ℕ} (hP : Asset.NoFee V s.asset)
    (h : GSolmate.deposit (Asset.variant V) s c a r = some (s', n)) (hc : c ≠ s.self)
    (hS : GSolmate.totalSupply s ≠ 0) :
    GSolmate.totalAssets (Asset.variant V) s * GSolmate.totalSupply s' ≤
      GSolmate.totalAssets (Asset.variant V) s' * GSolmate.totalSupply s :=
  GSolmate.deposit_price_mono (Asset.variant_exactOn V s.self) hP h hc hS

theorem noFee_solmate_mint_price_mono {V : Variant A} {s s' : GSolmate.State (VState A) A}
    {c r : A} {n a : ℕ} (hP : Asset.NoFee V s.asset)
    (h : GSolmate.mint (Asset.variant V) s c n r = some (s', a)) (hc : c ≠ s.self)
    (hS : GSolmate.totalSupply s ≠ 0) :
    GSolmate.totalAssets (Asset.variant V) s * GSolmate.totalSupply s' ≤
      GSolmate.totalAssets (Asset.variant V) s' * GSolmate.totalSupply s :=
  GSolmate.mint_price_mono (Asset.variant_exactOn V s.self) hP h hc hS

theorem noFee_solmate_withdraw_price_mono {V : Variant A} {s s' : GSolmate.State (VState A) A}
    {c r o : A} {a n : ℕ} (hP : Asset.NoFee V s.asset) (hi : GSolmate.Inv s)
    (h : GSolmate.withdraw (Asset.variant V) s c a r o = some (s', n))
    (hS : GSolmate.totalSupply s ≠ 0) :
    GSolmate.totalAssets (Asset.variant V) s * GSolmate.totalSupply s' ≤
      GSolmate.totalAssets (Asset.variant V) s' * GSolmate.totalSupply s :=
  GSolmate.withdraw_price_mono (Asset.variant_exactOn V s.self) hP hi h hS

theorem noFee_solmate_redeem_price_mono {V : Variant A} {s s' : GSolmate.State (VState A) A}
    {c r o : A} {n a : ℕ} (hP : Asset.NoFee V s.asset) (hi : GSolmate.Inv s)
    (h : GSolmate.redeem (Asset.variant V) s c n r o = some (s', a))
    (hS : GSolmate.totalSupply s ≠ 0) :
    GSolmate.totalAssets (Asset.variant V) s * GSolmate.totalSupply s' ≤
      GSolmate.totalAssets (Asset.variant V) s' * GSolmate.totalSupply s :=
  GSolmate.redeem_price_mono (Asset.variant_exactOn V s.self) hP hi h hS

/-- No dilution over any fee-free variant (OpenZeppelin deposit, any `δ`, unconditionally). -/
theorem noFee_oz_deposit_price_mono {V : Variant A} {δ : ℕ} {s s' : GOz.State (VState A) A}
    {c r : A} {a n : ℕ} (hP : Asset.NoFee V s.asset)
    (h : GOz.deposit (Asset.variant V) δ s c a r = some (s', n)) (hc : c ≠ s.self) :
    GOz.vT (Asset.variant V) s * GOz.vS δ s' ≤ GOz.vT (Asset.variant V) s' * GOz.vS δ s :=
  GOz.deposit_price_mono (Asset.variant_exactOn V s.self) hP h hc

theorem noFee_oz_mint_price_mono {V : Variant A} {δ : ℕ} {s s' : GOz.State (VState A) A}
    {c r : A} {n a : ℕ} (hP : Asset.NoFee V s.asset)
    (h : GOz.mint (Asset.variant V) δ s c n r = some (s', a)) (hc : c ≠ s.self) :
    GOz.vT (Asset.variant V) s * GOz.vS δ s' ≤ GOz.vT (Asset.variant V) s' * GOz.vS δ s :=
  GOz.mint_price_mono (Asset.variant_exactOn V s.self) hP h hc

theorem noFee_oz_withdraw_price_mono {V : Variant A} {δ : ℕ} {s s' : GOz.State (VState A) A}
    {c r o : A} {a n : ℕ} (hP : Asset.NoFee V s.asset) (hi : GOz.Inv s)
    (h : GOz.withdraw (Asset.variant V) δ s c a r o = some (s', n)) :
    GOz.vT (Asset.variant V) s * GOz.vS δ s' ≤ GOz.vT (Asset.variant V) s' * GOz.vS δ s :=
  GOz.withdraw_price_mono (Asset.variant_exactOn V s.self) hP hi h

theorem noFee_oz_redeem_price_mono {V : Variant A} {δ : ℕ} {s s' : GOz.State (VState A) A}
    {c r o : A} {n a : ℕ} (hP : Asset.NoFee V s.asset) (hi : GOz.Inv s)
    (h : GOz.redeem (Asset.variant V) δ s c n r o = some (s', a)) :
    GOz.vT (Asset.variant V) s * GOz.vS δ s' ≤ GOz.vT (Asset.variant V) s' * GOz.vS δ s :=
  GOz.redeem_price_mono (Asset.variant_exactOn V s.self) hP hi h

/-- **USDT (no fee) as the Solmate vault's asset**: a deposit never lowers the share price,
although USDT returns no data and fails with `INVALID`. -/
theorem usdt_solmate_deposit_price_mono {s s' : GSolmate.State (VState A) A} {c r : A} {a n : ℕ}
    (hfee : s.asset.feeBps = 0)
    (h : GSolmate.deposit (Asset.variant usdt) s c a r = some (s', n)) (hc : c ≠ s.self)
    (hS : GSolmate.totalSupply s ≠ 0) :
    GSolmate.totalAssets (Asset.variant usdt) s * GSolmate.totalSupply s' ≤
      GSolmate.totalAssets (Asset.variant usdt) s' * GSolmate.totalSupply s :=
  noFee_solmate_deposit_price_mono (usdt_noFee hfee) h hc hS

/-- **BNB as the Solmate vault's asset**: a deposit never lowers the share price. -/
theorem bnb_solmate_deposit_price_mono {s s' : GSolmate.State (VState A) A} {c r : A} {a n : ℕ}
    (h : GSolmate.deposit (Asset.variant bnb) s c a r = some (s', n)) (hc : c ≠ s.self)
    (hS : GSolmate.totalSupply s ≠ 0) :
    GSolmate.totalAssets (Asset.variant bnb) s * GSolmate.totalSupply s' ≤
      GSolmate.totalAssets (Asset.variant bnb) s' * GSolmate.totalSupply s :=
  noFee_solmate_deposit_price_mono (bnb_noFee _) h hc hS

/-! ### Other ways to call the asset -/

/-- A token called through `require(IERC20(t).transferFrom(…))` with a `returns (bool)`
interface (ABI-decoded return value). -/
def naive (V : Variant A) : Asset (VState A) A :=
  ⟨V.balanceOf, fun s c d v => (V.call s c (.transfer d v)).decoded,
    fun s c src d v => (V.call s c (.transferFrom src d v)).decoded⟩

/-- A token called with a low-level call whose return data is ignored. -/
def unchecked (V : Variant A) : Asset (VState A) A :=
  ⟨V.balanceOf, fun s c d v => (V.call s c (.transfer d v)).unchecked,
    fun s c src d v => (V.call s c (.transferFrom src d v)).unchecked⟩

/-- A Solmate vault that decodes a `bool` reverts on every USDT deposit. -/
theorem naive_usdt_deposit_eq_none (s : GSolmate.State (VState A) A) (c r : A) (a : ℕ) :
    GSolmate.deposit (naive usdt) s c a r = none := by
  have h : ∀ src d v, (naive (usdt : Variant A)).transferFrom s.asset s.self src d v = none :=
    fun src d v => usdt_decoded_eq_none _ _ _ (fun _ h => by cases h)
  unfold GSolmate.deposit
  cases GSolmate.convertToShares (naive usdt) s a with
  | none => rfl
  | some n => simp [h]

/-- … and on every USDT withdrawal. -/
theorem naive_usdt_withdraw_eq_none (s : GSolmate.State (VState A) A) (c r o : A) (a : ℕ) :
    GSolmate.withdraw (naive usdt) s c a r o = none := by
  have h : ∀ d v, (naive (usdt : Variant A)).transfer s.asset s.self d v = none :=
    fun d v => usdt_decoded_eq_none _ _ _ (fun _ h => by cases h)
  simp [GSolmate.withdraw, h]

/-- Against a token that "fails" by returning `false`, a vault ignoring the return data mints
the shares while its asset balance does not change (free shares). -/
theorem unchecked_returnFalse_deposit {V : Variant A} {s : GSolmate.State (VState A) A} {c r : A}
    {a n : ℕ} (hf : V.arithFail = .returnFalse) (hp : GSolmate.convertToShares (unchecked V) s a = some n)
    (hn : n ≠ 0) (hg : V.guardOk s.asset s.self (.transferFrom c s.self a) = true)
    (ho : V.overflows s.asset s.self (.transferFrom c s.self a) = false)
    (hs : V.transferFrom s.asset s.self c s.self a = none) {sh : Token A}
    (hm : s.shares.mint r n = some sh) (hb : s.afterDepositCount + 1 ≤ MAX) :
    GSolmate.deposit (unchecked V) s c a r =
      some ({ s with shares := sh, afterDepositCount := s.afterDepositCount + 1 }, n) := by
  have ht : (unchecked V).transferFrom s.asset s.self c s.self a = some s.asset :=
    V.unchecked_call_returnFalse _ _ _ hf hg ho hs
  have hb' : Solmate.bump s.afterDepositCount = Option.some (s.afterDepositCount + 1) := by
    have : ¬ MAX < s.afterDepositCount + 1 := by omega
    simp [Solmate.bump, checkedAdd, this]
  simp [GSolmate.deposit, hp, hn, ht, hm, hb']

/-! ## (b) Fee on transfer -/

theorem totalAssets_variant (V : Variant A) (hr : V.rebasing = false)
    (s : GSolmate.State (VState A) A) :
    GSolmate.totalAssets (Asset.variant V) s = s.asset.bal s.self := by
  simp [GSolmate.totalAssets, Asset.variant, balanceOf, hr]

/-- With a fee, a deposit of `a` raises `totalAssets` by `a − fee(a)` only, while the shares are
computed (and minted) for `a`. -/
theorem fee_deposit_totalAssets {V : Variant A} {s s' : GSolmate.State (VState A) A} {c r : A}
    {a n : ℕ} (hr : V.rebasing = false) (hsink : V.feeSink = .owner → s.self ≠ s.asset.admin)
    (h : GSolmate.deposit (Asset.variant V) s c a r = some (s', n)) (hc : c ≠ s.self) :
    GSolmate.totalAssets (Asset.variant V) s' + V.feeOf s.asset a =
        GSolmate.totalAssets (Asset.variant V) s + a ∧
      GSolmate.totalSupply s' = GSolmate.totalSupply s + n ∧ V.feeOf s.asset a ≤ a := by
  obtain ⟨-, -, ha, hself, hm⟩ := GSolmate.deposit_eq_some h
  rw [Asset.variant_transferFrom] at ha
  obtain ⟨s1, h1, h2⟩ := V.transferFrom_eq_some ha
  obtain ⟨e1, -, -, -, e5, -, e7, e8, -⟩ := V.spend_eq_some h1
  have hfe := Asset.feeOf_congr V e7 e8 a
  obtain ⟨-, -, hfa, -⟩ := (V.move_eq_some).1 h2
  have hd := V.move_fee_dst hr h2 hc (fun hk => e5 ▸ hsink hk)
  rw [totalAssets_variant V hr, totalAssets_variant V hr, hself, hd, e1, hfe]
  rw [hfe] at hfa
  refine ⟨by omega, ?_, hfa⟩
  obtain ⟨-, e⟩ := Token.mint_eq_some.1 hm
  unfold GSolmate.totalSupply; rw [e]

/-- **The dilution identity.** For a deposit into a vault with shares, with `ρ = a·S − n·T` the
rounding remainder (`ρ < T`): `T·S' + ρ = T'·S + f·S`. Without fee this is the no-dilution
inequality; with a fee the existing holders lose `f·S − ρ` (in units of `1/S'` assets). -/
theorem fee_deposit_dilution {V : Variant A} {s s' : GSolmate.State (VState A) A} {c r : A}
    {a n : ℕ} (hr : V.rebasing = false) (hsink : V.feeSink = .owner → s.self ≠ s.asset.admin)
    (h : GSolmate.deposit (Asset.variant V) s c a r = some (s', n)) (hc : c ≠ s.self)
    (hS : GSolmate.totalSupply s ≠ 0) :
    GSolmate.totalAssets (Asset.variant V) s * GSolmate.totalSupply s' +
        (a * GSolmate.totalSupply s - n * GSolmate.totalAssets (Asset.variant V) s) =
      GSolmate.totalAssets (Asset.variant V) s' * GSolmate.totalSupply s +
        V.feeOf s.asset a * GSolmate.totalSupply s ∧
    a * GSolmate.totalSupply s - n * GSolmate.totalAssets (Asset.variant V) s <
      GSolmate.totalAssets (Asset.variant V) s := by
  obtain ⟨hT, hS', -⟩ := fee_deposit_totalAssets hr hsink h hc
  obtain ⟨r1, r2⟩ := GSolmate.deposit_rounding h hS
  set T := GSolmate.totalAssets (Asset.variant V) s
  set T' := GSolmate.totalAssets (Asset.variant V) s'
  set S := GSolmate.totalSupply s
  set f := V.feeOf s.asset a
  rw [hS']
  constructor
  · have e1 : (T' + f) * S = (T + a) * S := by rw [hT]
    zify [r1] at e1 ⊢
    nlinarith
  · have : a * S < n * T + T := by nlinarith
    omega

/-- **Fee on transfer breaks no-dilution.** As soon as the fee is worth at least one share
(`T ≤ f·S`), a deposit strictly lowers the assets per share of the existing holders. -/
theorem fee_deposit_price_drop {V : Variant A} {s s' : GSolmate.State (VState A) A} {c r : A}
    {a n : ℕ} (hr : V.rebasing = false) (hsink : V.feeSink = .owner → s.self ≠ s.asset.admin)
    (h : GSolmate.deposit (Asset.variant V) s c a r = some (s', n)) (hc : c ≠ s.self)
    (hS : GSolmate.totalSupply s ≠ 0)
    (hf : GSolmate.totalAssets (Asset.variant V) s ≤ V.feeOf s.asset a * GSolmate.totalSupply s) :
    GSolmate.totalAssets (Asset.variant V) s' * GSolmate.totalSupply s <
      GSolmate.totalAssets (Asset.variant V) s * GSolmate.totalSupply s' := by
  obtain ⟨e, hlt⟩ := fee_deposit_dilution hr hsink h hc hS
  omega

/-- With a fee, `withdraw(a)` delivers `a − fee(a)` to the receiver (EIP-4626 requires
exactly `a`). -/
theorem fee_withdraw_receiver {V : Variant A} {s s' : GSolmate.State (VState A) A} {c r o : A}
    {a n : ℕ} (hr : V.rebasing = false) (hrs : r ≠ s.self)
    (hra : V.feeSink = .owner → r ≠ s.asset.admin)
    (h : GSolmate.withdraw (Asset.variant V) s c a r o = some (s', n)) :
    s'.asset.bal r = s.asset.bal r + a - V.feeOf s.asset a := by
  obtain ⟨-, ht, -, -⟩ := GSolmate.withdraw_eq_some h
  rw [Asset.variant_transfer] at ht
  unfold transfer at ht
  split_ifs at ht
  exact V.move_fee_dst hr ht (Ne.symm hrs) hra

/-- The OpenZeppelin vault (any `δ`): with `T̂ = T + 1`, `Ŝ = S + 10^δ`, a fee worth at least
one virtual share (`T̂ ≤ f·Ŝ`) makes a deposit strictly lower the price. -/
theorem oz_fee_deposit_price_drop {V : Variant A} {δ : ℕ} {s s' : GOz.State (VState A) A}
    {c r : A} {a n : ℕ} (hr : V.rebasing = false)
    (hsink : V.feeSink = .owner → s.self ≠ s.asset.admin)
    (h : GOz.deposit (Asset.variant V) δ s c a r = some (s', n)) (hc : c ≠ s.self)
    (hf : GOz.vT (Asset.variant V) s ≤ V.feeOf s.asset a * GOz.vS δ s) :
    GOz.vT (Asset.variant V) s' * GOz.vS δ s < GOz.vT (Asset.variant V) s * GOz.vS δ s' := by
  obtain ⟨hp, ha, hself, hm⟩ := GOz.deposit_eq_some h
  rw [Asset.variant_transferFrom] at ha
  obtain ⟨s1, h1, h2⟩ := V.transferFrom_eq_some ha
  obtain ⟨e1, -, -, -, e5, -, e7, e8, -⟩ := V.spend_eq_some h1
  have hfe := Asset.feeOf_congr V e7 e8 a
  obtain ⟨-, -, hfa, -⟩ := (V.move_eq_some).1 h2
  have hd := V.move_fee_dst hr h2 hc (fun hk => e5 ▸ hsink hk)
  rw [hfe] at hfa hd
  have hT : GOz.vT (Asset.variant V) s' + V.feeOf s.asset a = GOz.vT (Asset.variant V) s + a := by
    simp only [GOz.vT, GOz.totalAssets, Asset.variant, balanceOf, hr, Bool.false_eq_true,
      ↓reduceIte, hself, hd, e1]
    omega
  have hS' : GOz.vS δ s' = GOz.vS δ s + n := by
    obtain ⟨-, -, -, e⟩ := Token.ozMint_eq_some hm; unfold GOz.vS GOz.totalSupply; rw [e]; omega
  obtain ⟨-, hTpos, -, hn⟩ := GOz.toShares_eq_some.1 hp
  simp only [Bool.false_eq_true, ↓reduceIte] at hn
  have hvT : 0 < GOz.vT (Asset.variant V) s := by unfold GOz.vT; omega
  have r2 := lt_div_add_one_mul (a * GOz.vS δ s) _ hvT
  rw [← hn] at r2
  rw [hS']
  set T := GOz.vT (Asset.variant V) s
  set T' := GOz.vT (Asset.variant V) s'
  set S := GOz.vS δ s
  set f := V.feeOf s.asset a
  have e1 : (T' + f) * S = (T + a) * S := by rw [hT]
  nlinarith

/-! ### Witness: STA (fee `⌈v/100⌉`, burned) under the Solmate vault -/

/-- STA's storage: holders `1` (alice) and `2` (bob) with `100` each, both having approved the
vault `10` without limit (STA spends even `MAX` allowances). -/
def staAsset : VState ℕ where
  self := 20
  bal := single 1 100 + single 2 100
  supply := 200
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

/-- An empty Solmate vault at `10` over STA. -/
def staVault : GSolmate.State (VState ℕ) ℕ := ⟨10, staAsset, ⟨0, 0, fun _ _ => 0⟩, 0, 0⟩

theorem staAsset_wf : (sta : Variant ℕ).WF staAsset := by
  unfold WF
  simp only [sta, standard, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, staAsset]
  refine ⟨?_, by norm_num [MAX]⟩
  rw [Token.total_add_single]; simp [total, sum_single_index]

/-- **Fee-on-transfer breakage, concretely.** Alice deposits `100` (`100` shares, the vault
receives `99`), then bob deposits `100` (`⌊100·100/99⌋ = 101` shares, the vault holds `198`).
Alice's `100` shares were worth `99` and are now worth `98`; the price fell from `99/100` to
`198/201` (`99·201 > 198·100`, refuting `T·S' ≤ T'·S`); alice redeems her shares for `98`, of
which she receives `97`. -/
theorem sta_solmate_witness :
    ((GSolmate.deposit (Asset.variant sta) staVault 1 100 1).bind fun p1 =>
      (GSolmate.deposit (Asset.variant sta) p1.1 2 100 2).bind fun p2 =>
      (GSolmate.redeem (Asset.variant sta) p2.1 1 100 1 1).map fun p3 =>
        (p1.2, GSolmate.totalAssets (Asset.variant sta) p1.1, GSolmate.totalSupply p1.1,
         GSolmate.convertToAssets (Asset.variant sta) p1.1 100,
         p2.2, GSolmate.totalAssets (Asset.variant sta) p2.1, GSolmate.totalSupply p2.1,
         GSolmate.convertToAssets (Asset.variant sta) p2.1 100,
         p3.2, p3.1.asset.bal 1)) =
      some (100, 99, 100, some 99, 101, 198, 201, some 98, 98, 97) := by
  simp [GSolmate.deposit, GSolmate.redeem, GSolmate.convertToShares, GSolmate.convertToAssets,
    GSolmate.totalAssets, GSolmate.totalSupply, staVault, staAsset, Asset.variant, safe_call,
    step, Variant.transferFrom, Variant.transfer, moveOk, spend, move, credit, units, feeOf,
    feeOverflow,
    balanceOf, sta, standard, Infinite.test, VState.setAllowance, Token.mint, Token.burn,
    Solmate.spendIfNotOwner, Solmate.bump, checkedAdd, mulDivDown, Finsupp.add_apply,
    Function.update, MAX]

/-! ## (b) Rebasing -/

/-- A rebase of the asset (no vault call) sets the vault's assets to `gons / (TOTAL_GONS / S)`
and leaves its shares. -/
theorem rebase_totalAssets {V : Variant A} (hr : V.rebasing = true) {s : GSolmate.State (VState A) A}
    {a' : VState A} {m : A} {S : ℕ} (h : V.rebase s.asset m S = some a') (hS : S ≤ V.maxSupply) :
    GSolmate.totalAssets (Asset.variant V) { s with asset := a' } =
      s.asset.bal s.self / (V.totalGons / S) :=
  (V.rebase_balanceOf hr h hS s.self).1

/-- **A negative rebase lowers `totalAssets`** (every share is worth less, with no vault call). -/
theorem negative_rebase_totalAssets_le {V : Variant A} (hV : V.Sane) (hr : V.rebasing = true)
    {s : GSolmate.State (VState A) A} (hw : V.WF s.asset) {a' : VState A} {m : A} {S : ℕ}
    (h : V.rebase s.asset m S = some a') (hS : S ≤ s.asset.supply) :
    GSolmate.totalAssets (Asset.variant V) { s with asset := a' } ≤
      GSolmate.totalAssets (Asset.variant V) s := by
  have hw' := hw
  unfold WF at hw'; simp only [hr, ↓reduceIte] at hw'
  obtain ⟨-, hpos, hcap, hsc⟩ := hw'
  obtain ⟨-, hsq⟩ := hV.rebasing_cap hr
  rw [rebase_totalAssets hr h (hS.trans hcap)]
  have hS0 : 0 < S := by
    unfold rebase at h; split_ifs at h with h0; simp at h0; exact h0.2
  have hk : 0 < V.totalGons / s.asset.supply := by
    apply Nat.div_pos _ hpos
    calc s.asset.supply ≤ s.asset.supply * s.asset.supply := Nat.le_mul_self _
      _ ≤ V.maxSupply ^ 2 := by rw [sq]; exact Nat.mul_le_mul hcap hcap
      _ ≤ _ := hsq
  simp only [GSolmate.totalAssets, Asset.variant, balanceOf, hr, ↓reduceIte]
  rw [hsc]
  exact Nat.div_le_div_left (Nat.div_le_div_left hS hS0) hk

/-- **A positive rebase raises `totalAssets`**, and with it every holder's `convertToAssets`:
the gain accrues to the share holders. -/
theorem positive_rebase_accrues {V : Variant A} (hV : V.Sane) (hr : V.rebasing = true)
    {s : GSolmate.State (VState A) A} (hw : V.WF s.asset) {a' : VState A} {m : A} {S : ℕ}
    (h : V.rebase s.asset m S = some a') (hS : s.asset.supply ≤ S) (hSm : S ≤ V.maxSupply)
    (b : ℕ) :
    GSolmate.totalAssets (Asset.variant V) s ≤
        GSolmate.totalAssets (Asset.variant V) { s with asset := a' } ∧
      b * GSolmate.totalAssets (Asset.variant V) s / GSolmate.totalSupply s ≤
        b * GSolmate.totalAssets (Asset.variant V) { s with asset := a' } /
          GSolmate.totalSupply { s with asset := a' } := by
  have hw' := hw
  unfold WF at hw'; simp only [hr, ↓reduceIte] at hw'
  obtain ⟨-, hpos, -, hsc⟩ := hw'
  obtain ⟨-, hsq⟩ := hV.rebasing_cap hr
  have hk : 0 < V.totalGons / S := by
    apply Nat.div_pos _ (lt_of_lt_of_le hpos hS)
    calc S ≤ S * S := Nat.le_mul_self _
      _ ≤ V.maxSupply ^ 2 := by rw [sq]; exact Nat.mul_le_mul hSm hSm
      _ ≤ _ := hsq
  have hT : GSolmate.totalAssets (Asset.variant V) s ≤
      GSolmate.totalAssets (Asset.variant V) { s with asset := a' } := by
    rw [rebase_totalAssets hr h hSm]
    simp only [GSolmate.totalAssets, Asset.variant, balanceOf, hr, ↓reduceIte]
    rw [hsc]
    exact Nat.div_le_div_left (Nat.div_le_div_left hS hpos) hk
  exact ⟨hT, Nat.div_le_div_right (Nat.mul_le_mul_left _ hT)⟩

/-! ### Witness: AMPL under the Solmate vault -/

/-- `TOTAL_GONS / 5·10^16`: gons per AMPL at the initial supply. -/
def amplGpf : ℕ := amplTotalGons / (5 * 10 ^ 16)

/-- AMPL's storage at the initial supply `5·10^16`: alice (`1`) holds `100` AMPL, account `3`
the remaining gons; alice approved the vault `10`; the monetary policy is `0`. -/
def amplAsset : VState ℕ where
  self := 20
  bal := single 1 (100 * amplGpf) + single 3 (amplTotalGons - 100 * amplGpf)
  supply := 5 * 10 ^ 16
  allowance := fun _ sp => if sp = 10 then MAX else 0
  scale := amplGpf
  admin := 0
  paused := false
  blacklisted := fun _ => false
  feeBps := 0
  feeMax := 0
  ether := 0
  frozen := 0
  nonces := 0

/-- An empty Solmate vault at `10` over AMPL. -/
def amplVault : GSolmate.State (VState ℕ) ℕ := ⟨10, amplAsset, ⟨0, 0, fun _ _ => 0⟩, 0, 0⟩

theorem amplAsset_wf : (ampl : Variant ℕ).WF amplAsset := by
  unfold WF
  simp only [ampl, standard, ↓reduceIte, amplAsset]
  have hle : 100 * amplGpf ≤ amplTotalGons := by norm_num [amplGpf, amplTotalGons, MAX]
  refine ⟨?_, by norm_num, by norm_num, rfl⟩
  rw [Token.total_add_single]; simp only [total, sum_single_index]; omega

/-- **Rebasing breakage, concretely.** Alice deposits `100` AMPL for `100` shares. After the
monetary policy halves the supply, the vault holds `50` and her shares are worth `50`; the
`withdraw(100)` she could preview before reverts. After a doubling instead, they are worth
`200`. -/
theorem ampl_rebase_witness :
    ((GSolmate.deposit (Asset.variant ampl) amplVault 1 100 1).bind fun p1 =>
      ((ampl : Variant ℕ).rebase p1.1.asset 0 (25 * 10 ^ 15)).bind fun down =>
      ((ampl : Variant ℕ).rebase p1.1.asset 0 (10 ^ 17)).map fun up =>
        (p1.2, GSolmate.convertToAssets (Asset.variant ampl) p1.1 100,
         GSolmate.totalAssets (Asset.variant ampl) { p1.1 with asset := down },
         GSolmate.convertToAssets (Asset.variant ampl) { p1.1 with asset := down } 100,
         (GSolmate.withdraw (Asset.variant ampl) { p1.1 with asset := down } 1 100 1 1).isSome,
         GSolmate.convertToAssets (Asset.variant ampl) { p1.1 with asset := up } 100)) =
      some (100, some 100, 50, some 50, false, some 200) := by
  simp [GSolmate.deposit, GSolmate.withdraw, GSolmate.convertToShares, GSolmate.convertToAssets,
    GSolmate.previewWithdraw, GSolmate.totalAssets, GSolmate.totalSupply, amplVault, amplAsset,
    Asset.variant, safe_call, step, Variant.transferFrom, Variant.transfer, moveOk, spend, move,
    credit, units, feeOf, feeOverflow, balanceOf, rebase, ampl, standard, Infinite.test,
    VState.setAllowance,
    Token.mint, Token.burn, Solmate.spendIfNotOwner, Solmate.bump, checkedAdd, mulDivDown,
    mulDivUp, ceilDiv, Finsupp.add_apply, amplGpf, amplTotalGons, MAX]

/-! ## (c) USDT approve race guard -/

/-- For a token that never returns `false`, a successful call is a successful step. -/
theorem step_of_call_ok {V : Variant A} {s s' : VState A} {c : A} {op : Call A} {ret : RetData}
    (hg : V.guardFail ≠ .returnFalse) (ha : V.arithFail ≠ .returnFalse)
    (h : V.call s c op = .ok s' ret) : V.step s c op = some s' := by
  unfold call at h
  cases hst : V.step s c op with
  | some s1 => rw [hst] at h; cases h; rfl
  | none =>
    rw [hst] at h
    exfalso
    have hk : V.failKind s c op = .returnFalse := by
      revert h; cases V.failKind s c op <;> intro h <;> first | rfl | cases h
    unfold failKind at hk
    split_ifs at hk
    · exact hg hk
    · exact ha hk

/-- An integration that approves `x` and then `y` (both nonzero, nothing in between) reverts
(`REVERT`, not `INVALID`: the guard is a `require`). -/
theorem usdt_reapprove_reverts {s s1 : VState A} {c sp : A} {x y : ℕ} {ret : RetData}
    (hx : x ≠ 0) (hy : y ≠ 0) (h1 : (usdt : Variant A).call s c (.approve sp x) = .ok s1 ret) :
    (usdt : Variant A).call s1 c (.approve sp y) = .halt .revert := by
  have hs1 : (usdt : Variant A).approve s c sp x = some s1 :=
    step_of_call_ok (by simp [usdt, standard]) (by simp [usdt, standard]) h1
  have hal : s1.allowance c sp = x := by
    unfold approve at hs1; split_ifs at hs1; cases hs1; simp [VState.setAllowance]
  have hst : (usdt : Variant A).step s1 c (.approve sp y) = none := by
    simp [step, approve, approveOk, usdt, standard, hy, hal, hx]
  have hg : (usdt : Variant A).guardOk s1 c (.approve sp y) = false := by
    simp [guardOk, approveOk, usdt, standard, hy, hal, hx]
  simp only [call, failKind, hst, hg, Bool.not_false, ↓reduceIte]
  rfl

/-- **The precise condition after a pull.** An integration approves `x` (`0 < x < MAX`), the
spender pulls `x'` with `transferFrom`; the next `approve(y)`, `y ≠ 0`, succeeds iff the pull
used the whole allowance (`x' = x`). Pulling less leaves a nonzero allowance and bricks the
re-approval. -/
theorem usdt_reapprove_after_pull {s s1 s2 : VState A} {c sp d : A} {x x' y : ℕ} (hxm : x < MAX)
    (hy : y ≠ 0) (h1 : (usdt : Variant A).approve s c sp x = some s1)
    (h2 : (usdt : Variant A).transferFrom s1 sp c d x' = some s2) :
    ((usdt : Variant A).approve s2 c sp y).isSome ↔ x' = x := by
  have hal : s1.allowance c sp = x := by
    unfold approve at h1; split_ifs at h1; cases h1; simp [VState.setAllowance]
  obtain ⟨s3, h3, h4⟩ := (usdt : Variant A).transferFrom_eq_some h2
  obtain ⟨-, -, -, rfl⟩ := ((usdt : Variant A).move_eq_some).1 h4
  have hal3 : s3.allowance c sp = x - x' ∧ x' ≤ x := by
    unfold spend at h3
    have hinf : ¬ MAX ≤ x := by omega
    simp only [usdt, standard, Bool.false_and, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
      Infinite.test, hal, decide_eq_true_eq, hinf] at h3
    split_ifs at h3 with hlt
    cases h3
    exact ⟨by simp [VState.setAllowance], by omega⟩
  have hc := ((usdt : Variant A).credit_fields s3 c d x').2.2.1
  rw [usdt_approve_isSome_iff, hc, hal3.1]
  have := hal3.2
  constructor
  · rintro (h | h)
    · exact absurd h hy
    · omega
  · intro h; right; omega

end QEDefi.ERC4626.Integration
