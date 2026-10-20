module

public import Defi.ERC4626.Solmate
public import Defi.Math.Arith

/-!
# Properties of the Solmate vault

Theorems about the model in `Solmate.lean`, one per entry of
`docs/erc4626-invariants.md` (ids in brackets). Notation: `T = totalAssets`,
`S = totalSupply`, primes for the state after a call.

* previews equal the actual results [P-PREVIEW-*];
* rounding directions [R-*], as cross-multiplied inequalities and over `ℚ`;
* no dilution: the share price `T / S` never decreases through
  deposit/mint/withdraw/redeem [E-PRICE-*];
* solvency: `Σ convertToAssets(balanceOf[x]) ≤ totalAssets` [I-SOLVENT];
* the eight a16z round trips, which hold whenever `S > 0` (and the state in between
  still has shares), and fail — with proofs of the failure — when the vault starts with
  `S = 0 < T` or the first call drains it [RT-*];
* EIP-4626 clauses that Solmate violates [EIP-*].
-/

@[expose] public section

namespace EvmLeanSpecs.Vault.Solmate

open Token Finsupp

variable {A : Type} [DecidableEq A]

/-! ## Previews equal results (EIP-4626 `preview*` clauses, a16z `prop_preview*`) -/

/-- [P-PREVIEW-DEPOSIT] `deposit` mints exactly `previewDeposit(assets)` shares. -/
theorem deposit_eq_previewDeposit {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit s c a r = some (s', n)) : s.previewDeposit a = some n :=
  (deposit_eq_some h).1

/-- [P-PREVIEW-MINT] `mint` pulls exactly `previewMint(shares)` assets. -/
theorem mint_eq_previewMint {s s' : State A} {c r : A} {n a : ℕ}
    (h : mint s c n r = some (s', a)) : s.previewMint n = some a :=
  (mint_eq_some' h).1

/-- [P-PREVIEW-WITHDRAW] `withdraw` burns exactly `previewWithdraw(assets)` shares. -/
theorem withdraw_eq_previewWithdraw {s s' : State A} {c r o : A} {a n : ℕ}
    (h : withdraw s c a r o = some (s', n)) : s.previewWithdraw a = some n :=
  (withdraw_eq_some h).1

/-- [P-PREVIEW-REDEEM] `redeem` pays exactly `previewRedeem(shares)` assets. -/
theorem redeem_eq_previewRedeem {s s' : State A} {c r o : A} {n a : ℕ}
    (h : redeem s c n r o = some (s', a)) : s.previewRedeem n = some a :=
  (redeem_eq_some h).1

/-! ## Rounding directions (EIP-4626 "Security Considerations") -/

/-- [R-DEPOSIT] `deposit` rounds the shares down: `n = ⌊a·S/T⌋`. -/
theorem deposit_rounding {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit s c a r = some (s', n)) (hS : s.totalSupply ≠ 0) :
    n * s.totalAssets ≤ a * s.totalSupply ∧ a * s.totalSupply < (n + 1) * s.totalAssets := by
  rcases convertToShares_eq_some.1 (deposit_eq_some h).1 with ⟨h0, -⟩ | ⟨-, hT, -, rfl⟩
  · exact absurd h0 hS
  · exact ⟨Nat.div_mul_le_self _ _, lt_div_add_one_mul _ _ (Nat.pos_of_ne_zero hT)⟩

/-- [R-MINT] `mint` rounds the assets up: `a = ⌈n·T/S⌉`. -/
theorem mint_rounding {s s' : State A} {c r : A} {n a : ℕ}
    (h : mint s c n r = some (s', a)) (hS : s.totalSupply ≠ 0) :
    n * s.totalAssets ≤ a * s.totalSupply ∧ a * s.totalSupply < n * s.totalAssets + s.totalSupply := by
  rcases previewMint_eq_some.1 (mint_eq_some' h).1 with ⟨h0, -⟩ | ⟨-, -, rfl⟩
  · exact absurd h0 hS
  · exact ⟨le_ceilDiv_mul _ _ (Nat.pos_of_ne_zero hS), ceilDiv_mul_lt _ _ (Nat.pos_of_ne_zero hS)⟩

/-- [R-WITHDRAW] `withdraw` rounds the burned shares up: `n = ⌈a·S/T⌉`. -/
theorem withdraw_rounding {s s' : State A} {c r o : A} {a n : ℕ}
    (h : withdraw s c a r o = some (s', n)) (hS : s.totalSupply ≠ 0) :
    a * s.totalSupply ≤ n * s.totalAssets ∧ n * s.totalAssets < a * s.totalSupply + s.totalAssets := by
  rcases previewWithdraw_eq_some.1 (withdraw_eq_some h).1 with ⟨h0, -⟩ | ⟨-, hT, -, rfl⟩
  · exact absurd h0 hS
  · exact ⟨le_ceilDiv_mul _ _ (Nat.pos_of_ne_zero hT), ceilDiv_mul_lt _ _ (Nat.pos_of_ne_zero hT)⟩

/-- [R-REDEEM] `redeem` rounds the paid assets down: `a = ⌊n·T/S⌋`. -/
theorem redeem_rounding {s s' : State A} {c r o : A} {n a : ℕ}
    (h : redeem s c n r o = some (s', a)) (hS : s.totalSupply ≠ 0) :
    a * s.totalSupply ≤ n * s.totalAssets ∧ n * s.totalAssets < (a + 1) * s.totalSupply := by
  rcases convertToAssets_eq_some.1 (redeem_eq_some h).1 with ⟨h0, -⟩ | ⟨-, -, rfl⟩
  · exact absurd h0 hS
  · exact ⟨Nat.div_mul_le_self _ _, lt_div_add_one_mul _ _ (Nat.pos_of_ne_zero hS)⟩

/-- The exchange rate `T/S` as a rational number (assets per share). -/
def State.price (s : State A) : ℚ := (s.totalAssets : ℚ) / s.totalSupply

/-- [R-DEPOSIT] over `ℚ`: the depositor gets at most `a / price` shares. -/
theorem deposit_shares_le_fair {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit s c a r = some (s', n)) (hS : s.totalSupply ≠ 0) :
    (n : ℚ) ≤ a * s.totalSupply / s.totalAssets := by
  have hT : s.totalAssets ≠ 0 := by
    rcases convertToShares_eq_some.1 (deposit_eq_some h).1 with ⟨h0, -⟩ | ⟨-, hT, -⟩
    · exact absurd h0 hS
    · exact hT
  rw [le_div_iff₀ (by positivity)]
  exact_mod_cast (deposit_rounding h hS).1

/-- [R-REDEEM] over `ℚ`: the redeemer gets at most `n · price` assets. -/
theorem redeem_assets_le_fair {s s' : State A} {c r o : A} {n a : ℕ}
    (h : redeem s c n r o = some (s', a)) (hS : s.totalSupply ≠ 0) :
    (a : ℚ) ≤ n * s.price := by
  unfold State.price
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  exact_mod_cast (redeem_rounding h hS).1

/-- [R-MINT] over `ℚ`: the minter pays at least `n · price` assets. -/
theorem mint_assets_ge_fair {s s' : State A} {c r : A} {n a : ℕ}
    (h : mint s c n r = some (s', a)) (hS : s.totalSupply ≠ 0) :
    n * s.price ≤ (a : ℚ) := by
  unfold State.price
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  exact_mod_cast (mint_rounding h hS).1

/-- [R-WITHDRAW] over `ℚ`: the withdrawer burns at least `a / price` shares. -/
theorem withdraw_shares_ge_fair {s s' : State A} {c r o : A} {a n : ℕ}
    (h : withdraw s c a r o = some (s', n)) (hS : s.totalSupply ≠ 0) :
    (a : ℚ) * s.totalSupply / s.totalAssets ≤ n := by
  have hT : s.totalAssets ≠ 0 := by
    rcases previewWithdraw_eq_some.1 (withdraw_eq_some h).1 with ⟨h0, -⟩ | ⟨-, hT, -⟩
    · exact absurd h0 hS
    · exact hT
  rw [div_le_iff₀ (by positivity)]
  exact_mod_cast (withdraw_rounding h hS).1

/-! ## State changes in `T` and `S` -/

/-- `deposit` from a caller other than the vault: `T' = T + a`, `S' = S + n`. -/
theorem deposit_TS {s s' : State A} {c r : A} {a n : ℕ} (h : deposit s c a r = some (s', n))
    (hc : c ≠ s.self) : s'.totalAssets = s.totalAssets + a ∧ s'.totalSupply = s.totalSupply + n := by
  obtain ⟨-, -, -, -, hself, hb, -, -, hS⟩ := deposit_eq_some h
  exact ⟨totalAssets_in hc hself hb, hS⟩

/-- `mint` from a caller other than the vault: `T' = T + a`, `S' = S + n`. -/
theorem mint_TS {s s' : State A} {c r : A} {n a : ℕ} (h : mint s c n r = some (s', a))
    (hc : c ≠ s.self) : s'.totalAssets = s.totalAssets + a ∧ s'.totalSupply = s.totalSupply + n := by
  obtain ⟨-, -, -, hself, hb, -, -, hS⟩ := mint_eq_some' h
  exact ⟨totalAssets_in hc hself hb, hS⟩

/-- `withdraw` to a receiver other than the vault: `T' = T - a`, `S' = S - n`, with
`a ≤ T` and `n ≤ S`. -/
theorem withdraw_TS {s s' : State A} {c r o : A} {a n : ℕ} (hi : Inv s)
    (h : withdraw s c a r o = some (s', n)) (hr : r ≠ s.self) :
    s'.totalAssets = s.totalAssets - a ∧ s'.totalSupply = s.totalSupply - n ∧
      a ≤ s.totalAssets ∧ n ≤ s.totalSupply := by
  obtain ⟨-, hn, ha, hself, hb, -, -, hS⟩ := withdraw_eq_some h
  exact ⟨totalAssets_out hr hself hb, hS, ha, hn.trans (balanceOf_le_totalSupply hi.2 o)⟩

/-- `redeem` to a receiver other than the vault: `T' = T - a`, `S' = S - n`. -/
theorem redeem_TS {s s' : State A} {c r o : A} {n a : ℕ} (hi : Inv s)
    (h : redeem s c n r o = some (s', a)) (hr : r ≠ s.self) :
    s'.totalAssets = s.totalAssets - a ∧ s'.totalSupply = s.totalSupply - n ∧
      a ≤ s.totalAssets ∧ n ≤ s.totalSupply := by
  obtain ⟨-, -, hn, ha, hself, hb, -, -, hS⟩ := redeem_eq_some h
  exact ⟨totalAssets_out hr hself hb, hS, ha, hn.trans (balanceOf_le_totalSupply hi.2 o)⟩

/-! ## No dilution: the share price never decreases -/

/-- [E-PRICE-DEPOSIT] A deposit never lowers assets-per-share: `T·S' ≤ T'·S`. -/
theorem deposit_price_mono {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit s c a r = some (s', n)) (hc : c ≠ s.self) (hS : s.totalSupply ≠ 0) :
    s.totalAssets * s'.totalSupply ≤ s'.totalAssets * s.totalSupply := by
  obtain ⟨e1, e2⟩ := deposit_TS h hc
  have := (deposit_rounding h hS).1
  rw [e1, e2]; nlinarith

/-- [E-PRICE-MINT] A mint never lowers assets-per-share. -/
theorem mint_price_mono {s s' : State A} {c r : A} {n a : ℕ}
    (h : mint s c n r = some (s', a)) (hc : c ≠ s.self) (hS : s.totalSupply ≠ 0) :
    s.totalAssets * s'.totalSupply ≤ s'.totalAssets * s.totalSupply := by
  obtain ⟨e1, e2⟩ := mint_TS h hc
  have := (mint_rounding h hS).1
  rw [e1, e2]; nlinarith

/-- [E-PRICE-WITHDRAW] A withdrawal never lowers assets-per-share (for any receiver). -/
theorem withdraw_price_mono {s s' : State A} {c r o : A} {a n : ℕ} (hi : Inv s)
    (h : withdraw s c a r o = some (s', n)) (hS : s.totalSupply ≠ 0) :
    s.totalAssets * s'.totalSupply ≤ s'.totalAssets * s.totalSupply := by
  have hr := (withdraw_rounding h hS).1
  obtain ⟨-, hn, ha, hself, hb, -, -, hS'⟩ := withdraw_eq_some h
  have hnS : n ≤ s.totalSupply := hn.trans (balanceOf_le_totalSupply hi.2 o)
  rw [hS']
  by_cases hrs : r = s.self
  · subst hrs
    rw [totalAssets_out_self ha hself hb]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  · rw [totalAssets_out hrs hself hb]
    obtain ⟨T₁, hT⟩ := Nat.exists_eq_add_of_le ha
    obtain ⟨S₁, hS₁⟩ := Nat.exists_eq_add_of_le hnS
    rw [hT, hS₁] at hr ⊢
    simp only [Nat.add_sub_cancel_left]
    nlinarith

/-- [E-PRICE-REDEEM] A redemption never lowers assets-per-share (for any receiver). -/
theorem redeem_price_mono {s s' : State A} {c r o : A} {n a : ℕ} (hi : Inv s)
    (h : redeem s c n r o = some (s', a)) (hS : s.totalSupply ≠ 0) :
    s.totalAssets * s'.totalSupply ≤ s'.totalAssets * s.totalSupply := by
  have hr := (redeem_rounding h hS).1
  obtain ⟨-, -, hn, ha, hself, hb, -, -, hS'⟩ := redeem_eq_some h
  have hnS : n ≤ s.totalSupply := hn.trans (balanceOf_le_totalSupply hi.2 o)
  rw [hS']
  by_cases hrs : r = s.self
  · subst hrs
    rw [totalAssets_out_self ha hself hb]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  · rw [totalAssets_out hrs hself hb]
    obtain ⟨T₁, hT⟩ := Nat.exists_eq_add_of_le ha
    obtain ⟨S₁, hS₁⟩ := Nat.exists_eq_add_of_le hnS
    rw [hT, hS₁] at hr ⊢
    simp only [Nat.add_sub_cancel_left]
    nlinarith

/-- Cross-multiplied price monotonicity is monotonicity of `price` over `ℚ`. -/
theorem price_le_of_cross {s s' : State A} (hS : s.totalSupply ≠ 0) (hS' : s'.totalSupply ≠ 0)
    (h : s.totalAssets * s'.totalSupply ≤ s'.totalAssets * s.totalSupply) : s.price ≤ s'.price := by
  unfold State.price
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast h

/-- [E-PRICE-DEPOSIT] over `ℚ`: `price s ≤ price s'`. -/
theorem deposit_price_le {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit s c a r = some (s', n)) (hc : c ≠ s.self) (hS : s.totalSupply ≠ 0) :
    s.price ≤ s'.price :=
  price_le_of_cross hS (by rw [(deposit_TS h hc).2]; omega) (deposit_price_mono h hc hS)

/-- [E-PRICE-REDEEM] over `ℚ`, while shares remain. -/
theorem redeem_price_le {s s' : State A} {c r o : A} {n a : ℕ} (hi : Inv s)
    (h : redeem s c n r o = some (s', a)) (hS : s.totalSupply ≠ 0) (hS' : s'.totalSupply ≠ 0) :
    s.price ≤ s'.price :=
  price_le_of_cross hS hS' (redeem_price_mono hi h hS)

/-! ## Solvency -/

/-- [I-SOLVENT] The vault can always pay every holder's `convertToAssets` at once:
`Σₓ ⌊balanceOf[x]·T/S⌋ ≤ T` (in every state satisfying `Inv`, hence in every reachable
state by `Inv_exec`). -/
theorem solvent (s : State A) (hi : Inv s) :
    (s.shares.balanceOf.sum fun _ b => b * s.totalAssets / s.totalSupply) ≤ s.totalAssets := by
  have hsum : total s.shares.balanceOf = s.totalSupply := hi.2.1
  by_cases hS : s.totalSupply = 0
  · simp [hS]
  · have hpos := Nat.pos_of_ne_zero hS
    unfold Finsupp.sum
    rw [← Nat.mul_le_mul_right_iff hpos]
    calc (∑ x ∈ s.shares.balanceOf.support,
            s.shares.balanceOf x * s.totalAssets / s.totalSupply) * s.totalSupply
        = ∑ x ∈ s.shares.balanceOf.support,
            s.shares.balanceOf x * s.totalAssets / s.totalSupply * s.totalSupply :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ x ∈ s.shares.balanceOf.support, s.shares.balanceOf x * s.totalAssets :=
          Finset.sum_le_sum fun _ _ => Nat.div_mul_le_self _ _
      _ = total s.shares.balanceOf * s.totalAssets := by
          unfold total Finsupp.sum; rw [Finset.sum_mul]
      _ = s.totalAssets * s.totalSupply := by rw [hsum, Nat.mul_comm]

/-- Each holder's `convertToAssets`, when it does not revert, is the floor share used in
`solvent`. -/
theorem convertToAssets_balance {s : State A} {x : A} {v : ℕ} (hS : s.totalSupply ≠ 0)
    (h : s.convertToAssets (s.shares.balanceOf x) = some v) :
    v = s.shares.balanceOf x * s.totalAssets / s.totalSupply := by
  rcases convertToAssets_eq_some.1 h with ⟨h0, -⟩ | ⟨-, -, rfl⟩
  · exact absurd h0 hS
  · rfl

/-- [P-MAXWITHDRAW] `maxWithdraw(owner)` is withdrawable as far as shares go: the shares
`previewWithdraw` charges for it never exceed the owner's balance. -/
theorem previewWithdraw_maxWithdraw_le {s : State A} {o : A} {m n : ℕ}
    (hm : s.maxWithdraw o = some m) (hn : s.previewWithdraw m = some n) :
    n ≤ s.shares.balanceOf o := by
  unfold State.maxWithdraw at hm
  rcases convertToAssets_eq_some.1 hm with ⟨h0, rfl⟩ | ⟨hS, -, rfl⟩
  · rcases previewWithdraw_eq_some.1 hn with ⟨-, rfl⟩ | ⟨h1, -⟩
    · exact le_rfl
    · exact absurd h0 h1
  · rcases previewWithdraw_eq_some.1 hn with ⟨h1, -⟩ | ⟨-, hT, -, rfl⟩
    · exact absurd h1 hS
    · rw [ceilDiv_le_iff _ _ _ (Nat.pos_of_ne_zero hT)]
      exact Nat.div_mul_le_self _ _

/-! ## Round trips (a16z `test_RT_*`, crytic `verify_*RoundTrip*`) -/

/-- [RT-DEPOSIT-REDEEM] `redeem(deposit(a)) ≤ a` when the vault already has shares. -/
theorem rt_deposit_redeem {s s₁ s₂ : State A} {c r c' r' o : A} {a n a' : ℕ}
    (h₁ : deposit s c a r = some (s₁, n)) (h₂ : redeem s₁ c' n r' o = some (s₂, a'))
    (hc : c ≠ s.self) (hS : s.totalSupply ≠ 0) : a' ≤ a := by
  obtain ⟨eT, eS⟩ := deposit_TS h₁ hc
  have r1 := (deposit_rounding h₁ hS).1
  have r2 := (redeem_rounding h₂ (by rw [eS]; omega)).1
  rw [eT, eS] at r2
  exact rt_in_out_assets (by omega) r1 r2

/-- [RT-MINT-REDEEM] `redeem(n) ≤ mint(n)` (assets out ≤ assets in). -/
theorem rt_mint_redeem {s s₁ s₂ : State A} {c r c' r' o : A} {n a a' : ℕ}
    (h₁ : mint s c n r = some (s₁, a)) (h₂ : redeem s₁ c' n r' o = some (s₂, a'))
    (hc : c ≠ s.self) (hS : s.totalSupply ≠ 0) : a' ≤ a := by
  obtain ⟨eT, eS⟩ := mint_TS h₁ hc
  have r1 := (mint_rounding h₁ hS).1
  have r2 := (redeem_rounding h₂ (by rw [eS]; omega)).1
  rw [eT, eS] at r2
  exact rt_in_out_assets (by omega) r1 r2

/-- `withdraw` succeeding on a state with shares implies that state has assets. -/
theorem withdraw_totalAssets_pos {s s' : State A} {c r o : A} {a n : ℕ}
    (h : withdraw s c a r o = some (s', n)) (hS : s.totalSupply ≠ 0) : s.totalAssets ≠ 0 := by
  rcases previewWithdraw_eq_some.1 (withdraw_eq_some h).1 with ⟨h0, -⟩ | ⟨-, hT, -⟩
  · exact absurd h0 hS
  · exact hT

/-- `deposit` succeeding on a state with shares implies that state has assets. -/
theorem deposit_totalAssets_pos {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit s c a r = some (s', n)) (hS : s.totalSupply ≠ 0) : s.totalAssets ≠ 0 := by
  rcases convertToShares_eq_some.1 (deposit_eq_some h).1 with ⟨h0, -⟩ | ⟨-, hT, -⟩
  · exact absurd h0 hS
  · exact hT

/-- [RT-DEPOSIT-WITHDRAW] `withdraw(a)` burns at least the `deposit(a)` shares. -/
theorem rt_deposit_withdraw {s s₁ s₂ : State A} {c r c' r' o : A} {a n n' : ℕ}
    (h₁ : deposit s c a r = some (s₁, n)) (h₂ : withdraw s₁ c' a r' o = some (s₂, n'))
    (hc : c ≠ s.self) (hS : s.totalSupply ≠ 0) : n ≤ n' := by
  obtain ⟨eT, eS⟩ := deposit_TS h₁ hc
  have hS₁ : s₁.totalSupply ≠ 0 := by rw [eS]; omega
  have r1 := (deposit_rounding h₁ hS).1
  have r2 := (withdraw_rounding h₂ hS₁).1
  have hT := withdraw_totalAssets_pos h₂ hS₁
  rw [eT, eS] at r2; rw [eT] at hT
  exact rt_in_out_shares (by omega) r1 r2

/-- [RT-MINT-WITHDRAW] `withdraw(mint(n))` burns at least `n` shares. -/
theorem rt_mint_withdraw {s s₁ s₂ : State A} {c r c' r' o : A} {n a n' : ℕ}
    (h₁ : mint s c n r = some (s₁, a)) (h₂ : withdraw s₁ c' a r' o = some (s₂, n'))
    (hc : c ≠ s.self) (hS : s.totalSupply ≠ 0) : n ≤ n' := by
  obtain ⟨eT, eS⟩ := mint_TS h₁ hc
  have hS₁ : s₁.totalSupply ≠ 0 := by rw [eS]; omega
  have r1 := (mint_rounding h₁ hS).1
  have r2 := (withdraw_rounding h₂ hS₁).1
  have hT := withdraw_totalAssets_pos h₂ hS₁
  rw [eT, eS] at r2; rw [eT] at hT
  exact rt_in_out_shares (by omega) r1 r2

/-- [RT-REDEEM-DEPOSIT] `deposit(redeem(n)) ≤ n` while the vault keeps some shares. -/
theorem rt_redeem_deposit {s s₁ s₂ : State A} {c r o c' r' : A} {n a n' : ℕ} (hi : Inv s)
    (h₁ : redeem s c n r o = some (s₁, a)) (h₂ : deposit s₁ c' a r' = some (s₂, n'))
    (hr : r ≠ s.self) (hS : s.totalSupply ≠ 0) (hS₁ : s₁.totalSupply ≠ 0) : n' ≤ n := by
  obtain ⟨eT, eS, ha, hn⟩ := redeem_TS hi h₁ hr
  have r1 := (redeem_rounding h₁ hS).1
  have r2 := (deposit_rounding h₂ hS₁).1
  have hT := deposit_totalAssets_pos h₂ hS₁
  rw [eT, eS] at r2; rw [eT] at hT
  obtain ⟨T₁, hT₁⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨S₁, hS₁'⟩ := Nat.exists_eq_add_of_le hn
  simp only [hT₁, hS₁', Nat.add_sub_cancel_left] at r1 r2 hT
  exact rt_out_in_shares (by omega) r1 r2

/-- [RT-WITHDRAW-DEPOSIT] `deposit(a) ≤ withdraw(a)` (shares) while shares remain. -/
theorem rt_withdraw_deposit {s s₁ s₂ : State A} {c r o c' r' : A} {a n n' : ℕ} (hi : Inv s)
    (h₁ : withdraw s c a r o = some (s₁, n)) (h₂ : deposit s₁ c' a r' = some (s₂, n'))
    (hr : r ≠ s.self) (hS : s.totalSupply ≠ 0) (hS₁ : s₁.totalSupply ≠ 0) : n' ≤ n := by
  obtain ⟨eT, eS, ha, hn⟩ := withdraw_TS hi h₁ hr
  have r1 := (withdraw_rounding h₁ hS).1
  have r2 := (deposit_rounding h₂ hS₁).1
  have hT := deposit_totalAssets_pos h₂ hS₁
  rw [eT, eS] at r2; rw [eT] at hT
  obtain ⟨T₁, hT₁⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨S₁, hS₁'⟩ := Nat.exists_eq_add_of_le hn
  simp only [hT₁, hS₁', Nat.add_sub_cancel_left] at r1 r2 hT
  exact rt_out_in_shares (by omega) (by linarith) r2

/-- [RT-REDEEM-MINT] `mint(n)` after `redeem(n)` costs at least what the redemption paid. -/
theorem rt_redeem_mint {s s₁ s₂ : State A} {c r o c' r' : A} {n a a' : ℕ} (hi : Inv s)
    (h₁ : redeem s c n r o = some (s₁, a)) (h₂ : mint s₁ c' n r' = some (s₂, a'))
    (hr : r ≠ s.self) (hS : s.totalSupply ≠ 0) (hS₁ : s₁.totalSupply ≠ 0) : a ≤ a' := by
  obtain ⟨eT, eS, ha, hn⟩ := redeem_TS hi h₁ hr
  have r1 := (redeem_rounding h₁ hS).1
  have r2 := (mint_rounding h₂ hS₁).1
  rw [eT, eS] at r2; rw [eS] at hS₁
  obtain ⟨T₁, hT₁⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨S₁, hS₁'⟩ := Nat.exists_eq_add_of_le hn
  simp only [hT₁, hS₁', Nat.add_sub_cancel_left] at r1 r2 hS₁
  exact rt_out_in_assets (Nat.pos_of_ne_zero hS₁) r1 r2

/-- [RT-WITHDRAW-MINT] `mint(withdraw(a))` costs at least `a`. -/
theorem rt_withdraw_mint {s s₁ s₂ : State A} {c r o c' r' : A} {a n a' : ℕ} (hi : Inv s)
    (h₁ : withdraw s c a r o = some (s₁, n)) (h₂ : mint s₁ c' n r' = some (s₂, a'))
    (hr : r ≠ s.self) (hS : s.totalSupply ≠ 0) (hS₁ : s₁.totalSupply ≠ 0) : a ≤ a' := by
  obtain ⟨eT, eS, ha, hn⟩ := withdraw_TS hi h₁ hr
  have r1 := (withdraw_rounding h₁ hS).1
  have r2 := (mint_rounding h₂ hS₁).1
  rw [eT, eS] at r2; rw [eS] at hS₁
  obtain ⟨T₁, hT₁⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨S₁, hS₁'⟩ := Nat.exists_eq_add_of_le hn
  simp only [hT₁, hS₁', Nat.add_sub_cancel_left] at r1 r2 hS₁
  exact rt_out_in_assets (Nat.pos_of_ne_zero hS₁) (by linarith) r2

/-! ## Where the round trips fail -/

/-- [RT-DEPOSIT-REDEEM ✗] **Counterexample** (any state with `S = 0 < T`, e.g. after a
donation to an empty vault, or yield accrued after everyone left): a depositor who
immediately redeems receives `T + a`, strictly more than the `a` deposited. -/
theorem rt_deposit_redeem_empty_supply {s s₁ s₂ : State A} {c r c' r' o : A} {a n a' : ℕ}
    (h₁ : deposit s c a r = some (s₁, n)) (h₂ : redeem s₁ c' n r' o = some (s₂, a'))
    (hc : c ≠ s.self) (hS : s.totalSupply = 0) : n = a ∧ a' = s.totalAssets + a := by
  obtain ⟨eT, eS⟩ := deposit_TS h₁ hc
  have hn : n = a := by
    rcases convertToShares_eq_some.1 (deposit_eq_some h₁).1 with ⟨-, rfl⟩ | ⟨h0, -⟩
    · rfl
    · exact absurd hS h0
  have hn0 := (deposit_eq_some h₁).2.1
  refine ⟨hn, ?_⟩
  rcases convertToAssets_eq_some.1 (redeem_eq_some h₂).1 with ⟨h0, -⟩ | ⟨-, -, rfl⟩
  · rw [eS, hS] at h0; omega
  · rw [eT, eS, hS, hn, Nat.zero_add, Nat.mul_comm, Nat.mul_div_cancel _ (by omega)]

/-- [RT-MINT-REDEEM ✗] **Counterexample**: on `S = 0 < T`, `mint(n)` costs `n` but
`redeem(n)` immediately pays `T + n`. -/
theorem rt_mint_redeem_empty_supply {s s₁ s₂ : State A} {c r c' r' o : A} {n a a' : ℕ}
    (h₁ : mint s c n r = some (s₁, a)) (h₂ : redeem s₁ c' n r' o = some (s₂, a'))
    (hc : c ≠ s.self) (hS : s.totalSupply = 0) : a = n ∧ a' = s.totalAssets + n := by
  obtain ⟨eT, eS⟩ := mint_TS h₁ hc
  have ha : a = n := by
    rcases previewMint_eq_some.1 (mint_eq_some' h₁).1 with ⟨-, rfl⟩ | ⟨h0, -⟩
    · rfl
    · exact absurd hS h0
  refine ⟨ha, ?_⟩
  have hz := (redeem_eq_some h₂).2.1
  rcases convertToAssets_eq_some.1 (redeem_eq_some h₂).1 with ⟨h0, rfl⟩ | ⟨-, -, rfl⟩
  · rw [eS, hS] at h0; omega
  · have hn : n ≠ 0 := by rintro rfl; simp at hz
    rw [eT, eS, hS, ha, Nat.zero_add, Nat.mul_comm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn)]

/-- [RT-REDEEM-DEPOSIT ✗] **Counterexample** (share count only): the last holder redeems
all `S` shares for `T` assets and deposits them back into the now-empty vault, receiving
`T` shares — more than `S` whenever the price exceeded one asset per share. -/
theorem rt_redeem_deposit_drained {s s₁ s₂ : State A} {c r o c' r' : A} {a n' : ℕ} (hi : Inv s)
    (h₁ : redeem s c s.totalSupply r o = some (s₁, a)) (h₂ : deposit s₁ c' a r' = some (s₂, n'))
    (hr : r ≠ s.self) (hS : s.totalSupply ≠ 0) : a = s.totalAssets ∧ n' = s.totalAssets := by
  obtain ⟨-, eS, -, -⟩ := redeem_TS hi h₁ hr
  have ha : a = s.totalAssets := by
    rcases convertToAssets_eq_some.1 (redeem_eq_some h₁).1 with ⟨h0, -⟩ | ⟨-, -, rfl⟩
    · exact absurd h0 hS
    · exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hS)
  refine ⟨ha, ?_⟩
  rcases convertToShares_eq_some.1 (deposit_eq_some h₂).1 with ⟨-, rfl⟩ | ⟨h0, -⟩
  · exact ha
  · rw [eS, Nat.sub_self] at h0; exact absurd rfl h0

/-! ## EIP-4626 clauses Solmate does not meet -/

/-- [EIP-CONVERT-NOREVERT ✗] "`convertToShares` MUST NOT revert unless due to integer
overflow caused by an unreasonably large input." After a total loss (`T = 0` with `S > 0`)
it reverts on every input, including `0` (division by zero). -/
theorem convertToShares_reverts_of_totalAssets_zero {s : State A} (hS : s.totalSupply ≠ 0)
    (hT : s.totalAssets = 0) (a : ℕ) : s.convertToShares a = none := by
  simp [State.convertToShares, hS, mulDivDown, hT]

/-- [EIP-MAXDEPOSIT ✗] "`maxDeposit` MUST return the maximum amount … that would not cause
a revert": in the same state `maxDeposit = 2^256 - 1`, yet every `deposit` reverts. -/
theorem deposit_reverts_of_totalAssets_zero {s : State A} (hS : s.totalSupply ≠ 0)
    (hT : s.totalAssets = 0) (c r : A) (a : ℕ) :
    s.maxDeposit r = MAX ∧ deposit s c a r = none := by
  refine ⟨rfl, ?_⟩
  simp [deposit, State.previewDeposit, convertToShares_reverts_of_totalAssets_zero hS hT]

/-- [E-FREE-MINT] In the same state `mint(n)` costs nothing: anyone can mint arbitrary
shares for zero assets (they are worthless now, but will claim any later yield or
donation). -/
theorem previewMint_zero_of_totalAssets_zero {s : State A} (hS : s.totalSupply ≠ 0)
    (hT : s.totalAssets = 0) (n : ℕ) : s.previewMint n = some 0 := by
  have hmax : 0 < MAX := by unfold MAX; omega
  simp [State.previewMint, hS, mulDivUp, hT, ceilDiv]

/-- `redeem` reverts whenever `previewRedeem` is `0` (`ZERO_ASSETS`). -/
theorem redeem_eq_none_of_previewRedeem_zero {s : State A} {c r o : A} {n : ℕ}
    (h : s.previewRedeem n = some 0) : redeem s c n r o = none := by
  cases hr : redeem s c n r o with
  | none => rfl
  | some p =>
    obtain ⟨s', a⟩ := p
    obtain ⟨hp, hz, -⟩ := redeem_eq_some hr
    rw [h] at hp; cases hp; exact absurd rfl hz

/-- [EIP-MAXREDEEM ✗] "`maxRedeem` MUST return the maximum amount of shares that could be
transferred from `owner` through `redeem` and not cause a revert". When the owner's
balance is worth less than one asset (`b·T < S`), `maxRedeem = b > 0` but `redeem(b)`
reverts with `ZERO_ASSETS` (and so does every smaller amount). -/
theorem maxRedeem_reverts {s : State A} {c r o : A} (hi : Inv s) (hS : s.totalSupply ≠ 0)
    (hlt : s.shares.balanceOf o * s.totalAssets < s.totalSupply) :
    s.maxRedeem o = s.shares.balanceOf o ∧ redeem s c (s.maxRedeem o) r o = none := by
  refine ⟨rfl, redeem_eq_none_of_previewRedeem_zero ?_⟩
  have hmax : s.shares.balanceOf o * s.totalAssets ≤ MAX := hlt.le.trans hi.2.2
  rw [State.previewRedeem, convertToAssets_eq_some]
  exact Or.inr ⟨hS, hmax, (Nat.div_eq_of_lt hlt).symm⟩

end EvmLeanSpecs.Vault.Solmate
