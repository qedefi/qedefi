module

public import QEDefi.ERC4626.Solmate
public import QEDefi.Math.Arith
public import Mathlib.Tactic.Positivity

/-!
# Properties of the Solmate vault

Previews, rounding, no dilution, solvency, the eight a16z round trips (which hold while
`S > 0` and fail, proved, from `S = 0 < T` or a drained vault) and the EIP-4626 clauses
Solmate violates; catalogued in `docs/erc4626/properties.md`. `T = totalAssets`,
`S = totalSupply`.
-/

@[expose] public section

namespace QEDefi.ERC4626.Solmate
open QEDefi.Math QEDefi.ERC20 QEDefi.ERC20.Token Finsupp

variable {A : Type} [DecidableEq A]

/-! ## Previews equal results (EIP-4626 `preview*` clauses, a16z `prop_preview*`) -/

theorem deposit_eq_previewDeposit {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit s c a r = some (s', n)) : s.previewDeposit a = some n :=
  (deposit_eq_some h).1

theorem mint_eq_previewMint {s s' : State A} {c r : A} {n a : ℕ}
    (h : mint s c n r = some (s', a)) : s.previewMint n = some a :=
  (mint_eq_some' h).1

theorem withdraw_eq_previewWithdraw {s s' : State A} {c r o : A} {a n : ℕ}
    (h : withdraw s c a r o = some (s', n)) : s.previewWithdraw a = some n :=
  (withdraw_eq_some h).1

theorem redeem_eq_previewRedeem {s s' : State A} {c r o : A} {n a : ℕ}
    (h : redeem s c n r o = some (s', a)) : s.previewRedeem n = some a :=
  (redeem_eq_some h).1

/-! ## Rounding directions (EIP-4626 "Security Considerations") -/

/-- `deposit` rounds the shares down: `n = ⌊a·S/T⌋`. -/
theorem deposit_rounding {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit s c a r = some (s', n)) (hS : s.totalSupply ≠ 0) :
    n * s.totalAssets ≤ a * s.totalSupply ∧ a * s.totalSupply < (n + 1) * s.totalAssets := by
  rcases convertToShares_eq_some.1 (deposit_eq_some h).1 with ⟨h0, -⟩ | ⟨-, hT, -, rfl⟩
  · exact absurd h0 hS
  · exact ⟨Nat.div_mul_le_self _ _, lt_div_add_one_mul _ _ (Nat.pos_of_ne_zero hT)⟩

/-- `mint` rounds the assets up: `a = ⌈n·T/S⌉`. -/
theorem mint_rounding {s s' : State A} {c r : A} {n a : ℕ}
    (h : mint s c n r = some (s', a)) (hS : s.totalSupply ≠ 0) :
    n * s.totalAssets ≤ a * s.totalSupply ∧ a * s.totalSupply < n * s.totalAssets + s.totalSupply := by
  rcases previewMint_eq_some.1 (mint_eq_some' h).1 with ⟨h0, -⟩ | ⟨-, -, rfl⟩
  · exact absurd h0 hS
  · exact ⟨le_ceilDiv_mul _ _ (Nat.pos_of_ne_zero hS), ceilDiv_mul_lt _ _ (Nat.pos_of_ne_zero hS)⟩

/-- `withdraw` rounds the burned shares up: `n = ⌈a·S/T⌉`. -/
theorem withdraw_rounding {s s' : State A} {c r o : A} {a n : ℕ}
    (h : withdraw s c a r o = some (s', n)) (hS : s.totalSupply ≠ 0) :
    a * s.totalSupply ≤ n * s.totalAssets ∧ n * s.totalAssets < a * s.totalSupply + s.totalAssets := by
  rcases previewWithdraw_eq_some.1 (withdraw_eq_some h).1 with ⟨h0, -⟩ | ⟨-, hT, -, rfl⟩
  · exact absurd h0 hS
  · exact ⟨le_ceilDiv_mul _ _ (Nat.pos_of_ne_zero hT), ceilDiv_mul_lt _ _ (Nat.pos_of_ne_zero hT)⟩

/-- `redeem` rounds the paid assets down: `a = ⌊n·T/S⌋`. -/
theorem redeem_rounding {s s' : State A} {c r o : A} {n a : ℕ}
    (h : redeem s c n r o = some (s', a)) (hS : s.totalSupply ≠ 0) :
    a * s.totalSupply ≤ n * s.totalAssets ∧ n * s.totalAssets < (a + 1) * s.totalSupply := by
  rcases convertToAssets_eq_some.1 (redeem_eq_some h).1 with ⟨h0, -⟩ | ⟨-, -, rfl⟩
  · exact absurd h0 hS
  · exact ⟨Nat.div_mul_le_self _ _, lt_div_add_one_mul _ _ (Nat.pos_of_ne_zero hS)⟩

/-- The exchange rate `T/S` as a rational number (assets per share). -/
def State.price (s : State A) : ℚ := (s.totalAssets : ℚ) / s.totalSupply

theorem deposit_shares_le_fair {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit s c a r = some (s', n)) (hS : s.totalSupply ≠ 0) :
    (n : ℚ) ≤ a * s.totalSupply / s.totalAssets := by
  have hT : s.totalAssets ≠ 0 := by
    rcases convertToShares_eq_some.1 (deposit_eq_some h).1 with ⟨h0, -⟩ | ⟨-, hT, -⟩
    · exact absurd h0 hS
    · exact hT
  rw [le_div_iff₀ (by positivity)]
  exact_mod_cast (deposit_rounding h hS).1

theorem redeem_assets_le_fair {s s' : State A} {c r o : A} {n a : ℕ}
    (h : redeem s c n r o = some (s', a)) (hS : s.totalSupply ≠ 0) :
    (a : ℚ) ≤ n * s.price := by
  unfold State.price
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  exact_mod_cast (redeem_rounding h hS).1

theorem mint_assets_ge_fair {s s' : State A} {c r : A} {n a : ℕ}
    (h : mint s c n r = some (s', a)) (hS : s.totalSupply ≠ 0) :
    n * s.price ≤ (a : ℚ) := by
  unfold State.price
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  exact_mod_cast (mint_rounding h hS).1

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

theorem deposit_TS {s s' : State A} {c r : A} {a n : ℕ} (h : deposit s c a r = some (s', n))
    (hc : c ≠ s.self) : s'.totalAssets = s.totalAssets + a ∧ s'.totalSupply = s.totalSupply + n := by
  obtain ⟨-, -, -, -, hself, hb, -, -, hS⟩ := deposit_eq_some h
  exact ⟨totalAssets_in hc hself hb, hS⟩

theorem mint_TS {s s' : State A} {c r : A} {n a : ℕ} (h : mint s c n r = some (s', a))
    (hc : c ≠ s.self) : s'.totalAssets = s.totalAssets + a ∧ s'.totalSupply = s.totalSupply + n := by
  obtain ⟨-, -, -, hself, hb, -, -, hS⟩ := mint_eq_some' h
  exact ⟨totalAssets_in hc hself hb, hS⟩

theorem withdraw_TS {s s' : State A} {c r o : A} {a n : ℕ} (hi : Inv s)
    (h : withdraw s c a r o = some (s', n)) (hr : r ≠ s.self) :
    s'.totalAssets = s.totalAssets - a ∧ s'.totalSupply = s.totalSupply - n ∧
      a ≤ s.totalAssets ∧ n ≤ s.totalSupply := by
  obtain ⟨-, hn, ha, hself, hb, -, -, hS⟩ := withdraw_eq_some h
  exact ⟨totalAssets_out hr hself hb, hS, ha, hn.trans (balanceOf_le_totalSupply hi.2 o)⟩

theorem redeem_TS {s s' : State A} {c r o : A} {n a : ℕ} (hi : Inv s)
    (h : redeem s c n r o = some (s', a)) (hr : r ≠ s.self) :
    s'.totalAssets = s.totalAssets - a ∧ s'.totalSupply = s.totalSupply - n ∧
      a ≤ s.totalAssets ∧ n ≤ s.totalSupply := by
  obtain ⟨-, -, hn, ha, hself, hb, -, -, hS⟩ := redeem_eq_some h
  exact ⟨totalAssets_out hr hself hb, hS, ha, hn.trans (balanceOf_le_totalSupply hi.2 o)⟩

/-! ## No dilution: the share price never decreases -/

/-- A deposit never lowers assets-per-share: `T·S' ≤ T'·S`. -/
theorem deposit_price_mono {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit s c a r = some (s', n)) (hc : c ≠ s.self) (hS : s.totalSupply ≠ 0) :
    s.totalAssets * s'.totalSupply ≤ s'.totalAssets * s.totalSupply := by
  obtain ⟨e1, e2⟩ := deposit_TS h hc
  have := (deposit_rounding h hS).1
  rw [e1, e2]; nlinarith

theorem mint_price_mono {s s' : State A} {c r : A} {n a : ℕ}
    (h : mint s c n r = some (s', a)) (hc : c ≠ s.self) (hS : s.totalSupply ≠ 0) :
    s.totalAssets * s'.totalSupply ≤ s'.totalAssets * s.totalSupply := by
  obtain ⟨e1, e2⟩ := mint_TS h hc
  have := (mint_rounding h hS).1
  rw [e1, e2]; nlinarith

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

theorem price_le_of_cross {s s' : State A} (hS : s.totalSupply ≠ 0) (hS' : s'.totalSupply ≠ 0)
    (h : s.totalAssets * s'.totalSupply ≤ s'.totalAssets * s.totalSupply) : s.price ≤ s'.price := by
  unfold State.price
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast h

theorem deposit_price_le {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit s c a r = some (s', n)) (hc : c ≠ s.self) (hS : s.totalSupply ≠ 0) :
    s.price ≤ s'.price :=
  price_le_of_cross hS (by rw [(deposit_TS h hc).2]; omega) (deposit_price_mono h hc hS)

theorem redeem_price_le {s s' : State A} {c r o : A} {n a : ℕ} (hi : Inv s)
    (h : redeem s c n r o = some (s', a)) (hS : s.totalSupply ≠ 0) (hS' : s'.totalSupply ≠ 0) :
    s.price ≤ s'.price :=
  price_le_of_cross hS hS' (redeem_price_mono hi h hS)

/-! ## Solvency -/

/-- **Solvency.** The vault can pay every holder's `convertToAssets` at once:
`Σₓ ⌊balanceOf[x]·T/S⌋ ≤ T` whenever `Inv` holds (so in every reachable state). -/
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

theorem convertToAssets_balance {s : State A} {x : A} {v : ℕ} (hS : s.totalSupply ≠ 0)
    (h : s.convertToAssets (s.shares.balanceOf x) = some v) :
    v = s.shares.balanceOf x * s.totalAssets / s.totalSupply := by
  rcases convertToAssets_eq_some.1 h with ⟨h0, -⟩ | ⟨-, -, rfl⟩
  · exact absurd h0 hS
  · rfl

/-- The shares `previewWithdraw` charges for `maxWithdraw(owner)` never exceed the owner's
balance. -/
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

/-- `redeem(deposit(a)) ≤ a` when the vault already has shares. -/
theorem rt_deposit_redeem {s s₁ s₂ : State A} {c r c' r' o : A} {a n a' : ℕ}
    (h₁ : deposit s c a r = some (s₁, n)) (h₂ : redeem s₁ c' n r' o = some (s₂, a'))
    (hc : c ≠ s.self) (hS : s.totalSupply ≠ 0) : a' ≤ a := by
  obtain ⟨eT, eS⟩ := deposit_TS h₁ hc
  have r1 := (deposit_rounding h₁ hS).1
  have r2 := (redeem_rounding h₂ (by rw [eS]; omega)).1
  rw [eT, eS] at r2
  exact rt_in_out_assets (by omega) r1 r2

/-- `redeem(n) ≤ mint(n)` (assets out ≤ assets in) when the vault already has shares. -/
theorem rt_mint_redeem {s s₁ s₂ : State A} {c r c' r' o : A} {n a a' : ℕ}
    (h₁ : mint s c n r = some (s₁, a)) (h₂ : redeem s₁ c' n r' o = some (s₂, a'))
    (hc : c ≠ s.self) (hS : s.totalSupply ≠ 0) : a' ≤ a := by
  obtain ⟨eT, eS⟩ := mint_TS h₁ hc
  have r1 := (mint_rounding h₁ hS).1
  have r2 := (redeem_rounding h₂ (by rw [eS]; omega)).1
  rw [eT, eS] at r2
  exact rt_in_out_assets (by omega) r1 r2

theorem withdraw_totalAssets_pos {s s' : State A} {c r o : A} {a n : ℕ}
    (h : withdraw s c a r o = some (s', n)) (hS : s.totalSupply ≠ 0) : s.totalAssets ≠ 0 := by
  rcases previewWithdraw_eq_some.1 (withdraw_eq_some h).1 with ⟨h0, -⟩ | ⟨-, hT, -⟩
  · exact absurd h0 hS
  · exact hT

theorem deposit_totalAssets_pos {s s' : State A} {c r : A} {a n : ℕ}
    (h : deposit s c a r = some (s', n)) (hS : s.totalSupply ≠ 0) : s.totalAssets ≠ 0 := by
  rcases convertToShares_eq_some.1 (deposit_eq_some h).1 with ⟨h0, -⟩ | ⟨-, hT, -⟩
  · exact absurd h0 hS
  · exact hT

/-- `withdraw(a)` burns at least the shares `deposit(a)` minted. -/
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

/-- `withdraw(mint(n))` burns at least `n` shares. -/
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

/-- `deposit(redeem(n)) ≤ n` while the vault keeps some shares. -/
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

/-- `deposit(a) ≤ withdraw(a)` (shares) while shares remain. -/
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

/-- `mint(n)` after `redeem(n)` costs at least what the redemption paid. -/
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

/-- `mint(withdraw(a))` costs at least `a`. -/
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

/-- Refutes `redeem(deposit(a)) ≤ a` on `S = 0 < T` (e.g. a donation to an empty vault):
the depositor redeems `T + a`. -/
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

/-- Refutes `redeem(n) ≤ mint(n)` on `S = 0 < T`: `mint(n)` costs `n`, `redeem(n)` pays
`T + n`. -/
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

/-- Refutes `deposit(redeem(n)) ≤ n` when the vault is drained: redeeming all `S` shares
and depositing back yields `T` shares, more than `S` when `T > S`. -/
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

/-- Violates EIP-4626 "`convertToShares` MUST NOT revert": after a total loss
(`T = 0 < S`) it reverts on every input (division by zero). -/
theorem convertToShares_reverts_of_totalAssets_zero {s : State A} (hS : s.totalSupply ≠ 0)
    (hT : s.totalAssets = 0) (a : ℕ) : s.convertToShares a = none := by
  simp [State.convertToShares, hS, mulDivDown, hT]

/-- Violates the EIP-4626 `maxDeposit` clause: when `T = 0 < S`, `maxDeposit = MAX` yet
every `deposit` reverts. -/
theorem deposit_reverts_of_totalAssets_zero {s : State A} (hS : s.totalSupply ≠ 0)
    (hT : s.totalAssets = 0) (c r : A) (a : ℕ) :
    s.maxDeposit r = MAX ∧ deposit s c a r = none := by
  refine ⟨rfl, ?_⟩
  simp [deposit, State.previewDeposit, convertToShares_reverts_of_totalAssets_zero hS hT]

/-- When `T = 0 < S`, `mint(n)` is free: the shares will claim any later yield or
donation. -/
theorem previewMint_zero_of_totalAssets_zero {s : State A} (hS : s.totalSupply ≠ 0)
    (hT : s.totalAssets = 0) (n : ℕ) : s.previewMint n = some 0 := by
  have hmax : 0 < MAX := by unfold MAX; omega
  simp [State.previewMint, hS, mulDivUp, hT, ceilDiv]

theorem redeem_eq_none_of_previewRedeem_zero {s : State A} {c r o : A} {n : ℕ}
    (h : s.previewRedeem n = some 0) : redeem s c n r o = none := by
  cases hr : redeem s c n r o with
  | none => rfl
  | some p =>
    obtain ⟨s', a⟩ := p
    obtain ⟨hp, hz, -⟩ := redeem_eq_some hr
    rw [h] at hp; cases hp; exact absurd rfl hz

/-- Violates the EIP-4626 `maxRedeem` clause: when the owner's balance `b` is worth less
than one asset (`b·T < S`), `redeem(maxRedeem = b)` reverts with `ZERO_ASSETS`. -/
theorem maxRedeem_reverts {s : State A} {c r o : A} (hi : Inv s) (hS : s.totalSupply ≠ 0)
    (hlt : s.shares.balanceOf o * s.totalAssets < s.totalSupply) :
    s.maxRedeem o = s.shares.balanceOf o ∧ redeem s c (s.maxRedeem o) r o = none := by
  refine ⟨rfl, redeem_eq_none_of_previewRedeem_zero ?_⟩
  have hmax : s.shares.balanceOf o * s.totalAssets ≤ MAX := hlt.le.trans hi.2.2
  rw [State.previewRedeem, convertToAssets_eq_some]
  exact Or.inr ⟨hS, hmax, (Nat.div_eq_of_lt hlt).symm⟩

end QEDefi.ERC4626.Solmate
