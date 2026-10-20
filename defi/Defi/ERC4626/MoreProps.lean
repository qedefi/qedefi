module

public import Defi.ERC4626.Inflation

/-!
# Further catalogue entries

* access control of `withdraw`/`redeem` by third parties (a16z `prop_withdraw`/`prop_redeem`
  "access control", crytic ERC4626-011/012) [A-AUTH];
* the `convertTo*` round trips (crytic `verify_convertRoundTrip`, `…2`) [RT-CONVERT];
* "no free shares / no free assets" (crytic ERC4626-014/017/020/021) [R-FREE];
* the crytic share-price-inflation property (ERC4626-033) for OpenZeppelin with a decimals
  offset [INFL-CRYTIC].
-/

@[expose] public section

namespace EvmLeanSpecs.Vault

open Token Finsupp

variable {A : Type} [DecidableEq A]

/-! ## Access control -/

namespace Solmate

theorem spendIfNotOwner_auth {t t' : Token A} {c o : A} {n : ℕ}
    (h : spendIfNotOwner t c o n = some t') (hco : c ≠ o) :
    t.allowance o c = MAX ∨ n ≤ t.allowance o c := by
  unfold spendIfNotOwner at h
  simp only [ne_eq, hco, not_false_eq_true, ↓reduceIte] at h
  unfold spend at h
  split_ifs at h with h1 h2
  · exact Or.inl h1
  · exact Or.inr (not_lt.1 h2)

/-- [A-AUTH] A third party can only `withdraw` shares it is allowed to spend: either the
owner granted an infinite approval or the burned shares are within the allowance. -/
theorem withdraw_auth {s s' : State A} {c r o : A} {a n : ℕ}
    (h : withdraw s c a r o = some (s', n)) (hco : c ≠ o) :
    s.shares.allowance o c = MAX ∨ n ≤ s.shares.allowance o c := by
  unfold withdraw at h
  obtain ⟨n', hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, -, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact spendIfNotOwner_auth hs1 hco

/-- [A-AUTH] The same for `redeem`. -/
theorem redeem_auth {s s' : State A} {c r o : A} {n a : ℕ}
    (h : redeem s c n r o = some (s', a)) (hco : c ≠ o) :
    s.shares.allowance o c = MAX ∨ n ≤ s.shares.allowance o c := by
  unfold redeem at h
  obtain ⟨sh1, hs1, -⟩ := Option.bind_eq_some_iff.1 h
  exact spendIfNotOwner_auth hs1 hco

/-! ## `convertTo*` round trips and free shares -/

/-- [RT-CONVERT] `convertToAssets(convertToShares(a)) ≤ a` (crytic `verify_convertRoundTrip`;
holds in every state, including `S = 0`). -/
theorem convert_roundtrip {s : State A} {a n a' : ℕ} (h₁ : s.convertToShares a = some n)
    (h₂ : s.convertToAssets n = some a') : a' ≤ a := by
  rcases convertToShares_eq_some.1 h₁ with ⟨hS, rfl⟩ | ⟨hS, hT, -, rfl⟩
  · rcases convertToAssets_eq_some.1 h₂ with ⟨-, rfl⟩ | ⟨h0, -⟩
    · exact le_rfl
    · exact absurd hS h0
  · rcases convertToAssets_eq_some.1 h₂ with ⟨h0, -⟩ | ⟨-, -, rfl⟩
    · exact absurd h0 hS
    · apply Nat.div_le_of_le_mul
      have := Nat.div_mul_le_self (a * s.totalSupply) s.totalAssets
      nlinarith

/-- [RT-CONVERT] `convertToShares(convertToAssets(n)) ≤ n` (crytic `verify_convertRoundTrip2`). -/
theorem convert_roundtrip2 {s : State A} {n a n' : ℕ} (h₁ : s.convertToAssets n = some a)
    (h₂ : s.convertToShares a = some n') : n' ≤ n := by
  rcases convertToAssets_eq_some.1 h₁ with ⟨hS, rfl⟩ | ⟨hS, -, rfl⟩
  · rcases convertToShares_eq_some.1 h₂ with ⟨-, rfl⟩ | ⟨h0, -⟩
    · exact le_rfl
    · exact absurd hS h0
  · rcases convertToShares_eq_some.1 h₂ with ⟨h0, -⟩ | ⟨-, hT, -, rfl⟩
    · exact absurd h0 hS
    · apply Nat.div_le_of_le_mul
      have := Nat.div_mul_le_self (n * s.totalAssets) s.totalSupply
      nlinarith

/-- [R-FREE] `withdraw` of a positive amount always burns a positive number of shares
(crytic ERC4626-017/021). -/
theorem previewWithdraw_pos {s : State A} {a n : ℕ} (h : s.previewWithdraw a = some n)
    (ha : 0 < a) : 0 < n := by
  rcases previewWithdraw_eq_some.1 h with ⟨-, rfl⟩ | ⟨hS, hT, -, rfl⟩
  · exact ha
  · rw [lt_ceilDiv_iff _ _ _ (Nat.pos_of_ne_zero hT), Nat.zero_mul]
    exact Nat.mul_pos ha (Nat.pos_of_ne_zero hS)

/-- [EIP-MAX-NOREVERT] **Refuted for Solmate.** EIP-4626 says `maxWithdraw` MUST NOT revert,
but Solmate computes it as `convertToAssets(balanceOf[owner])`, whose `mulDivDown` reverts
when `shares · totalAssets` exceeds `2²⁵⁶ - 1`. Found independently by the a16z suite
against the compiled contract (`contracts/README.md`). -/
theorem maxWithdraw_reverts_of_overflow (s : State A) (owner : A) (hS : s.totalSupply ≠ 0)
    (hT : s.totalAssets ≠ 0) (h : MAX / s.totalAssets < s.shares.balanceOf owner) :
    s.maxWithdraw owner = none := by
  simp [State.maxWithdraw, State.convertToAssets, hS, mulDivDown, hT, h]

end Solmate

namespace Oz

variable [Zero A] {δ : ℕ}

theorem spendIfNotOwner_auth {t t' : Token A} {c o : A} {n : ℕ}
    (h : spendIfNotOwner t c o n = some t') (hco : c ≠ o) :
    MAX ≤ t.allowance o c ∨ n ≤ t.allowance o c := by
  unfold spendIfNotOwner at h
  simp only [ne_eq, hco, not_false_eq_true, ↓reduceIte] at h
  unfold ozSpend at h
  split_ifs at h with h1 h2
  · exact Or.inr (not_lt.1 h2)
  · exact Or.inl (not_lt.1 h1)

/-- [A-AUTH] A third party can only `withdraw` within its allowance (or with an infinite
one). -/
theorem withdraw_auth {s s' : State A} {c r o : A} {a n : ℕ}
    (h : withdraw δ s c a r o = some (s', n)) (hco : c ≠ o) :
    MAX ≤ s.shares.allowance o c ∨ n ≤ s.shares.allowance o c := by
  unfold withdraw at h
  obtain ⟨m, -, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h
  obtain ⟨n', -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh1, hs1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh2, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨asset, -, h⟩ := Option.map_eq_some_iff.1 h
  cases h
  exact spendIfNotOwner_auth hs1 hco

/-- [A-AUTH] The same for `redeem`. -/
theorem redeem_auth {s s' : State A} {c r o : A} {n a : ℕ}
    (h : redeem δ s c n r o = some (s', a)) (hco : c ≠ o) :
    MAX ≤ s.shares.allowance o c ∨ n ≤ s.shares.allowance o c := by
  unfold redeem at h
  split_ifs at h
  obtain ⟨a', -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sh1, hs1, -⟩ := Option.bind_eq_some_iff.1 h
  exact spendIfNotOwner_auth hs1 hco

/-- [RT-CONVERT] `convertToAssets(convertToShares(a)) ≤ a`. -/
theorem convert_roundtrip {s : State A} {a n a' : ℕ} (h₁ : s.convertToShares δ a = some n)
    (h₂ : s.convertToAssets δ n = some a') : a' ≤ a := by
  obtain ⟨-, -, -, rfl⟩ := toShares_eq_some.1 h₁
  obtain ⟨-, -, -, rfl⟩ := toAssets_eq_some.1 h₂
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply Nat.div_le_of_le_mul
  have := Nat.div_mul_le_self (a * s.vS δ) s.vT
  nlinarith

/-- [RT-CONVERT] `convertToShares(convertToAssets(n)) ≤ n`. -/
theorem convert_roundtrip2 {s : State A} {n a n' : ℕ} (h₁ : s.convertToAssets δ n = some a)
    (h₂ : s.convertToShares δ a = some n') : n' ≤ n := by
  obtain ⟨-, -, -, rfl⟩ := toAssets_eq_some.1 h₁
  obtain ⟨-, -, -, rfl⟩ := toShares_eq_some.1 h₂
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply Nat.div_le_of_le_mul
  have := Nat.div_mul_le_self (n * s.vT) (s.vS δ)
  nlinarith

/-- [R-FREE] `previewMint(n) > 0` for `n > 0`: shares are never free (crytic ERC4626-014/020),
in every state — contrast `Solmate.previewMint_zero_of_totalAssets_zero`. -/
theorem previewMint_pos {s : State A} {n a : ℕ} (h : s.previewMint δ n = some a) (hn : 0 < n) :
    0 < a := by
  obtain ⟨-, -, -, rfl⟩ := toAssets_eq_some.1 h
  simp only [↓reduceIte]
  rw [lt_ceilDiv_iff _ _ _ (State.vS_pos s), Nat.zero_mul]
  exact Nat.mul_pos hn (State.vT_pos s)

/-- [R-FREE] `previewWithdraw(a) > 0` for `a > 0` (crytic ERC4626-017/021). -/
theorem previewWithdraw_pos {s : State A} {a n : ℕ} (h : s.previewWithdraw δ a = some n)
    (ha : 0 < a) : 0 < n := by
  obtain ⟨-, -, -, rfl⟩ := toShares_eq_some.1 h
  simp only [↓reduceIte]
  rw [lt_ceilDiv_iff _ _ _ (State.vT_pos s), Nat.zero_mul]
  exact Nat.mul_pos ha (State.vS_pos s)

/-- [INFL-CRYTIC] crytic ERC4626-033 in its own setting: the attacker deposited `1` asset into
a fresh vault (so `S = 10^δ`, `T = 1`) and donates `D ≥ 1`; a victim depositing `a ≥ D + 1`
loses less than `(3/4)·a/10^δ`, measured at the vault's exchange rate. With `δ ≥ 3` this is
below crytic's 0.1 % threshold. -/
theorem crytic_inflation_bound {s s₁ s₂ : State A} {att v r : A} {D a n : ℕ}
    (hS : s.totalSupply = 10 ^ δ) (hT : s.totalAssets = 1) (hD : 1 ≤ D) (ha : D + 1 ≤ a)
    (hatt : att ≠ s.self) (hvs : v ≠ s.self)
    (hd : step δ s (.assetTransfer att s.self D) = some s₁)
    (h : deposit δ s₁ v a r = some (s₂, n)) :
    (a : ℚ) - s₂.value δ n < 3 / 4 * a / 10 ^ δ := by
  obtain ⟨-, -, hL, -, -⟩ := oz_donation_attack (b := 0) (Nat.zero_le _) hatt hvs hd h
  obtain ⟨dT, dS, -⟩ := donate_eq hd hatt
  have hp : s₁.price δ = ((D : ℚ) + 2) / (2 * 10 ^ δ) := by
    simp only [State.price, State.vT, State.vS, dT, dS, hS, hT]; push_cast; ring
  rw [hp] at hL
  refine lt_of_lt_of_le hL ?_
  have hk : (0 : ℚ) < 10 ^ δ := by positivity
  rw [div_le_div_iff₀ (by positivity) hk]
  have : (D : ℚ) + 1 ≤ a := by exact_mod_cast ha
  have : (1 : ℚ) ≤ D := by exact_mod_cast hD
  nlinarith

end Oz

end EvmLeanSpecs.Vault
