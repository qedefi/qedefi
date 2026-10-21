module

public import QEDefi.ERC4626.SolmateProps
public import QEDefi.ERC4626.OzProps
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The algebra of the donation ("inflation") attack

One computation over `ℚ` for both vaults, with virtual totals `T + vT`, `S + vS` (Solmate
`0, 0`; OpenZeppelin `1, 10^δ`). An attacker holding `b` shares donates `D`; a victim then
deposits `a` for `n` shares. At the vault's rate, the victim's loss `L` and the attacker's
profit `P` satisfy `P·(S+vS) = b·L − D·(S − b + vS)` and `0 ≤ L <` one share.
-/

section

@[expose] public section

namespace QEDefi.ERC4626.Inflation
open QEDefi.Math QEDefi.ERC20

variable {T S vT vS D a n b : ℚ}

theorem profit_mul (h0 : S + vS ≠ 0) (h2 : S + n + vS ≠ 0) :
    (b * ((T + D + a + vT) / (S + n + vS)) - b * ((T + vT) / (S + vS)) - D) * (S + vS) =
      b * (a - n * ((T + D + a + vT) / (S + n + vS))) - D * (S - b + vS) := by
  field_simp
  ring

theorem loss_mul (h2 : S + n + vS ≠ 0) :
    (a - n * ((T + D + a + vT) / (S + n + vS))) * (S + n + vS) =
      a * (S + vS) - n * (T + D + vT) := by
  field_simp
  ring

theorem loss_bounds (h0 : 0 < S + vS) (hn : 0 ≤ n)
    (hr1 : n * (T + D + vT) ≤ a * (S + vS)) (hr2 : a * (S + vS) < (n + 1) * (T + D + vT)) :
    0 ≤ a - n * ((T + D + a + vT) / (S + n + vS)) ∧
      a - n * ((T + D + a + vT) / (S + n + vS)) < (T + D + vT) / (S + vS) := by
  have h2 : 0 < S + n + vS := by linarith
  have e := loss_mul (T := T) (D := D) (a := a) (vT := vT) h2.ne'
  constructor
  · by_contra hc
    push Not at hc
    have : (a - n * ((T + D + a + vT) / (S + n + vS))) * (S + n + vS) < 0 :=
      mul_neg_of_neg_of_pos hc h2
    linarith
  · rw [lt_div_iff₀ h0]
    set L := a - n * ((T + D + a + vT) / (S + n + vS))
    have hL : 0 ≤ L := by
      by_contra hc
      push Not at hc
      have : L * (S + n + vS) < 0 := mul_neg_of_neg_of_pos hc h2
      linarith
    nlinarith

theorem oz_profit_bound {k : ℚ} (hk : 1 ≤ k) (hb0 : 0 ≤ b) (hbS : b ≤ S) (hn : 0 ≤ n)
    (hD : 0 ≤ D)
    (hr1 : n * (T + D + 1) ≤ a * (S + k)) (hr2 : a * (S + k) < (n + 1) * (T + D + 1)) :
    (b * ((T + D + a + 1) / (S + n + k)) - b * ((T + 1) / (S + k)) - D) * (S + k) ≤
      T + 1 - (k - 1) * D := by
  have hS : 0 < S + k := by linarith
  have h2 : 0 < S + n + k := by linarith
  rw [profit_mul hS.ne' h2.ne']
  obtain ⟨hL0, hL1⟩ := loss_bounds (T := T) (D := D) (a := a) (vT := 1) hS hn hr1 hr2
  set L := a - n * ((T + D + a + 1) / (S + n + k))
  have h3 : b * L ≤ T + D + 1 := by
    have : L * (S + k) < T + D + 1 := by rwa [lt_div_iff₀ hS] at hL1
    nlinarith
  nlinarith

theorem oz_cost_bound {k : ℚ} (hk : 1 ≤ k) (hn : 0 ≤ n) (hS0 : 0 ≤ S)
    (hr1 : n * (T + D + 1) ≤ a * (S + k)) (hr2 : a * (S + k) < (n + 1) * (T + D + 1)) :
    k * (a - n * ((T + D + a + 1) / (S + n + k))) - k * ((T + 1) / (S + k)) < D * k / (S + k) := by
  have hS : 0 < S + k := by linarith
  obtain ⟨-, hL1⟩ := loss_bounds (T := T) (D := D) (a := a) (vT := 1) hS hn hr1 hr2
  set L := a - n * ((T + D + a + 1) / (S + n + k))
  have : L * (S + k) < T + D + 1 := by rwa [lt_div_iff₀ hS] at hL1
  rw [← sub_pos]
  have e : D * k / (S + k) - (k * L - k * ((T + 1) / (S + k))) =
      k * ((T + D + 1) - L * (S + k)) / (S + k) := by
    field_simp; ring
  rw [e]
  apply div_pos _ hS
  apply mul_pos (by linarith); linarith

theorem solmate_profit_eq_loss (hS : 0 < S) (hn : 0 ≤ n) :
    (S * ((T + D + a) / (S + n)) - S * (T / S) - D) =
      a - n * ((T + D + a) / (S + n)) := by
  have h2 : S + n ≠ 0 := by positivity
  field_simp
  ring

end QEDefi.ERC4626.Inflation
end

end

section

/-!
## The donation ("inflation") attack on both vaults

An attacker donates `D` assets to the vault so a victim's `deposit(a)` rounds down. On
Solmate this is free when the attacker holds every share; OpenZeppelin's `k = 10^δ` virtual
shares make inflicting a loss `L` cost about `k·L`. Value is measured at the vault's `price`.
-/

@[expose] public section

namespace QEDefi.ERC4626
open QEDefi.Math QEDefi.ERC20 QEDefi.ERC20.Token Finsupp

variable {A : Type} [DecidableEq A]

namespace Solmate

/-- What `x` shares are worth at the current exchange rate, `x·T/S`. -/
def State.value (s : State A) (x : ℕ) : ℚ := x * s.price

theorem donate_eq {s s₁ : State A} {att : A} {D : ℕ}
    (h : step s (.assetTransfer att s.self D) = some s₁) (hatt : att ≠ s.self) :
    s₁.totalAssets = s.totalAssets + D ∧ s₁.totalSupply = s.totalSupply ∧ s₁.self = s.self ∧
      s₁.shares = s.shares := by
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨-, rfl⟩ := transfer_eq_some.1 ht
  exact ⟨move_apply_dst _ _ hatt, rfl, rfl, rfl⟩

/-- On an empty vault the attacker deposits `1` and donates `D`: it holds the single share
of a vault with `D + 1` assets. -/
theorem solmate_attack_setup {s₀ s₁ s₂ : State A} {att : A} {D n : ℕ} (hi : Inv s₀)
    (hS : s₀.totalSupply = 0) (hT : s₀.totalAssets = 0) (hatt : att ≠ s₀.self)
    (h₁ : deposit s₀ att 1 att = some (s₁, n))
    (h₂ : step s₁ (.assetTransfer att s₁.self D) = some s₂) :
    n = 1 ∧ s₂.totalSupply = 1 ∧ s₂.totalAssets = D + 1 ∧ s₂.shares.balanceOf att = 1 := by
  have hn : n = 1 := by
    rcases convertToShares_eq_some.1 (deposit_eq_some h₁).1 with ⟨-, rfl⟩ | ⟨h0, -⟩
    · rfl
    · exact absurd hS h0
  subst hn
  obtain ⟨eT, eS⟩ := deposit_TS h₁ hatt
  obtain ⟨-, -, -, -, hself, -, -, hb, -⟩ := deposit_eq_some h₁
  obtain ⟨dT, dS, -, dsh⟩ := donate_eq h₂ (by rw [hself]; exact hatt)
  have h0 : s₀.shares.balanceOf att = 0 := by
    have := balanceOf_le_totalSupply hi.2 att
    unfold State.totalSupply at hS; omega
  refine ⟨rfl, by rw [dS, eS, hS], by rw [dT, eT, hT]; ring, ?_⟩
  rw [dsh, hb, add_single_apply, h0]; simp

/-- Then every victim `deposit(a)` with `a ≤ D` reverts (`ZERO_SHARES`). -/
theorem solmate_attack_victim_reverts {s : State A} {v r : A} {D a : ℕ} (hi : Inv s)
    (hS : s.totalSupply = 1) (hT : s.totalAssets = D + 1) (ha : a ≤ D) :
    s.previewDeposit a = some 0 ∧ deposit s v a r = none := by
  have hp : s.previewDeposit a = some 0 := by
    have hmax : s.totalAssets ≤ MAX :=
      (balanceOf_le_totalSupply hi.1 s.self).trans hi.1.2
    rw [State.previewDeposit, convertToShares_eq_some]
    refine Or.inr ⟨by omega, by omega, by rw [hS]; omega, ?_⟩
    rw [hS, hT, Nat.mul_one, Nat.div_eq_of_lt (by omega)]
  refine ⟨hp, ?_⟩
  cases hd : deposit s v a r with
  | none => rfl
  | some p =>
    obtain ⟨s', n⟩ := p
    obtain ⟨hp', hn, -⟩ := deposit_eq_some hd
    rw [hp] at hp'; cases hp'; exact absurd rfl hn

/-- Then a victim `deposit(a)` with `D < a ≤ 2D + 1` mints one share worth `⌊(a+D+1)/2⌋`:
the victim loses `⌊(a−D)/2⌋` (up to a quarter) and the attacker gains `⌊(a−D−1)/2⌋`. -/
theorem solmate_attack_victim_one_share {s s' : State A} {v r : A} {D a n : ℕ} (hi : Inv s)
    (hS : s.totalSupply = 1) (hT : s.totalAssets = D + 1) (ha₁ : D < a) (ha₂ : a ≤ 2 * D + 1)
    (hvs : v ≠ s.self) (h : deposit s v a r = some (s', n)) :
    n = 1 ∧ s'.totalSupply = 2 ∧ s'.totalAssets = a + D + 1 ∧
      s'.convertToAssets 1 = Option.some ((a + D + 1) / 2) ∧
      a - (a + D + 1) / 2 = (a - D) / 2 ∧ (a + D + 1) / 2 = D + 1 + (a - D - 1) / 2 := by
  have hn : n = 1 := by
    rcases convertToShares_eq_some.1 (deposit_eq_some h).1 with ⟨h0, -⟩ | ⟨-, -, -, rfl⟩
    · omega
    · rw [hS, hT, Nat.mul_one]
      apply Nat.div_eq_of_lt_le <;> omega
  subst hn
  obtain ⟨eT, eS⟩ := deposit_TS h hvs
  have hi' := Inv_deposit hi h
  have hmax : s'.totalAssets ≤ MAX := (balanceOf_le_totalSupply hi'.1 s'.self).trans hi'.1.2
  have e2 : s'.totalSupply = 2 := by rw [eS, hS]
  have e3 : s'.totalAssets = a + D + 1 := by rw [eT, hT]; ring
  refine ⟨rfl, e2, e3, ?_, by omega, by omega⟩
  rw [convertToAssets_eq_some]
  exact Or.inr ⟨by omega, by rw [e3] at hmax ⊢; omega, by rw [e2, e3, Nat.one_mul]⟩

/-- From any state with shares, an attacker holding `b` shares donates `D` and a victim
deposits `a` for `n` shares: profit `P = value₂(b) − value₀(b) − D` and loss
`L = a − value₂(n)` satisfy `P·S = b·L − D·(S − b)` and `0 ≤ L < price₁`. -/
theorem solmate_donation_attack {s s₁ s₂ : State A} {att v r : A} {D a n : ℕ} (b : ℕ)
    (hS : s.totalSupply ≠ 0) (hatt : att ≠ s.self) (hvs : v ≠ s.self)
    (hd : step s (.assetTransfer att s.self D) = some s₁)
    (h : deposit s₁ v a r = some (s₂, n)) :
    (s₂.value b - s.value b - D) * s.totalSupply =
        b * (a - s₂.value n) - D * (s.totalSupply - b) ∧
      0 ≤ (a : ℚ) - s₂.value n ∧ (a : ℚ) - s₂.value n < s₁.price := by
  obtain ⟨dT, dS, dself, -⟩ := donate_eq hd hatt
  have hS₁ : s₁.totalSupply ≠ 0 := by rw [dS]; exact hS
  obtain ⟨eT, eS⟩ := deposit_TS h (by rw [dself]; exact hvs)
  obtain ⟨r1, r2⟩ := deposit_rounding h hS₁
  rw [dT, dS] at r1 r2
  rw [dS] at eS
  rw [dT] at eT
  have hSq : (0 : ℚ) < s.totalSupply := by exact_mod_cast Nat.pos_of_ne_zero hS
  have hr1 : (n : ℚ) * (s.totalAssets + D + 0) ≤ a * (s.totalSupply + 0) := by
    simp only [add_zero]; exact_mod_cast r1
  have hr2 : (a : ℚ) * (s.totalSupply + 0) < (n + 1) * (s.totalAssets + D + 0) := by
    simp only [add_zero]; exact_mod_cast r2
  have hb := Inflation.loss_bounds (S := (s.totalSupply : ℚ)) (vS := 0) (by simpa using hSq)
    (Nat.cast_nonneg n) hr1 hr2
  have hp := Inflation.profit_mul (T := (s.totalAssets : ℚ)) (D := D) (a := a) (vT := 0)
    (b := b) (S := (s.totalSupply : ℚ)) (vS := 0) (n := n) (by simpa using hSq.ne')
    (by simp only [add_zero]; positivity)
  simp only [add_zero] at hb hp
  have v2 : ∀ x : ℕ, s₂.value x = x * ((s.totalAssets + D + a : ℚ) / (s.totalSupply + n)) := by
    intro x; simp only [State.value, State.price, eT, eS]; push_cast; ring
  have v0 : ∀ x : ℕ, s.value x = x * ((s.totalAssets : ℚ) / s.totalSupply) := fun _ => rfl
  have p1 : s₁.price = (s.totalAssets + D : ℚ) / s.totalSupply := by
    simp only [State.price, dT, dS]; push_cast; ring
  rw [v2, v2, v0, p1]
  exact ⟨hp, hb.1, hb.2⟩

/-- If the attacker holds every share, its profit is exactly the victim's loss (`P = L`). -/
theorem solmate_donation_attack_all_shares {s s₁ s₂ : State A} {att v r : A} {D a n : ℕ}
    (hS : s.totalSupply ≠ 0) (hatt : att ≠ s.self) (hvs : v ≠ s.self)
    (hd : step s (.assetTransfer att s.self D) = some s₁)
    (h : deposit s₁ v a r = some (s₂, n)) :
    s₂.value s.totalSupply - s.value s.totalSupply - D = a - s₂.value n := by
  have := (solmate_donation_attack s.totalSupply hS hatt hvs hd h).1
  have hSq : (s.totalSupply : ℚ) ≠ 0 := by exact_mod_cast hS
  simp only [sub_self, mul_zero, sub_zero] at this
  exact mul_right_cancel₀ hSq (by rw [this, mul_comm])

end Solmate

namespace Oz

variable [Zero A] {δ : ℕ}

/-- What `x` shares are worth at the current virtual exchange rate, `x·T̂/Ŝ`. -/
def State.value (δ : ℕ) (s : State A) (x : ℕ) : ℚ := x * s.price δ

theorem donate_eq {s s₁ : State A} {att : A} {D : ℕ}
    (h : step δ s (.assetTransfer att s.self D) = some s₁) (hatt : att ≠ s.self) :
    s₁.totalAssets = s.totalAssets + D ∧ s₁.totalSupply = s.totalSupply ∧ s₁.self = s.self := by
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨-, -, -, hb, -⟩ := ozTransfer_eq_some ht
  refine ⟨?_, rfl, rfl⟩
  simp only [State.totalAssets, hb, move_apply_dst _ _ hatt]

/-- The attack on OpenZeppelin (`k = 10^δ`, `Ŝ = S + k`, attacker holds `b ≤ S`), with `P`, `L`
as for Solmate: `P·Ŝ = b·L − D·(Ŝ − b)`; `0 ≤ L < price₁`; `P·Ŝ ≤ T + 1 − (k − 1)·D` (less
than one pre-attack share, a loss once `(k−1)·D > T + 1`); and `k·L − k·price₀ < D·k/Ŝ`
(the donation lost to virtual shares exceeds about `k·L`). -/
theorem oz_donation_attack {s s₁ s₂ : State A} {att v r : A} {D a n b : ℕ}
    (hbS : b ≤ s.totalSupply) (hatt : att ≠ s.self) (hvs : v ≠ s.self)
    (hd : step δ s (.assetTransfer att s.self D) = some s₁)
    (h : deposit δ s₁ v a r = some (s₂, n)) :
    (s₂.value δ b - s.value δ b - D) * s.vS δ = b * (a - s₂.value δ n) - D * (s.vS δ - b) ∧
      0 ≤ (a : ℚ) - s₂.value δ n ∧ (a : ℚ) - s₂.value δ n < s₁.price δ ∧
      (s₂.value δ b - s.value δ b - D) * s.vS δ ≤ s.totalAssets + 1 - (10 ^ δ - 1) * D ∧
      10 ^ δ * ((a : ℚ) - s₂.value δ n) - 10 ^ δ * s.price δ < D * 10 ^ δ / s.vS δ := by
  obtain ⟨dT, dS, dself⟩ := donate_eq hd hatt
  obtain ⟨eT, eS⟩ := deposit_vTS h (by rw [dself]; exact hvs)
  obtain ⟨r1, r2⟩ := deposit_rounding h
  have vT1 : s₁.vT = s.totalAssets + D + 1 := by simp only [State.vT, dT]
  have vS1 : s₁.vS δ = s.totalSupply + 10 ^ δ := by simp only [State.vS, dS]
  rw [vT1, vS1] at r1 r2
  rw [vT1] at eT; rw [vS1] at eS
  set S : ℚ := (s.totalSupply : ℚ)
  set T : ℚ := (s.totalAssets : ℚ)
  set k : ℚ := ((10 ^ δ : ℕ) : ℚ)
  have hk : (1 : ℚ) ≤ k := by simp only [k]; exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  have hS0 : (0 : ℚ) ≤ S := Nat.cast_nonneg _
  have hSk : 0 < S + k := by linarith
  have hr1 : (n : ℚ) * (T + D + 1) ≤ a * (S + k) := by
    simp only [S, T, k]; exact_mod_cast r1
  have hr2 : (a : ℚ) * (S + k) < (n + 1) * (T + D + 1) := by
    simp only [S, T, k]; exact_mod_cast r2
  have hbq : (b : ℚ) ≤ S := by simp only [S]; exact_mod_cast hbS
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have hp := Inflation.profit_mul (T := T) (D := D) (a := a) (vT := 1) (b := b) (S := S) (vS := k)
    (n := n) hSk.ne' (by positivity)
  have hb := Inflation.loss_bounds (T := T) (D := D) (a := a) (vT := 1) hSk hn hr1 hr2
  have hpb := Inflation.oz_profit_bound (b := b) hk (Nat.cast_nonneg b) hbq hn (Nat.cast_nonneg D) hr1 hr2
  have hcb := Inflation.oz_cost_bound (T := T) (D := D) (a := a) hk hn hS0 hr1 hr2
  have vS0 : (s.vS δ : ℚ) = S + k := by simp only [State.vS, S, k]; push_cast; ring
  have v2 : ∀ x : ℕ, s₂.value δ x = x * ((T + D + a + 1) / (S + n + k)) := by
    intro x
    simp only [State.value, State.price, eT, eS, T, S, k]; push_cast; ring
  have v0 : ∀ x : ℕ, s.value δ x = x * ((T + 1) / (S + k)) := by
    intro x; simp only [State.value, State.price, State.vT, State.vS, T, S, k]; push_cast; ring
  have p1 : s₁.price δ = (T + D + 1) / (S + k) := by
    simp only [State.price, vT1, vS1, T, S, k]; push_cast; ring
  have p0 : s.price δ = (T + 1) / (S + k) := by
    simp only [State.price, State.vT, State.vS, T, S, k]; push_cast; ring
  have ek : ((10 : ℚ) ^ δ) = k := by simp [k]
  rw [v2, v2, v0, p1, p0, vS0, ek]
  refine ⟨by rw [hp]; ring, hb.1, hb.2, hpb, hcb⟩

end Oz

end QEDefi.ERC4626
end

end
