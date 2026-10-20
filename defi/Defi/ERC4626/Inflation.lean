module

public import Mathlib
public import Defi.ERC4626.SolmateProps
public import Defi.ERC4626.OzProps

/-!
# The algebra of the donation ("inflation") attack

One computation covers both vaults. Before the attack the vault has `T` assets and `S`
shares; the conversions use *virtual* totals `T + vT` and `S + vS` (Solmate: `vT = vS = 0`;
OpenZeppelin: `vT = 1`, `vS = 10^δ`). The attacker holds `b` of the `S` shares, donates `D`
assets (a plain asset transfer to the vault), then the victim deposits `a` assets and
receives `n = ⌊a·(S+vS)/(T+D+vT)⌋` shares.

Value is measured at the vault's own exchange rate, `value(x) = x·(T+vT)/(S+vS)`:

* the victim's loss `L = a − value₂(n)`;
* the attacker's profit `P = value₂(b) − value₀(b) − D`.

Then (`profit_mul`) `P·(S+vS) = b·L − D·(S − b + vS)`: the attacker gets a `b/(S+vS)` share
of whatever the victim loses, and loses the part `D·(S−b+vS)/(S+vS)` of the donation that
accrues to the other (real and virtual) shares. And (`loss_mul`)
`L·(S+n+vS) = a·(S+vS) − n·(T+D+vT)`, i.e. `0 ≤ L <` one share at the post-donation price.
-/

section

@[expose] public section

namespace Defi.ERC4626.Inflation
open Defi.Math Defi.ERC20

variable {T S vT vS D a n b : ℚ}

/-- The profit identity: `P·(S+vS) = b·L − D·(S − b + vS)`. -/
theorem profit_mul (h0 : S + vS ≠ 0) (h2 : S + n + vS ≠ 0) :
    (b * ((T + D + a + vT) / (S + n + vS)) - b * ((T + vT) / (S + vS)) - D) * (S + vS) =
      b * (a - n * ((T + D + a + vT) / (S + n + vS))) - D * (S - b + vS) := by
  field_simp
  ring

/-- The loss identity: `L·(S+n+vS) = a·(S+vS) − n·(T+D+vT)`. -/
theorem loss_mul (h2 : S + n + vS ≠ 0) :
    (a - n * ((T + D + a + vT) / (S + n + vS))) * (S + n + vS) =
      a * (S + vS) - n * (T + D + vT) := by
  field_simp
  ring

/-- With floor rounding (`n·(T+D+vT) ≤ a·(S+vS) < (n+1)·(T+D+vT)`) the victim's loss is
non-negative and below one share at the post-donation price `(T+D+vT)/(S+vS)`. -/
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
    -- L·(S+vS) ≤ L·(S+n+vS) = a(S+vS) − n(T+D+vT) < T+D+vT
    set L := a - n * ((T + D + a + vT) / (S + n + vS))
    have hL : 0 ≤ L := by
      by_contra hc
      push Not at hc
      have : L * (S + n + vS) < 0 := mul_neg_of_neg_of_pos hc h2
      linarith
    nlinarith

/-- **OpenZeppelin bound.** With `vS = k ≥ 1`, `vT = 1` and the attacker holding `b ≤ S`
shares, the attacker's profit satisfies `P·(S+k) ≤ T + 1 − (k−1)·D`: below the value of one
pre-attack share, and negative as soon as `(k−1)·D > T + 1`. -/
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
  -- b·L ≤ b·(T+D+1)/(S+k) ≤ T+D+1
  have h3 : b * L ≤ T + D + 1 := by
    have : L * (S + k) < T + D + 1 := by rwa [lt_div_iff₀ hS] at hL1
    nlinarith
  nlinarith

/-- **OpenZeppelin cost.** To inflict a loss `L` on the victim the attacker must donate
`D > L·(S+k) − (T+1)`; the share of the donation captured by the `k` virtual shares,
`D·k/(S+k)`, then exceeds `k·L − k·(T+1)/(S+k)`. In an empty vault (`(T+1)/(S+k) = 1/k`)
the attacker pays more than `k·L − 1` to make the victim lose `L`. -/
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

/-- **Solmate.** With no virtual offsets and the attacker holding every share (`b = S`), the
attacker's profit is exactly the victim's loss: the donation is fully recovered. -/
theorem solmate_profit_eq_loss (hS : 0 < S) (hn : 0 ≤ n) :
    (S * ((T + D + a) / (S + n)) - S * (T / S) - D) =
      a - n * ((T + D + a) / (S + n)) := by
  have h2 : S + n ≠ 0 := by positivity
  field_simp
  ring

end Defi.ERC4626.Inflation
end

end

section

/-!
## The donation ("inflation") attack on both vaults

The attack: an attacker holding shares transfers `D` assets directly to the vault
(`asset.transfer(vault, D)`), raising the price per share, so that a victim's subsequent
`deposit(a)` rounds down to few or zero shares; the attacker's shares absorb the
difference.

**Solmate** (`solmate_*`):

* `solmate_attack_setup` — on an empty vault the attacker `deposit(1)`s and donates `D`,
  reaching `S = 1`, `T = D + 1` with the single share in hand;
* `solmate_attack_victim_reverts` — every victim deposit `a ≤ D` then has
  `previewDeposit(a) = 0`, and `deposit` reverts (`ZERO_SHARES`): denial of service;
* `solmate_attack_victim_one_share` — every victim deposit `D < a ≤ 2D+1` mints exactly one
  share; the victim's shares are worth `⌊(a+D+1)/2⌋` and the victim loses `⌊(a−D)/2⌋`
  (≈ 25 % of the deposit at `a = 2D+1`); the attacker's share is worth the same
  `⌊(a+D+1)/2⌋ ≥ D + 1 + ⌊(a−D−1)/2⌋`, i.e. at least its cost plus the victim's loss
  rounded down;
* `solmate_donation_attack` — in general (any `S > 0`), the attacker's profit is
  `(b·L − D·(S−b))/S` and equals the victim's loss `L` exactly when the attacker holds every
  share: donating costs nothing.

**OpenZeppelin** with `k = 10^δ` virtual shares (`oz_donation_attack`): the profit is
`(b·L − D·(S−b+k))/(S+k)`, bounded by `(T + 1 − (k−1)·D)/(S+k)` (less than one
pre-attack share, negative once `(k−1)·D > T+1`), and the part of the donation lost to the
virtual shares exceeds `k·L − k·(T+1)/(S+k)`: making the victim lose `L` costs about
`k·L`.

Value is measured at the vault's exchange rate (`price`), i.e. before the final
redemption's own rounding.
-/

@[expose] public section

namespace Defi.ERC4626
open Defi.Math Defi.ERC20

open Defi.ERC20.Token Finsupp

variable {A : Type} [DecidableEq A]

namespace Solmate
open Defi.Math Defi.ERC20

/-- What `x` shares are worth at the current exchange rate, `x·T/S`. -/
def State.value (s : State A) (x : ℕ) : ℚ := x * s.price

/-- A donation (`asset.transfer(vault, D)` by `att ≠ vault`) raises `T` by `D` and leaves
the shares untouched. -/
theorem donate_eq {s s₁ : State A} {att : A} {D : ℕ}
    (h : step s (.assetTransfer att s.self D) = some s₁) (hatt : att ≠ s.self) :
    s₁.totalAssets = s.totalAssets + D ∧ s₁.totalSupply = s.totalSupply ∧ s₁.self = s.self ∧
      s₁.shares = s.shares := by
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨-, rfl⟩ := transfer_eq_some.1 ht
  exact ⟨move_apply_dst _ _ hatt, rfl, rfl, rfl⟩

/-- **Setup of the attack on an empty vault.** The attacker deposits one asset and donates
`D`: the vault then has one share, held by the attacker, and `D + 1` assets. -/
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

/-- **Victim deposits up to `D` revert.** With `S = 1` and `T = D + 1`, `previewDeposit(a)`
is `0` for every `a ≤ D` and `deposit(a)` reverts (`ZERO_SHARES`). -/
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

/-- **Victim deposits between `D+1` and `2D+1` lose up to a quarter.** With `S = 1` and
`T = D + 1` (attacker holds the one share), a victim `deposit(a)` with `D < a ≤ 2D + 1`
mints exactly one share; afterwards each of the two shares converts to `⌊(a+D+1)/2⌋`
assets, so the victim's loss is `a − ⌊(a+D+1)/2⌋ = ⌊(a−D)/2⌋` and the attacker's share,
which cost `D + 1`, is worth `D + 1 + ⌊(a−D−1)/2⌋`. -/
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

/-- **The general Solmate attack.** From any state with shares, a donation of `D` by an
attacker holding `b` shares followed by a victim `deposit(a)` minting `n` shares gives

* attacker's profit `P = value₂(b) − value₀(b) − D` with `P·S = b·L − D·(S − b)`,
* victim's loss `L = a − value₂(n)` with `0 ≤ L < price₁` (less than one share at the
  post-donation price). -/
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

/-- **Solmate: the attacker gains exactly what the victim loses.** If the attacker holds
every share, `P = L`. -/
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
open Defi.Math Defi.ERC20

variable [Zero A] {δ : ℕ}

/-- What `x` shares are worth at the current virtual exchange rate, `x·T̂/Ŝ`. -/
def State.value (δ : ℕ) (s : State A) (x : ℕ) : ℚ := x * s.price δ

/-- A donation raises `T` by `D` and leaves the shares untouched. -/
theorem donate_eq {s s₁ : State A} {att : A} {D : ℕ}
    (h : step δ s (.assetTransfer att s.self D) = some s₁) (hatt : att ≠ s.self) :
    s₁.totalAssets = s.totalAssets + D ∧ s₁.totalSupply = s.totalSupply ∧ s₁.self = s.self := by
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨-, -, -, hb, -⟩ := ozTransfer_eq_some ht
  refine ⟨?_, rfl, rfl⟩
  simp only [State.totalAssets, hb, move_apply_dst _ _ hatt]

/-- **The attack on the OpenZeppelin vault** (`k = 10^δ`, attacker holds `b ≤ S` shares,
donates `D`, victim deposits `a` and gets `n` shares). With `Ŝ = S + k`, profit
`P = value₂(b) − value₀(b) − D` and victim loss `L = a − value₂(n)`:

1. `P·Ŝ = b·L − D·(Ŝ − b)`;
2. `0 ≤ L < price₁` (less than one share at the post-donation price);
3. `P·Ŝ ≤ T + 1 − (k − 1)·D`: the attack yields less than one pre-attack share's worth,
   and loses money once `(k−1)·D > T + 1`;
4. `k·L − k·price₀ < D·k/Ŝ`: the donation the virtual shares capture exceeds `k` times
   the victim's loss, minus `k·price₀` (`= 1` in an empty vault). -/
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

end Defi.ERC4626
end

end
