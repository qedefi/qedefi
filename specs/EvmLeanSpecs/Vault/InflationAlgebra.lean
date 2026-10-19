module

public import Mathlib

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

@[expose] public section

namespace EvmLeanSpecs.Vault.Inflation

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

end EvmLeanSpecs.Vault.Inflation
