module

public import EvmLeanSpecs.Vault.Arith

/-!
# The arithmetic behind the round-trip properties

Four inequalities on `ℕ`, one per shape of round trip, phrased with the cross-multiplied
rounding facts that the vault operations provide. `T, S` are total assets and supply
before the first call; the first call moves `a` assets and `n` shares, the second
returns `a'` assets or `n'` shares. Each one works for both Solmate (no virtual offsets)
and OpenZeppelin (apply it to `T + 1` and `S + 10^δ`).
-/

@[expose] public section

namespace EvmLeanSpecs.Vault

/-- In, then out, measured in assets (`deposit→redeem`, `mint→redeem`): if the entry gave
at most fair shares (`n·T ≤ a·S`) and the exit gave at most fair assets at the new price
(`a'·(S+n) ≤ n·(T+a)`), then `a' ≤ a`. -/
theorem rt_in_out_assets {T S a n a' : ℕ} (hpos : 0 < S + n) (h1 : n * T ≤ a * S)
    (h2 : a' * (S + n) ≤ n * (T + a)) : a' ≤ a := by
  by_contra hc
  push Not at hc
  have : (a + 1) * (S + n) ≤ a' * (S + n) := Nat.mul_le_mul_right _ hc
  nlinarith

/-- In, then out, measured in shares (`deposit→withdraw`, `mint→withdraw`): `n ≤ n'`. -/
theorem rt_in_out_shares {T S a n n' : ℕ} (hpos : 0 < T + a) (h1 : n * T ≤ a * S)
    (h2 : a * (S + n) ≤ n' * (T + a)) : n ≤ n' := by
  by_contra hc
  push Not at hc
  have : (n' + 1) * (T + a) ≤ n * (T + a) := Nat.mul_le_mul_right _ hc
  nlinarith

/-- Out, then in, measured in shares (`redeem→deposit`, `withdraw→deposit`): with
`T = a + T₁`, `S = n + S₁` (the state between the calls is `T₁, S₁`, `T₁ > 0`), if the
exit gave at most fair assets (`a·S ≤ n·T`) and the re-entry at most fair shares
(`n'·T₁ ≤ a·S₁`), then `n' ≤ n`. -/
theorem rt_out_in_shares {T₁ S₁ a n n' : ℕ} (hpos : 0 < T₁) (h1 : a * (n + S₁) ≤ n * (a + T₁))
    (h2 : n' * T₁ ≤ a * S₁) : n' ≤ n := by
  by_contra hc
  push Not at hc
  have : (n + 1) * T₁ ≤ n' * T₁ := Nat.mul_le_mul_right _ hc
  nlinarith

/-- Out, then in, measured in assets (`redeem→mint`, `withdraw→mint`): `a ≤ a'` when the
state in between has `S₁ > 0` shares. -/
theorem rt_out_in_assets {T₁ S₁ a n a' : ℕ} (hpos : 0 < S₁) (h1 : a * (n + S₁) ≤ n * (a + T₁))
    (h2 : n * T₁ ≤ a' * S₁) : a ≤ a' := by
  by_contra hc
  push Not at hc
  have : (a' + 1) * S₁ ≤ a * S₁ := Nat.mul_le_mul_right _ hc
  nlinarith

end EvmLeanSpecs.Vault
