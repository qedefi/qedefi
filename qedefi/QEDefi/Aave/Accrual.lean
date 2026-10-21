module

public import QEDefi.Aave.Reserve

/-!
# Accrual: `updateState` keeps indexes monotone and the backing invariant up to rounding

* `updateState_eq_some`: what a successful `updateState` changes (indexes, treasury accrual,
  timestamp) and how the cache it returns relates to the new storage.
* `updateState_liquidityIndex_le`/`updateState_variableBorrowIndex_le`: the indexes never
  decrease.
* `updateState_solvent`: under `RateSound`, `Solvent k → Solvent (k + accrualSlack)`; the
  slack is about half a wei. It cannot be `0` in general:
  `QEDefiTest.Aave` evaluates a reserve where `Solvent 0` holds with equality, the rates
  satisfy `RateSound` with equality, and one second of accrual breaks `Solvent 0`
  (half-up rounding of the liquidity index).
-/

section

@[expose] public noncomputable section

namespace QEDefi.Aave
open QEDefi.Math

/-- The arithmetic core of `updateState_solvent`: one accrual with half-up indexes,
floor treasury accrual and the rate condition adds at most `(M + D)/2 + D·B/R + R/2` (in units
of `index · scaled amount`). Variables: `M = S + T`, `W = V + deficit`, `Sp = SECONDS_PER_YEAR`,
`P = 10⁴`, `R = 2H`, `P = 2HP`. -/
theorem accrual_core {M sc I I' B B' D W k rl rb dt x tda amt rf Sp P R H HP : ℕ}
    (hR : R = 2 * H) (hP : P = 2 * HP) (hrf : rf ≤ P) (hSp : 0 < Sp) (hPpos : 0 < P)
    (h0 : M * I ≤ W * R + D * B + k)
    (hI : Sp * R * I' ≤ Sp * R * I + rl * dt * I + Sp * H)
    (hB : D * (R * B + x * B + H + 1) ≤ D * (R * B' + R))
    (hx : D * B * (rb * dt) ≤ D * B * ((x + 1) * Sp))
    (hrate : P * rl * (M * I) ≤ (P - rf) * rb * (D * B))
    (htda : tda * R + D * B ≤ D * B')
    (hamt : amt * P ≤ tda * rf + HP)
    (hsc : sc * I' ≤ amt * R) :
    2 * R * ((M + sc) * I') ≤ 2 * R * (W * R + D * B' + k) + R * (M + D) + 2 * D * B + R * R := by
  obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + rf := ⟨P - rf, by omega⟩
  have hQ : Q + rf - rf = Q := by omega
  rw [hQ] at hrate
  subst hR
  have a1 := Nat.mul_le_mul_left (2 * (Q + rf) * M) hI
  have a2 := Nat.mul_le_mul_left (2 * dt) hrate
  have a3 := Nat.mul_le_mul_left (2 * Q) hx
  have a4 := Nat.mul_le_mul_left (2 * Q * Sp) hB
  have a5 := Nat.mul_le_mul_left (2 * (Q + rf) * Sp * (2 * H)) h0
  have a6 := Nat.mul_le_mul_left (2 * (2 * H) * Sp * (Q + rf)) hsc
  have hamt2 : 2 * (amt * (Q + rf)) ≤ 2 * (tda * rf) + (Q + rf) := by omega
  have a7 := Nat.mul_le_mul_left (Sp * (2 * H) * (2 * H)) hamt2
  have a8 := Nat.mul_le_mul_left (2 * Sp * (2 * H) * rf) htda
  have hPS : 0 < (Q + rf) * Sp := Nat.mul_pos hPpos hSp
  refine Nat.le_of_mul_le_mul_left ?_ hPS
  linarith [a1, a2, a3, a4, a5, a6, a7, a8, Nat.zero_le (Q * Sp * D * H),
    Nat.zero_le (rf * Sp * D * B), Nat.zero_le (rf * Sp * D * (2 * H)), Nat.zero_le (Q * Sp * D),
    Nat.zero_le (rf * Sp * M * (2 * H))]


namespace ReserveState

variable {A : Type} [DecidableEq A]

/-- `updateLiquidityIndex`: either nothing (rate `0`) or a new index `ni ≥ I` with
`SPY·RAY·ni ≤ SPY·RAY·I + rate·Δt·I + SPY·RAY/2`. -/
theorem updateLiquidityIndex_spec {r r1 : ReserveState A} {c c1 : ReserveCache} {now : ℕ}
    (h : r.updateLiquidityIndex c now = some (r1, c1)) :
    (∃ ni, r1 = { r with liquidityIndex := ni } ∧ c1 = { c with nextLiquidityIndex := ni } ∧
      c.currLiquidityIndex ≤ ni ∧
      SECONDS_PER_YEAR * RAY * ni ≤
        SECONDS_PER_YEAR * RAY * c.currLiquidityIndex +
          c.currLiquidityRate * (now - c.reserveLastUpdateTimestamp) * c.currLiquidityIndex +
          SECONDS_PER_YEAR * (RAY / 2)) ∨
    (c.currLiquidityRate = 0 ∧ r1 = r ∧ c1 = c) := by
  unfold updateLiquidityIndex at h
  split_ifs at h with h0
  · cases h; exact Or.inr ⟨h0, rfl, rfl⟩
  · simp only [Option.bind_eq_some_iff, Option.ite_none_left_eq_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨f, hf, ni, hni, -, rfl, rfl⟩ := h
    refine Or.inl ⟨ni, rfl, rfl, le_rayMul_of_ray_le (ray_le_calculateLinearInterest hf) hni, ?_⟩
    obtain ⟨-, -, -, rfl⟩ := calculateLinearInterest_eq_some.1 hf
    have hb := (rayMul_bounds hni).1
    have hy : yearFrac c.currLiquidityRate (now - c.reserveLastUpdateTimestamp) *
        SECONDS_PER_YEAR ≤ c.currLiquidityRate * (now - c.reserveLastUpdateTimestamp) :=
      Nat.div_mul_le_self _ _
    have h1 := Nat.mul_le_mul_left SECONDS_PER_YEAR hb
    have h2 := Nat.mul_le_mul_right c.currLiquidityIndex hy
    nlinarith [h1, h2]

/-- `updateBorrowIndex`: either nothing (no debt) or a new index `nb ≥ B` growing at least by
the first-order term `x = ⌊rate·Δt/SPY⌋`, up to half a ray unit. -/
theorem updateBorrowIndex_spec {r r1 : ReserveState A} {c c1 : ReserveCache} {now : ℕ}
    (h : r.updateBorrowIndex c now = some (r1, c1))
    (hw : c.currVariableBorrowRate * (now - c.reserveLastUpdateTimestamp) ≤ MAX) :
    (∃ nb x, r1 = { r with variableBorrowIndex := nb } ∧
      c1 = { c with nextVariableBorrowIndex := nb } ∧ c.currVariableBorrowIndex ≤ nb ∧
      RAY * c.currVariableBorrowIndex + x * c.currVariableBorrowIndex + RAY / 2 + 1 ≤
        RAY * nb + RAY ∧
      c.currVariableBorrowRate * (now - c.reserveLastUpdateTimestamp) <
        (x + 1) * SECONDS_PER_YEAR) ∨
    (c.currScaledVariableDebt = 0 ∧ r1 = r ∧ c1 = c) := by
  unfold updateBorrowIndex at h
  split_ifs at h with h0
  · cases h; exact Or.inr ⟨h0, rfl, rfl⟩
  · simp only [Option.bind_eq_some_iff, Option.ite_none_left_eq_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨f, hf, nb, hnb, -, rfl, rfl⟩ := h
    have hle := le_rayMul_of_ray_le (ray_le_calculateCompoundedInterest hf) hnb
    have hb := (rayMul_bounds hnb).2
    obtain ⟨-, ⟨he, rfl⟩ | ⟨-, -, -, rfl⟩⟩ := calculateCompoundedInterest_eq_some.1 hf
    · refine Or.inl ⟨nb, 0, rfl, rfl, hle, ?_, ?_⟩
      · linarith [hb]
      · rw [he, Nat.sub_self, Nat.mul_zero]; simp [SECONDS_PER_YEAR_pos]
    · have hU := MAX_lt_U256
      rw [Nat.mod_eq_of_lt (by omega)] at hb
      refine Or.inl ⟨nb, c.currVariableBorrowRate * (now - c.reserveLastUpdateTimestamp) /
        SECONDS_PER_YEAR, rfl, rfl, hle, ?_, lt_div_add_one_mul _ _ SECONDS_PER_YEAR_pos⟩
      nlinarith [hb]

/-- `_accrueToTreasury` adds `sc` scaled units with `sc·I' ≤ amt·RAY`,
`amt·10⁴ ≤ tda·rf + 10⁴/2` and `tda·RAY ≤ D·(B' - B)`. -/
theorem accrueToTreasury_spec {r r1 : ReserveState A} {c : ReserveCache}
    (h : r.accrueToTreasury c = some r1) (hle : c.currVariableBorrowIndex ≤ c.nextVariableBorrowIndex) :
    ∃ sc tda amt, r1 = { r with accruedToTreasury := r.accruedToTreasury + sc } ∧
      tda * RAY + c.currScaledVariableDebt * c.currVariableBorrowIndex ≤
          c.currScaledVariableDebt * c.nextVariableBorrowIndex ∧
        amt * PERCENTAGE_FACTOR ≤ tda * c.reserveFactor + PERCENTAGE_FACTOR / 2 ∧
        sc * c.nextLiquidityIndex ≤ amt * RAY := by
  have triv : 0 * RAY + c.currScaledVariableDebt * c.currVariableBorrowIndex ≤
      c.currScaledVariableDebt * c.nextVariableBorrowIndex := by
    rw [Nat.zero_mul, Nat.zero_add]; exact Nat.mul_le_mul_left _ hle
  unfold accrueToTreasury at h
  split_ifs at h with h0 h1
  · cases h; exact ⟨0, 0, 0, by simp, triv, by simp, by simp⟩
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨tda, htda, amt, hamt, h⟩ := h
    have e1 : tda * RAY + c.currScaledVariableDebt * c.currVariableBorrowIndex ≤
        c.currScaledVariableDebt * c.nextVariableBorrowIndex := by
      have := (rayMulFloor_bounds htda).1
      rw [Nat.mul_sub] at this
      have := Nat.mul_le_mul_left c.currScaledVariableDebt hle
      omega
    have e2 := (halfUpMul_bounds PERCENTAGE_FACTOR_pos hamt).1
    split_ifs at h with h2
    · cases h; exact ⟨0, tda, amt, by simp, e1, e2, by simp⟩
    · simp only [Option.bind_eq_some_iff, Option.ite_none_left_eq_some, Option.some.injEq] at h
      obtain ⟨sc, hsc, -, -, rfl⟩ := h
      exact ⟨sc, tda, amt, rfl, e1, e2, (rayDivFloor_bounds hsc).1⟩

/-- What a successful `updateState` from a fresh cache changes: only the two indexes (upward),
`accruedToTreasury` (upward) and the timestamp; and the returned cache's `next*` fields are the
new storage values. -/
theorem updateState_spec {cfg : ReserveConfig} {r r1 : ReserveState A} {c1 : ReserveCache}
    {now : ℕ} (h : r.updateState (r.cache cfg) now = some (r1, c1)) :
    ∃ nI nB nT, r1 =
        { r with liquidityIndex := nI, variableBorrowIndex := nB, accruedToTreasury := nT,
                 lastUpdateTimestamp := now % TS40 } ∧
      r.liquidityIndex ≤ nI ∧ r.variableBorrowIndex ≤ nB ∧ r.accruedToTreasury ≤ nT ∧
      c1.nextLiquidityIndex = nI ∧ c1.nextVariableBorrowIndex = nB ∧
      c1.nextScaledVariableDebt = r.vToken.totalSupply ∧
      c1.currScaledVariableDebt = r.vToken.totalSupply ∧
      c1.reserveFactor = cfg.reserveFactor := by
  unfold updateState at h
  split_ifs at h with h0
  · cases h
    exact ⟨_, _, _, by cases r; simp_all [cache], le_refl _, le_refl _, le_refl _, rfl, rfl, rfl,
      rfl, rfl⟩
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨ra, ca⟩, ha, ⟨rb, cb⟩, hb, r3, h3, rfl, rfl⟩ := h
    simp only at hb h3
    have hla : ∃ ni, ra = { r with liquidityIndex := ni } ∧
        ca = { r.cache cfg with nextLiquidityIndex := ni } ∧ r.liquidityIndex ≤ ni := by
      rcases updateLiquidityIndex_spec ha with ⟨ni, e1, e2, e3, -⟩ | ⟨-, e1, e2⟩
      · exact ⟨ni, e1, e2, e3⟩
      · exact ⟨r.liquidityIndex, by rw [e1], e2, le_refl _⟩
    obtain ⟨ni, rfl, rfl, hni⟩ := hla
    have hlb : ∃ nb, rb = { r with liquidityIndex := ni, variableBorrowIndex := nb } ∧
        cb = { r.cache cfg with nextLiquidityIndex := ni, nextVariableBorrowIndex := nb } ∧
        r.variableBorrowIndex ≤ nb := by
      unfold updateBorrowIndex at hb
      split_ifs at hb with hz
      · cases hb; exact ⟨r.variableBorrowIndex, rfl, rfl, le_refl _⟩
      · simp only [Option.bind_eq_some_iff, Option.ite_none_left_eq_some, Option.some.injEq,
          Prod.mk.injEq] at hb
        obtain ⟨f, hf, nb, hnb, -, rfl, rfl⟩ := hb
        exact ⟨nb, rfl, rfl, le_rayMul_of_ray_le (ray_le_calculateCompoundedInterest hf) hnb⟩
    obtain ⟨nb, rfl, rfl, hnb⟩ := hlb
    obtain ⟨sc, -, -, rfl, -⟩ := accrueToTreasury_spec h3 hnb
    exact ⟨ni, nb, r.accruedToTreasury + sc, rfl, hni, hnb, by simp, rfl, rfl, rfl, rfl, rfl⟩

/-- **Index monotonicity** of `updateState`. -/
theorem updateState_indexes_le {cfg : ReserveConfig} {r r1 : ReserveState A} {c1 : ReserveCache}
    {now : ℕ} (h : r.updateState (r.cache cfg) now = some (r1, c1)) :
    r.liquidityIndex ≤ r1.liquidityIndex ∧ r.variableBorrowIndex ≤ r1.variableBorrowIndex := by
  obtain ⟨nI, nB, nT, rfl, h1, h2, -⟩ := updateState_spec h
  exact ⟨h1, h2⟩

/-- `updateState` does not touch the tokens, so `TokensWF` is preserved. -/
theorem updateState_tokensWF {cfg : ReserveConfig} {r r1 : ReserveState A} {c1 : ReserveCache}
    {now : ℕ} (h : r.updateState (r.cache cfg) now = some (r1, c1)) (hw : r.TokensWF) :
    r1.TokensWF := by
  obtain ⟨nI, nB, nT, rfl, -⟩ := updateState_spec h
  exact hw

theorem Solvent.mono {k k' : ℕ} {r : ReserveState A} (h : r.Solvent k) (hk : k ≤ k') :
    r.Solvent k' := by
  unfold Solvent at *; omega

/-- **Accrual and the backing invariant.** Under `RateSound`, one `updateState` adds at most
`accrualSlack` (about half a wei) to the slack of `Solvent`; none if the reserve was already
updated in this block. -/
theorem updateState_solvent {cfg : ReserveConfig} {r r1 : ReserveState A} {c1 : ReserveCache}
    {now k : ℕ} (h : r.updateState (r.cache cfg) now = some (r1, c1)) (hs : r.Solvent k)
    (hr : RateSound cfg.reserveFactor now r) : r1.Solvent (k + accrualSlack now r) := by
  unfold updateState at h
  split_ifs at h with h0
  · cases h; simp only [cache] at h0; simpa [accrualSlack, h0] using hs
  obtain ⟨hrf, hrate, hw⟩ := hr
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨ra, ca⟩, ha, ⟨rb, cb⟩, hb, r3, h3, rfl, rfl⟩ := h
  simp only at hb h3
  simp only [cache] at h0
  -- liquidity
  have hla : ∃ ni, ra = { r with liquidityIndex := ni } ∧
      ca = { r.cache cfg with nextLiquidityIndex := ni } ∧
      SECONDS_PER_YEAR * RAY * ni ≤
        SECONDS_PER_YEAR * RAY * r.liquidityIndex +
          r.currentLiquidityRate * (now - r.lastUpdateTimestamp) * r.liquidityIndex +
          SECONDS_PER_YEAR * (RAY / 2) := by
    rcases updateLiquidityIndex_spec ha with ⟨ni, e1, e2, -, e4⟩ | e
    · exact ⟨ni, e1, e2, e4⟩
    · obtain ⟨-, e1, e2⟩ := e
      exact ⟨r.liquidityIndex, by rw [e1], e2, by omega⟩
  obtain ⟨ni, rfl, rfl, hI⟩ := hla
  -- borrow
  have hlb : ∃ nb x, rb = { r with liquidityIndex := ni, variableBorrowIndex := nb } ∧
      cb = { r.cache cfg with nextLiquidityIndex := ni, nextVariableBorrowIndex := nb } ∧
      r.variableBorrowIndex ≤ nb ∧
      r.vToken.totalSupply * (RAY * r.variableBorrowIndex + x * r.variableBorrowIndex +
          RAY / 2 + 1) ≤ r.vToken.totalSupply * (RAY * nb + RAY) ∧
      r.vToken.totalSupply * r.variableBorrowIndex *
          (r.currentVariableBorrowRate * (now - r.lastUpdateTimestamp)) ≤
        r.vToken.totalSupply * r.variableBorrowIndex * ((x + 1) * SECONDS_PER_YEAR) := by
    rcases updateBorrowIndex_spec hb hw with ⟨nb, x, e1, e2, e3, e4, e5⟩ | ⟨hz, rfl, rfl⟩
    · exact ⟨nb, x, e1, e2, e3, Nat.mul_le_mul_left _ e4, Nat.mul_le_mul_left _ e5.le⟩
    · simp only [cache] at hz
      exact ⟨r.variableBorrowIndex, 0, rfl, rfl, le_refl _, by simp [hz], by simp [hz]⟩
  obtain ⟨nb, x, rfl, rfl, hnb, hB, hx⟩ := hlb
  -- treasury
  obtain ⟨sc, tda, amt, rfl, htda, hamt, hsc⟩ := accrueToTreasury_spec h3 hnb
  simp only [cache] at htda hamt hsc
  have core := accrual_core (M := r.aToken.totalSupply + r.accruedToTreasury) (sc := sc)
    (W := r.virtualUnderlyingBalance + r.deficit) (k := k) (rf := cfg.reserveFactor)
    (H := RAY / 2) (HP := PERCENTAGE_FACTOR / 2)
    (by unfold RAY; norm_num) (by unfold PERCENTAGE_FACTOR; norm_num) hrf SECONDS_PER_YEAR_pos
    PERCENTAGE_FACTOR_pos hs hI hB hx hrate htda hamt hsc
  unfold Solvent accrualSlack
  simp only [h0, ite_false]
  rw [show r.aToken.totalSupply + (r.accruedToTreasury + sc) =
    r.aToken.totalSupply + r.accruedToTreasury + sc by omega,
    Nat.mul_comm (r.aToken.totalSupply + r.accruedToTreasury + r.vToken.totalSupply) RAY]
  generalize (r.aToken.totalSupply + r.accruedToTreasury + sc) * ni = L at core ⊢
  generalize (r.virtualUnderlyingBalance + r.deficit) * RAY = W at core ⊢
  generalize r.vToken.totalSupply * nb = Dn at core ⊢
  unfold RAY at *
  omega

end ReserveState

end QEDefi.Aave
end

end
