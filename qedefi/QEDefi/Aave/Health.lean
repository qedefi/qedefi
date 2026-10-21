module

public import QEDefi.Aave.Frame

/-!
# Health factor guarantees

* `healthFactorOf_eq_some`, `threshold_le_healthFactor_iff`: the exact health factor
  `⌊⌊(Σ collateralᵢ·LTᵢ·WAD + debt/2) / debt⌋ / 10⁴⌋` and the meaning of `HF ≥ 1`:
  `10⁴·WAD·debt ≤ Σ collateralᵢ·LTᵢ·WAD + debt/2` (all in base currency). Because `wadDiv`
  rounds half up, a position with `debt ≥ 2·WAD` base units can have `HF ≥ 1` with risk-adjusted
  collateral slightly *below* its debt (by at most `debt/(2·WAD)` units of `collateral·LT`).
* `borrow_healthFactor`, `withdraw_healthFactor`, `transfer_healthFactor`: after a successful
  borrow (resp. a withdrawal or aToken transfer of collateral by a user who still borrows), the
  user's health factor, computed from the *new* state with the oracle prices of the same
  transaction, is `≥ HEALTH_FACTOR_LIQUIDATION_THRESHOLD` (and for a borrow, LTV is non-zero and
  the collateral covers the debt at that LTV).
* `liquidationCall_healthFactor`: a successful liquidation implies that the borrower's health
  factor, after accruing the two reserves involved, was `< 1`; with both reserves already
  updated in this block, the health factor of the pre-state is `< 1`
  (`liquidationCall_healthFactor_of_fresh`).
-/

section

@[expose] public noncomputable section

namespace QEDefi.Aave
open QEDefi.Math

namespace Market

variable {A R : Type} [DecidableEq A] [DecidableEq R]

theorem healthFactorOf_eq_some {s d hf : ℕ} (hd : d ≤ MAX) :
    healthFactorOf s d = some hf ↔
      (d = 0 ∧ hf = MAX) ∨
        (d ≠ 0 ∧ s * WAD + d / 2 ≤ MAX ∧ hf = (s * WAD + d / 2) / d / PERCENTAGE_FACTOR) := by
  unfold healthFactorOf
  split_ifs with h0
  · simp only [Option.some.injEq, h0, ne_eq, not_true_eq_false, false_and, or_false, true_and]
    exact eq_comm
  · simp only [Option.map_eq_some_iff, h0, false_and, false_or, ne_eq, not_false_eq_true,
      true_and]
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨-, h1, rfl⟩ := (wadDiv_eq_some hd).1 hq
      exact ⟨h1, rfl⟩
    · rintro ⟨h1, rfl⟩
      exact ⟨_, (wadDiv_eq_some hd).2 ⟨h0, h1, rfl⟩, rfl⟩

/-- `HF ≥ 1` exactly when the risk-adjusted collateral (`Σ collateral·LT`, base currency × bps)
covers the debt, up to the half-up rounding of `wadDiv`. -/
theorem threshold_le_healthFactor_iff {s d hf : ℕ} (hd0 : d ≠ 0) (hd : d ≤ MAX)
    (h : healthFactorOf s d = some hf) :
    HEALTH_FACTOR_LIQUIDATION_THRESHOLD ≤ hf ↔
      PERCENTAGE_FACTOR * HEALTH_FACTOR_LIQUIDATION_THRESHOLD * d ≤ s * WAD + d / 2 := by
  rcases (healthFactorOf_eq_some hd).1 h with ⟨h0, -⟩ | ⟨-, -, rfl⟩
  · exact absurd h0 hd0
  rw [Nat.le_div_iff_mul_le PERCENTAGE_FACTOR_pos, Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hd0),
    Nat.mul_comm HEALTH_FACTOR_LIQUIDATION_THRESHOLD]

/-! ## Borrow, withdraw, transfer -/

theorem validateHealthFactor_eq_some {m : Market A R} {env : Env R} {u : A} {z : Bool}
    (h : m.validateHealthFactor env u = some z) :
    ∃ ad, m.calculateUserAccountData env.now env.price u = some ad ∧
      HEALTH_FACTOR_LIQUIDATION_THRESHOLD ≤ ad.healthFactor := by
  unfold validateHealthFactor at h
  simp only [Option.bind_eq_some_iff, Option.ite_none_left_eq_some] at h
  obtain ⟨ad, had, hlt, -⟩ := h
  exact ⟨ad, had, Nat.le_of_not_lt hlt⟩

theorem validateHFAndLtvzero_eq_some {m : Market A R} {env : Env R} {a : R} {u : A} {x : Unit}
    (h : m.validateHFAndLtvzero env a u = some x) :
    ∃ ad, m.calculateUserAccountData env.now env.price u = some ad ∧
      HEALTH_FACTOR_LIQUIDATION_THRESHOLD ≤ ad.healthFactor := by
  unfold validateHFAndLtvzero at h
  obtain ⟨z, hz, -⟩ := Option.bind_eq_some_iff.1 h
  exact validateHealthFactor_eq_some hz

/-- **A successful borrow leaves the borrower healthy**: in the new state, with the prices of
the same transaction, `HF ≥ 1`, the average LTV is non-zero and the collateral covers the debt at
that LTV (`totalCollateral ≥ ⌈totalDebt / ltv⌉`). -/
theorem borrow_healthFactor {m m' : Market A R} {env : Env R} {asset : R} {amount : ℕ}
    {user ob : A} (h : m.borrow env asset amount user ob = some m') :
    ∃ ad, m'.calculateUserAccountData env.now env.price ob = some ad ∧
      HEALTH_FACTOR_LIQUIDATION_THRESHOLD ≤ ad.healthFactor ∧ ad.avgLtv ≠ 0 ∧
      ∃ x, percentDivCeil ad.totalDebt ad.avgLtv = some x ∧ x ≤ ad.totalCollateral := by
  unfold borrow at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.ite_none_left_eq_some] at h
  obtain ⟨_, -, _, -, -, _, -, -, -, _, -, _, -, -, _, -, _, -, _, -, u, hval, rfl⟩ := h
  unfold validateHFAndLtv at hval
  simp only [Option.bind_eq_some_iff, Option.ite_none_left_eq_some] at hval
  obtain ⟨ad, had, hltv, hhf, x, hx, hcov, -⟩ := hval
  exact ⟨ad, had, Nat.le_of_not_lt hhf, hltv, x, hx, Nat.le_of_not_lt hcov⟩

/-- **A withdrawal of collateral leaves a borrowing user healthy.** -/
theorem withdraw_healthFactor {m m' : Market A R} {env : Env R} {asset : R} {amount : ℕ}
    {user dst : A} {out : ℕ} (h : m.withdraw env asset amount user dst = some (m', out))
    (hc : m.usingAsCollateral user asset = true) (hb : m'.isBorrowingAny user = true) :
    ∃ ad, m'.calculateUserAccountData env.now env.price user = some ad ∧
      HEALTH_FACTOR_LIQUIDATION_THRESHOLD ≤ ad.healthFactor := by
  unfold withdraw at h
  simp only [Option.bind_eq_some_iff, Option.ite_none_left_eq_some] at h
  obtain ⟨-, _, -, _, -, -, -, -, _, -, _, -, hfin⟩ := h
  rw [ite_eq_left hc] at hfin
  split_ifs at hfin with hz hbor hbor
  · obtain ⟨x, hx, he⟩ := Option.map_eq_some_iff.1 hfin
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact validateHFAndLtvzero_eq_some hx
  · simp only [Option.some.injEq, Prod.mk.injEq] at hfin
    obtain ⟨rfl, -⟩ := hfin
    exact absurd hb hbor
  · obtain ⟨x, hx, he⟩ := Option.map_eq_some_iff.1 hfin
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact validateHFAndLtvzero_eq_some hx
  · simp only [Option.some.injEq, Prod.mk.injEq] at hfin
    obtain ⟨rfl, -⟩ := hfin
    exact absurd hb hbor

/-- **An aToken transfer of collateral leaves a borrowing sender healthy.** -/
theorem transfer_healthFactor {m m' : Market A R} {env : Env R} {asset : R} {src dst : A}
    {amount : ℕ} (h : m.transfer env asset src dst amount = some m') (hne : src ≠ dst)
    (hpos : amount ≠ 0) (hc : m.usingAsCollateral src asset = true)
    (hb : m'.isBorrowingAny src = true) :
    ∃ ad, m'.calculateUserAccountData env.now env.price src = some ad ∧
      HEALTH_FACTOR_LIQUIDATION_THRESHOLD ≤ ad.healthFactor := by
  unfold transfer at h
  simp only [Option.bind_eq_some_iff, Option.ite_none_left_eq_some] at h
  obtain ⟨-, idx, -, sa, hsa, a', -, -, hfin⟩ := h
  have hsa0 : sa ≠ 0 := by
    have := (rayDivCeil_bounds hsa).1
    intro h0; subst h0
    have : 0 < amount * RAY := Nat.mul_pos (Nat.pos_of_ne_zero hpos) RAY_pos
    simp_all
  rw [ite_eq_left ⟨hne, hsa0, hc⟩] at hfin
  split_ifs at hfin with hz hbor hbor
  · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hfin
    exact validateHFAndLtvzero_eq_some hx
  · cases hfin; exact absurd hb hbor
  · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hfin
    exact validateHFAndLtvzero_eq_some hx
  · cases hfin; exact absurd hb hbor

/-! ## Liquidation -/

/-- `updateState` of reserve `a`, written to storage (the first step of every entry point). -/
def accrue (m : Market A R) (now : ℕ) (a : R) : Option (Market A R) :=
  ((m.reserves a).updateState ((m.reserves a).cache (m.config a)) now).map fun p =>
    m.setReserve a p.1

theorem accrue_of_fresh {m : Market A R} {now : ℕ} {a : R}
    (h : (m.reserves a).lastUpdateTimestamp = now % TS40) : m.accrue now a = some m := by
  unfold accrue
  rw [ReserveState.updateState_of_fresh h]
  simp [setReserve]

/-- **Liquidation needs `HF < 1`.** A successful `liquidationCall` implies that the borrower's
health factor, computed after accruing the debt and the collateral reserve (as the call does),
with the prices of the same transaction, is below `HEALTH_FACTOR_LIQUIDATION_THRESHOLD`. -/
theorem liquidationCall_healthFactor {m m' : Market A R} {env : Env R} {collAsset debtAsset : R}
    {borrower liquidator : A} {dtc : ℕ} {recv : Bool}
    (h : m.liquidationCall env collAsset debtAsset borrower liquidator dtc recv = some m') :
    ∃ m1 m2 ad, m.accrue env.now debtAsset = some m1 ∧ m1.accrue env.now collAsset = some m2 ∧
      m2.calculateUserAccountData env.now env.price borrower = some ad ∧
      ad.healthFactor < HEALTH_FACTOR_LIQUIDATION_THRESHOLD := by
  unfold liquidationCall at h
  dsimp only at h
  obtain ⟨⟨rd1, cd1⟩, hud, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨rc1, cc1⟩, huc, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ad, had, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  obtain ⟨hhf, -⟩ := Option.ite_none_left_eq_some.1 h
  refine ⟨m.setReserve debtAsset rd1, (m.setReserve debtAsset rd1).setReserve collAsset rc1, ad,
    ?_, ?_, had, Nat.lt_of_not_le hhf⟩
  · simp only [accrue, hud, Option.map_some]
  · simp only [accrue, config_setReserve]
    rw [huc]; rfl

/-- With both reserves already updated in this block, a successful liquidation implies that the
borrower's health factor in the pre-state is below 1. -/
theorem liquidationCall_healthFactor_of_fresh {m m' : Market A R} {env : Env R}
    {collAsset debtAsset : R} {borrower liquidator : A} {dtc : ℕ} {recv : Bool}
    (h : m.liquidationCall env collAsset debtAsset borrower liquidator dtc recv = some m')
    (hd : (m.reserves debtAsset).lastUpdateTimestamp = env.now % TS40)
    (hc : (m.reserves collAsset).lastUpdateTimestamp = env.now % TS40) :
    ∃ ad, m.calculateUserAccountData env.now env.price borrower = some ad ∧
      ad.healthFactor < HEALTH_FACTOR_LIQUIDATION_THRESHOLD := by
  obtain ⟨m1, m2, ad, h1, h2, h3, h4⟩ := liquidationCall_healthFactor h
  rw [accrue_of_fresh hd] at h1
  cases h1
  rw [accrue_of_fresh hc] at h2
  cases h2
  exact ⟨ad, h3, h4⟩

end Market

end QEDefi.Aave
end

end
