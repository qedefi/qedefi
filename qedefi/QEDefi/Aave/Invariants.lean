module

public import QEDefi.Aave.Frame

/-!
# The reserve invariants of the Aave v3.7 Pool model

`Market.Tx` lists the modelled entry points and `Market.exec` runs one. For every successful
transaction, at `block.timestamp = now`:

* **Σ scaled balances = scaled total supply** for every aToken and variable debt token
  (`exec_tokensWF`).
* **Indexes never decrease**: `liquidityIndex` and `variableBorrowIndex` of every reserve
  (`exec_indexes_mono`).
* **Backing** (`exec_solvent`): if every reserve satisfies `Solvent k` and its rates are
  `RateSound`, every reserve satisfies `Solvent (k + accrualSlack)` afterwards; the slack is `0`
  for a reserve already updated in this block (`exec_solvent_of_fresh`: the exact invariant is
  preserved by every entry point when nothing accrues). The slack is necessary:
  `accrual_breaks_exact_backing` is a reserve with `Solvent 0` (tight) and `RateSound` rates that
  violates `Solvent 0` one second later.
-/

section

@[expose] public noncomputable section

namespace QEDefi.Aave
open QEDefi.Math

namespace Market

variable {A R : Type} [DecidableEq A] [DecidableEq R]

/-- The modelled Pool (and aToken) entry points. -/
inductive Tx (A R : Type) where
  /-- `Pool.supply(asset, amount, onBehalfOf, _)` from `user`. -/
  | supply (asset : R) (amount : ℕ) (user onBehalfOf : A)
  /-- `Pool.withdraw(asset, amount, to)` from `user`. -/
  | withdraw (asset : R) (amount : ℕ) (user dst : A)
  /-- `Pool.borrow(asset, amount, VARIABLE, _, onBehalfOf)` from `user`. -/
  | borrow (asset : R) (amount : ℕ) (user onBehalfOf : A)
  /-- `Pool.repay` (`useATokens = false`) / `Pool.repayWithATokens` (`true`). -/
  | repay (asset : R) (amount : ℕ) (user onBehalfOf : A) (useATokens : Bool)
  /-- `AToken.transfer(dst, amount)` from `src`. -/
  | transfer (asset : R) (src dst : A) (amount : ℕ)
  /-- `Pool.mintToTreasury(assets)`. -/
  | mintToTreasury (assets : List R)
  /-- `Pool.liquidationCall(collateralAsset, debtAsset, borrower, debtToCover, receiveAToken)`
  from `liquidator`. -/
  | liquidationCall (collAsset debtAsset : R) (borrower liquidator : A) (debtToCover : ℕ)
      (receiveAToken : Bool)

/-- Run one transaction (`none` = revert). -/
def exec (m : Market A R) (env : Env R) : Tx A R → Option (Market A R)
  | .supply a x u o => m.supply env a x u o
  | .withdraw a x u d => (m.withdraw env a x u d).map Prod.fst
  | .borrow a x u o => m.borrow env a x u o
  | .repay a x u o b => (m.repay env a x u o b).map Prod.fst
  | .transfer a s d x => m.transfer env a s d x
  | .mintToTreasury as => m.mintToTreasury env as
  | .liquidationCall c d b l x r => m.liquidationCall env c d b l x r

theorem exec_reaches {m m' : Market A R} {env : Env R} {tx : Tx A R}
    (h : m.exec env tx = some m') : Reaches m env.now m' := by
  cases tx with
  | supply a x u o => exact supply_reaches (asset := a) (amount := x) (user := u) (ob := o) h
  | withdraw a x u d =>
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
    exact withdraw_reaches (out := p.2) hp
  | borrow a x u o => exact borrow_reaches (asset := a) (amount := x) (user := u) (ob := o) h
  | repay a x u o b =>
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
    exact repay_reaches (out := p.2) hp
  | transfer => exact Reaches.of_allStep (transfer_allStep h)
  | mintToTreasury => exact Reaches.of_allStep (mintToTreasury_allStep h)
  | liquidationCall => exact liquidationCall_reaches h

/-! ## Consequences of `Reaches` -/

theorem Reaches.tokensWF {m m' : Market A R} {now : ℕ} (h : Reaches m now m')
    (hw : ∀ b, (m.reserves b).TokensWF) (b : R) : (m'.reserves b).TokensWF := by
  obtain ⟨r1, hr1, hs⟩ := h b
  refine hs.wf ?_
  rcases hr1 with rfl | ⟨c1, hu⟩
  · exact hw b
  · exact ReserveState.updateState_tokensWF hu (hw b)

theorem Reaches.indexes_mono {m m' : Market A R} {now : ℕ} (h : Reaches m now m') (b : R) :
    (m.reserves b).liquidityIndex ≤ (m'.reserves b).liquidityIndex ∧
      (m.reserves b).variableBorrowIndex ≤ (m'.reserves b).variableBorrowIndex := by
  obtain ⟨r1, hr1, hs⟩ := h b
  rw [hs.liquidityIndex, hs.variableBorrowIndex]
  rcases hr1 with rfl | ⟨c1, hu⟩
  · exact ⟨le_refl _, le_refl _⟩
  · exact ReserveState.updateState_indexes_le hu

theorem Reaches.solvent {m m' : Market A R} {now : ℕ} {k : R → ℕ} (h : Reaches m now m')
    (hs : ∀ b, (m.reserves b).Solvent (k b))
    (hr : ∀ b, ReserveState.RateSound (m.config b).reserveFactor now (m.reserves b)) (b : R) :
    (m'.reserves b).Solvent (k b + ReserveState.accrualSlack now (m.reserves b)) := by
  obtain ⟨r1, hr1, hst⟩ := h b
  refine ReserveState.Solvent.of_backed ?_ hst.backed
  rcases hr1 with rfl | ⟨c1, hu⟩
  · exact (hs b).mono (Nat.le_add_right _ _)
  · exact ReserveState.updateState_solvent hu (hs b) (hr b)

theorem Reaches.solvent_of_fresh {m m' : Market A R} {now : ℕ} {k : R → ℕ}
    (h : Reaches m now m') (hs : ∀ b, (m.reserves b).Solvent (k b))
    (hf : ∀ b, (m.reserves b).lastUpdateTimestamp = now % TS40) (b : R) :
    (m'.reserves b).Solvent (k b) := by
  obtain ⟨r1, hr1, hst⟩ := h b
  refine ReserveState.Solvent.of_backed ?_ hst.backed
  rcases hr1 with rfl | ⟨c1, hu⟩
  · exact hs b
  · rw [ReserveState.updateState_of_fresh (hf b)] at hu
    cases hu
    exact hs b

/-! ## The invariants for every transaction -/

/-- **Invariant 4.** Every transaction keeps `Σ scaled balances = scaledTotalSupply` for the
aToken and the variable debt token of every reserve. -/
theorem exec_tokensWF {m m' : Market A R} {env : Env R} {tx : Tx A R}
    (h : m.exec env tx = some m') (hw : ∀ b, (m.reserves b).TokensWF) (b : R) :
    (m'.reserves b).TokensWF :=
  (exec_reaches h).tokensWF hw b

/-- **Index monotonicity.** No transaction decreases a reserve's liquidity index or variable
borrow index. -/
theorem exec_indexes_mono {m m' : Market A R} {env : Env R} {tx : Tx A R}
    (h : m.exec env tx = some m') (b : R) :
    (m.reserves b).liquidityIndex ≤ (m'.reserves b).liquidityIndex ∧
      (m.reserves b).variableBorrowIndex ≤ (m'.reserves b).variableBorrowIndex :=
  (exec_reaches h).indexes_mono b

/-- **Backing (invariant 3).** If every reserve is `Solvent` with slack `k` and has `RateSound`
rates, then after any transaction every reserve is `Solvent` with slack
`k + accrualSlack` (about half a wei, and `0` for reserves already updated in this block). -/
theorem exec_solvent {m m' : Market A R} {env : Env R} {tx : Tx A R} {k : R → ℕ}
    (h : m.exec env tx = some m') (hs : ∀ b, (m.reserves b).Solvent (k b))
    (hr : ∀ b, ReserveState.RateSound (m.config b).reserveFactor env.now (m.reserves b)) (b : R) :
    (m'.reserves b).Solvent (k b + ReserveState.accrualSlack env.now (m.reserves b)) :=
  (exec_reaches h).solvent hs hr b

/-- **Exact backing between accruals.** When every reserve was already updated in this block,
every transaction preserves `Solvent k` exactly, for any slack `k` (in particular `k = 0`):
all rounding in supply, withdraw, borrow, repay, transfers, `mintToTreasury` and liquidations is
in favour of the protocol. -/
theorem exec_solvent_of_fresh {m m' : Market A R} {env : Env R} {tx : Tx A R} {k : R → ℕ}
    (h : m.exec env tx = some m') (hs : ∀ b, (m.reserves b).Solvent (k b))
    (hf : ∀ b, (m.reserves b).lastUpdateTimestamp = env.now % TS40) (b : R) :
    (m'.reserves b).Solvent (k b) :=
  (exec_reaches h).solvent_of_fresh hs hf b

end Market

/-! ## The exact invariant is not preserved by accrual -/

/-- A reserve with 2 scaled aTokens at liquidity index `1.5`, 1 scaled debt unit at borrow index
`3`, nothing else: `Solvent 0` holds with equality. -/
def tightReserve : ReserveState Unit where
  liquidityIndex := 3 * RAY / 2
  currentLiquidityRate := SECONDS_PER_YEAR
  variableBorrowIndex := 3 * RAY
  currentVariableBorrowRate := SECONDS_PER_YEAR
  deficit := 0
  lastUpdateTimestamp := 0
  liquidationGracePeriodUntil := 0
  accruedToTreasury := 0
  virtualUnderlyingBalance := 0
  aToken := ⟨Finsupp.single () 2, 2, fun _ => 0⟩
  vToken := ⟨Finsupp.single () 1, 1, fun _ => 0⟩

/-- The configuration of `tightReserve`: reserve factor `0`. -/
def tightConfig : ReserveConfig :=
  ⟨0, 0, 0, 0, 0, 18, 0, 0, true, false, false, true⟩

/-- **Counterexample to exact backing under accrual.** `tightReserve` is `Solvent 0` with
equality, its rates (`1/SECONDS_PER_YEAR` ray per second for both) are `RateSound` with
equality, yet one second later `Solvent 0` fails: the half-up `rayMul` rounds the liquidity
index up (`1.5 + 1.5e-27 → 1.5 + 2e-27`) while the debt (scaled 1 at index 3) gains exactly
`3e-27`, so suppliers are owed `4e-27` more against `3e-27` more of debt. The violation is
`1` (in units of `index · scaled amount`, i.e. `1e-27` wei). -/
theorem accrual_breaks_exact_backing :
    tightReserve.Solvent 0 ∧ ReserveState.RateSound tightConfig.reserveFactor 1 tightReserve ∧
    ∃ r1 c1, tightReserve.updateState (tightReserve.cache tightConfig) 1 = some (r1, c1) ∧
      ¬ r1.Solvent 0 ∧ r1.Solvent 1 := by
  refine ⟨?_, ?_,
    { tightReserve with liquidityIndex := 3 * RAY / 2 + 2, variableBorrowIndex := 3 * RAY + 3,
                        lastUpdateTimestamp := 1 },
    { tightReserve.cache tightConfig with nextLiquidityIndex := 3 * RAY / 2 + 2,
                                          nextVariableBorrowIndex := 3 * RAY + 3,
                                          reserveLastUpdateTimestamp := 1 }, ?_, ?_, ?_⟩
  · simp [ReserveState.Solvent, tightReserve, RAY]
  · refine ⟨by simp [tightConfig, PERCENTAGE_FACTOR], ?_, ?_⟩ <;>
      simp [tightReserve, tightConfig, PERCENTAGE_FACTOR, RAY, SECONDS_PER_YEAR, MAX]
  · rfl
  · simp [ReserveState.Solvent, tightReserve, RAY]
  · simp [ReserveState.Solvent, tightReserve, RAY]

end QEDefi.Aave
end

end
