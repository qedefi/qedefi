module

public import QEDefi.Aave.MathUtils
public import QEDefi.Aave.ScaledToken

/-!
# Aave v3 reserve state and `ReserveLogic`

One reserve of the deployed Aave v3.7 Pool: the `ReserveData` fields the accounting uses, its
aToken and variable debt token storage (`ScaledToken`), the `ReserveCache`, and
`ReserveLogic.cache`/`updateState` (`_updateIndexes` + `_accrueToTreasury`)/
`updateInterestRatesAndVirtualBalance`/`getNormalizedIncome`/`getNormalizedDebt`, plus
`TokenMath` (the v3.5+ rounding directions: in favour of the protocol).

The interest rate strategy is an external contract; it is a parameter (`Strategy`), any
function of the `CalculateInterestRatesParams` that may revert. `block.timestamp` is `now`;
`uint40(block.timestamp)` truncates (`now % 2^40`).
-/

section

@[expose] public noncomputable section

namespace QEDefi.Aave
open QEDefi.Math

/-! ## `TokenMath` -/

/-- `TokenMath.getATokenMintScaledAmount = rayDivFloor`. -/
def getATokenMintScaledAmount (amount index : ℕ) : Option ℕ := rayDivFloor amount index
/-- `TokenMath.getATokenBurnScaledAmount = rayDivCeil`. -/
def getATokenBurnScaledAmount (amount index : ℕ) : Option ℕ := rayDivCeil amount index
/-- `TokenMath.getATokenTransferScaledAmount = rayDivCeil`. -/
def getATokenTransferScaledAmount (amount index : ℕ) : Option ℕ := rayDivCeil amount index
/-- `TokenMath.getATokenBalance = rayMulFloor`. -/
def getATokenBalance (scaled index : ℕ) : Option ℕ := rayMulFloor scaled index
/-- `TokenMath.getVTokenMintScaledAmount = rayDivCeil`. -/
def getVTokenMintScaledAmount (amount index : ℕ) : Option ℕ := rayDivCeil amount index
/-- `TokenMath.getVTokenBurnScaledAmount = rayDivFloor`. -/
def getVTokenBurnScaledAmount (amount index : ℕ) : Option ℕ := rayDivFloor amount index
/-- `TokenMath.getVTokenBalance = rayMulCeil`. -/
def getVTokenBalance (scaled index : ℕ) : Option ℕ := rayMulCeil scaled index

/-! ## State -/

/-- The static part of a reserve's configuration (`ReserveConfigurationMap`) that the modelled
operations read. Admin operations are out of scope, so it never changes. -/
structure ReserveConfig where
  /-- Reserve factor, bps. -/
  reserveFactor : ℕ
  /-- Loan to value, bps. -/
  ltv : ℕ
  /-- Liquidation threshold, bps. -/
  liquidationThreshold : ℕ
  /-- Liquidation bonus, bps (`10500` = 5% bonus). -/
  liquidationBonus : ℕ
  /-- Liquidation protocol fee, bps of the bonus. -/
  liquidationProtocolFee : ℕ
  /-- Decimals of the underlying. -/
  decimals : ℕ
  /-- Supply cap in whole tokens (0 = none). -/
  supplyCap : ℕ
  /-- Borrow cap in whole tokens (0 = none). -/
  borrowCap : ℕ
  /-- Active flag. -/
  active : Bool
  /-- Frozen flag. -/
  frozen : Bool
  /-- Paused flag. -/
  paused : Bool
  /-- Borrowing enabled flag. -/
  borrowingEnabled : Bool

/-- The storage of one reserve: `ReserveData` (the fields read by the accounting) together with
its aToken and variable debt token storage. -/
structure ReserveState (A : Type) where
  /-- `liquidityIndex` (ray, `uint128`). -/
  liquidityIndex : ℕ
  /-- `currentLiquidityRate` (ray, `uint128`). -/
  currentLiquidityRate : ℕ
  /-- `variableBorrowIndex` (ray, `uint128`). -/
  variableBorrowIndex : ℕ
  /-- `currentVariableBorrowRate` (ray, `uint128`). -/
  currentVariableBorrowRate : ℕ
  /-- `deficit`: bad debt written off, in underlying units (`uint128`). -/
  deficit : ℕ
  /-- `lastUpdateTimestamp` (`uint40`). -/
  lastUpdateTimestamp : ℕ
  /-- `liquidationGracePeriodUntil` (`uint40`). -/
  liquidationGracePeriodUntil : ℕ
  /-- `accruedToTreasury`: scaled aTokens owed to the treasury, not yet minted (`uint128`). -/
  accruedToTreasury : ℕ
  /-- `virtualUnderlyingBalance`: the underlying the protocol accounts as held (`uint128`). -/
  virtualUnderlyingBalance : ℕ
  /-- aToken storage (scaled balances). -/
  aToken : ScaledToken A
  /-- Variable debt token storage (scaled balances). -/
  vToken : ScaledToken A

/-- `DataTypes.ReserveCache` (the fields used). -/
structure ReserveCache where
  /-- `reserveFactor`. -/
  reserveFactor : ℕ
  /-- `currScaledVariableDebt`. -/
  currScaledVariableDebt : ℕ
  /-- `nextScaledVariableDebt`. -/
  nextScaledVariableDebt : ℕ
  /-- `currLiquidityIndex`. -/
  currLiquidityIndex : ℕ
  /-- `nextLiquidityIndex`. -/
  nextLiquidityIndex : ℕ
  /-- `currVariableBorrowIndex`. -/
  currVariableBorrowIndex : ℕ
  /-- `nextVariableBorrowIndex`. -/
  nextVariableBorrowIndex : ℕ
  /-- `currLiquidityRate`. -/
  currLiquidityRate : ℕ
  /-- `currVariableBorrowRate`. -/
  currVariableBorrowRate : ℕ
  /-- `reserveLastUpdateTimestamp`. -/
  reserveLastUpdateTimestamp : ℕ

/-- `DataTypes.CalculateInterestRatesParams` (with `usingVirtualBalance = true`). -/
structure RateParams where
  /-- `unbacked` (= `reserve.deficit`). -/
  unbacked : ℕ
  /-- `liquidityAdded`. -/
  liquidityAdded : ℕ
  /-- `liquidityTaken`. -/
  liquidityTaken : ℕ
  /-- `totalDebt`. -/
  totalDebt : ℕ
  /-- `reserveFactor`. -/
  reserveFactor : ℕ
  /-- `virtualUnderlyingBalance` (before this action). -/
  virtualUnderlyingBalance : ℕ

/-- An interest rate strategy: `(liquidityRate, variableBorrowRate)`, or a revert. -/
abbrev Strategy := RateParams → Option (ℕ × ℕ)

/-- `2^40`: `uint40(block.timestamp) = now % 2^40`. -/
def TS40 : ℕ := 2 ^ 40

namespace ReserveState

variable {A : Type} [DecidableEq A]

/-- `ReserveLogic.cache`. -/
def cache (cfg : ReserveConfig) (r : ReserveState A) : ReserveCache where
  reserveFactor := cfg.reserveFactor
  currScaledVariableDebt := r.vToken.totalSupply
  nextScaledVariableDebt := r.vToken.totalSupply
  currLiquidityIndex := r.liquidityIndex
  nextLiquidityIndex := r.liquidityIndex
  currVariableBorrowIndex := r.variableBorrowIndex
  nextVariableBorrowIndex := r.variableBorrowIndex
  currLiquidityRate := r.currentLiquidityRate
  currVariableBorrowRate := r.currentVariableBorrowRate
  reserveLastUpdateTimestamp := r.lastUpdateTimestamp

/-- The liquidity half of `_updateIndexes`: only if `currLiquidityRate ≠ 0`. -/
def updateLiquidityIndex (r : ReserveState A) (c : ReserveCache) (now : ℕ) :
    Option (ReserveState A × ReserveCache) :=
  if c.currLiquidityRate = 0 then some (r, c) else
  (calculateLinearInterest c.currLiquidityRate c.reserveLastUpdateTimestamp now).bind fun f =>
  (rayMul f c.currLiquidityIndex).bind fun ni =>
  if UINT128_MAX < ni then none else                                   -- toUint128
  some ({ r with liquidityIndex := ni }, { c with nextLiquidityIndex := ni })

/-- The borrow half of `_updateIndexes`: only if `currScaledVariableDebt ≠ 0`. -/
def updateBorrowIndex (r : ReserveState A) (c : ReserveCache) (now : ℕ) :
    Option (ReserveState A × ReserveCache) :=
  if c.currScaledVariableDebt = 0 then some (r, c) else
  (calculateCompoundedInterest c.currVariableBorrowRate c.reserveLastUpdateTimestamp now).bind
    fun f =>
  (rayMul f c.currVariableBorrowIndex).bind fun nb =>
  if UINT128_MAX < nb then none else
  some ({ r with variableBorrowIndex := nb }, { c with nextVariableBorrowIndex := nb })

/-- `ReserveLogic._accrueToTreasury`. -/
def accrueToTreasury (r : ReserveState A) (c : ReserveCache) : Option (ReserveState A) :=
  if c.reserveFactor = 0 then some r else
  if c.nextVariableBorrowIndex < c.currVariableBorrowIndex then none else
  (rayMulFloor c.currScaledVariableDebt (c.nextVariableBorrowIndex - c.currVariableBorrowIndex)).bind
    fun totalDebtAccrued =>
  (percentMul totalDebtAccrued c.reserveFactor).bind fun amountToMint =>
  if amountToMint = 0 then some r else
  (getATokenMintScaledAmount amountToMint c.nextLiquidityIndex).bind fun sc =>
  if UINT128_MAX < sc then none else                                   -- toUint128
  if UINT128_MAX < r.accruedToTreasury + sc then none else             -- uint128 +=
  some { r with accruedToTreasury := r.accruedToTreasury + sc }

/-- `ReserveLogic.updateState(reserve, reserveCache)` at `block.timestamp = now`. -/
def updateState (r : ReserveState A) (c : ReserveCache) (now : ℕ) :
    Option (ReserveState A × ReserveCache) :=
  if c.reserveLastUpdateTimestamp = now % TS40 then some (r, c) else
  (r.updateLiquidityIndex c now).bind fun p =>
  (p.1.updateBorrowIndex p.2 now).bind fun q =>
  (q.1.accrueToTreasury q.2).map fun r3 =>
  ({ r3 with lastUpdateTimestamp := now % TS40 },
   { q.2 with reserveLastUpdateTimestamp := now % TS40 })

/-- The virtual balance update of `updateInterestRatesAndVirtualBalance`:
`+= liquidityAdded.toUint128()` (checked `uint128`), `-= liquidityTaken.toUint128()`. -/
def nextVirtualBalance (v added taken : ℕ) : Option ℕ :=
  (if added = 0 then some v
   else if UINT128_MAX < added ∨ UINT128_MAX < v + added then none else some (v + added)).bind
  fun v1 =>
  if taken = 0 then some v1
  else if UINT128_MAX < taken ∨ v1 < taken then none else some (v1 - taken)

/-- `ReserveLogic.updateInterestRatesAndVirtualBalance(reserve, cache, _, added, taken, irs)`. -/
def updateInterestRatesAndVirtualBalance (irs : Strategy) (r : ReserveState A) (c : ReserveCache)
    (added taken : ℕ) : Option (ReserveState A) :=
  (getVTokenBalance c.nextScaledVariableDebt c.nextVariableBorrowIndex).bind fun totalDebt =>
  (irs ⟨r.deficit, added, taken, totalDebt, c.reserveFactor, r.virtualUnderlyingBalance⟩).bind
    fun rates =>
  if UINT128_MAX < rates.1 ∨ UINT128_MAX < rates.2 then none else    -- toUint128
  (nextVirtualBalance r.virtualUnderlyingBalance added taken).map fun v =>
  { r with currentLiquidityRate := rates.1, currentVariableBorrowRate := rates.2,
           virtualUnderlyingBalance := v }

/-- `ReserveLogic.getNormalizedIncome` at `block.timestamp = now`. -/
def getNormalizedIncome (r : ReserveState A) (now : ℕ) : Option ℕ :=
  if r.lastUpdateTimestamp = now then some r.liquidityIndex
  else (calculateLinearInterest r.currentLiquidityRate r.lastUpdateTimestamp now).bind fun f =>
    rayMul f r.liquidityIndex

/-- `ReserveLogic.getNormalizedDebt` at `block.timestamp = now`. -/
def getNormalizedDebt (r : ReserveState A) (now : ℕ) : Option ℕ :=
  if r.lastUpdateTimestamp = now then some r.variableBorrowIndex
  else (calculateCompoundedInterest r.currentVariableBorrowRate r.lastUpdateTimestamp now).bind
    fun f => rayMul f r.variableBorrowIndex

/-! ## Invariants -/

/-- The backing invariant with slack `k` (all quantities scaled by `RAY`):

`(aToken scaled supply + accruedToTreasury) · liquidityIndex
   ≤ (virtualUnderlyingBalance + deficit) · RAY + scaled variable debt · variableBorrowIndex + k`.

The left side is what the aToken holders and the treasury are owed; the right side is what the
reserve holds (`virtualUnderlyingBalance`), what borrowers owe, and the bad debt `deficit` that
was written off (and is to be covered by the Umbrella `eliminateReserveDeficit`). -/
def Solvent (k : ℕ) (r : ReserveState A) : Prop :=
  (r.aToken.totalSupply + r.accruedToTreasury) * r.liquidityIndex ≤
    (r.virtualUnderlyingBalance + r.deficit) * RAY +
      r.vToken.totalSupply * r.variableBorrowIndex + k

/-- Both tokens of the reserve are well formed (`Σ scaled balances = scaled total supply`). -/
def TokensWF (r : ReserveState A) : Prop := r.aToken.WF ∧ r.vToken.WF

/-- The rate consistency the accrual needs: the stored liquidity rate does not pay suppliers
more than borrowers pay net of the reserve factor,
`10⁴ · liquidityRate · (S + T)·I ≤ (10⁴ - rf) · borrowRate · D·B`, plus `rf ≤ 10⁴` and no
wrap-around of `borrowRate · Δt` (always true for a `uint128` rate and `uint40` times).
The deployed `DefaultReserveInterestRateStrategyV2` computes
`liquidityRate = borrowRate · D·B/(D·B + (V + deficit)·RAY) · (1 - rf)`, which satisfies this
whenever `Solvent 0` holds, up to its own half-up rounding (not modelled here). -/
def RateSound (rf now : ℕ) (r : ReserveState A) : Prop :=
  rf ≤ PERCENTAGE_FACTOR ∧
  PERCENTAGE_FACTOR * r.currentLiquidityRate *
      ((r.aToken.totalSupply + r.accruedToTreasury) * r.liquidityIndex) ≤
    (PERCENTAGE_FACTOR - rf) * r.currentVariableBorrowRate *
      (r.vToken.totalSupply * r.variableBorrowIndex) ∧
  r.currentVariableBorrowRate * (now - r.lastUpdateTimestamp) ≤ MAX

/-- The rounding slack one accrual may add to `Solvent`, `0` when the reserve was already
updated in this block:
`⌈((S + T + D)·RAY + 2·D·B + RAY²) / (2·RAY)⌉`, i.e. about half a wei plus
`(S + T + D)/(2·RAY) + D·B/RAY²` wei. -/
def accrualSlack (now : ℕ) (r : ReserveState A) : ℕ :=
  if r.lastUpdateTimestamp = now % TS40 then 0 else
  ((r.aToken.totalSupply + r.accruedToTreasury + r.vToken.totalSupply) * RAY +
      2 * r.vToken.totalSupply * r.variableBorrowIndex + RAY * RAY) / (2 * RAY) + 1

end ReserveState

end QEDefi.Aave
end

end
