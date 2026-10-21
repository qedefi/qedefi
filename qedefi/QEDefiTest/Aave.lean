import QEDefi.Aave.MathUtils

/-!
# Tests for the Aave v3.7 model's arithmetic (`QEDefi.Aave`)

Unit checks of `WadRayMath`/`PercentageMath` (rounding and the exact overflow boundaries), and a
comparison with the deployed Ethereum Core Pool (`0x8787…4E2`, implementation
`0x728a138a4823392c2efa55e028d434f526fe03cf`, `POOL_REVISION = 11`) at block 26243228
(timestamp 1792612775): the model recomputes `getReserveNormalizedIncome`,
`getReserveNormalizedVariableDebt` and the aToken / variable debt token `totalSupply()` of
WETH and USDC from the reserve data read at the same block (`cast call … --block 26243228`).
-/

namespace QEDefi.Aave.Tests
open QEDefi.Math QEDefi.Aave

/-! ## `WadRayMath` -/

-- half-up rounding
#guard rayMul 3 (RAY / 2) == some 2          -- 1.5 rounds up
#guard rayMul 1 (RAY / 2) == some 1          -- 0.5 rounds up
#guard rayMul 1 (RAY / 2 - 1) == some 0
#guard rayMulFloor 3 (RAY / 2) == some 1
#guard rayMulCeil 1 1 == some 1
#guard rayMulCeil 0 5 == some 0
#guard rayDiv 1 (2 * RAY) == some 1          -- 0.5 rounds up
#guard rayDivFloor 1 (2 * RAY) == some 0
#guard rayDivCeil 1 (3 * RAY) == some 1
#guard rayDiv 5 0 == none
#guard wadMul WAD WAD == some WAD
#guard wadDiv WAD (2 * WAD) == some (WAD / 2)
#guard percentMul 10001 5000 == some 5001    -- 5000.5 rounds up
#guard percentMulFloor 10001 5000 == some 5000
#guard percentMulCeil 10001 5000 == some 5001
#guard percentDivCeil 1 3 == some 3334
#guard rayToWad (WAD_RAY_RATIO / 2) == 1
#guard rayToWad (WAD_RAY_RATIO / 2 - 1) == 0
#guard wadToRay (MAX / WAD_RAY_RATIO) == some (MAX / WAD_RAY_RATIO * WAD_RAY_RATIO)
#guard wadToRay (MAX / WAD_RAY_RATIO + 1) == none
#guard mulDivCeil 7 3 2 == some 11

-- exact overflow boundaries: `a * b + HALF_RAY ≤ MAX` for `rayMul`, `a * b ≤ MAX` for the floor
-- and ceiling variants, `a * RAY + b / 2 ≤ MAX` for `rayDiv`
#guard rayMul ((MAX - RAY / 2) / 3) 3 |>.isSome
#guard rayMul ((MAX - RAY / 2) / 3 + 1) 3 == none
#guard rayMulFloor (MAX / 3) 3 |>.isSome
#guard rayMulFloor (MAX / 3 + 1) 3 == none
#guard rayDiv ((MAX - 1) / RAY) 2 |>.isSome
#guard rayDiv ((MAX - 1) / RAY + 1) 2 == none
#guard rayDivCeil (MAX / RAY) 7 |>.isSome
#guard rayDivCeil (MAX / RAY + 1) 7 == none

/-! ## `MathUtils` -/

#guard calculateLinearInterest RAY 0 SECONDS_PER_YEAR == some (2 * RAY)   -- 100% for a year
#guard calculateCompoundedInterest RAY 0 0 == some RAY
-- 100% for a year: 1 + 1 + 1/2 + 1/6, with the library's rounding
#guard calculateCompoundedInterest RAY 0 SECONDS_PER_YEAR ==
  some (RAY + RAY + (RAY * (RAY / 2 + (RAY * (RAY / 6) + RAY / 2) / RAY) + RAY / 2) / RAY)
#guard calculateCompoundedInterest RAY 5 4 == none                         -- now < last

/-! ## The deployed Pool at block 26243228 (timestamp 1792612775) -/

/-- `block.timestamp`. -/
def now₀ : ℕ := 1792612775

-- WETH (`getReserveData`): liquidityIndex, currentLiquidityRate, variableBorrowIndex,
-- currentVariableBorrowRate, lastUpdateTimestamp
/-- WETH `liquidityIndex`. -/
def wethLI : ℕ := 1072234718374827704762277692
/-- WETH `currentLiquidityRate`. -/
def wethLR : ℕ := 12962979977749697337695696
/-- WETH `variableBorrowIndex`. -/
def wethVBI : ℕ := 1109016394188578893200168790
/-- WETH `currentVariableBorrowRate`. -/
def wethVBR : ℕ := 19331548153312252050987870
/-- WETH `lastUpdateTimestamp`. -/
def wethTs : ℕ := 1792612415

-- `getReserveNormalizedIncome(WETH)` and `getReserveNormalizedVariableDebt(WETH)`
#guard ((calculateLinearInterest wethLR wethTs now₀).bind (rayMul · wethLI)) ==
  some 1072234877043288729202654762
#guard ((calculateCompoundedInterest wethVBR wethTs now₀).bind (rayMul · wethVBI)) ==
  some 1109016638926092507888097516
-- aWETH / variableDebtWETH `totalSupply()` from `scaledTotalSupply()`
#guard rayMulFloor 2046197723505244072258514 1072234877043288729202654762 ==
  some 2194004564468902685820994
#guard rayMulCeil 1560731335827539298976632 1109016638926092507888097516 ==
  some 1730877020326088178100008

/-- USDC `liquidityIndex`. -/
def usdcLI : ℕ := 1190524192324904896679502649
/-- USDC `currentLiquidityRate`. -/
def usdcLR : ℕ := 37922086334905249013030192
/-- USDC `variableBorrowIndex`. -/
def usdcVBI : ℕ := 1254942360192142119435452025
/-- USDC `currentVariableBorrowRate`. -/
def usdcVBR : ℕ := 44912495513042383504743541
/-- USDC `lastUpdateTimestamp`. -/
def usdcTs : ℕ := 1792612655

#guard ((calculateLinearInterest usdcLR usdcTs now₀).bind (rayMul · usdcLI)) ==
  some 1190524364117755753370463532
#guard ((calculateCompoundedInterest usdcVBR usdcTs now₀).bind (rayMul · usdcVBI)) ==
  some 1254942574661692870720202148
#guard rayMulFloor 2010512262023252 1190524364117755753370463532 == some 2393563832296182
#guard rayMulCeil 1789459246953324 1254942574661692870720202148 == some 2245668594623779

/-! ## The backing invariant on the live reserves

`ReserveState.Solvent 0` evaluated on the stored state (at its `lastUpdateTimestamp`):
`(scaledTotalSupply + accruedToTreasury) · liquidityIndex` vs
`(virtualUnderlyingBalance + deficit) · RAY + scaledVariableDebt · variableBorrowIndex`.
It does **not** hold at this block: the aToken holders and the treasury are owed about
1.18 WETH (`5.4e-7` of the supply) and 287 USDC (`1.2e-7`) more than the reserve accounts for.
The model's theorems show that no modelled operation creates such a gap beyond the per-accrual
rounding slack, so it comes from what the model leaves out (the reserves' history under older
versions and rounding rules, the strategy's rounding, flash loans, …). -/

/-- `(S + T)·I - ((V + deficit)·RAY + D·B)` for the stored reserve, as an integer. -/
def backingGap (S T I V F D B : ℕ) : Int :=
  ((S + T) * I : ℕ) - (((V + F) * RAY + D * B : ℕ) : Int)

-- WETH: scaledTotalSupply, accruedToTreasury, liquidityIndex, virtualUnderlyingBalance,
-- deficit, scaled variable debt, variableBorrowIndex
#guard backingGap 2046197723505244072258514 45227915800480417217 wethLI
  410210458252136274548108 52964453912595963038573 1560731335827539298976632 wethVBI ==
  1184222106089346625981642811783512475985377572
#guard backingGap 2010512262023252 84098210844 usdcLI 147995108111101 1604836 1789459246953324
  usdcVBI == 287303895951178855429188486475839204

end QEDefi.Aave.Tests
