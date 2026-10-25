# Aave v3.7 core accounting model (`QEDefi.Aave`)

A model of the Aave v3 Ethereum Core Pool's accounting in `qedefi/QEDefi/Aave/`, ℕ-valued with
the deployed code's revert conditions as `none`, and machine-checked invariants. It is an
abstract model (like `QEDefi.ERC20`), not yet refined against the bytecode.

## Version modelled

Read from Ethereum mainnet at block ~26243030 (October 2026):

| Contract | Address | Version |
|---|---|---|
| Pool proxy | `0x87870Bca3F3fD6335C3F4ce8392D69350B4fA4E2` | |
| Pool implementation (EIP-1967 slot) | `0x728a138a4823392c2efa55e028d434f526fe03cf` | `PoolInstance`, `POOL_REVISION = 11` (Aave v3.7, `aave-v3-origin`) |
| aWETH implementation | `0xadc45df3cf1584624c97338bef33363bf5b97ada` | `ATOKEN_REVISION = 5` |
| variableDebtWETH implementation | `0xb27c52c7f84819e3157993489741cb60786ae330` | `DEBT_TOKEN_REVISION = 5` |
| Interest rate strategy | `0x9ec6F08190DeA04A54f8Afc53Db96134e5E3FdFB` | `DefaultReserveInterestRateStrategyV2` (not modelled, a parameter) |

Sources: Sourcify (`/server/v2/contract/1/<impl>?fields=sources`); the pinned targets and their
verified sources are in `contracts/mainnet/` ([aave-v3.md](aave-v3.md)). v3.7 features visible in the code: `TokenMath` floor/ceil rounding (v3.5+),
virtual balance accounting always on (v3.4+), `deficit` and bad-debt burning (v3.3+), stable
debt and isolation mode removed, liquidation grace periods, `MIN_LEFTOVER_BASE` dust rule.

## Files

| Module | Contents |
|---|---|
| `WadRayMath` | `WadRayMath` (`rayMul`, `rayDiv`, `wadMul`, `wadDiv`, `rayMulFloor/Ceil`, `rayDivFloor/Ceil`, `rayToWad`, `wadToRay`), `PercentageMath` (all six), `MathUtils.mulDivCeil`, each mirroring its assembly overflow test |
| `MathUtils` | `calculateLinearInterest` (checked), `calculateCompoundedInterest` (the `unchecked` 3-term Taylor expansion, `mod 2^256`) |
| `ScaledToken` | `ScaledBalanceTokenBase._mintScaled/_burnScaled`, `AToken._transfer`, `MintableIncentivizedERC20._mint/_burn` (uint120 balances, uint128 indexes, every checked operation) |
| `Reserve` | `ReserveState`, `ReserveConfig`, `ReserveCache`, `TokenMath`, `ReserveLogic.cache/updateState/_updateIndexes/_accrueToTreasury/updateInterestRatesAndVirtualBalance/getNormalizedIncome/getNormalizedDebt`; the invariant `Solvent`, `RateSound`, `accrualSlack` |
| `Accrual` | effect of `updateState`, index monotonicity, the accrual bound on `Solvent` |
| `Pool` | `Market`, `Env`; `supply`, `withdraw`, `transfer` (aToken), `borrow`, `repay` (underlying or aTokens), `mintToTreasury`, `liquidationCall`, `calculateUserAccountData` and the HF validations |
| `Frame` | per-entry-point frame lemmas: what each does to the reserves (`Step`, `Reaches`) |
| `Invariants` | `Tx`, `exec`, the three reserve invariants, initial state, the accrual counterexample |
| `Health` | health factor characterisation and the HF guarantees |
| `QEDefiTest/Aave` | `#guard` unit tests and a comparison with the live Pool at block 26243228 |

## Theorems

All proved (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound` only).

### 1. `WadRayMath` / `PercentageMath` (`WadRayMath.lean`)

Each library function is an instance of one of five shapes in the unit `U` (`RAY`, `WAD`,
`PERCENTAGE_FACTOR`); the theorems are stated for the shapes and specialised.

- `halfUpMul_eq_some` / `rayMul_eq_some`: `rayMul a b = some c ↔ a·b + RAY/2 ≤ MAX ∧ c = ⌊(a·b + RAY/2)/RAY⌋`; `rayMul_eq_none`: reverts iff `MAX < a·b + RAY/2` (same for `wadMul`, `percentMul`).
- `floorMul_eq_some`/`ceilMul_eq_some` (`rayMulFloor_eq_some`, `rayMulCeil_eq_some`): succeed iff `a·b ≤ MAX`, result `⌊a·b/U⌋` / `⌈a·b/U⌉`; `*_eq_none`.
- `halfUpDiv_eq_some` (`rayDiv_eq_some`, `wadDiv_eq_some`, for `b ≤ MAX`): `b ≠ 0 ∧ a·U + ⌊b/2⌋ ≤ MAX ∧ c = ⌊(a·U + ⌊b/2⌋)/b⌋`; `halfUpDiv_eq_none`.
- `floorDiv_eq_some`/`ceilDivU_eq_some` (`rayDivFloor_eq_some`, `rayDivCeil_eq_some`): `b ≠ 0 ∧ a·U ≤ MAX`, result `⌊a·U/b⌋` / `⌈a·U/b⌉`; `*_eq_none`.
- `mulDivCeil_eq_some`, `wadToRay_eq_some` (the `div(b, 1e9) ≠ a` test is exactly `a·1e9 > MAX`).
- Error bounds: `halfUpMul_bounds` (`|c·U − a·b| ≤ U/2`, precisely `c·U ≤ a·b + U/2 < (c+1)·U`), `floorMul_bounds`, `ceilMul_bounds`, `halfUpDiv_bounds`, `floorDiv_bounds`, `ceilDivU_bounds` and their `ray*` versions.
- Monotonicity: `halfUpMul_mono`, `floorMul_mono`, `ceilMul_mono` (both arguments; success of the larger call implies success of the smaller), `halfUpDiv_mono_left`, `floorDiv_mono_left`, `ceilDivU_mono_left` (numerator), `floorDiv_anti_right`, `ceilDivU_anti_right`, `halfUpDiv_anti_right` (denominator; for `rayDiv` only when both succeed: its overflow test gets *harder* as `b` grows).
- Rounding order: `floorMul_le_halfUpMul`, `halfUpMul_le_ceilMul`; `le_rayMul_of_ray_le` (a factor `≥ RAY` never decreases), `rayMul_ray`.

### 2. Interest and indexes (`MathUtils.lean`, `Accrual.lean`, `Invariants.lean`)

- `calculateLinearInterest_eq_some`: exact value `RAY + ⌊rate·Δt/SECONDS_PER_YEAR⌋` and revert conditions; `ray_le_calculateLinearInterest`; `calculateLinearInterest_mono` (rate and time).
- `calculateCompoundedInterest_eq_some`: a successful call never wraps despite `unchecked`: it returns `RAY` for `Δt = 0`, else `RAY + x + taylorTail x` with both `rayMul` overflow tests passing; `ray_le_calculateCompoundedInterest`; `calculateCompoundedInterest_mono` (rate and time, given no wrap of `rate·Δt`, true for `uint128` rates and `uint40` times); `calculateLinearInterest_le_compounded` (compounded ≥ linear).
- `updateState_spec`, `updateState_indexes_le`: `updateState` changes only the two indexes (upward), `accruedToTreasury` (upward) and the timestamp.
- `Market.exec_indexes_mono`: **no entry point decreases `liquidityIndex` or `variableBorrowIndex` of any reserve.**

### 3. Backing invariant (`Reserve.lean`, `Accrual.lean`, `Frame.lean`, `Invariants.lean`)

`ReserveState.Solvent k r` (all scaled by `RAY`):

    (aToken scaledTotalSupply + accruedToTreasury) · liquidityIndex
      ≤ (virtualUnderlyingBalance + deficit) · RAY + scaledVariableDebt · variableBorrowIndex + k

- `Market.exec_solvent_of_fresh`: **between accruals the invariant is exact**: if every reserve was already updated in this block, every entry point (supply, withdraw, borrow, repay with underlying or aTokens, aToken transfer, mintToTreasury, liquidation in both modes, including the deficit write and the protocol fee) preserves `Solvent k` for every `k`, in particular `k = 0`. This uses every v3.5+ rounding direction (`*_frame`, `burnDebtTokens_step`, `liquidateCollateral_allStep`, …).
- `ReserveState.updateState_solvent`: under `RateSound` (the stored liquidity rate does not pay more than borrowers pay net of the reserve factor, which the default strategy satisfies when `Solvent 0` holds, up to its own rounding), one accrual maps `Solvent k` to `Solvent (k + accrualSlack)`, `accrualSlack ≈ ⌈((S+T+D)·RAY + 2·D·B + RAY²)/(2·RAY)⌉`, about half a wei plus `(S+T+D)/(2·RAY) + D·B/RAY²` wei, and `0` when already updated in the block. The arithmetic core is `accrual_core`.
- `Market.exec_solvent`: both together for any transaction.
- `ReserveState.initial_invariants`: a freshly initialised reserve satisfies `Solvent 0`, `TokensWF`, `RateSound`.
- **Counterexample** `accrual_breaks_exact_backing`: the exact invariant is *not* preserved by accrual. A reserve with 2 scaled aTokens at index 1.5, 1 scaled debt unit at index 3 (tight: both sides `3·RAY`) and both rates `SECONDS_PER_YEAR` (so `RateSound` holds with equality) violates `Solvent 0` by `1` (i.e. `1e-27` wei) after one second, because `rayMul` rounds the liquidity index half up (`+2` instead of `+1.5`) while the debt gains exactly `3`; `Solvent 1` holds.

### 4. Σ scaled balances = scaled total supply (`ScaledToken.lean`, `Invariants.lean`)

- `ScaledToken.WF_mintScaled`, `WF_burnScaled`, `WF_transferScaled`: each token operation keeps `Σ balances = totalSupply`.
- `Market.exec_tokensWF`: **every entry point keeps it for the aToken and the variable debt token of every reserve** (transfers and liquidation transfers included).

### 5. Health factor (`Health.lean`)

- `healthFactorOf_eq_some`, `threshold_le_healthFactor_iff`: `HF = ⌊⌊(Σ coll·LT·WAD + ⌊debt/2⌋)/debt⌋/10⁴⌋`, and `HF ≥ 1 ↔ 10⁴·WAD·debt ≤ Σ coll·LT·WAD + ⌊debt/2⌋`. Because of the half-up `wadDiv`, a position with debt `≥ 2·WAD` base units (`2e18`, i.e. $20 billion at 8 decimals) can have `HF ≥ 1` with risk-adjusted collateral below its debt (by at most `debt/(2·WAD)` units of collateral·LT); irrelevant in practice.
- `borrow_healthFactor`: after a successful borrow, the `onBehalfOf` account's health factor in the **new** state, with the same transaction's prices, is `≥ 1e18`, its average LTV is non-zero and `totalCollateral ≥ ⌈totalDebt/ltv⌉`.
- `withdraw_healthFactor`, `transfer_healthFactor`: after withdrawing or transferring (a non-zero amount of) a reserve the user had enabled as collateral, if the user still borrows, the new health factor is `≥ 1e18`.
- `liquidationCall_healthFactor`: a successful liquidation implies that the borrower's health factor, after accruing the debt and collateral reserves, was `< 1e18`; `liquidationCall_healthFactor_of_fresh`: with both reserves already updated in the block, the pre-state health factor is `< 1e18`.

## Tests against the live Pool (`QEDefiTest/Aave.lean`)

At block 26243228 the model reproduces, from `getReserveData` read at the same block,
`getReserveNormalizedIncome` and `getReserveNormalizedVariableDebt` of WETH and USDC and the
`totalSupply()` of aWETH, variableDebtWETH, aUSDC and variableDebtUSDC, exactly.

**Observation.** Evaluating `Solvent 0` on the same live reserves fails: the aToken holders and
the treasury are owed about **1.18 WETH** (`5.4e-7` of the supply) and **287 USDC**
(`1.2e-7`) more than `virtualUnderlyingBalance + deficit + debt`. Counting the actual underlying
held by the aToken instead of the virtual balance covers USDC but leaves WETH about 1.02 WETH
short. The model shows that no modelled v3.7 operation opens such a gap (beyond about half a
wei per accrual). **Cause** (found by bisecting the gap over historical blocks with `eth_call`
and `eth_getStorageAt`): v3.5 (Pool revision 9, block 23,088,584) and v3.6 (revision 10, block
24,247,927) read both reserves' cache before updating either in `liquidationCall`; when the
collateral and the debt are the same asset the second update sees the stale timestamp and
credits the treasury its reserve-factor share of the debt interest twice, a claim with nothing
behind it. Every jump of the gap bisects to one block containing such a same-asset liquidation
and matches the excess treasury credit to within 1e-6 WETH; together they account for the
whole change since v3.4 (WETH +1.18, USDC +352 minus slow drift in the protocol's favour). v3.1
(block 20,398,674) had set the virtual balance so that the gap was −1 wei (WETH) and 0 (USDC),
so older history (half-up rounding, stable debt, portals, the migration) contributes nothing.
v3.7 (revision 11, block 25,199,939) restores the safe order, which is what this model
implements; since then the gap only grows with interest, because the rate strategy pays
suppliers on `V + deficit + debt` (so `RateSound` fails by the same relative amount): about
0.006 WETH predicted and 0.0056 observed over v3.7's first ~145 days. Other reserves with
same-asset liquidations in the same period (USDT, LINK) probably carry a gap too (not
measured). The WETH `deficit` (52,964.45 WETH) is unrelated: a single governance transaction
(block 25,037,701, 2026-05-06) wrote off two rsETH-collateralised WETH positions; the invariant
counts the deficit as backing, so it does not show in the gap.

## Not modelled / shortcomings

- **Oracles**: prices are an arbitrary `R → ℕ` given per transaction (Chainlink, sentinel,
  price caps not modelled); `10 ** decimals` is taken as exact (true for `decimals < 78`).
- **eMode** (categories, LTV/LT/bonus overrides, `isolated` categories, `ltvzeroBitmap`): users
  are assumed in eMode 0; `setUserEMode` not modelled.
- **Isolation mode / siloed borrowing**: removed in v3.7 (their configuration bits are marked
  deprecated in `ReserveConfiguration`), so there is nothing to model.
- **Caps**: supply and borrow caps are modelled (as in `validateSupply`/`validateBorrow`);
  `ReserveConfig` is static (no admin/configurator operations, no reserve listing/dropping).
- **Flash loans** (`flashLoan`, `flashLoanSimple`), `setUserUseReserveAsCollateral`,
  `eliminateReserveDeficit` (Umbrella), `aToken.transferFrom`/`permit`, credit delegation
  allowances (`borrow` on behalf of someone else is allowed unconditionally in the model),
  `rescueTokens`, `GHO`/facilitators, stable debt remnants: not modelled.
- **Liquidation (simplified)**: the full `executeLiquidationCall` path is modelled (close factor,
  `_calculateAvailableCollateralToLiquidate` with bonus and protocol fee, `MIN_LEFTOVER_BASE`
  dust rule, `hasNoCollateralLeft`, deficit, `receiveAToken` or burn, fee to treasury), except
  that a liquidation which would also sweep the borrower's bad debt in *other* reserves
  (`_burnBadDebt`) is outside the model (`none`).
- **Interest rate strategy**: an arbitrary function of `CalculateInterestRatesParams`; the
  accrual theorem assumes `RateSound`, which is not proved for
  `DefaultReserveInterestRateStrategyV2` (it holds up to the strategy's half-up rounding when
  `Solvent 0` holds, not at all once it fails).
- **Treasury and incentives**: the treasury is an address in the market; the incentives
  controller hook (`handleAction`) is assumed not to revert and to have no effect.
- **Underlying token**: `safeTransferFrom`/`safeTransfer` are not modelled (assumed to succeed
  and to move exactly the amount); only the virtual balance is tracked, so donations,
  fee-on-transfer or rebasing underlyings are outside the model; reentrancy is not considered.
- **Time**: `block.timestamp` is an input; `uint40(block.timestamp)` truncates as in the code;
  the theorems are per transaction (no trace-level statements about many blocks; the slack adds
  up per accrual).
- **Multi-reserve interaction**: `calculateUserAccountData` iterates over all reserves; the
  invariants are per reserve; no cross-reserve solvency notion (e.g. the protocol's total
  collateral vs debt) is stated.
- **Rounding gaps**: exact preservation only between accruals; the accrual slack is necessary
  (counterexample) and accumulates across accruals.
- **Events and gas**: not modelled.
- **Bytecode refinement**: not done. The model is written to make it possible (literal overflow
  tests, `uint120`/`uint128` casts and checked arithmetic as reverts), as `QEDefi.ERC20` was.
