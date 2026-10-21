module

public import QEDefi.Aave.Reserve

/-!
# The Aave v3.7 Pool: supply, withdraw, borrow, repay, transfer, mintToTreasury, liquidation

A market of reserves `R` and accounts `A` (users and contracts share the address type): the
reserves' storage, their (static) configuration, the aToken addresses, the treasury, the
`_reservesList` order and the users' configuration bits (`isUsingAsCollateral`,
`isBorrowing`). Each entry point mirrors its `*Logic.execute*` function statement by statement
(`none` = revert), including `GenericLogic.calculateUserAccountData` and the health factor
checks, with `block.timestamp`, the oracle prices and the interest rate strategy given by the
environment `Env`.

Scope (see `docs/aave-v3-model.md`): users are in eMode 0 (no eMode categories); the underlying
token transfers (`safeTransferFrom`/`safeTransfer`) and the incentives controller are not
modelled (assumed to succeed; the protocol's own accounting uses `virtualUnderlyingBalance`);
credit delegation allowances for `borrow`/aToken allowances for `transferFrom` are not modelled;
a liquidation that would also burn the borrower's bad debt in *other* reserves
(`_burnBadDebt`) is outside the model (it is `none`).
-/

section

@[expose] public noncomputable section

namespace QEDefi.Aave
open QEDefi.Math

/-- `ValidationLogic.HEALTH_FACTOR_LIQUIDATION_THRESHOLD = 1e18`. -/
def HEALTH_FACTOR_LIQUIDATION_THRESHOLD : ℕ := 10 ^ 18

/-- `LiquidationLogic.DEFAULT_LIQUIDATION_CLOSE_FACTOR = 0.5e4`. -/
def DEFAULT_LIQUIDATION_CLOSE_FACTOR : ℕ := 5000

/-- `LiquidationLogic.CLOSE_FACTOR_HF_THRESHOLD = 0.95e18`. -/
def CLOSE_FACTOR_HF_THRESHOLD : ℕ := 95 * 10 ^ 16

/-- `LiquidationLogic.MIN_BASE_MAX_CLOSE_FACTOR_THRESHOLD = 2000e8`. -/
def MIN_BASE_MAX_CLOSE_FACTOR_THRESHOLD : ℕ := 2000 * 10 ^ 8

/-- `LiquidationLogic.MIN_LEFTOVER_BASE = MIN_BASE_MAX_CLOSE_FACTOR_THRESHOLD / 2`. -/
def MIN_LEFTOVER_BASE : ℕ := MIN_BASE_MAX_CLOSE_FACTOR_THRESHOLD / 2

/-- The Pool's storage, restricted to what the modelled operations read and write. -/
structure Market (A R : Type) where
  /-- `_reserves[asset]` together with its tokens. -/
  reserves : R → ReserveState A
  /-- `_reserves[asset].configuration` (static). -/
  config : R → ReserveConfig
  /-- `_reserves[asset].aTokenAddress`. -/
  aTokenAddress : R → A
  /-- The aTokens' `RESERVE_TREASURY_ADDRESS`. -/
  treasury : A
  /-- `_reservesList` in id order. -/
  reservesList : List R
  /-- `_usersConfig[user].isUsingAsCollateral(id)`. -/
  usingAsCollateral : A → R → Bool
  /-- `_usersConfig[user].isBorrowing(id)`. -/
  borrowing : A → R → Bool

/-- What a transaction sees from outside the Pool's storage. -/
structure Env (R : Type) where
  /-- `block.timestamp`. -/
  now : ℕ
  /-- The oracle's `getAssetPrice` (base currency, 8 decimals for USD markets). -/
  price : R → ℕ
  /-- The interest rate strategy (`RESERVE_INTEREST_RATE_STRATEGY`), per reserve. -/
  irs : R → Strategy

/-- The values `calculateUserAccountData` returns. -/
structure AccountData where
  /-- Total collateral in base currency. -/
  totalCollateral : ℕ
  /-- Total debt in base currency. -/
  totalDebt : ℕ
  /-- Average LTV (bps). -/
  avgLtv : ℕ
  /-- Average liquidation threshold (bps). -/
  avgLiquidationThreshold : ℕ
  /-- Health factor (wad). -/
  healthFactor : ℕ
  /-- Whether some collateral has LTV 0. -/
  hasZeroLtvCollateral : Bool

/-- The loop accumulator of `calculateUserAccountData`. -/
structure AccountAcc where
  /-- `totalCollateralInBaseCurrency`. -/
  coll : ℕ
  /-- `totalDebtInBaseCurrency`. -/
  debt : ℕ
  /-- `avgLtv` before the division: `Σ collateral · ltv`. -/
  ltvSum : ℕ
  /-- `avgLiquidationThreshold` before the division: `Σ collateral · liquidationThreshold`. -/
  ltSum : ℕ
  /-- `hasZeroLtvCollateral`. -/
  zeroLtv : Bool

namespace Market

variable {A R : Type} [DecidableEq A] [DecidableEq R]

/-- Write one reserve's storage. -/
def setReserve (m : Market A R) (a : R) (r : ReserveState A) : Market A R :=
  { m with reserves := Function.update m.reserves a r }

/-- `userConfig.setUsingAsCollateral(id, asset, user, b)`. -/
def setCollateral (m : Market A R) (u : A) (a : R) (b : Bool) : Market A R :=
  { m with usingAsCollateral :=
      Function.update m.usingAsCollateral u (Function.update (m.usingAsCollateral u) a b) }

/-- `userConfig.setBorrowing(id, b)`. -/
def setBorrowing (m : Market A R) (u : A) (a : R) (b : Bool) : Market A R :=
  { m with borrowing := Function.update m.borrowing u (Function.update (m.borrowing u) a b) }

/-- `userConfig.isBorrowingAny()`. -/
def isBorrowingAny (m : Market A R) (u : A) : Bool := m.reservesList.any (m.borrowing u)

/-- `userConfig.isEmpty()`. -/
def isEmptyConfig (m : Market A R) (u : A) : Bool :=
  m.reservesList.all fun a => !(m.usingAsCollateral u a) && !(m.borrowing u a)

/-- `10 ** decimals`. -/
def assetUnit (m : Market A R) (a : R) : ℕ := 10 ^ (m.config a).decimals

/-! ## `GenericLogic.calculateUserAccountData` (eMode 0) -/

/-- One iteration of the loop of `calculateUserAccountData` for reserve `a`. -/
def accountStep (m : Market A R) (now : ℕ) (price : R → ℕ) (u : A) (acc : AccountAcc) (a : R) :
    Option AccountAcc :=
  let isColl := m.usingAsCollateral u a
  let isBorrowed := m.borrowing u a
  if !isColl && !isBorrowed then some acc else
  let r := m.reserves a
  let cfg := m.config a
  let p := price a
  let unit := m.assetUnit a
  (if isColl then
    (r.getNormalizedIncome now).bind fun ni =>
    (getATokenBalance (r.aToken.balance u) ni).bind fun bal =>
    if MAX < bal * p then none else                                   -- `* assetPrice`, checked
    let v := bal * p / unit
    if MAX < acc.coll + v then none else
    (if cfg.ltv = 0 then some (acc.ltvSum, true)
     else if MAX < v * cfg.ltv ∨ MAX < acc.ltvSum + v * cfg.ltv then none
     else some (acc.ltvSum + v * cfg.ltv, acc.zeroLtv)).bind fun lz =>
    if MAX < v * cfg.liquidationThreshold ∨ MAX < acc.ltSum + v * cfg.liquidationThreshold then
      none else
    some { acc with coll := acc.coll + v, ltvSum := lz.1, zeroLtv := lz.2,
                    ltSum := acc.ltSum + v * cfg.liquidationThreshold }
   else some acc).bind fun acc1 =>
  if isBorrowed then
    (r.getNormalizedDebt now).bind fun nd =>
    (getVTokenBalance (r.vToken.balance u) nd).bind fun d =>
    (mulDivCeil d p unit).bind fun dv =>
    if MAX < acc1.debt + dv then none else some { acc1 with debt := acc1.debt + dv }
  else some acc1

/-- `healthFactor = totalDebt == 0 ? MAX : avgLiquidationThreshold.wadDiv(totalDebt) / 100_00`. -/
def healthFactorOf (ltSum debt : ℕ) : Option ℕ :=
  if debt = 0 then some MAX else (wadDiv ltSum debt).map (· / PERCENTAGE_FACTOR)

/-- `GenericLogic.calculateUserAccountData` for a user in eMode 0. -/
def calculateUserAccountData (m : Market A R) (now : ℕ) (price : R → ℕ) (u : A) :
    Option AccountData :=
  if m.isEmptyConfig u then some ⟨0, 0, 0, 0, MAX, false⟩ else
  (m.reservesList.foldlM (m.accountStep now price u) ⟨0, 0, 0, 0, false⟩).bind fun acc =>
  (healthFactorOf acc.ltSum acc.debt).map fun hf =>
  ⟨acc.coll, acc.debt, if acc.coll ≠ 0 then acc.ltvSum / acc.coll else 0,
   if acc.coll ≠ 0 then acc.ltSum / acc.coll else 0, hf, acc.zeroLtv⟩

/-- `ValidationLogic.validateHealthFactor`: returns `hasZeroLtvCollateral`. -/
def validateHealthFactor (m : Market A R) (env : Env R) (u : A) : Option Bool :=
  (m.calculateUserAccountData env.now env.price u).bind fun ad =>
  if ad.healthFactor < HEALTH_FACTOR_LIQUIDATION_THRESHOLD then none else some ad.hasZeroLtvCollateral

/-- `ValidationLogic.validateHFAndLtv` (after a borrow). -/
def validateHFAndLtv (m : Market A R) (env : Env R) (u : A) : Option Unit :=
  (m.calculateUserAccountData env.now env.price u).bind fun ad =>
  if ad.avgLtv = 0 then none else
  if ad.healthFactor < HEALTH_FACTOR_LIQUIDATION_THRESHOLD then none else
  (percentDivCeil ad.totalDebt ad.avgLtv).bind fun x =>
  if ad.totalCollateral < x then none else some ()

/-- `ValidationLogic.validateHFAndLtvzero` (after a withdraw / transfer of `asset`). -/
def validateHFAndLtvzero (m : Market A R) (env : Env R) (asset : R) (u : A) : Option Unit :=
  (m.validateHealthFactor env u).bind fun z =>
  if z ∧ (m.config asset).ltv ≠ 0 then none else some ()

/-! ## Supply and withdraw (`SupplyLogic`) -/

/-- The supply cap test of `validateSupply`. -/
def supplyCapOk (cfg : ReserveConfig) (r : ReserveState A) (sa idx : ℕ) : Option Unit :=
  if cfg.supplyCap = 0 then some () else
  if MAX < r.aToken.totalSupply + sa + r.accruedToTreasury then none else
  (getATokenBalance (r.aToken.totalSupply + sa + r.accruedToTreasury) idx).bind fun v =>
  if cfg.supplyCap * 10 ^ cfg.decimals < v then none else some ()

/-- `SupplyLogic.executeSupply`: `supply(asset, amount, onBehalfOf)` by `user`. -/
def supply (m : Market A R) (env : Env R) (asset : R) (amount : ℕ) (user onBehalfOf : A) :
    Option (Market A R) :=
  let cfg := m.config asset
  let r := m.reserves asset
  (r.updateState (r.cache cfg) env.now).bind fun rc =>
  let r1 := rc.1
  let c1 := rc.2
  (getATokenMintScaledAmount amount c1.nextLiquidityIndex).bind fun sa =>
  if sa = 0 then none else                                            -- validateSupply
  if !cfg.active || cfg.paused || cfg.frozen then none else
  if onBehalfOf = m.aTokenAddress asset then none else
  (supplyCapOk cfg r1 sa c1.nextLiquidityIndex).bind fun _ =>
  (r1.updateInterestRatesAndVirtualBalance (env.irs asset) c1 amount 0).bind fun r2 =>
  -- `IERC20(asset).safeTransferFrom(user, aToken, amount)`: not modelled
  let _ := user
  (r2.aToken.mintScaled getATokenBalance onBehalfOf sa c1.nextLiquidityIndex).map fun res =>
  let m1 := m.setReserve asset { r2 with aToken := res.1 }
  if res.2 && cfg.ltv != 0 then m1.setCollateral onBehalfOf asset true else m1

/-- `SupplyLogic.executeWithdraw`: `withdraw(asset, amount, to)` by `user`; returns the amount
withdrawn. `amount = type(uint256).max` withdraws the whole balance. -/
def withdraw (m : Market A R) (env : Env R) (asset : R) (amount : ℕ) (user dst : A) :
    Option (Market A R × ℕ) :=
  let cfg := m.config asset
  let r := m.reserves asset
  if dst = m.aTokenAddress asset then none else
  (r.updateState (r.cache cfg) env.now).bind fun rc =>
  let r1 := rc.1
  let c1 := rc.2
  let sub := r1.aToken.balance user
  (if amount = MAX then (getATokenBalance sub c1.nextLiquidityIndex).map fun a => (sub, a)
   else (getATokenBurnScaledAmount amount c1.nextLiquidityIndex).map fun s => (s, amount)).bind
    fun sw =>
  if sw.1 = 0 then none else                                          -- validateWithdraw
  if sub < sw.1 then none else
  if !cfg.active || cfg.paused then none else
  (r1.updateInterestRatesAndVirtualBalance (env.irs asset) c1 0 sw.2).bind fun r2 =>
  (r2.aToken.burnScaled getATokenBalance user sw.1 c1.nextLiquidityIndex).bind fun res =>
  let m1 := m.setReserve asset { r2 with aToken := res.1 }
  if m.usingAsCollateral user asset then
    let m2 := if res.2 then m1.setCollateral user asset false else m1
    if m2.isBorrowingAny user then
      (m2.validateHFAndLtvzero env asset user).map fun _ => (m2, sw.2)
    else some (m2, sw.2)
  else some (m1, sw.2)

/-- aToken `transfer(dst, amount)` by `src` (`IncentivizedERC20.transfer` → `AToken._transfer`
→ `Pool.finalizeTransfer`). Does not update the reserve state. -/
def transfer (m : Market A R) (env : Env R) (asset : R) (src dst : A) (amount : ℕ) :
    Option (Market A R) :=
  if UINT120_MAX < amount then none else                               -- toUint120
  let r := m.reserves asset
  (r.getNormalizedIncome env.now).bind fun idx =>
  let before := r.aToken.balance src
  (getATokenTransferScaledAmount amount idx).bind fun sa =>
  (r.aToken.transferScaled getATokenBalance src dst sa idx).bind fun a' =>
  let m1 := m.setReserve asset { r with aToken := a' }
  if (m.config asset).paused then none else                           -- validateTransfer
  if src ≠ dst ∧ sa ≠ 0 ∧ m1.usingAsCollateral src asset then
    let m2 := if before = sa then m1.setCollateral src asset false else m1
    if m2.isBorrowingAny src then (m2.validateHFAndLtvzero env asset src).map fun _ => m2
    else some m2
  else some m1

/-! ## Borrow and repay (`BorrowLogic`) -/

/-- `BorrowLogic.executeBorrow`: `borrow(asset, amount, VARIABLE, _, onBehalfOf)` by `user`. -/
def borrow (m : Market A R) (env : Env R) (asset : R) (amount : ℕ) (user onBehalfOf : A) :
    Option (Market A R) :=
  let cfg := m.config asset
  let r := m.reserves asset
  (r.updateState (r.cache cfg) env.now).bind fun rc =>
  let r1 := rc.1
  let c1 := rc.2
  (getVTokenMintScaledAmount amount c1.nextVariableBorrowIndex).bind fun sd =>
  if sd = 0 then none else                                            -- validateBorrow
  (getVTokenBalance sd c1.nextVariableBorrowIndex).bind fun vamt =>
  if !cfg.active || cfg.paused || cfg.frozen then none else
  if !cfg.borrowingEnabled then none else
  (r1.getNormalizedIncome env.now).bind fun ni =>
  (getATokenBalance r1.aToken.totalSupply ni).bind fun aSupply =>       -- aToken.totalSupply()
  if aSupply < vamt then none else
  (if cfg.borrowCap = 0 then some () else
    if MAX < c1.currScaledVariableDebt + sd then none else
    (getVTokenBalance (c1.currScaledVariableDebt + sd) c1.nextVariableBorrowIndex).bind fun td =>
    if cfg.borrowCap * m.assetUnit asset < td then none else some ()).bind fun _ =>
  -- credit delegation allowance (`user ≠ onBehalfOf`) not modelled
  let _ := user
  (r1.vToken.mintScaled getVTokenBalance onBehalfOf sd c1.nextVariableBorrowIndex).bind fun res =>
  let r2 := { r1 with vToken := res.1 }
  let c2 := { c1 with nextScaledVariableDebt := res.1.totalSupply }
  let m1 := m.setBorrowing onBehalfOf asset true
  (r2.updateInterestRatesAndVirtualBalance (env.irs asset) c2 0 amount).bind fun r3 =>
  let m2 := m1.setReserve asset r3
  -- `aToken.transferUnderlyingTo(user, amount)`: not modelled
  (m2.validateHFAndLtv env onBehalfOf).map fun _ => m2

/-- `BorrowLogic.executeRepay`: `repay(asset, amount, VARIABLE, onBehalfOf)` by `user`
(`useATokens = false`) or `repayWithATokens(asset, amount, VARIABLE)` (`useATokens = true`,
`onBehalfOf = user`). Returns the amount repaid. -/
def repay (m : Market A R) (env : Env R) (asset : R) (amount : ℕ) (user onBehalfOf : A)
    (useATokens : Bool) : Option (Market A R × ℕ) :=
  if useATokens ∧ user ≠ onBehalfOf then none else                     -- entry point
  let cfg := m.config asset
  let r := m.reserves asset
  (r.updateState (r.cache cfg) env.now).bind fun rc =>
  let r1 := rc.1
  let c1 := rc.2
  let uds := r1.vToken.balance onBehalfOf
  (getVTokenBalance uds c1.nextVariableBorrowIndex).bind fun userDebt =>
  if amount = 0 then none else                                        -- validateRepay
  if amount = MAX ∧ user ≠ onBehalfOf then none else
  if !cfg.active || cfg.paused then none else
  if uds = 0 then none else
  (if useATokens ∧ amount = MAX then getATokenBalance (r1.aToken.balance user) c1.nextLiquidityIndex
   else some amount).bind fun pb0 =>
  let pb := if userDebt < pb0 then userDebt else pb0
  (getVTokenBurnScaledAmount pb c1.nextVariableBorrowIndex).bind fun sd =>
  (r1.vToken.burnScaled getVTokenBalance onBehalfOf sd c1.nextVariableBorrowIndex).bind fun res =>
  let r2 := { r1 with vToken := res.1 }
  let c2 := { c1 with nextScaledVariableDebt := res.1.totalSupply }
  (r2.updateInterestRatesAndVirtualBalance (env.irs asset) c2 (if useATokens then 0 else pb) 0).bind
    fun r3 =>
  let m1 := m.setReserve asset r3
  let m2 := if res.2 then m1.setBorrowing onBehalfOf asset false else m1
  if useATokens then
    (getATokenBurnScaledAmount pb c1.nextLiquidityIndex).bind fun sa =>
    (r3.aToken.burnScaled getATokenBalance user sa c1.nextLiquidityIndex).bind fun ares =>
    let m3 := m2.setReserve asset { r3 with aToken := ares.1 }
    if m3.usingAsCollateral onBehalfOf asset then
      let m4 := if ares.2 then m3.setCollateral user asset false else m3
      if m4.isBorrowingAny onBehalfOf then (m4.validateHealthFactor env user).map fun _ => (m4, pb)
      else some (m4, pb)
    else some (m3, pb)
  else some (m2, pb)                                -- `safeTransferFrom(user, aToken, pb)`

/-! ## `PoolLogic.executeMintToTreasury` -/

/-- One iteration of `executeMintToTreasury`. -/
def mintToTreasuryOne (m : Market A R) (env : Env R) (a : R) : Option (Market A R) :=
  if !(m.config a).active then some m else
  let r := m.reserves a
  if r.accruedToTreasury = 0 then some m else
  (r.getNormalizedIncome env.now).bind fun ni =>
  (getATokenBalance r.accruedToTreasury ni).bind fun _amountToMint =>
  (r.aToken.mintScaled getATokenBalance m.treasury r.accruedToTreasury ni).map fun res =>
  m.setReserve a { r with accruedToTreasury := 0, aToken := res.1 }

/-- `PoolLogic.executeMintToTreasury(assets)`. -/
def mintToTreasury (m : Market A R) (env : Env R) (assets : List R) : Option (Market A R) :=
  assets.foldlM (fun m a => m.mintToTreasuryOne env a) m

/-! ## `LiquidationLogic.executeLiquidationCall` -/

/-- `_calculateAvailableCollateralToLiquidate`: `(collateral to the liquidator, debt repaid,
protocol fee)`. -/
def calculateAvailableCollateralToLiquidate (protocolFee collPrice collUnit debtPrice debtUnit
    debtToCover collBalance bonus : ℕ) : Option (ℕ × ℕ × ℕ) :=
  if MAX < debtPrice * debtToCover ∨ MAX < debtPrice * debtToCover * collUnit ∨
    MAX < collPrice * debtUnit ∨ collPrice * debtUnit = 0 then none else
  let base := debtPrice * debtToCover * collUnit / (collPrice * debtUnit)
  (percentMulFloor base bonus).bind fun maxColl =>
  (if collBalance < maxColl then
    if MAX < collPrice * collBalance ∨ MAX < collPrice * collBalance * debtUnit ∨
      MAX < debtPrice * collUnit ∨ debtPrice * collUnit = 0 then none else
    (percentDivCeil (collPrice * collBalance * debtUnit / (debtPrice * collUnit)) bonus).map
      fun need => (collBalance, need)
   else some (maxColl, debtToCover)).bind fun cd =>
  if protocolFee = 0 then some (cd.1, cd.2, 0) else
  (percentDivFloor cd.1 bonus).bind fun x =>
  if cd.1 < x then none else
  (percentMulCeil (cd.1 - x) protocolFee).bind fun fee =>
  if cd.1 < fee then none else some (cd.1 - fee, cd.2, fee)

/-- `_burnDebtTokens` on the debt reserve: returns the new reserve, the cache with the new
`nextScaledVariableDebt`, and `noMoreDebt`. -/
def burnDebtTokens (irs : Strategy) (r : ReserveState A) (c : ReserveCache) (borrower : A)
    (debt actual : ℕ) (noColl : Bool) : Option (ReserveState A × ReserveCache × Bool) :=
  (if debt ≠ 0 then
    (getVTokenBurnScaledAmount (if noColl then debt else actual) c.nextVariableBorrowIndex).bind
      fun sd =>
    (r.vToken.burnScaled getVTokenBalance borrower sd c.nextVariableBorrowIndex).map fun res =>
    (({ r with vToken := res.1 } : ReserveState A),
      ({ c with nextScaledVariableDebt := res.1.totalSupply } : ReserveCache), res.2)
   else some (r, c, true)).bind fun t =>
  if debt < actual then none else                                    -- outstandingDebt
  (if noColl ∧ debt - actual ≠ 0 then
    if UINT128_MAX < debt - actual ∨ UINT128_MAX < t.1.deficit + (debt - actual) then none
    else some { t.1 with deficit := t.1.deficit + (debt - actual) }
   else some t.1).bind fun r2 =>
  (r2.updateInterestRatesAndVirtualBalance irs t.2.1 actual 0).map fun r3 => (r3, t.2.1, t.2.2)

/-- The collateral leg of a liquidation: with `receiveAToken`, `transferOnLiquidation` of the
seized aTokens to the liquidator; otherwise `_burnCollateralATokens` (rates and virtual balance
update of the collateral reserve, then burn; `nextScaledDebt` is the debt reserve's new scaled
debt, used when both assets are the same). -/
def liquidateCollateral (m : Market A R) (env : Env R) (collAsset debtAsset : R)
    (borrower liquidator : A) (receiveAToken : Bool) (cc1 : ReserveCache) (nextScaledDebt collLiq : ℕ) :
    Option (Market A R) :=
  if receiveAToken then
    (getATokenTransferScaledAmount collLiq cc1.nextLiquidityIndex).bind fun st =>
    ((m.reserves collAsset).aToken.transferScaled getATokenBalance borrower liquidator st
      cc1.nextLiquidityIndex).map fun a' =>
    m.setReserve collAsset { m.reserves collAsset with aToken := a' }
  else
    let cc2 := if collAsset = debtAsset then { cc1 with nextScaledVariableDebt := nextScaledDebt }
      else cc1
    ((m.reserves collAsset).updateInterestRatesAndVirtualBalance (env.irs collAsset) cc2 0
      collLiq).bind fun rc2 =>
    (getATokenBurnScaledAmount collLiq cc1.nextLiquidityIndex).bind fun sb =>
    (rc2.aToken.burnScaled getATokenBalance borrower sb cc1.nextLiquidityIndex).map fun res =>
    m.setReserve collAsset { rc2 with aToken := res.1 }

/-- The protocol fee leg of a liquidation: `transferOnLiquidation` of `fee` (capped at the
borrower's scaled balance) to the treasury. -/
def transferLiquidationFee (m : Market A R) (collAsset : R) (borrower : A) (idx fee : ℕ) :
    Option (Market A R) :=
  if fee ≠ 0 then
    let rcx := m.reserves collAsset
    (getATokenTransferScaledAmount fee idx).bind fun sf0 =>
    let bal := rcx.aToken.balance borrower
    (if bal < sf0 then (getATokenBalance bal idx).map fun f => (bal, f)
     else some (sf0, fee)).bind fun sf =>
    (rcx.aToken.transferScaled getATokenBalance borrower m.treasury sf.1 idx).map fun a' =>
    m.setReserve collAsset { rcx with aToken := a' }
  else some m

/-- `LiquidationLogic.executeLiquidationCall` by `liquidator` (eMode 0, simplified: the
`_burnBadDebt` sweep over the borrower's other debt reserves is outside the model). -/
def liquidationCall (m : Market A R) (env : Env R) (collAsset debtAsset : R)
    (borrower liquidator : A) (debtToCover : ℕ) (receiveAToken : Bool) : Option (Market A R) :=
  let now := env.now
  let cfgD := m.config debtAsset
  let cfgC := m.config collAsset
  let rd := m.reserves debtAsset
  (rd.updateState (rd.cache cfgD) now).bind fun dc =>
  let m1 := m.setReserve debtAsset dc.1
  let cd1 := dc.2
  let rc := m1.reserves collAsset
  (rc.updateState (rc.cache cfgC) now).bind fun cc =>
  let m2 := m1.setReserve collAsset cc.1
  let cc1 := cc.2
  (m2.calculateUserAccountData now env.price borrower).bind fun ad =>
  let scaledColl := (m2.reserves collAsset).aToken.balance borrower
  (getATokenBalance scaledColl cc1.nextLiquidityIndex).bind fun collBal =>
  (getVTokenBalance ((m2.reserves debtAsset).vToken.balance borrower)
    cd1.nextVariableBorrowIndex).bind fun bd =>
  -- validateLiquidationCall
  if borrower = liquidator then none else
  if !cfgC.active || !cfgD.active then none else
  if cfgC.paused || cfgD.paused then none else
  if ¬((m2.reserves collAsset).liquidationGracePeriodUntil < now % TS40 ∧
      (m2.reserves debtAsset).liquidationGracePeriodUntil < now % TS40) then none else
  if HEALTH_FACTOR_LIQUIDATION_THRESHOLD ≤ ad.healthFactor then none else
  if !(m.usingAsCollateral borrower collAsset) then none else
  if bd = 0 then none else
  let pC := env.price collAsset
  let pD := env.price debtAsset
  let uC := m.assetUnit collAsset
  let uD := m.assetUnit debtAsset
  (mulDivCeil bd pD uD).bind fun bdBase =>
  if MAX < collBal * pC then none else
  let collBase := collBal * pC / uC
  (if MIN_BASE_MAX_CLOSE_FACTOR_THRESHOLD ≤ collBase ∧ MIN_BASE_MAX_CLOSE_FACTOR_THRESHOLD ≤ bdBase ∧
      CLOSE_FACTOR_HF_THRESHOLD < ad.healthFactor then
    (percentMul ad.totalDebt DEFAULT_LIQUIDATION_CLOSE_FACTOR).bind fun tdl =>
    if tdl < bdBase then (if MAX < tdl * uD ∨ pD = 0 then none else some (tdl * uD / pD))
    else some bd
   else some bd).bind fun maxLiq =>
  let actual0 := if maxLiq < debtToCover then maxLiq else debtToCover
  (calculateAvailableCollateralToLiquidate cfgC.liquidationProtocolFee pC uC pD uD actual0 collBal
    cfgC.liquidationBonus).bind fun cdf =>
  let collLiq := cdf.1
  let actual := cdf.2.1
  let fee := cdf.2.2
  -- dust
  (if actual < bd ∧ collLiq + fee < collBal then
    (mulDivCeil (bd - actual) pD uD).bind fun dl =>
    if MAX < (collBal - collLiq - fee) * pC then none else
    if MIN_LEFTOVER_BASE ≤ dl ∧ MIN_LEFTOVER_BASE ≤ (collBal - collLiq - fee) * pC / uC then some ()
    else none
   else some ()).bind fun _ =>
  -- hasNoCollateralLeft
  (getATokenBurnScaledAmount collLiq cc1.nextLiquidityIndex).bind fun s1 =>
  (getATokenTransferScaledAmount fee cc1.nextLiquidityIndex).bind fun s2 =>
  if MAX < s1 + s2 then none else
  let consumed := if scaledColl < s1 + s2 then scaledColl else s1 + s2
  (getATokenBalance consumed cc1.nextLiquidityIndex).bind fun cbal =>
  if MAX < cbal * pC then none else
  let noColl := cbal * pC / uC == ad.totalCollateral
  let m3 := if consumed == scaledColl || noColl then m2.setCollateral borrower collAsset false
    else m2
  (burnDebtTokens (env.irs debtAsset) (m3.reserves debtAsset) cd1 borrower bd actual noColl).bind
    fun dres =>
  let m4 := m3.setReserve debtAsset dres.1
  let m5 := if dres.2.2 then m4.setBorrowing borrower debtAsset false else m4
  (m5.liquidateCollateral env collAsset debtAsset borrower liquidator receiveAToken cc1
    dres.2.1.nextScaledVariableDebt collLiq).bind fun m6 =>
  (m6.transferLiquidationFee collAsset borrower cc1.nextLiquidityIndex fee).bind fun m7 =>
  -- `_burnBadDebt` over other reserves: outside the model
  if noColl && m7.isBorrowingAny borrower then none else
  -- `IERC20(debtAsset).safeTransferFrom(liquidator, aToken, actual)`: not modelled
  some m7

end Market

end QEDefi.Aave
end

end
