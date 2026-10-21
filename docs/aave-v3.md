# Aave V3 (Ethereum Core market) as verification targets

The deployed bytecode of Aave V3's Core market on Ethereum mainnet, pinned as mainnet targets
(`contracts/mainnet/<Name>/`, generated modules `qedefi/Examples/AaveV3/Contracts/<Name>.lean`,
namespace `Examples.AaveV3.Contracts.<Name>`). The WETH reserve is the worked reserve. This file
records what the targets are, exactly, and what is proved about them
([Proved on the bytecode](#proved-on-the-bytecode)). Fetch and build workflow:
[contracts/README.md](../contracts/README.md#mainnet-targets).

## Deployment (read on chain at block 26,243,038–26,243,102, 2026-10-21)

| Role | Address | Notes |
|---|---|---|
| `PoolAddressesProvider` | `0x2f39d218133AFaB8F2B819B1066c7E434Ad94E9e` | market id `"Aave Ethereum Market"`; not a target |
| Pool (proxy) | `0x87870Bca3F3fD6335C3F4ce8392D69350B4fA4E2` | target `PoolProxy` |
| Pool implementation | `0x728a138A4823392C2EFA55e028d434F526fE03CF` | target `Pool` (`PoolInstance`, `POOL_REVISION = 11`), deployed at block 24,776,283 |
| PoolConfigurator (proxy) | `0x64b761D848206f447Fe2dd461b0c635Ec39EbB27` | admin of the token proxies; not a target |
| ACLManager | `0xc2aaCf6553D20d1e9d78E365AAba8032af9c85b0` | not a target |
| aEthWETH (proxy) | `0x4d5F47FA6A74757f35C14fD3a6Ef8E3C9BC514E8` | target `ATokenProxy` |
| AToken implementation | `0xadC45Df3cf1584624C97338BEF33363BF5b97AdA` | target `AToken` (`ATokenInstance`, `ATOKEN_REVISION = 5`), block 23,839,436 |
| variableDebtEthWETH (proxy) | `0xeA51d7853EEFb32b6ee06b1C12E6dcCA88Be0fFE` | target `VariableDebtTokenProxy` |
| VariableDebtToken implementation | `0xb27C52c7f84819e3157993489741cB60786aE330` | target `VariableDebtToken` (`DEBT_TOKEN_REVISION = 5`), block 23,839,437 |
| Interest-rate strategy | `0x9ec6F08190DeA04A54f8Afc53Db96134e5E3FdFB` | target `InterestRateStrategy` (`DefaultReserveInterestRateStrategyV2`, shared by all reserves: the Pool's immutable `RESERVE_INTEREST_RATE_STRATEGY`) |
| Treasury (Collector) | `0x464C71f6c2F760DdA6093dCB91C24c39e5d6e18c` | aToken immutable `TREASURY` |
| Rewards controller | `0x8164Cc65827dcFe994AB23944CBC90e0aa80bFcb` | token immutable `REWARDS_CONTROLLER` |
| WETH (underlying) | `0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2` | reserve id 0; target `Examples.WETH9.Contracts.WETH9` |

The sources are `aave-v3-origin` (tokens, libraries; comments refer to v3.4 and v3.5), the
Pool's from `aave-v3-origin-private`. The data provider reports no stable debt token for WETH
(stable debt was removed in v3.2); `getReserveData` still returns a "stable debt" address, read
from the addresses provider (`MOCK_STABLE_DEBT`), not from storage. The token implementations
compile the treasury and rewards controller as immutables (v3.4+), so the old storage fields
are deprecated (`_deprecated_treasury`, `__deprecated_incentivesController`, still holding the
old values on mainnet).

## Linked libraries (external, called by `DELEGATECALL`)

The Pool implementation links five libraries (Sourcify's `libraries` setting; the addresses
pushed by `PUSH20` in the code; the Pool's own getters `getPoolLogic()` … return the same).
Byte offsets of the 20-byte address in the Pool's runtime code (`Pool.linkedLibraries`):

| Library | Address | Offsets in `Pool` |
|---|---|---|
| `PoolLogic` | `0xD70593841C57cbaA04957cc3EAcE95708e48853b` | 2895, 8977, 9717, 9808, 10795, 12124, 12389, 13171 |
| `BorrowLogic` | `0x52Da0ce88202D1542543598D1e1e27F0d344726A` | 1374, 5022, 6725, 10295, 13943 |
| `SupplyLogic` | `0x584C7d8c4cb05304FE5Ac7fbc97f20A10Fb07564` | 2014, 3688, 4170, 4747, 6441, 7233, 7532, 8195, 9347 |
| `FlashLoanLogic` | `0x6D414cd0d5eAf8C43200ac0c325A7E2Ad83B8be6` | 1419, 6336, 11508 |
| `LiquidationLogic` | `0x96D5686812e33Ab509ECCDb38C89d15607B2a413` | 2086, 3167, 10200 |

`FlashLoanLogic` itself links `BorrowLogic` (offset 1385, a library `DELEGATECALL`ing a library;
`FlashLoanLogic.linkedLibraries`, from the hand-written `links.json`: Blockscout gives no
offsets). There is no `EModeLogic` or `BridgeLogic` in this version (the strategy contract's
compilation settings still list older ones; they are not linked into anything here). Each
library's code starts with `PUSH20 <its own address>` (call protection: state-changing
functions revert unless reached by `DELEGATECALL`), so a library must be installed at its
mainnet address.

Library entry points take storage pointers (`mapping(address => DataTypes.ReserveData) storage`
is passed as the slot number) and are absent from the library ABI; their selectors are
`librarySelectors.json` (solc's `methodIdentifiers`), e.g. `SupplyLogic.executeSupply`
`0x66656e4e`, `executeWithdraw` `0x186dea44`, `executeFinalizeTransfer` `0x8a5dadd1`,
`BorrowLogic.executeBorrow` `0x1e6473f9`, `executeRepay`
`0x38ca4d8a`, `FlashLoanLogic.executeFlashLoan` `0x2e7263ea`, `executeFlashLoanSimple`
`0xa1fe0e8d`, `LiquidationLogic.executeLiquidationCall` `0x83c1087d`.

## Proxies

All three proxies are Aave's `InitializableImmutableAdminUpgradeabilityProxy` (solc 0.8.10,
optimizer 100,000 runs, Berlin; Sourcify exact match; 2,400 B). The implementation is in the
EIP-1967 slot `0x360894a1…382bbc`; the admin is an immutable `_admin` (offsets 335, 417, 628,
1041, 1082, 1451): the PoolConfigurator for the token proxies (their code is identical, code
hash `0x82c6d153…`), the PoolAddressesProvider for the Pool proxy (code hash `0x96107dc4…`).
`admin()`, `implementation()`, `upgradeTo`, `upgradeToAndCall` run only for the admin
(`ifAdmin`); anyone else falls through to the `DELEGATECALL`, and the admin cannot use the
fallback. `initialize(address,bytes)` is not admin-guarded but reverts once the implementation
slot is set. The token state lives in the proxy's storage with the implementation's layout.

## Immutables (offsets in the runtime code, mainnet values)

Recorded in `immutables.json` (AST id → name, from a local recompilation) and generated as
`immutableRefs`/`immutableValues`; offsets from Sourcify's bytecode transformations, values
read from the code (the build checks they agree at every offset).

| Contract | Immutable | Offsets | Value |
|---|---|---|---|
| `AToken` | `POOL` | 911, 1658, 1828, 2038, 2209, 2346, 2465, 2546, 2820, 3082, 3418, 3569, 4859, 5093 | Pool proxy `0x8787…A4E2` |
| | `REWARDS_CONTROLLER` | 947, 1243, 3200, 7567, 7630, 7780, 8178, 8238 | `0x8164…bFcb` |
| | `TREASURY` | 702, 1120, 2579, 3167 | `0x464C…e18c` |
| | `_addressesProvider` | 3666 | `0x2f39…4E9e` |
| | `_chainId` | 5885 | 1 |
| `VariableDebtToken` | `POOL` | 781, 1899, 2132, 2414, 2570, 2777, 3020 | Pool proxy |
| | `REWARDS_CONTROLLER` | 841, 1090, 2655, 5403, 5493 | `0x8164…bFcb` |
| | `_chainId` | 2040 | 1 |
| `Pool` | `ADDRESSES_PROVIDER` | 19 offsets (1089 … 14964) | `0x2f39…4E9e` |
| | `RESERVE_INTEREST_RATE_STRATEGY` | 14 offsets (1287 … 13631) | `0x9ec6…FdFB` |
| `InterestRateStrategy` | `ADDRESSES_PROVIDER` | 238, 1130, 2043 | `0x2f39…4E9e` |
| proxies | `_admin` | 335, 417, 628, 1041, 1082, 1451 | configurator / provider |

The tokens are shared implementations: the reserve-specific parts (underlying, name, symbol,
decimals, domain separator) are proxy storage, set by `initialize`; `POOL`, the treasury and
the rewards controller are the same for every reserve of the market.

## Storage (proxy storage, implementation layout)

Hand-derived by C3 linearization (`storageLayout.json`), equal to solc's `storageLayout` output
for the verified standard-JSON input, and checked against mainnet in `layout-check.txt`
(slots by `eth_getStorageAt`, getters by `eth_call`, one block: AToken 84 OK, VariableDebtToken
88 OK, Pool 130 OK, strategy 12 OK, proxies 2 OK each; 0 failures; `CMP` rows are deprecated
fields without getters).

**AToken** (`ATokenInstance` → `AToken is VersionedInitializable, ScaledBalanceTokenBase,
EIP712Base, IAToken`):

| Slot | Variable |
|---|---|
| 0 | `lastInitializedRevision` (5 on aEthWETH) |
| 1 | `initializing` (bool) |
| 2–51 | `______gap` (`uint256[50]`) |
| 52 | `_userState`: `mapping(address => UserState)`, `UserState = {uint120 balance; DelegationMode delegationMode (byte 15); uint128 additionalData (bytes 16–31)}`: the **scaled** balance in the low 15 bytes, the user's last index (`getPreviousIndex`) in the high 16 |
| 53 | `_allowances`: `mapping(address => mapping(address => uint256))` |
| 54 | `_totalSupply` (scaled; `scaledTotalSupply()`) |
| 55, 56 | `_name`, `_symbol` (strings) |
| 57 | `_decimals` (byte 0), `__deprecated_incentivesController` (bytes 1–20) |
| 58 | `_nonces`: `mapping(address => uint256)` |
| 59 | `_domainSeparator` |
| 60 | `_deprecated_treasury` |
| 61 | `_underlyingAsset` |

`_userState[a]` at `keccak(pad(a) ‖ pad(52))`, `_allowances[o][s]` at
`keccak(pad(s) ‖ keccak(pad(o) ‖ pad(53)))`, `_nonces[a]` at `keccak(pad(a) ‖ pad(58))`.

**VariableDebtToken**: 0–51 as above; `_nonces` 52, `_domainSeparator` 53,
`_borrowAllowances` 54 (`[delegator][delegatee]`), `_underlyingAsset` 55, `_userState` 56,
`_allowances` 57 (unused: debt tokens are not transferable), `_totalSupply` 58, `_name` 59
(long string on mainnet: `"Aave Ethereum Variable Debt WETH"` is 32 bytes), `_symbol` 60,
`_decimals` + deprecated incentives controller 61, `__unusedGap` 62–64,
`__DEPRECATED_AND_NEVER_TO_BE_REUSED` 65.

**Pool**: 0–51 as above; `_reserves` 52 (`ReserveData`, 10 slots per reserve: configuration;
liquidityIndex | currentLiquidityRate; variableBorrowIndex | currentVariableBorrowRate;
deficit | lastUpdateTimestamp | id | liquidationGracePeriodUntil; aTokenAddress; deprecated
stable debt token; variableDebtTokenAddress; deprecated strategy; accruedToTreasury |
virtualUnderlyingBalance; two deprecated `uint128`), `_usersConfig` 53, `_reservesList` 54,
`_eModeCategories` 55 (3 slots), `_usersEModeCategory` 56, deprecated bridge fee 57,
`_flashLoanPremium` 58 (low 16 bytes; 5 bps on mainnet) | deprecated premium to protocol,
deprecated max stable size 59 (bytes 0–7) | `_reservesCount` 59 (bytes 8–9),
`_positionManager` 60.

**InterestRateStrategy**: `_interestRateData` 0: `mapping(address => InterestRateData)`, one
packed slot per reserve (`uint16 optimalUsageRatio`, `uint32 baseVariableBorrowRate`,
`uint32 variableRateSlope1`, `uint32 variableRateSlope2`, in bps).

## AToken entry points

| Selector | Function | Guard |
|---|---|---|
| `0xb3f1c93d` | `mint(address caller, address onBehalfOf, uint256 scaledAmount, uint256 index)` | `onlyPool` |
| `0xb18d6afd` | `burn(address from, address receiverOfUnderlying, uint256 amount, uint256 scaledAmount, uint256 index)` | `onlyPool` |
| `0x7df5bd3b` | `mintToTreasury(uint256 scaledAmount, uint256 index)` | `onlyPool` |
| `0x353b7b9a` | `transferOnLiquidation(address from, address to, uint256 amount, uint256 scaledAmount, uint256 index)` | `onlyPool` |
| `0x4efecaa5` | `transferUnderlyingTo(address target, uint256 amount)` | `onlyPool` |
| `0xa9059cbb` / `0x23b872dd` | `transfer` / `transferFrom` | calls `POOL.getReserveNormalizedIncome` and `POOL.finalizeTransfer` |
| `0x1da24f3e` / `0xb1bf962d` | `scaledBalanceOf` / `scaledTotalSupply` | views of slots 52, 54 |
| `0x70a08231` / `0x18160ddd` | `balanceOf` / `totalSupply` | scaled value × `POOL.getReserveNormalizedIncome(underlying)` |
| `0xd505accf` | `permit` | EIP-2612 with `_domainSeparator`, `_nonces` |
| `0x7fdd585f` | `initialize(address,address,uint8,string,string,bytes)` | `initializer` (revision 5) |
| `0xcea9d26f` | `rescueTokens(address,address,uint256)` | pool admin (ACLManager) |

There is no `handleRepayment` in this version (removed upstream). All 35 selectors, the events
and the custom errors are in the generated module (`selectors`, `events`, `errors`).

## Proved on the bytecode

`qedefi/Examples/AaveV3/AToken/` (namespace `Examples.AaveV3.AToken`), about the deployed AToken
implementation `AToken.runtimeCode` (immutables concrete in the code; `pool` = the Pool proxy).
Every theorem is a `Halts` statement for an arbitrary frame `m` with `Fresh AToken.runtimeCode m`:
any executing address (on mainnet the aToken proxy, reaching the implementation by
`DELEGATECALL`, so storage is the proxy's), any caller, world, `Crypto` and depth. It is a
top-level fact and a callee summary at once. `Code.lean` adds the kernel code table
(`code_table runtimeCode`, about 6 s).

Postconditions (`Basic.lean`): `Unchanged m mf` (world, transient storage, created accounts and
logs as in `m`); `RevertsWith out g m` (`REVERT` with data `out`, `Unchanged`, at most `g` gas);
`NoEffect g m` (`REVERT` with some data, `Unchanged`, at most `g` gas). `callerMustBePool` is the
revert data `0x54b39ce2` of `CallerMustBePool()`.

**Access control** (`Guard/<Function>.lean`, `Guard.lean`). solc runs the ABI decoder before the
`onlyPool` modifier, and every AToken function is non-payable.

| Theorem | Statement (hypotheses beyond `Fresh`, gas ≥ 3000, calldata size < 2^64) |
|---|---|
| `mint_reverts_of_not_pool` | selector `0xb3f1c93d`, ≥ 132 bytes, both address words clean, no value, caller ≠ `pool` → `RevertsWith callerMustBePool 3000` |
| `burn_reverts_of_not_pool` | the same for `0xb18d6afd`, ≥ 164 bytes, two address words |
| `mintToTreasury_reverts_of_not_pool` | the same for `0x7df5bd3b`, ≥ 68 bytes |
| `transferOnLiquidation_reverts_of_not_pool` | the same for `0x353b7b9a`, ≥ 164 bytes, two address words |
| `transferUnderlyingTo_reverts_of_not_pool` | the same for `0x4efecaa5`, ≥ 68 bytes, one address word |
| `<f>_noEffect_of_not_pool` (each of the five) | selector of `f`, any further calldata, any value, caller ≠ `pool` → `NoEffect 3000` (short calldata, dirty address words and value revert with empty data) |
| `poolOnly_noEffect` | selector ∈ `poolOnlySelectors` (the five), caller ≠ `pool` → `NoEffect 3000` |
| `poolOnly_sload_unchanged` | the same → revert, and every slot of the executing account (`_totalSupply` 54, `_userState` rows) unchanged |

`poolOnlySelectors_abi` ties the five selectors to the verified ABI.

**Views** (`State.lean`, `Views/Ledger.lean`, `Views/Addresses.lean`). Storage readings of the
executing account `t` in world `w`: `scaledBalance` (low 120 bits of `_userState[a]` at
`userStateSlot a = keccak(pad(a) ‖ pad(52))`), `previousIndex` (its high 128 bits),
`scaledTotalSupply` (slot 54), `underlyingAsset` (low 160 bits of slot 61). `Returns out g m`:
`RETURN` of `out`, `Unchanged`, at most `g` gas. Hypotheses: no value, the selector, calldata of
at least 4 (+32 per argument) bytes and < 2^64, an address argument a clean word
`Word.ofAddress a`, gas ≥ the bound.

| Theorem | Returns (gas bound) |
|---|---|
| `scaledBalanceOf_halts` | `ofWord (scaledBalance crypto w t a)` (3000) |
| `scaledTotalSupply_halts` | `ofWord (scaledTotalSupply w t)` (3000) |
| `getScaledUserBalanceAndSupply_halts` | `ofWord (scaledBalance …) ++ ofWord (scaledTotalSupply …)` (5000) |
| `getPreviousIndex_halts` | `ofWord (previousIndex crypto w t a)` (3000) |
| `POOL_halts`, `TREASURY_halts`, `RESERVE_TREASURY_ADDRESS_halts`, `REWARDS_CONTROLLER_halts` | `ofWord (Word.ofAddress pool / treasury / treasury / rewardsController)` (1000) |
| `UNDERLYING_ASSET_ADDRESS_halts` | `ofWord (underlyingAsset w t)` (3000) |
| `noEffect_of_value` | any calldata with value ≠ 0 → `NoEffect 100` (every function is non-payable) |

`viewSelectors_abi` and `immutables_eq` tie the selectors and immutables to the generated tables.

**`mint` by the Pool** (`Mint/Basic.lean`, `Mint/Success.lean`, `Mint/Effect.lean`). In this
version the Pool passes the *scaled* amount (`mint(caller, onBehalfOf, scaledAmount, index)`),
so no `rayDiv` happens in the token; `rayMulFloor` only computes the event amounts, and its
overflow guard and the checked subtractions are hypotheses. `mintWorld` is the storage after
the three writes (`_userState[u]` with `index` in bits 128–255, `_totalSupply + amt`,
`_userState[u]` with `balance + amt` in bits 0–119; `userWordIndexed`, `userWordMinted` are the
words exactly as the code computes them). `HandleActionOk rc t` is the **modelling assumption**
on the rewards controller: called by `t` without value with `handleAction(user, supply,
balance)` calldata, in any frame, its code `rc` succeeds and leaves `t`'s storage unchanged.

| Theorem | Statement |
|---|---|
| `mint_halts_ok` | Pool caller, no value, non-static frame, gas in `[10^6, 2^64)`, well-formed calldata `mint(c, u, amt, idx)`; `userStateSlot u ≠ 54`; `amt ≠ 0`, `scaledBalance u + amt < 2^120`, `idx < 2^128`, `(scaledBalance u + amt) · idx < 2^256`, `⌊scaledBalance u · previousIndex u / RAY⌋ ≤ ⌊scaledBalance u · idx / RAY⌋`, `scaledTotalSupply + amt < 2^256`; rewards controller: `HandleActionOk`, code size in `(0, 2^256)`, not a precompile, not EIP-7702-delegated, depth < 1024 → returns `iszero(scaledBalance u)`, and every slot of the executing account equals `mintWorld`'s (`MintOk`) |
| `mint_halts_effect` | the same → `MintEffect`: `scaledBalance u` and `scaledTotalSupply` both grow by `amt`, `previousIndex u = idx`, the delegation byte and every other slot unchanged |
| `mint_reverts_of_zero` | Pool caller, no value, well-formed calldata with `scaledAmount = 0` → `RevertsWith invalidMintAmount 3000` (`InvalidMintAmount()`, `0xccfad018`) |
| `mint_reverts_of_cast` | Pool caller, no value, non-static frame, gas ≥ 10^5, well-formed calldata with `scaledAmount ≥ 2^120` → the frame reverts (whichever check fails first: supply-side add, `rayMulFloor` guard, interest subtraction, `toUint128(index)`, `toUint120(amount)` after the index write) |
| `mintWorld_ledger` | `scaledBalance' u + supply = scaledBalance u + supply'` (the scaled ledger stays balanced) |
| `scaledBalance_mintWorld`, `scaledTotalSupply_mintWorld`, `previousIndex_mintWorld`, `delegation_mintWorld`, `sload_mintWorld_other`, `sload_mintWorld_account` | the field-by-field reading of `mintWorld` |

**`burn` by the Pool** (`Burn/Basic.lean`, `Burn/Success.lean`, `Burn/Effect.lean`). Two
external calls: the rewards controller (assumption `HandleActionOkCode`: as `HandleActionOk`,
and every account's code is unchanged, so that the underlying is still there) and the
underlying's `transfer(receiver, amount)` through `GPv2SafeERC20.safeTransfer` (assumption
`TransferOk ua t`: from `t`, without value, the code at `ua` returns the word `true` and leaves
`t`'s storage unchanged; in particular the aToken is assumed to hold enough underlying).
`burnWorld` mirrors `mintWorld` with `_totalSupply - amt` and `balance - amt`.

| Theorem | Statement |
|---|---|
| `burn_halts_ok` | Pool caller, no value, non-static frame, gas in `[5·10^6, 2^64)`, well-formed calldata `burn(u, r, amount, amt, idx)` with `r` ≠ the executing account; `userStateSlot u ∉ {54, 61}`; `amt ≠ 0`, `amt ≤ scaledBalance u`, `amt ≤ scaledTotalSupply`, `idx < 2^128`, `scaledBalance u · idx < 2^256`, interest not negative; rewards controller as for `mint` with `HandleActionOkCode`; underlying (`underlyingAddress`, slot 61) not a precompile, not delegated, `TransferOk` → returns `iszero(scaledBalance u - amt)`, storage = `burnWorld` (`BurnOk`); both event branches (`Mint` / `Burn`) |
| `burn_halts_effect` | the same → `BurnEffect`: `scaledBalance u` and `scaledTotalSupply` both shrink by `amt`, `previousIndex u = idx`, delegation byte and other slots unchanged |
| `burnWorld_ledger` | `scaledBalance' u + supply = scaledBalance u + supply'` |

**Not proved yet.** The effects of `mintToTreasury`, `transferOnLiquidation` and
`transferUnderlyingTo` with the Pool as caller; `burn` with `receiverOfUnderlying` = the token
itself (no transfer); the revert cases of `burn`; `transfer`, `transferFrom`, `balanceOf`,
`totalSupply` (they call the Pool's `getReserveNormalizedIncome` / `finalizeTransfer`, which
need summaries of the Pool proxy and implementation); `permit`, `approve`, `initialize`,
`rescueTokens` (calls the ACL manager). Build times (incremental, this machine): `Code` 6 s,
each `Guard/*` 3–4 s, `Views/*` 5–6 s, `Mint/Success` 19 s, `Mint/Revert` 14 s, `Burn/Success`
29 s, the rest about 1 s each.

Proof tools added in `Tactic.lean` (generic, candidates for `EvmLogic`): `wp_abstract`
(abstract the memory, gas, substate or world of a `WP` goal without `generalize`),
`access_bounds`, `step_extcodesize`, `step_returndatacopy`.

## Reproducibility

Every target is reproduced byte for byte by a local recompilation of the verified
standard-JSON input with the recorded compiler (0.8.27, 0.8.20 and 0.8.10, all in
`~/.svm`), up to the immutables, the libraries' call-protection address and the Pool's
library links, which then equal the deployed values (checked 2026-10-21; not part of the
build). Sourcify reports `match` (not `exact_match`) for the 0.8.27 contracts and has no
record of `BorrowLogic` and `FlashLoanLogic`, which are taken from Blockscout (partially
verified there).

## Test state (`genesis.json`)

`ATokenProxy`: implementation slot → the AToken implementation, revision 5, name/symbol/
decimals/underlying/domain separator as on mainnet, alice 100e18 and bob 50e18 scaled with
index 1 ray, scaled supply 150e18. `VariableDebtTokenProxy`: initialized, no debt.
`PoolProxy`: implementation and revision only (no reserves): balances and transfers of the
aToken need the WETH reserve's index from the Pool, so a test or proof of them must add the
reserve (10 slots, mainnet values in `Pool/layout-check.txt`) or summarize the Pool's
`getReserveNormalizedIncome`/`finalizeTransfer`.
