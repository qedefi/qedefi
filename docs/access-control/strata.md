# Strata USDe CDO: actor and authority model as deployed

Snapshot: `contracts/snapshots/StrataUSDe/`, Ethereum mainnet, block 26239549
(2026-10-21 07:42:35 UTC), fork Osaka, 27 accounts, 160 slots, 162 recorded calls
(2 hand-written seeds plus every argument-free view of the 8 targets, from `autoViews`).
Everything below comes from that directory (state.json, calls.json, code/, the verified sources,
verification.json) plus a keccak computation. The repo was not modified. Helper scripts
(pure-Python keccak, ABI selector dump) are in `scratchpad/tools/`.

Notation: "S" means the snapshot determines it (storage slot or recorded call). "V" means
verification metadata (constructor args, deployer), which is historical and not current state.
"U" means unknowable from the snapshot.

> Correction to the task text: the ERC-1967 implementation slot is
> `0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc`. The value given in the task
> (`…492e993ee8e9…`) is wrong and 63 digits long. `Snapshot/Fetch.lean` has the correct one.

---

## 1. Inventory

### 1.1 Strata system (8 proxies, 7 distinct implementations, 1 helper)

All 8 targets are **OpenZeppelin v5.2 `TransparentUpgradeableProxy`** (solc 0.8.28, 813-byte
runtime). The OZ v5 pattern applies: each proxy's constructor deploys **its own `ProxyAdmin`**
(`new ProxyAdmin(initialOwner)`) and stores that address as an **immutable** `_admin`. Routing
reads the immutable. The ERC-1967 admin slot is only written once, for information. I checked
that the immutable embedded in each proxy's bytecode (PUSH32) equals the admin slot value.

The Blockscout source trees contain `contracts/HashKeyChainStakingProxy.sol`, and the Sourcify tree of
srUSDe contains an unrelated "Ailey/Genesis" project. These are **red herrings**. The explorers
matched the bytecode against a foreign compilation of the same OZ file. The deployed contract
is plain `@openzeppelin/contracts/proxy/transparent/TransparentUpgradeableProxy.sol:TransparentUpgradeableProxy`
(Sourcify fullyQualifiedName). Its constructor args (V) show `initialOwner = 0x296400d8…` (the
deployer) and init calldata.

| Label | Proxy | Impl (S, ERC-1967 slot) | Impl contract | ProxyAdmin (S, immutable = slot) |
|---|---|---|---|---|
| srUSDe (Senior tranche, "Strata Senior USDe") | 0x3d7d6fdf07ee548b939a80edbc9b2256d0cdc003 | 0xe894055ca1c73648927e225f3ca38ed48e30210b | `Tranche` | 0x30a17d6bcbdbf1579d6fbba453acf776d01fbb50 |
| jrUSDe (Junior tranche, "Strata Junior USDe") | 0xc58d044404d8b14e953c115e67823784dea53d8f | 0xe91869f96806b480dd61d57e17919068d35ac09c | `Tranche` (same code hash `00a67719…`) | 0x89d2573471dc0bf81c7c553fffc1e31ce9e75bf1 |
| USDeCDO | 0x908b3921aae4fc17191d382bb61020f2ee6c0e20 | 0xb3d4f2c2123f8c3ca85ae7a6d48aa2ef049c79ba | `StrataCDO` | 0xcab791d0d44ebac17378ff2af6356c012f15c9e6 |
| USDeAccounting | 0xa436c5dd1ba62c55d112c10cd10e988bb3355102 | 0x5a8d34d785b5008cce9b9f4aaa0e445f6959cbff | `Accounting` | 0x25a733feba393a48c07a76441777324b471d212e |
| SUSDeStrategy | 0xdbf4fb6c310c1c85d0b41b5dbca06096f2e7099f | 0x2b9796606c8480312a572742c00f606ef4adb107 | `sUSDeStrategy` (immutables sUSDe, USDe) | 0x32d0d70a8da4c0c2f354a986fd3738afe92542f7 |
| USDeAprFeeds | 0x2bb416614d740e5313aa64a0e3e419b39e800ec2 | 0x74188a2a8a5177dd217a8149f1fb1370240fbadc | `AprPairFeed` | 0xe60442f1a12ec03e22ddd3bc5fea62b7bd89d6df |
| ERC20Cooldown | 0xd6dad17d025cddded27305aebab8b277996a6faf | 0x73dfde427d6f9271a451dd01415c8f26e6292219 | `ERC20Cooldown` | 0xed6c7b379f73df0618406d263b13b2386e398166 |
| UnstakeCooldown | 0x735eddf50ca2371aa48466469c742e684c610f74 | 0xd2843c620d188796b031d805fd869b597f6f3451 | `UnstakeCooldown` (EIP-1167 `Clones` factory; proxy nonce 0x8dc, so about 2266 clones created) | 0x4b47433703687cc49ddc61b2d8ae1adfacd55bcd |
| (helper) AaveAprPairProvider | 0x1c137776e04803f807616c382abba12d9bf0af73 | not a proxy | `AaveAprPairProvider`: no access control, no setters (aave=Pool 0x87870b…, sUSDe, benchmarks [USDC, USDT]) | none |

Implementations have changed since deployment (V vs S): for example, the CDO was deployed with impl
0x30faefa3… and is now 0xb3d4f2c2…, and the feed was initialised with provider 0xaff405c3… and now
uses 0x1c137776…. Upgrades have happened, so the ProxyAdmin keys are live.

### 1.2 External dependencies reached by the recorded calls (not Strata-controlled)

| Address | Contract | Pattern | Relevance |
|---|---|---|---|
| 0x4c9edd5852cd905f086c759e8383e09bff1e68b3 | Ethena `USDe` (0.8.19) | not a proxy; `Ownable2Step` (renounce disabled), single `minter` | base asset of both tranches |
| 0x9d39a5de30e57443bff2a8307a4256c8797a3497 | Ethena `StakedUSDeV2` (sUSDe) | not a proxy; **`SingleAdminAccessControl`** (two-step single admin over OZ 4.x AccessControl) | Strategy holds 18.37 M sUSDe (S: `_balances[strategy]`, slot `keccak(strategy‖4)`) |
| 0x87870bca3f3fd6335c3f4ce8392d69350b4fa4e2 | Aave v3 Pool proxy | **Aave `InitializableImmutableAdminUpgradeabilityProxy`**, immutable admin = PoolAddressesProvider 0x2f39d218… | read by AaveAprPairProvider (APR target) |
| 0x728a138a4823392c2efa55e028d434f526fe03cf | Aave `PoolInstance` | Pool implementation | |
| 0x98c23e9d8f34fefb1b7bd6a91b7ff122f4e16f5c / 0x23878914efe38d27c4d67ab83ed1b93a74d4086a | aUSDC / aUSDT proxies | Aave immutable-admin proxy, admin = 0x64b761d848206f447fe2dd461b0c635ec39ebb27 (Aave PoolConfigurator, not in snapshot) | `totalSupply` read for weighting |
| 0xadc45df3cf1584624c97338bef33363bf5b97ada | Aave `ATokenInstance` | aToken implementation | |
| 0x2f39d218133afab8f2b819b1066c7e434ad94e9e | Aave `PoolAddressesProvider` | `Ownable`; admin of the Pool proxy | |

The snapshot does **not** contain the ACM, the owner, any ProxyAdmin, the TwoStepConfigManager,
the treasury, or any UnstakeCooldown clone or handler implementation. No recorded call
touched them (§4).

---

## 2. Access-control mechanisms (exact source, all from the verified impls)

### 2.1 `contracts/governance/AccessControlled.sol` (identical bytes in all 7 impls, md5 303ce2eb…)

```solidity
abstract contract AccessControlled is Initializable, Ownable2StepUpgradeable, ReentrancyGuardUpgradeable {
  bytes32 PAUSER_ROLE, UPDATER_CDO_APR_ROLE, UPDATER_FEED_ROLE, UPDATER_STRAT_CONFIG_ROLE,
          RESERVE_MANAGER_ROLE, COOLDOWN_WORKER_ROLE, PROPOSER_CONFIG_ROLE   // keccak256(name)
  IAccessControlManager public acm;      // slot 0
  address public twoStepConfigManager;   // slot 1
  uint256[48] __gap;                     // slots 2..49
  constructor() { _disableInitializers(); }
  modifier onlyRole(bytes32 role) { _checkRole(role, _msgSender()); _; }
  modifier onlyTwoStepConfigManager() { require(twoStepConfigManager == _msgSender(), "ConfigManagerOnly"); _; }
  function setAccessControlManager(address a) external onlyOwner   // a != 0; acm := a
  function setTwoStepConfigManager(address a) external onlyOwner   // a != 0; twoStepConfigManager := a
  function _checkAccessAllowed(bytes4 sel) internal view            // acm.isAllowedToCall(msg.sender, sel) — NEVER CALLED
  function _checkRole(bytes32 role, address account) internal view { if (!acm.hasRole(role, account)) revert …; }
}
```

Guard predicates (world `w`, target `t`, caller `c`):

- `onlyOwner(t)`: `c = sload(t, 0x9016d09d…9300)` (OZ ERC-7201 `Ownable` slot).
- `onlyRole(r)(t)`: `STATICCALL(sload(t, 0), hasRole(r, c))` returns `true`. The authority
  is an **external oracle at an owner-replaceable address**. A role is **global across
  targets**: the ACM is asked `hasRole(role, account)` with no target argument, so one grant works
  on every contract that names the same ACM. All 8 do.
- `onlyTwoStepConfigManager(t)`: `c = sload(t, 1)` (must be non-zero to be meaningful; setter
  forbids 0).
- `_checkAccessAllowed` (per-selector `isAllowedToCall`) is **dead code**. No source calls it,
  and no impl bytecode contains the selector `0x32fd3741`. `hasRole` sites are present (the
  optimizer emits the selector as `PUSH4 0x24745215; PUSH1 0xe2; SHL`, which is `0x91d14854 << 224`).
  Any `grantCall`/`revokeCall` on the ACM therefore has **no effect** on these contracts.

Authority-mutating transitions inside the Strata contracts:

| Transition | Guard | Effect |
|---|---|---|
| `transferOwnership(n)` (0xf2fde38b) | owner | pending := n (n = 0 allowed: cancels) |
| `acceptOwnership()` (0x79ba5097) | `c = pending` | owner := c, pending := 0 |
| `renounceOwnership()` (0x715018a6) | owner | owner := 0, pending := 0 (**irreversible**) |
| `setAccessControlManager(a)` (0x0e32cb86) | owner | acm := a (≠0): **replaces the entire role oracle** |
| `setTwoStepConfigManager(a)` (0x593ec077) | owner | twoStepConfigManager := a (≠0) |
| `initialize(…)` | `initializer` (version 0, top level) | sets owner, acm, wiring |

Role grants and revocations are **outside** the snapshot, in the ACM.

### 2.2 `IAccessControlManager.sol` and the ACM

`interface IAccessControlManager is IAccessControl { grantCall(contract, sel, account); revokeCall(…); isAllowedToCall(account, sel); hasPermission(account, contract, sel); }`.
This is the Venus-style `AccessControlManager` shape: OZ `AccessControl` plus per-(contract, selector)
permissions, normally stored as role `keccak(contract ‖ sel)`. It is **not** OZ `AccessManager`:
there are no execution delays, no `canCall(caller, target, sel)`, no guardians. Here only its plain
`hasRole` is used. The **implementation is not in the snapshot** (address
0x1d19e18ecac4ef332a0d5d6aa3a0f0f772605f60, S via `acm()` and slot 0 on all 8). Its role admin
structure (`getRoleAdmin`, `DEFAULT_ADMIN_ROLE` holders), members and storage layout are U.

### 2.3 OZ `Ownable2StepUpgradeable` v5.1 / `OwnableUpgradeable` v5.0 (ERC-7201)
Owner at `0x9016d09d72d40fdae2fd8ceac6b6234c7706214fd39c1cd1e609a0528c199300`, pending owner at
`0x237e158222e3e6968b72b9db0d8043aacf074ad9f650f0d1606b4d82ee432c00`. Transitions are as in the table
above.

### 2.4 `Initializable` v5.3 (ERC-7201 slot `0xf0c57e16840df040f15088dc2f81fe391c3923bec73e23a9662efc9c229c6a00`)
Every impl constructor runs `_disableInitializers()`, which sets the impl's own `_initialized` to 2^64-1, so impl
`initialize` is closed. No impl has a `reinitializer`. Each proxy's `initialize` ran inside the
proxy constructor: the constructor `_data` is the `initialize` calldata. V confirms this for the 7
Blockscout-verified proxies: CDO `0x485cc955(owner0, acm)`; Accounting `0xf8c8765e(owner0, acm, cdo, feed)`;
Strategy `0x1459457a(owner0, acm, cdo, erc20Cooldown, unstakeCooldown)`; Feed
`0x6cfa2a82(owner0, acm, provider0, 14400, "Ethena CDO APR Pair")`; both cooldowns `0x485cc955`;
jrUSDe `0x0c5b2ab3(owner0, acm, "Strata Junior USDe", "jrUSDe", USDe, cdo)`. For srUSDe
(Sourcify) the constructor args are not in the snapshot, but the same pattern is very likely. The
`_initialized` slot itself was **not fetched**, so "no open initializer" is U from state alone. It
follows from code plus deployment data.

### 2.5 OZ v5.2 `TransparentUpgradeableProxy` + `ProxyAdmin`
- Proxy: if `c = _admin` (immutable) then only `upgradeToAndCall(address,bytes)` (0x4f1ef286) is
  accepted (it sets the ERC-1967 impl slot and optionally delegatecalls `data`). Anything else
  reverts `ProxyDeniedAdminAccess`. Every other caller is delegated to the impl. **There is no `changeAdmin`.**
  The admin is fixed in code.
- `ProxyAdmin is Ownable` (v5.0, single step): `upgradeAndCall(proxy, impl, data)` (0x9623609d)
  `onlyOwner`, `transferOwnership` (single step, ≠0), `renounceOwnership` (freezes upgrades
  forever). Owner at slot 0 of each ProxyAdmin: **U** (not fetched).

### 2.6 Address-wired guards (storage-defined callers, no roles)
- `CDOComponent.onlyCDO`: `c = sload(t, 50)` (`cdo`) on Tranche, Accounting, Strategy.
- `StrataCDO.onlyTranche`: `c = sload(cdo, 52) ∨ c = sload(cdo, 53)` (jrtVault, srtVault).
- `StrataCDO.configure`: owner **and** `sload(cdo,50) = 0` (one-shot). It is already configured
  (S: accounting ≠ 0), so it is permanently closed.
- No setter exists for `cdo` (Tranche, Accounting, Strategy), `erc20Cooldown`/`unstakeCooldown`
  (Strategy), or CDO's four components. The wiring is **frozen except through upgrades**.
  `Accounting.aprPairFeed` and `AprPairFeed.provider` are owner-settable.

### 2.7 Ethena `SingleAdminAccessControl` (sUSDe), read in full
OZ 4.x `AccessControl` (`_roles` at slot 0, confirmed indirectly because `_balances` is at slot 4) plus
`_currentDefaultAdmin` (slot 1) and `_pendingDefaultAdmin` (slot 2):
- `transferAdmin(n)`: `onlyRole(DEFAULT_ADMIN)`, `n ≠ msg.sender`. Sets pending := n.
- `acceptAdmin()`: `c = pending`. Then `_grantRole(DEFAULT_ADMIN, c)`, which **revokes the old admin**, sets
  current := c and clears pending. This is a two-step single admin. The old admin keeps full power until acceptance.
- `grantRole`/`revokeRole`: `onlyRole(DEFAULT_ADMIN)` and `role ≠ DEFAULT_ADMIN` (admin is never granted
  or revoked directly). `renounceRole`: StakedUSDe overrides it to **always revert**.
- `getRoleAdmin` is inherited, so DEFAULT_ADMIN administers every role.
- StakedUSDe: `transferInRewards` (REWARDER), `addToBlacklist`/`removeFromBlacklist`
  (BLACKLIST_MANAGER; not the owner), `rescueTokens` (DEFAULT_ADMIN; not USDe),
  `redistributeLockedAmount(from,to)` (DEFAULT_ADMIN; `from` FULL_RESTRICTED: burn and re-mint),
  `setCooldownDuration` (DEFAULT_ADMIN, ≤ 90 d). The SOFT and FULL restricted roles gate deposits,
  withdrawals and transfers.

---

## 3. Privileged functions per contract

Effect categories: **UPG** upgrade, **MB** mint/burn, **PAR** parameter, **PAU** pause,
**FUND** fund movement/rescue, **RA** role/authority admin.

### Common to all 7 Strata impls (AccessControlled)
| Sel | Function | Guard | Cat |
|---|---|---|---|
| f2fde38b | transferOwnership(address) | owner | RA |
| 79ba5097 | acceptOwnership() | pendingOwner | RA |
| 715018a6 | renounceOwnership() | owner | RA |
| 0e32cb86 | setAccessControlManager(address) | owner | RA (replaces the role oracle) |
| 593ec077 | setTwoStepConfigManager(address) | owner | RA |
| (proxy) 4f1ef286 | upgradeToAndCall(address,bytes) | `c = ProxyAdmin` (immutable), reached via `ProxyAdmin.upgradeAndCall` (owner of ProxyAdmin) | UPG |

### StrataCDO (USDeCDO)
| Sel | Function | Guard | Cat / bound |
|---|---|---|---|
| d3e0c4af | reduceReserve(address,uint256) | RESERVE_MANAGER_ROLE | FUND: sends sUSDe/USDe to `treasury`, ≤ `Accounting.reserveNav` (via Accounting.reduceReserve → Strategy.reduceReserve → cooldown.transfer) |
| d9b89244 | distributeReserve(uint256,uint256) | RESERVE_MANAGER_ROLE | PAR/value: reserve → tranche NAVs |
| 9e4bca6b | setReserveTreasury(address) | RESERVE_MANAGER_ROLE | FUND destination (no check; 0 only blocks reduceReserve) |
| 8c936c0d | setActionStates(address,bool,bool) | PAUSER_ROLE | PAU **both directions** (can also re-enable after the automatic shortfall pause) |
| ea75991d | setJrtShortfallPausePrice(uint256) | PAUSER_ROLE | PAR, ≤ current jrUSDe price |
| 1872cc60 | setExitFees(uint256,uint256) | twoStepConfigManager | PAR, each ≤ 1% |
| 5acb5082 | configure(address,address,address,address) | owner ∧ unconfigured | wiring (closed) |
| ff5e3893 / 494347e7 / 20e8c565 / 390425b0 | accrueFee / updateAccounting / deposit / withdraw | onlyTranche | relay entry points |

### Accounting
| Sel | Function | Guard | Cat |
|---|---|---|---|
| 81cb657e | onAprChanged() | UPDATER_FEED_ROLE | PAR (pull APR) |
| 29b39158 | setRiskParameters(uint256,uint256,uint256) | UPDATER_STRAT_CONFIG_ROLE | PAR (risk premium < 100%) |
| bd748176 | setAprPairFeed(address) | owner | PAR/oracle swap (decimals = 12; APRs clamped to [0, 200%]) |
| e9308c25 | setReserveBps(uint256) | owner | PAR ≤ 10% |
| b3f56b10 | setFeeRetentionBps(uint256,uint256) | owner | PAR ≤ 100% |
| 384c80a7 / b54678e6 | setMinimumJrtSrtRatio / …Buffer | owner | PAR (min ≤ buffer ≤ 100x) |
| 0fdc442f / 3bc35c21 / 3a3ef88f / 80099504 | reduceReserve / updateAccounting / updateBalanceFlow / accrueFee | onlyCDO | NAV bookkeeping |

### sUSDeStrategy
| Sel | Function | Guard | Cat |
|---|---|---|---|
| cd123d41 | setCooldowns(uint256,uint256) | UPDATER_STRAT_CONFIG_ROLE | PAR ≤ 7 d; **relays** `ERC20Cooldown.setCooldownDisabled(sUSDe, jrt==0 && srt==0)` |
| a3ed9cd0 | deposit(…) | onlyCDO | FUND in (pulls from tranche) |
| 390425b0 | withdraw(…) | onlyCDO | FUND out via cooldowns |
| 6fb93754 | reduceReserve(address,uint256,address) | onlyCDO | FUND out to receiver |
| initialize | gave **max sUSDe allowance** to ERC20Cooldown and UnstakeCooldown | (done) | standing approvals |

### AprPairFeed (USDeAprFeeds)
| Sel | Function | Guard | Cat |
|---|---|---|---|
| 2317705f | updateRoundData(int64,int64,uint64) | UPDATER_FEED_ROLE | PAR/oracle push, APR ∈ [-50%, 200%], fresh, ordered; source := Feed |
| 21e541dd | updateRoundData() | UPDATER_FEED_ROLE | pull from provider; source := Strategy |
| cfd8d6c0 | setProvider(address) | owner | oracle swap |
| fad7206a | setRoundStaleAfter(uint256) | owner | PAR (unbounded) |

### ERC20Cooldown
| Sel | Function | Guard | Cat |
|---|---|---|---|
| 903fa446 | transfer(address,address,address,uint256,uint256) | COOLDOWN_WORKER_ROLE | FUND: pulls **from msg.sender only**; instant if cooldown 0 |
| 16d0bf83 | setCooldownDisabled(address,bool) | COOLDOWN_WORKER_ROLE | PAU-like: makes **every user's** pending requests for that token claimable at once |
| bcdf569b / 5e9d2afe | finalize(…) | permissionless (pays `user`) | — |

### UnstakeCooldown
| Sel | Function | Guard | Cat |
|---|---|---|---|
| f18d03cc | transfer(address,address,address,uint256) | COOLDOWN_WORKER_ROLE | FUND: pulls from msg.sender into a per-user clone, then `clone.request()` |
| 1f160951 | setImplementations(address[],address[]) | owner | **code choice** (UPG-like) for future clones; `implementations[token].isCooldownActive()` also gates `finalize` of all existing requests |
| finalize | permissionless | | |

### Tranche (srUSDe, jrUSDe)
Only the AccessControlled set plus `configure()` (onlyCDO: max approval of the Strategy's
supported tokens to the Strategy). User functions (ERC-4626 and meta deposit/mint/withdraw/redeem,
ERC-20, EIP-2612 `permit`) are permissionless, with allowance (Q) and signature (G) authority.

### Unused role constants
`UPDATER_CDO_APR_ROLE` and `PROPOSER_CONFIG_ROLE` guard nothing in these 7 impls. They exist for
off-snapshot contracts (presumably the TwoStepConfigManager uses PROPOSER_CONFIG_ROLE).

---

## 4. Concrete assignments at block 26239549

Role hashes (S from `*_ROLE()` calls, all equal to `keccak256(name)`):
PAUSER `0x65d7a28e…862a`, UPDATER_CDO_APR `0x67944e00…7897`, UPDATER_FEED `0x2c85ecd2…491b`,
UPDATER_STRAT_CONFIG `0xb93bf808…bff4`, RESERVE_MANAGER `0xcc938097…02ac`, COOLDOWN_WORKER
`0x97d8f58e…e880`, PROPOSER_CONFIG `0xe1014dbb…fa40`.

### Known (S)
| Item | Value | Where |
|---|---|---|
| owner of all 8 Strata proxies | **0xb2a3cf69c97afd4de7882e5fee120e4efc77b706** | slot 0x9016…9300 and `owner()` |
| pendingOwner of all 8 | 0 | slot 0x237e…2c00 and `pendingOwner()` |
| acm of all 8 | **0x1d19e18ecac4ef332a0d5d6aa3a0f0f772605f60** | slot 0 and `acm()` |
| twoStepConfigManager | CDO: **0x0f93bac77c3ddd1341d3ecc388c5f8a180818994**; the other 7: 0 (so no exit-fee-like setters elsewhere) | slot 1 |
| ProxyAdmin per proxy | table §1.1 | ERC-1967 admin slot = bytecode immutable |
| implementation per proxy | table §1.1 | ERC-1967 impl slot |
| beacon slot / zos impl slot | 0 / 0 | |
| treasury (reserve sink) | 0x40c5c15ec27526ad769b04e767cd319551f7f4e4 | CDO slot 54 |
| wiring | CDO: accounting, strategy, jrt, srt as in §1.1; tranches/Accounting/Strategy `cdo` = 0x908b…; Strategy cooldowns = 0xd6da…/0x735e…; Accounting.aprPairFeed = 0x2bb4…; Feed.provider = 0x1c13… (sourcePref = Feed, packed in slot 55) | |
| action states | jrt and srt: deposit = withdraw = enabled (0x0101) | CDO slots 55, 56 |
| params | exitFeeJrt 0.1%, exitFeeSrt 0.025%, shortfall price 0.01; reserveBps 5%, retention 50%/50%, minJrt/Srt 5%, buffer 6%, risk (x, y, k) = (0.1, 0.2, 0.3); roundStaleAfter 14400 s; sUSDe cooldowns jrt = srt = 0 | |
| feed freshness | last push `updatedAt` = 1778191199 (2026-05-07), more than 4 h stale, so `latestRoundData` falls back to **AaveAprPairProvider** (live Aave liquidity rates and sUSDe vesting). The UPDATER_FEED push has been dormant for about 5.5 months. | Feed slot 52 and recorded `latestRoundData` |
| TVL | strategy 23.03 M USDe; srtNav 17.04 M, jrtNav 5.99 M, reserveNav 2,882 | Accounting |
| Aave Pool proxy admin | PoolAddressesProvider 0x2f39d218… (immutable) | code |
| aUSDC/aUSDT proxy admin | 0x64b761d848206f447fe2dd461b0c635ec39ebb27 (immutable) | code |

### Historical (V, not current state)
- Initial Strata owner (init calldata): 0x4be3749a0f6557b8fd98f3967e859dbd7c694ef4. A two-step
  transfer to 0xb2a3… has completed.
- Initial ProxyAdmin owner (proxy constructor `initialOwner`) for the 7 Blockscout-verified
  proxies: **0x296400d87be5cfb63c5025904cd006ebb23d15d5**, the deployer that sent the deployment
  transactions, so it was an EOA at the time (EIP-7702 caveat). Whether ownership moved since is U.

### Unknowable from the snapshot (U), and how to get it
| Unknown | Why | Fetch |
|---|---|---|
| Every ACM role member, role admin, ACM admin/owner, ACM code | the ACM account was never read | add 0x1d19… as a target (autoViews: `owner()`, `DEFAULT_ADMIN_ROLE()`…), plus calls `hasRole(r, x)` for x ∈ {owner, deployer, initial owner, Strategy, CDO, config manager, treasury, ProxyAdmins} and `getRoleAdmin(r)` for all 8 roles and `0x00`; if Enumerable, `getRoleMemberCount`/`getRoleMember` |
| Owners of the 8 ProxyAdmins | not fetched | add them as targets (`owner()`, slot 0) |
| Nature of 0xb2a3… (owner), 0x0f93… (config manager), 0x40c5… (treasury), ProxyAdmin owners | no `eth_getCode` | add as targets; if Safe: `getOwners()`, `getThreshold()`, modules (`getModulesPaginated`), guard slot `0x4a204f62…`; if TimelockController: `getMinDelay()` and roles |
| `_initialized` of the proxies | slot `0xf0c57e16…6a00` not read | add it to `proxySlots`-style probes |
| `UnstakeCooldown.implementations[sUSDe]` (owner-chosen clone code) | not read | slot `0x37728f91571899aae9192b7b441acdc0275aa879648c38ef1bd0ebebea00cdfb` (`keccak(sUSDe‖50)`) |
| `ERC20Cooldown.cooldownDisabled[sUSDe]` | not read | slot `0xb851ccc88b2635ccb1be2979cec15a61625f57b90979c28547ac5ea46c64bf22` (`keccak(sUSDe‖51)`) |
| Whether Ethena has restricted the Strategy | not read | sUSDe slots `0xf1346ca9…d324` (FULL) and `0xea455660…c0d2` (SOFT) = `keccak(strategy ‖ keccak(role ‖ 0))`; also sUSDe slot 1 (`owner()`), USDe `owner()`/`minter()` |
| Aave governance (PoolAddressesProvider owner, ACL manager) | out of scope | |

Note: Strata role membership lives **only** in the external ACM. No `keccak(account ‖ keccak(role ‖ base))`
slot of any Strata contract is meaningful, because the contracts have no local roles. The
ERC-7201 OZ AccessControl namespace would be `0x02dd7bc7dec4dceedda775e58dd541e08a116c6c53815c0bd028192f7b626800`
if the ACM uses `AccessControlUpgradeable`, or slot 0 for a plain `AccessControl`. Which one applies is U until the ACM's code is fetched.

---

## 5. Composition graph (who is a contract)

Contracts with code in the snapshot: the 8 proxies, 7 impls, AaveAprPairProvider, USDe, sUSDe, and the
Aave Pool/aToken proxies and impls. **All authority holders are outside the snapshot**, so their
nature is unknown. Known edges:

```
ProxyAdmin_i (8 separate, Ownable)  ──upgradeToAndCall──▶ proxy_i      [owner(ProxyAdmin_i) = U; initially 0x2964… EOA]
owner 0xb2a3… (U kind) ──onlyOwner──▶ all 8 impls (setACM, setTwoStep, params, setProvider, setImplementations, renounce)
ACM 0x1d19… (U code) ◀──hasRole STATICCALL── CDO, Accounting, Strategy, Feed, ERC20Cooldown, UnstakeCooldown (Tranches never ask)
TwoStepConfigManager 0x0f93… (U) ──setExitFees──▶ CDO
Tranche(sr|jr) ──onlyTranche──▶ CDO ──onlyCDO──▶ {Accounting, Strategy, Tranche.configure}
Strategy ──COOLDOWN_WORKER (expected holder)──▶ {ERC20Cooldown, UnstakeCooldown}; max sUSDe allowance to both
Tranche ──max allowance (sUSDe, USDe)──▶ Strategy
UnstakeCooldown ──Clones.clone(impl[token])──▶ per-user handler clones (initialize(handler=UnstakeCooldown, user))
Accounting ──latestRoundData──▶ Feed ──getAprPair (fallback, active now)──▶ AaveAprPairProvider ──▶ Aave Pool, aTokens, sUSDe
External controllers over the assets: sUSDe DEFAULT_ADMIN / BLACKLIST_MANAGER / REWARDER; USDe owner → minter; Aave governance (APR input only)
```

Relay contracts (R) to model: the 8 ProxyAdmins; the Tranches (relay users to CDO); the CDO (relays
tranches and RESERVE_MANAGER to Strategy and Accounting); the Strategy (relays CDO and
UPDATER_STRAT_CONFIG to the cooldowns, and holds COOLDOWN_WORKER); the TwoStepConfigManager (code U,
presumably timelocked/proposer-based); and whatever kinds of contract the owner, ACM admins and ProxyAdmin owners turn out to be.

---

## 6. Effective control per effect (closure)

Let `PA_i = owner(ProxyAdmin_i)`, `O = 0xb2a3…`, `A = ACM admins` (U), `H_r = ACM members of r` (U).

| Effect | Direct controllers | Closure (Ctl) | Notes |
|---|---|---|---|
| Upgrade proxy i | PA_i | PA_i, plus whoever controls PA_i (U) | upgrading CDO, Strategy, ERC20Cooldown, UnstakeCooldown or a Tranche is each enough to **drain all Strategy funds** (onlyCDO paths, or the standing max sUSDe allowances to the cooldowns, or forged tranche shares → CDO.withdraw). An Accounting upgrade re-splits NAV. |
| Replace role oracle on t | O | O | `setAccessControlManager` to a yes-oracle gives O **every role on t**. So O ⊇ H_r for every role-gated effect, per contract. |
| Role-gated effects (pause, reserve, feed, strat config, cooldown worker) | H_r | H_r ∪ A ∪ O (∪ ACM upgrade/owner authority, U) | roles are global across all 8 contracts |
| Exit fees (≤ 1%) | 0x0f93… | 0x0f93…'s own controllers (PROPOSER_CONFIG holders?, U) ∪ O (setTwoStepConfigManager) | |
| Reserve → arbitrary address | H_RESERVE_MANAGER (setReserveTreasury + reduceReserve) | ∪ A ∪ O ∪ PA_{CDO, Accounting, Strategy, cooldowns} | bounded by reserveNav (2,882 USDe now), and reserveNav grows via reserveBps (O) and fee retention (O) |
| Senior/junior value split | H_UPDATER_FEED (push APR ∈ [0, 200%] effective), H_UPDATER_STRAT_CONFIG (risk), O (feed, provider, staleness, reserveBps, ratios), PA_Accounting / PA_Feed | plus Aave governance and Ethena REWARDER while the feed is stale (current state) | no key is needed: the live pull path makes **external protocols' state** an input |
| Pause/unpause deposits/withdrawals | H_PAUSER (both ways), automatic shortfall pause | ∪ A ∪ O ∪ PA_CDO | PAUSER is **not** purely negative authority |
| Emergency cooldown bypass (sUSDe) | H_COOLDOWN_WORKER (directly), H_UPDATER_STRAT_CONFIG (via Strategy) | ∪ A ∪ O ∪ PA_ERC20Cooldown, PA_Strategy | releases every user's pending sUSDe early |
| Unstake handler code (future USDe withdrawals) | O (`setImplementations`) | O ∪ PA_UnstakeCooldown | malicious impl receives users' sUSDe in later `transfer`s. Existing clones keep their code, but `finalize` consults the **current** impl's `isCooldownActive()` |
| Freeze/seize Strategy's sUSDe (≈ all TVL) | Ethena BLACKLIST_MANAGER (freeze), DEFAULT_ADMIN (redistribute) | Ethena governance (U) | external, outside Strata's model, but it bounds any "funds safe unless Strata keys act" theorem |
| USDe supply | USDe minter (owner sets it) | Ethena (U) | |
| Ownership of Strata contracts | O (transfer/renounce), pending (none now) | O ∪ PA_i (an upgrade can rewrite the owner slot) | |

What closes the analysis: (1) code and storage of the ACM, (2) owners of the 8 ProxyAdmins, (3) code of O,
0x0f93…, the PA owners and the ACM admins (Safe parameters, or timelock delay and roles), (4) `implementations[sUSDe]`
in UnstakeCooldown and that handler's code, (5) Initializable slots. Without these, the only
true statement is: **"for every effect, Ctl ⊆ {PA_1..8, O, A, H_*, 0x0f93…} ∪ their controllers ∪
external Ethena/Aave authorities"**, with O dominating all role-gated effects and PA_i dominating
everything on proxy i.

---

## 7. Pitfalls

1. **Owner-swappable authority oracle** (`setAccessControlManager`). The owner is a super-role.
   Any "role R alone controls E" statement must include O. Renouncing ownership freezes the ACM
   pointer, so roles stay governed by the ACM forever.
2. **Global roles in one shared ACM.** COOLDOWN_WORKER granted for one cooldown contract works on the
   other. Any extra COOLDOWN_WORKER holder can disable the sUSDe cooldown for everyone. Roles do not
   name a target.
3. **Dead per-selector permissions.** `isAllowedToCall`/`grantCall` exist on the ACM interface, but
   no deployed code consults them. An off-chain reviewer reading ACM `grantCall` events would get a wrong picture.
4. **Standing infinite approvals** (Strategy → both cooldowns, Tranches → Strategy). They make the
   cooldowns' and the Strategy's upgrade keys equivalent to custody of the funds. Allowance edges
   must be in the authority graph.
5. **Owner-chosen clone implementation** (`setImplementations`). This is a code-change effect without a
   proxy upgrade, and it affects `finalize` of existing requests through `isCooldownActive()`.
6. **`renounceOwnership`** is present on all 7 Strata impls (Ownable2Step) and on all 8 ProxyAdmins
   (Ownable). Renouncing a ProxyAdmin makes the proxy immutable. Renouncing O freezes params and
   the oracle pointer. `transferOwnership(0)` cancels a pending transfer.
   ProxyAdmin ownership is **single-step**.
7. **PAUSER can unpause**, including overriding the automatic shortfall pause. Form (e) (negative
   authority) fails for PAUSER as deployed.
8. **Transparent-proxy routing**: the admin is an immutable in code. The ERC-1967 admin slot is
   informational, and a malicious impl writing to it changes nothing. A model that reads the
   slot is right only by coincidence. Each ProxyAdmin can call nothing on its proxy except upgrade.
9. **Initializers**: closed on impls by `_disableInitializers`. On proxies they are closed because init ran
   atomically in the constructor. No `reinitializer` exists, so upgrades did not re-run init.
   This is not confirmable from the snapshot state.
10. **No arbitrary-call relays and no delegatecall** in the Strata sources: no `execute`, no multicall,
    no `delegatecall`, no `selfdestruct`. The only `DELEGATECALL` paths are the proxies (to the impl,
    and in `upgradeToAndCall`) and the EIP-1167 clones. The relays that exist (CDO, Strategy, Tranche) issue a
    fixed set of calls with fixed selectors. Unknown relays: the owner, ACM admins, ProxyAdmin owners and
    the config manager (U).
11. **Oracle fallback**: the push feed is stale, so senior APR comes from Aave and Ethena state. This is an
    authority path with no key at all.
12. **External seizure**: sUSDe `FULL_RESTRICTED_STAKER_ROLE` plus `redistributeLockedAmount` can move
    the Strategy's entire sUSDe balance. `renounceRole` reverting on sUSDe is harmless.
13. Minor: `setReserveTreasury(0)` is allowed (DoS only), `setRoundStaleAfter` is unbounded (huge value
    means stale pushes are trusted forever; 0 means pushes must have `t = now`), and `CDO.configure` is one-shot by
    `accounting ≠ 0`.
14. Snapshot artifacts: wrong-project source trees attached to the proxies (HashKeyChain, Ailey).
    A source-driven model must key on the fullyQualifiedName or on bytecode equivalence, not on the
    files present.

---

## 8. Primitives a formal model needs, and existing evm-lean infrastructure

### 8.1 Primitives
1. **Storage-address guard** (ingredient C): `caller = sload t slot`, for ERC-7201 constants (Ownable
   `0x9016…`), linear slots (`acm` 0, `twoStepConfigManager` 1, `cdo` 50, `jrtVault`/`srtVault` 52/53),
   and disjunctions (`onlyTranche`).
2. **External role oracle with a replaceable pointer** (X with `setAuthority`): the guard is
   "STATICCALL to `sload t 0` with `hasRole(r, caller)` returns true". This needs an answer lemma
   `AcmAnswers w r a ↔ …` as a hypothesis while the ACM code is unknown. The oracle is
   **target-independent**: one role predicate shared by 6 targets. The pointer write
   (`setAccessControlManager`) is an authority-mutating effect controlled by O, so the `Ctl` closure adds O to
   every role effect automatically (§5 last clause of access-control.md).
3. **Two-step ownership** (C, T): owner and pending slots, `transferOwnership`/`acceptOwnership`/
   `renounceOwnership`/cancel. The same machine with a different storage shape serves Ethena `SingleAdminAccessControl`
   (pending admin, accept revokes the old admin, renounce disabled).
4. **Single-step `Ownable`** (ProxyAdmin) with renounce.
5. **Transparent proxy with an immutable admin** (U, R): routing on a code constant (`EvmLogic.Solidity.Immutables`),
   an upgrade effect that writes the impl slot and runs an optional delegatecall. Theorem forms: "until the first
   upgrade" or "∀ impl ⊨ Spec".
6. **Relay issuance lemmas** (R): `ProxyAdmin.upgradeAndCall` (owner only); `Tranche → CDO`;
   `CDO → Strategy/Accounting` (onlyTranche, RESERVE_MANAGER); `Strategy → Cooldowns` (onlyCDO,
   UPDATER_STRAT_CONFIG); and the unknown config manager as an assumed `Issues` lemma.
7. **Allowance edges** (Q): standing ERC-20 approvals as authority (Strategy → cooldowns, Tranche → Strategy),
   and user allowances plus EIP-2612 `permit` (G) on tranche shares.
8. **Quantitative bounds** (Q): reserve outflow ≤ `reserveNav`, exit fee ≤ 1%, cooldown ≤ 7 d,
   APR clamp [0, 2e12], reserveBps ≤ 10%, risk < 100%.
9. **Factory and clone code choice** (U without a proxy): EIP-1167 clones whose code is chosen by
   an owner-set mapping, with a per-clone `initialize(handler, user)`.
10. **Frozen wiring and one-shot configuration**: invariants "cdo/strategy/… constant until upgrade",
    and `configure` closed when `accounting ≠ 0`. Initializer state (`_initialized` ≥ 1 on proxies, max on
    impls) is a world predicate.
11. **External environment principals**: Ethena (sUSDe admin, blacklist, rewarder; USDe minter) and
    Aave (rates) as world inputs that no Strata key controls. Theorems need either a hypothesis
    "Ethena does not restrict the Strategy" or a statement relative to the sUSDe balance.
12. **Two-sided pause** (PAUSER): a model where pause roles are not negative-only.

### 8.2 Existing evm-lean infrastructure that helps
- `Snapshot/` (Fetch/Access/State/Run/Check): `runObserved` records exactly what a run reads, and
  `State.missing` gives the "known vs unknowable" split mechanically. To close §4's U set, extend
  `targets.json` with the ACM, the 8 ProxyAdmins, O, 0x0f93…, the treasury, and explicit
  `hasRole`/`getRoleAdmin`/`owner()` calls. Add the Initializable ERC-7201 slot and the
  Ownable/Ownable2Step slots to the probe list next to `proxySlots` (`Fetch.lean` already has
  `eip1967Impl/Admin/Beacon` and `zosImpl`, with the correct constants).
- `EvmLogic/Solidity/Layout.lean` (`mappingSlot`, `mappingSlot2`, `Field` for packed slots such as
  `TActionState`, Feed `provider‖sourcePref`, `TRound`) and `Keccak.lean` (`KeccakAvoids`,
  hypotheses keyed by role, e.g. sUSDe `keccak(a ‖ keccak(r ‖ 0))`). ERC-7201 constants are plain words.
- `EvmLogic/Solidity/Immutables.lean`: for the proxy `_admin` immutable and the Strategy's
  `sUSDe`/`USDe` immutables.
- `EvmLogic/Program/Nested/Run.lean` (`DangerStart`, `processMessageCall_good`): the frame-level
  guard lemma (form a) with symbolic `msg.caller`, and the base for the `Issues` frame condition.
- `EvmLogic/Solidity/ERC20Oz.lean` and the recent OZ ERC-20 bytecode refinement (`OzAsset`): the
  tranches are OZ v5 `ERC20Upgradeable`/`ERC4626Upgradeable` with ERC-7201 storage (`0x52c63247…`, `0x0773e532…`), close to what exists.
- `qedefi/Examples/WeirdERC20/AMPL/Contracts/AMPLProxy.lean`: the planned first `Guards` instance
  for a transparent proxy. Strata's OZ v5 proxy differs (immutable admin, separate ProxyAdmin), which makes it a good second instance.
- `docs/access-control.md`: Strata exercises ingredients C, X (with a replaceable pointer),
  R, U (proxy and clone impl), T (Ownable2Step, the feed's freshness and staleness), Q (allowances, reserve bound),
  G (permit), and W-like external state (Aave and Ethena). It also shows two gaps in §3 of that note: an ACM
  of the Venus `hasRole`-only shape (target-independent roles), and owner-chosen clone code.
