# Actor / authority models: Hats, Aragon ACL, Aave v3 ACL, Euler EVC, ERC-4337/7579, EIP-7702, Permit2

Source-grounded specification. Every citation is `repo@commit:path:line`. Only source was read; no
build tool or script from any clone was executed.

## Sources (shallow clones under `research/`)

| id | repo | commit / tag | notes |
|----|------|--------------|-------|
| HATS | Hats-Protocol/hats-protocol | `cccb71a061cdb9095af7d11dfdb47026993d8c4e` | Hats v1 (`src/Hats.sol`, `src/HatsIdUtilities.sol`) |
| HSG2 | Hats-Protocol/hats-zodiac | `v2.0.0` = `2c0172e979e64f6f73647adc634a4622cba465ef` | Hats Signer Gate v2 |
| HSG1 | Hats-Protocol/hats-zodiac | `v1.2-beta` = `016d4ee1a3e66d757999970fe5a4b68f7ab9986f` | HSG v1 (skimmed only) |
| SAFE | safe-global/safe-smart-account | `bf943f80` (v1.4.1, already in scratch) | guard call order only |
| ARA | aragon/aragonOS | `v4.4.0` = `f3ae59b00f73984e562df00129c925339cd069ff` | version pinned by Lido (`@aragon/os: 4.4.0`, lido `package.json:135`). `next` branch (`4bbe3e96`, 5.0.0-rc.0) has a semantically identical ACL (diff = comments/formatting only) |
| APPS | aragon/aragon-apps | `b72da2c6606a361d0160d5d78fb534018ba3ce91` | Voting, Agent (forwarders) |
| LIDO | lidofinance/core | `2bd532298d85cdf520169fdc0c5fb0cc9baf03c3` | `_auth/_authP` usage |
| AAVE | aave-dao/aave-v3-origin | `8305565ae342f1773c42cd2e4593f175fe5968a0` | Pool `POOL_REVISION = 11` (`src/contracts/instances/PoolInstance.sol:15`) |
| EVC | euler-xyz/ethereum-vault-connector | `79455bc3d5d72fe7c727880894257458d0afe073` | |
| EP7 | eth-infinitism/account-abstraction | `v0.7.0` = `7af70c8993a6f42973f520ae0752386a5032abe7` | |
| EP8 | eth-infinitism/account-abstraction | `v0.8.0` = `4cbc06072cdc19fd60f285c5997f4f7f57a588de` | primary 4337 reference below |
| EP9 | eth-infinitism/account-abstraction | HEAD `1c6b669d` (0.9.0) | not analysed beyond noting it exists |
| 7579 | erc7579/erc7579-implementation | `99cbd34479b9d125651316ff2d92f38611ddf665` | `MSAAdvanced` |
| P2 | Uniswap/permit2 | `cc56ad0f3439c502c246fc5cfcc3db92bb8b7219` | |
| 7702 | ethereum/EIPs `EIPS/eip-7702.md` | last commit `bbc3f958` (2025-10-07), status **Final** | cited as `eip-7702.md:line` |

Path prefixes used below: HATS = `src/`, AAVE = `src/contracts/`, ARA = `contracts/`, EVC = `src/`,
EP8/EP7 = `contracts/`, 7579 = `src/`, P2 = `src/`.

---

## 1. Hats Protocol v1

### 1.1 Authority state

* `Hat` struct (`Hats.sol:57-69`), keyed by hat id in `_hats` (`Hats.sol:85`):
  slot 1 `eligibility:address | maxSupply:uint32 | supply:uint32 | lastHatId:uint16`;
  slot 2 `toggle:address | config:uint96`; then `details`, `imageURI` strings.
  `config` bit layout (code, not the comment): bit **95** = stored `active` status
  (`_getHatStatus`: `config >> 95 != 0`, `Hats.sol:1050-1052`), bit **94** = `mutable`
  (`_isMutable`: `config & (1<<94)`, `Hats.sol:1058-1060`). Creation writes `3<<94` (mutable+active) or
  `1<<95` (immutable, active) (`Hats.sol:452`). The comment at `Hats.sol:49-53` ("0th bit / 1") refers
  to MSB-first numbering.
* Wearer balances: ERC1155 `_balanceOf[account][id]` (vendored `lib/ERC1155/ERC1155.sol:35`), always 0/1.
* `badStandings[hatId][wearer]` (`Hats.sol:90`) - stored fallback standing (true = bad).
* `lastTopHatId:uint32` (`Hats.sol:79`).
* Tree linking: `linkedTreeRequests[topHatDomain:uint32] -> requestedAdminHatId` and
  `linkedTreeAdmins[topHatDomain] -> adminHatId` (`HatsIdUtilities.sol:32,36`).

**Id encoding** (`HatsIdUtilities.sol:38-62`): `id = domain:32 bits || L1:16 || L2:16 || ... || L14:16`
(MSB first). `TOPHAT_ADDRESS_SPACE = 32`, `LOWER_LEVEL_ADDRESS_SPACE = 16`, `MAX_LEVELS = 14`.
* top hat: `id = uint256(domain) << 224`, `isLocalTopHat(id) := id > 0 && uint224(id) == 0`
  (`:149-151`); `isTopHat` additionally requires not linked (`:141-143`).
* `getLocalHatLevel(id)` = number of trailing non-empty 16-bit levels via successive masks
  (`:120-136`).
* `getAdminAtLocalLevel(id, l) = id & (~0 << 16*(14-l))` (`:197-201`) - pure prefix truncation.
* `buildHatId(admin, n)`: find the first i in 0..13 with `admin & (~0 >> (32+16i)) == 0`, return
  `admin | n << 16*(13-i)`; revert `MaxLevelsReached` if none (`:69-99`).
* `isValidHatId(id)`: no empty level above the hat's own level (`:153-173`).
* Linked levels: `getHatLevel(id) = local + (linked ? 1 + getHatLevel(linkedAdmin) : 0)` (`:104-114`);
  `getAdminAtLevel` follows `linkedTreeAdmins` (`:181-190`); `getTippyTopHatDomain` follows links to
  the root (`:214-218`); `noCircularLinkage` walks the chain (`:224-230`).

### 1.2 Derived predicates (read-time, dynamic)

* `_isActive(hat,id)` (`Hats.sol:1010-1037`): `staticcall(toggle, getHatStatus(id))`;
  if `success && returndata.length == 32` and word ∈ {0,1} → that value; **otherwise** (revert, EOA/no
  code → empty returndata, wrong length, word ≥ 2) → stored bit 95.
* `_isEligible(wearer,hat,id)` (`Hats.sol:1098-1125`): `staticcall(eligibility,
  getWearerStatus(wearer,id))`; if success, length 64, both words < 2: `eligible = standing && first==1`
  with `standing = second==1`; **otherwise** `!badStandings[id][wearer]`.
* `balanceOf(w,id) = (_isActive ∧ _isEligible) ? _balanceOf[w][id] : 0` (`Hats.sol:1297-1310`).
* `isWearerOfHat(u,id) := balanceOf(u,id) > 0` (`Hats.sol:942-944`).
* `isInGoodStanding` same fallback structure (`Hats.sol:1066-1090`).
* `isAdminOfHat(u, id)` (`Hats.sol:951-1003`):
  1. If `id` is a local top hat: if tree unlinked → `isWearerOfHat(u,id)` (a top-hat wearer is its own
     admin). If linked: `isWearerOfHat(u, linkedAdmin)` → true, else continue the search from
     `linkedAdmin` (set `id := linkedAdmin`, level := its local level).
  2. Else level := `localLevel(id) - 1`.
  3. For levels `level..1`: if `u` wears `getAdminAtLocalLevel(id, l)` → true.
  4. If `u` wears the local top hat → true.
  5. If the tree is linked: wears `linkedAdmin` → true, else recurse `isAdminOfHat(u, linkedAdmin)`.
  Net: **admin(u,h) ⇔ u currently wears some strict ancestor of h in the (linked) forest**, except an
  unlinked top hat is its own admin. Wearing `h` itself never grants admin over `h` (non-top-hats).
  Each "wears" check is the dynamic `balanceOf` (toggle+eligibility of the ancestor hat).

### 1.3 Guarded entry points (check order)

| function | predicate (in order) | effect |
|---|---|---|
| `mintTopHat(target, details, uri)` `Hats.sol:117-136` | none (permissionless) | `id = ++lastTopHatId << 224`; create hat (maxSupply 1, eligibility=toggle=0, immutable); `_mintHat(target,id)` |
| `createHat(admin, details, maxSupply, elig, toggle, mutable, uri)` `:149-175` | `uint16(admin)==0` else `MaxLevelsReached`; `elig≠0`, `toggle≠0` (`ZeroAddress`); `isValidHatId(admin)`; `newId = getNextId(admin)` (= `buildHatId(admin, lastHatId+1)`, checked uint16 add); `isAdminOfHat(msg.sender, newId)` | `_createHat` writes struct (preserves `lastHatId` of newId), `++_hats[admin].lastHatId` |
| `batchCreateHats` `:188-230` | equal lengths; loop `createHat` | |
| `mintHat(id, w)` `:246-263` | `maxSupply≠0` (existence); `isEligible(w,id)`; `_isActive`; `isAdminOfHat(msg.sender,id)`; `supply < maxSupply`; `_balanceOf[w][id]==0` | `_balanceOf=1; ++supply` |
| `setHatStatus(id, s)` `:289-297` | `msg.sender == hat.toggle` | if differs: set bit 95 |
| `checkHatStatus(id)` `:303-314` | toggle call must succeed with valid bool (`_pullHatStatus` `:316-344`) else revert `NotHatsToggle`; permissionless | store pulled status |
| `setHatWearerStatus(id, w, elig, standing)` `:354-365` | `msg.sender == hat.eligibility` | `_processHatWearerStatus` |
| `checkHatWearerStatus(id, w)` `:372-404` | eligibility call must return 64 valid bytes else revert; permissionless | `_processHatWearerStatus` with pulled values |
| `renounceHat(id)` `:409-415` | `_balanceOf[msg.sender][id] ≥ 1` (static) | burn |
| `transferHat(id, from, to)` `:554-573` | `isAdminOfHat(msg.sender,id)`; if not top hat: mutable; `_balanceOf[from]≥1` (static, so revoked-by-module hats can be moved); `_balanceOf[to]==0`; `isEligible(to)`; `_isActive` | balances swap (supply unchanged) |
| `makeHatImmutable(id)` `:578-590` | admin; currently mutable | clear bit 94 (one-way) |
| `changeHatDetails / changeHatImageURI` `:596-611 / :663-677` | len ≤ 7000; admin; mutable unless top hat | |
| `changeHatEligibility(id, e)` `:617-630` | `e≠0`; admin; mutable | |
| `changeHatToggle(id, t)` `:636-657` | `t≠0`; admin; mutable | first pulls status from old toggle and stores it if valid, then sets toggle |
| `changeHatMaxSupply(id, m)` `:683-699` | admin; mutable; `m ≥ supply` | |
| `requestLinkTopHatToTree(dom, adminHat)` `:711-719` | `isAdminOfHat(msg.sender, dom<<224)` (unlinked: top-hat wearer; linked: admins in parent tree) | `linkedTreeRequests[dom] = adminHat` (overwrites) |
| `approveLinkTopHatToTree(dom, adminHat, e, t, d, uri)` `:730-755` | if `getHatLevel(adminHat) < 14`: `isAdminOfHat(msg.sender, buildHatId(adminHat,1))` (i.e. wearer or admin of adminHat); else admin-or-wearer of adminHat; `adminHat == linkedTreeRequests[dom]` | delete request; `_linkTopHatToTree` |
| `unlinkTopHatFromTree(dom, wearer)` `:766-785` | admin of top hat; `wearer≠0 ∧ isWearerOfHat(wearer, tophat)` | delete link + request; clear top hat eligibility & toggle |
| `relinkTopHatWithinTree(dom, adminHat, ...)` `:798-821` | admin of top hat (requester) **and** wearer-or-admin of `adminHat` (approver) | `_linkTopHatToTree` |
| `_linkTopHatToTree` `:832-893` | `noCircularLinkage`; if already linked: caller wears tippy top hat → dest must share tippy top domain; else dest local top hat ∈ {origin local top hat, tippy top hat} | optional new elig/toggle/details/uri; `linkedTreeAdmins[dom] = adminHat` |
| ERC1155 `setApprovalForAll`, `safeTransferFrom`, `safeBatchTransferFrom` `:1347-1364` | always revert | |

`Hats` also inherits solady `Multicallable` (`Hats.sol:33`): `multicall` delegatecalls itself, so
`msg.sender` is preserved across a batch (solady submodule not checked out; standard pattern).

### 1.4 Authority-mutating transitions (exact effects)

* `_mintHat` (`:1316-1327`): `_balanceOf[w][id] = 1; ++supply`.
* `_burnHat` (`:1333-1343`): `_balanceOf[w][id] = 0; --supply` (unchecked).
* `_processHatStatus` (`:462-471`): write bit 95 iff different.
* `_processHatWearerStatus(id,w,elig,standing)` (`:482-506`): if `_balanceOf>0 ∧ (¬elig ∨ ¬standing)`
  → burn; if `standing == badStandings[id][w]` → `badStandings := ¬standing`. Note: a burn for
  `elig=false, standing=true` leaves `badStandings` false, so with a non-contract eligibility the
  wearer is again "eligible" by fallback and can be re-minted.
* Links: `linkedTreeRequests`, `linkedTreeAdmins` writes as above; unlinking zeroes top-hat
  eligibility/toggle (`:781-782`).
* Mutability: one-way true→false (`makeHatImmutable`). Top hats are created immutable but can still
  change details/imageURI and be transferred by their admin (`:557, :604, :670`).

### 1.5 Time, nonces, replay

No time or nonce logic in Hats itself. Status/eligibility are **evaluated at read time** through
external modules (which may themselves be time-based). There are no signatures.

### 1.6 Relay behaviour

Hats makes only `staticcall`s to toggle/eligibility modules (`getHatStatus(uint256)`,
`getWearerStatus(address,uint256)`; interfaces `Interfaces/IHatsToggle.sol`,
`Interfaces/IHatsEligibility.sol`). Downstream contracts authenticate a principal by calling
`HATS.isWearerOfHat(msg.sender, hatId)` (e.g. HSG `_checkOwner` `HatsSignerGate.sol:128-130`). Hats
never forwards calls.

### 1.7 Hats Signer Gate (relation to Safe)

HSG v2 (`v2.0.0`) is simultaneously a Safe **module** and Safe **guard** (`README.md`):
* State (`HatsSignerGate.sol:64-90`): `safe`, `locked`, `claimableFor`, `ownerHat`,
  `enabledDelegatecallTargets`, `registeredSignerHats[signer]`, append-only `_validSignerHats`,
  `_thresholdConfig {min, target, ABSOLUTE|PROPORTIONAL}`; transient guards (`:97-121`).
* Owner = **current wearer of `ownerHat`** (`_checkOwner` `:128-130`); owner functions also require
  `!locked` (`:132-135`): `lock` (irreversible), `setOwnerHat`, `addSignerHats`, `setThresholdConfig`,
  `setClaimableFor`, `detachHSG`, `migrateToNewHSG`, `en/disableDelegatecallTarget`,
  `enable/disableModule`, `setGuard` (`:297-398, :893-923`).
* Signer admission: `claimSigner(hat)` by the wearer itself (`:209-215`), `claimSignerFor(s)` by anyone
  when `claimableFor` (`:218-283`); `_registerSigner` requires `_validSignerHats[hat]` and
  `isWearerOfHat(signer, hat)` (`:702-720`); `_addSigner` adds a Safe owner via
  `execTransactionFromModule` and recomputes threshold (`:726-751`).
* `removeSigner(s)` permissionless iff `!isValidSigner(s)` (`:285-290`), where
  `isValidSigner(a) = HATS.isWearerOfHat(a, registeredSignerHats[a])` (`:549-554`).
* Guard `checkTransaction` (`:405-511`), order: `msg.sender == safe`; not inside another
  exec/module exec; exactly-once-per-`execTransaction` via Safe nonce delta vs transient counter;
  optional nested guard; DELEGATECALL only to enabled targets (snapshot owners/threshold/fallback),
  CALL to the Safe itself forbidden; `threshold == requiredValidSignatures(#owners)`;
  `_countValidSignatures(txHash(nonce-1), sigs, threshold) ≥ threshold`, where a signature counts only
  if its recovered/declared owner is a **currently valid hat wearer** (`:649-689`). Safe v1.4.1 has
  already run `checkSignatures` before the guard (`SAFE contracts/Safe.sol:170-177`), so contract
  (v=0) / approved-hash (v=1) signatures were verified by the Safe.
* `checkAfterExecution` (`:518-539`): for delegatecalls, `_checkSafeState` (`:958-981`) requires guard
  unchanged, threshold, owners hash, fallback handler unchanged, and HSG the only module.
* Module path `execTransactionFromModule` (`:849-873`): only enabled (Zodiac) modules, same
  pre/post-flight constraints.
* HSG v1 (`v1.2-beta`, `HatsSignerGateBase.sol`) differs: `minThreshold/targetThreshold/maxSigners`
  (`:24, :87-160`), `reconcileSignerCount` (`:162-194`), single/multi signer hat variants; guard
  checks similar (`:407-500`).

### 1.8 Edge cases / pitfalls

1. **Gas-dependent fallback.** `_isActive`/`_isEligible` treat *any* failed staticcall as "use stored
   value". A caller that supplies little gas can make a module call fail (63/64 rule) and force the
   stored-status path; whether this flips a decision depends on the module/stored values. Contrast
   `checkHatStatus`/`checkHatWearerStatus`, which revert instead of falling back.
2. Malformed return (wrong length, word ≥ 2) also falls back (view paths) but reverts in the
   `check*` paths.
3. Top hats have `eligibility = toggle = address(0)`: staticcall to 0 succeeds with empty return →
   stored values (active, eligible unless bad standing). `setHatStatus`/`setHatWearerStatus` cannot be
   called for them (msg.sender ≠ 0) until a link sets modules.
4. `maxSupply == 0` means "does not exist" for `mintHat`, but `createHat` accepts `maxSupply = 0`.
5. `supply` counts only explicit mints/burns; dynamically revoked wearers still count.
6. A linked top hat's wearer is **not** its admin; admins come from the parent tree.
7. Transfer/renounce use static balance, so a module-revoked hat can still be transferred by an admin
   or renounced.
8. HSG warning (README): if the Safe itself has authority over signer hats (admin, toggle, eligibility),
   signers can change owners/threshold indirectly.

### 1.9 Abstract actor model

A forest of roles addressed by 256-bit ids whose bit-prefixes encode the admin chain (32-bit domain +
14×16-bit levels), optionally grafted under other trees by link pointers (acyclic, two-party
request/approve). A principal *holds* role h iff a static token bit is set **and** two
per-role predicates hold at evaluation time: an activity predicate (oracle contract `getHatStatus`, or
stored bit pushed by an EOA toggle) and an eligibility predicate (oracle `getWearerStatus`, or stored
bad-standing pushed by an EOA), with "oracle failure ⇒ stored value". Authority over h (mint, transfer,
reconfigure if mutable) belongs to anyone currently holding a strict ancestor of h. Downstream systems
(e.g. HSG over a Safe) use `isWearerOfHat(msg.sender|signer, h)` as their membership predicate.

---

## 2. Aragon OS ACL (v4.4.0, as used by Lido)

### 2.1 Authority state

`ACL.sol` (`ARA contracts/acl/ACL.sol`):
* `permissions[keccak256("PERMISSION", who, where, what)] -> paramsHash` (`:50`, hash fn `:464-466`).
  `NO_PERMISSION = 0` (`:41`); `EMPTY_PARAM_HASH = keccak256(uint256(0))` = unconditional (`:40`).
* `permissionParams[paramsHash] -> Param[]` with `Param{id:uint8, op:uint8, value:uint240}` (`:21-27,
  :51`). Params content-addressed by `keccak256(abi.encodePacked(uint256[]))`, stored once
  (`_saveParams` `:303-316`).
* `permissionManager[keccak256("ROLE", where, what)] -> manager` (`:54`, `:460-462`).
  `address(0)` = no manager; `BURN_ENTITY = address(1)` = burned (`:43`).
* `ANY_ENTITY = address(-1)` (`:42`).
* Encoded param word (`ACLSyntaxSugar.sol:90-104`): `id = byte 31 (MSB)`, `op = byte 30`,
  `value = low 240 bits`; logic params pack up to three `uint32` param indices in value
  (`decodeParamsList`: bits 0-31, 32-63, 64-95).
* Kernel: `apps[namespace][appId]`, ACL is `apps[APP_ADDR_NAMESPACE][DEFAULT_ACL_APP_ID]`
  (`kernel/Kernel.sol:196-198`).
* Initialization: `INITIALIZATION_BLOCK_POSITION` unstructured slot; `hasInitialized ⇔ initBlock ≠ 0
  ∧ block.number ≥ initBlock` (`common/Initializable.sol`), petrified = `uint256(-1)`
  (`common/Petrifiable.sol`).

### 2.2 Permission check

`hasPermission(who, where, what, how:uint256[])` (`ACL.sol:247-259`):
```
p := permissions[H(who,where,what)];  if p≠0 ∧ evalParams(p, who, where, what, how) → true
q := permissions[H(ANY_ENTITY,where,what)]; if q≠0 ∧ evalParams(q, ANY_ENTITY, where, what, how) → true
false
```
`evalParams` (`:266-281`): `EMPTY_PARAM_HASH → true`, else `_evalParam(hash, 0, ...)`.

`_evalParam(hash, i, ...)` (`:318-362`):
* `i ≥ len → false` (`:327-329`).
* `id == LOGIC_OP_PARAM_ID (204)` → `_evalLogic`.
* value source: `ORACLE (203)` → `checkOracle(value as address)` → 1/0 and `comparedTo := 1`;
  `BLOCK_NUMBER (200)` → `block.number`; `TIMESTAMP (201)` → `block.timestamp`;
  `PARAM_VALUE (205)` → `value` itself; otherwise `id` is an index into `how`:
  `id ≥ how.length → false`, `value = uint240(how[id])` (**truncation to 240 bits**, `:354`).
  `202` is unused (`:31`); there is **no SENDER param in 4.x** - the entity is matched by the
  permission key, or an app passes the sender explicitly in `how`.
* `op == RET (7)` → `value > 0`; else `compare(value, op, comparedTo)` with EQ/NEQ/GT/LT/GTE/LTE,
  any other op (incl. `NONE`) → false (`:407-415`).

`_evalLogic` (`:364-405`): `IF_ELSE(c,s,f)` → eval c, then s or f; `NOT(a)`; `OR`/`AND` short-circuit
on `a`; `XOR(a,b)`; for OR/AND the result is `b` after the short-circuit test.

`checkOracle` (`:417-450`): `staticcall(gas, oracle, canPerform(who, where, what, how))`; revert or
`returndatasize ≠ 32` → **false** (fail-closed); else the returned word as bool.

### 2.3 Guarded entry points

* App side (`apps/AragonApp.sol:24-58`): `auth(role) ≡ require(canPerform(msg.sender, role, []))`,
  `authP(role, params) ≡ require(canPerform(msg.sender, role, params))`.
  `canPerform`: false if `!hasInitialized()` or kernel unset; else
  `kernel.hasPermission(sender, address(this), role, params)` (`:42-58`).
* Kernel (`Kernel.sol:209-213`): false if no ACL app; else delegate to ACL. Kernel's own `auth` uses
  `APP_MANAGER_ROLE` with params `arr(namespace, appId)` (`:147-163, :231-237`) - permissions scoped by
  namespace/app id.
* Lido: `_auth(role)` = `canPerform(msg.sender, role, [])` (`LIDO contracts/0.4.24/Lido.sol:1389-1391`),
  `_auth(address)` = `msg.sender == address` (`:1394-1396`) for protocol contracts (staking router,
  accounting, vault hub, ...). NodeOperatorsRegistry: `_authP(SET_NODE_OPERATOR_LIMIT_ROLE,
  arr(id, vettedCount))` (`nos/NodeOperatorsRegistry.sol:386`); `_onlyNodeOperatorManager(sender, id) :=
  (sender == op.rewardAddress ∧ op.active) ∨ canPerform(sender, MANAGE_SIGNING_KEYS, arr(id))`
  (`:1472-1476`). So params let a role be restricted to a specific operator id / range.
* Agent (`APPS apps/agent/contracts/Agent.sol`): `execute(target, value, data)` guarded by
  `authP(EXECUTE_ROLE, arr(target, value, uint256(sig(data))))` (`:70-72`);
  `safeExecute` `authP(SAFE_EXECUTE_ROLE, arr(target, sig))` (`:97-99`);
  `forward(script)` requires `canPerform(sender, RUN_SCRIPT_ROLE, arr(uint256(keccak256(script))))`
  (`:238-256, :335-337`).
* Voting (`apps/voting/contracts/Voting.sol`): `newVote` `auth(CREATE_VOTES_ROLE)` (`:126`), `forward`
  requires `CREATE_VOTES_ROLE` (`:185-199`); `executeVote` is permissionless once `_canExecute`
  (`:165, :341-357`).

### 2.4 Authority-mutating transitions (ACL)

| function | guard | effect |
|---|---|---|
| `initialize(creator)` `:76-81` | `onlyInit`; `msg.sender == kernel` | `_createPermission(creator, ACL, CREATE_PERMISSIONS_ROLE, creator)` |
| `createPermission(e, app, role, mgr)` `:96-102` | `auth(CREATE_PERMISSIONS_ROLE)` on the ACL; `manager(app,role) == 0` | `permissions[e,app,role] = EMPTY_PARAM_HASH; manager = mgr` |
| `grantPermission(e, app, role)` / `grantPermissionP(..., params)` `:111-131` | `msg.sender == manager(app,role)` | `permissions[e,app,role] = params.len>0 ? saveParams : EMPTY` (overwrites) |
| `revokePermission(e, app, role)` `:140-145` | manager | `permissions[...] = 0` |
| `setPermissionManager(new, app, role)` `:153-158` | manager | manager := new |
| `removePermissionManager(app, role)` `:165-170` | manager | manager := 0 (re-creatable by CREATE_PERMISSIONS_ROLE holders) |
| `createBurnedPermission(app, role)` `:177-183` | `CREATE_PERMISSIONS_ROLE`; no manager | manager := `address(1)` |
| `burnPermissionManager(app, role)` `:190-195` | manager | manager := `address(1)` (no one can ever be msg.sender = 0x1 ⇒ frozen) |

Manager is per `(app, role)`, not per entity: a manager can grant any entity with any param program.

### 2.5 Time / replay

Time enters only via `BLOCK_NUMBER`/`TIMESTAMP` param sources (e.g. `TIMESTAMP LT t` = expiry,
`GTE t` = activation), and the initialization block. No signatures or nonces in the ACL (Agent's
ERC-1271 uses presigned hashes or a designated signer, `Agent.sol:266-283`).

### 2.6 Relay behaviour (EVMScripts / forwarders)

* `runScript(script, input, blacklist)` (`evmscript/EVMScriptRunner.sol:34-100`): executor =
  `registry.getScriptExecutor(script)` by the first 4 bytes spec id (enabled only,
  `EVMScriptRegistry.sol:101-109`); **delegatecall** into the executor in the app's context;
  `protectState` requires kernel and appId slots unchanged afterwards (`:102-108`).
* `CallsScript.execScript` (`evmscript/executors/CallsScript.sol:33-96`): script =
  `specId(4) ‖ [to(20) ‖ len(4) ‖ calldata(len)]*`; reject `to ∈ blacklist`; `call(gas-5000, to, 0,
  calldata)` - value is always 0; any failure reverts the whole script.
* Hence the callee sees `msg.sender = the forwarding app` (Voting, Agent). The original principal
  (voter, script creator) is **not** propagated; the ACL decides on the app's own grants
  (e.g. Lido grants roles to Voting/Agent). Agent `execute` forwards a single call with value from
  Agent; `msg.sender` at the target = Agent.

### 2.7 Edge cases / pitfalls

1. ANY_ENTITY branch evaluates params with `who = ANY_ENTITY` (`ACL.sol:254`): an oracle attached to an
   ANY_ENTITY permission receives `0xff..ff`, not the real sender.
2. `how` words are truncated to `uint240` before comparison (`:354`); address args fit, 256-bit hashes
   lose 16 bits (Agent's `RUN_SCRIPT_ROLE` param is `uint256(keccak(script))`, compared after
   truncation; param `value` itself is only 240 bits).
3. Out-of-range param index or arg index → false (fail-closed). A param program with a logic node
   pointing to itself recurses until gas runs out (no cycle check).
4. Oracle is fail-closed but receives all gas; an oracle that burns gas makes the outer call fail.
5. `grantPermission` to an entity already holding a param'd permission overwrites the params.
6. Removing a manager re-opens the role to `createPermission` by any `CREATE_PERMISSIONS_ROLE` holder.
7. `canPerform` is false before initialization, and before the init block.

### 2.8 Abstract actor model

A global, centrally stored relation `Perm ⊆ Entity × App × Role → ParamProgram`, where Entity
includes a wildcard, and `ParamProgram` is a small boolean expression tree over the call's argument
vector (supplied by the app), constants, block number/timestamp and external fail-closed oracles. Each
`(App, Role)` has one manager that may grant/revoke any entity and transfer/remove/burn management;
burning makes the role's grant set immutable. An app checks `Perm(msg.sender, this, role)(args)`. Relay
is by *forwarder apps* that execute scripts as themselves (delegatecalled executor issuing CALLs),
so authority is re-rooted at the forwarder; principals are never propagated.

---

## 3. Aave v3 (aave-v3-origin, Pool revision 11)

### 3.1 Authority state

* `PoolAddressesProvider` (`protocol/configuration/PoolAddressesProvider.sol`): `Ownable` owner;
  `_addresses[bytes32 id] -> address` (`:20`), ids `POOL, POOL_CONFIGURATOR, PRICE_ORACLE,
  ACL_MANAGER, ACL_ADMIN, PRICE_ORACLE_SENTINEL, DATA_PROVIDER` (`:23-29`) plus arbitrary ids (e.g.
  `UMBRELLA`, read by Pool `protocol/pool/Pool.sol:76`).
* `ACLManager` (`protocol/configuration/ACLManager.sol`) = OZ `AccessControl`
  (`dependencies/openzeppelin/contracts/AccessControl.sol`): `_roles[role].members[account]`,
  `_roles[role].adminRole` (`:50-56`), `DEFAULT_ADMIN_ROLE = 0x00` (`:56`).
  Roles: `POOL_ADMIN, EMERGENCY_ADMIN, RISK_ADMIN, FLASH_BORROWER, BRIDGE, ASSET_LISTING_ADMIN`
  = `keccak256('<NAME>')` (`ACLManager.sol:15-20`). Constructor grants `DEFAULT_ADMIN_ROLE` to
  `provider.getACLAdmin()` (non-zero) **once** (`:29-34`).
* Proxies: `InitializableImmutableAdminUpgradeabilityProxy` with `_admin` **immutable** = provider
  (`misc/aave-upgradeability/BaseImmutableAdminUpgradeabilityProxy.sol:17-25`), implementation in
  the EIP-1967 slot (`BaseUpgradeabilityProxy`).
* Pool user-level authority: `_positionManager[user][manager]` (`Pool.sol:840-899`), debt-token
  `_borrowAllowances[delegator][delegatee]` (`protocol/tokenization/base/DebtTokenBase.sol:24`).

### 3.2 Guarded entry points

* Provider: every setter `onlyOwner` (`PoolAddressesProvider.sol:47-156`): `setMarketId`,
  `setAddress(id, a)` (raw overwrite of any id, including proxy ids), `setAddressAsProxy(id, impl)`,
  `setPoolImpl`, `setPoolConfiguratorImpl`, `setPriceOracle`, `setACLManager`, `setACLAdmin`,
  `setPriceOracleSentinel`, `setPoolDataProvider`.
  `_updateImpl(id, impl)` (`:167-181`): if no proxy → `new Proxy(admin = provider)`, store, and
  `proxy.initialize(impl, initialize(provider))`; else `proxy.upgradeToAndCall(impl,
  initialize(provider))`.
* Proxy (`BaseImmutableAdminUpgradeabilityProxy.sol:27-84`): `ifAdmin` - if `msg.sender == _admin`
  run `admin/implementation/upgradeTo/upgradeToAndCall`, else delegate to implementation;
  `_willFallback` reverts if the admin tries to reach the implementation (transparent proxy).
  `InitializableUpgradeabilityProxy.initialize(logic, data)` is unguarded except
  `_implementation()==0` (`dependencies/openzeppelin/upgradeability/InitializableUpgradeabilityProxy.sol:20-21`);
  the provider calls it in the creating tx.
* Pool implementation `initialize(provider)` - `initializer` (revision-versioned) and
  `provider == ADDRESSES_PROVIDER` immutable (`instances/PoolInstance.sol:29-31`).
* ACLManager: `setRoleAdmin` `onlyRole(DEFAULT_ADMIN_ROLE)` (`:37-42`); `addX/removeX` call public
  `grantRole/revokeRole` which require `hasRole(getRoleAdmin(role), msg.sender)`
  (`AccessControl.sol:129-150`); `renounceRole(role, a)` requires `a == msg.sender` (`:166-170`).
* Pool (`Pool.sol`): `onlyPoolConfigurator := provider.getPoolConfigurator() == msg.sender`
  (`:80-85`) on `initReserve, syncIndexesState, syncRatesState, setConfiguration,
  updateFlashloanPremium, configureEModeCategory*, setLiquidationGracePeriod, ...` (`:602-783`);
  `onlyPoolAdmin := ACLManager(provider.getACLManager()).isPoolAdmin(msg.sender)` (`:87-92`) on
  `rescueTokens` (`:789-797`); `onlyUmbrella := provider.getAddress('UMBRELLA') == msg.sender` on
  `eliminateReserveDeficit` (`:75-78, :822-838`); `onlyPositionManager(onBehalfOf) :=
  _positionManager[onBehalfOf][msg.sender]` on `setUserUseReserveAsCollateralOnBehalfOf`,
  `setUserEModeOnBehalfOf` (`:94-96, :859-893`). Flash loans: premium = 0 iff
  `ACLManager.isFlashBorrower(msg.sender)` (`:395-399`, `libraries/logic/FlashLoanLogic.sol:75`).
  `BRIDGE_ROLE` is defined but **no function in this revision checks `isBridge`** (grep: only
  `ACLManager.sol:19,105-117`).
* PoolConfigurator (`protocol/pool/PoolConfigurator.sol:38-73, 584-620`) - role matrix (each check
  reads the ACLManager from the provider at call time):
  * `onlyPoolAdmin`: `updateAToken`, `updateVariableDebtToken`, `setReserveActive`,
    `updateFlashloanPremium`.
  * `onlyAssetListingOrPoolAdmins`: `initReserves`.
  * `onlyRiskOrPoolAdmins`: `setReserveBorrowing`, `configureReserveAsCollateral`,
    `setReserveFlashLoaning`, `setReserveFactor`, `setBorrowCap`, `setSupplyCap`,
    `setLiquidationProtocolFee`, `setEModeCategory`, `setAssetCollateralInEMode`,
    `setAssetBorrowableInEMode`, `setReserveInterestRateData`.
  * `onlyRiskOrPoolOrEmergencyAdmins`: `setReserveFreeze`, `setReserveLtvzero`,
    `setAssetLtvzeroInEMode`, `setEModeCategoryIsolated`.
  * `onlyEmergencyOrPoolAdmin`: `setReservePause` (both overloads),
    `disableLiquidationGracePeriod`, `setPoolPause` (both overloads).
* User ops: `supply/deposit(asset, amt, onBehalfOf)` pull funds from `msg.sender`, credit
  `onBehalfOf` (`Pool.sol:118-139, 799-820`); `withdraw` burns `msg.sender`'s aTokens; `borrow(...,
  onBehalfOf)` debits `onBehalfOf`'s credit: if `user ≠ onBehalfOf`, `_decreaseBorrowAllowance(
  onBehalfOf, user, amount, debtIncrease)` (`tokenization/VariableDebtToken.sol:113-118`,
  `DebtTokenBase.sol:103-120`: require `allowance ≥ amount`, consume `min(allowance, debtIncrease)`).

### 3.3 Authority-mutating transitions

* Provider owner (governance executor): any address/implementation; can swap `ACL_MANAGER`
  (instantly re-rooting all role checks) and `ACL_ADMIN` (affects only *future* ACLManager
  deployments, because the constructor reads it once).
* `DEFAULT_ADMIN_ROLE` holders: grant/revoke any role whose admin is `DEFAULT_ADMIN_ROLE`; re-point
  role admins via `setRoleAdmin`.
* Users: `approvePositionManager(m, bool)` (`Pool.sol:840-850`); managers self-revoke via
  `renouncePositionManagerRole(user)` (`:852-857`); `approveDelegation` on debt tokens.

### 3.4 Time / replay

Roles have no expiry. Time appears in pause grace periods (`setPoolPause(paused, gracePeriod)`,
`PoolConfigurator.sol:474`) and liquidation grace periods (`Pool.setLiquidationGracePeriod`), and in
EIP-2612 `supplyWithPermit/repayWithPermit` (token-side nonces). Credit delegation allowances have no
expiry.

### 3.5 Relay behaviour

No principal relay: every guard uses `msg.sender` (`_msgSender()` = `msg.sender`, OZ `Context`).
The `onBehalfOf` parameter names the *account affected*, authorised by (a) no check when it only
benefits that account (supply/repay), (b) credit-delegation allowance (borrow), (c) position-manager
approval (collateral/eMode toggles). Proxy indirection: Pool/Configurator run behind proxies whose
immutable admin is the provider.

### 3.6 Edge cases / pitfalls

1. ACLManager admin is fixed at construction; changing `ACL_ADMIN` in the provider later has no effect
   on the live ACLManager.
2. `setAddress` can overwrite a proxied id with a non-proxy address, bypassing `_updateImpl`.
3. The proxy admin (provider) can never call Pool functions through the proxy (`_willFallback`).
4. `initialize` on a freshly created proxy is front-runnable in principle, but the provider creates and
   initializes atomically.
5. `rescueTokens` (pool admin) and Configurator `updateAToken/updateVariableDebtToken` are upgrade-level
   powers held by POOL_ADMIN, below the provider owner.

### 3.7 Abstract actor model

A two-level hierarchy: a root owner of a registry (`PoolAddressesProvider`) that maps names to
addresses, is the immutable admin of all core proxies, and can replace implementations or the ACL
contract itself; below it, an RBAC store (`ACLManager`) of flat roles with configurable admin roles
bootstrapped from the registry. Protocol contracts resolve "who is the configurator / ACL / umbrella"
**dynamically** through the registry at each call and check `msg.sender` against it. User-level
delegation is explicit and per-pair: position managers (boolean) and borrow allowances (bounded,
consumable).

---

## 4. Euler Ethereum Vault Connector (EVC)

### 4.1 Authority state

* Account algebra (`EthereumVaultConnector.sol:54-66, 1182-1195`): an *account* is any address; its
  `addressPrefix = bytes19(account >> 8)`; `haveCommonOwner(a,b) := (a xor b) < 0x100`; the 256
  accounts of an owner are `owner xor id`, `id ∈ [0,255]`.
* `ownerLookup[prefix] = {owner, isLockdownMode, isPermitDisabledMode}` (`:69-78`).
* `operatorLookup[prefix][operator] = uint256 bitfield` (`:80`); bit `owner xor account` authorises the
  operator for that sub-account (`:1205-1221`).
* `nonceLookup[prefix][nonceNamespace] = uint256` (`:82`).
* `accountCollaterals[account]`, `accountControllers[account]` - `SetStorage` (max 10 elements,
  `Set.sol:7`); `accountControllers` metadata stores the last successful status-check timestamp
  (`:955`).
* Execution context (`ExecutionContext.sol:23-33`, stored in ordinary storage
  `TransientStorage.sol:23`): bits 0-159 `onBehalfOfAccount`; byte masks `CHECKS_DEFERRED`,
  `CHECKS_IN_PROGRESS`, `CONTROL_COLLATERAL_IN_PROGRESS`, `OPERATOR_AUTHENTICATED`, `SIMULATION`; stamp.
  Deferred-check sets `accountStatusChecks`, `vaultStatusChecks`.

### 4.2 Authentication core

`_msgSender() = (msg.sender == EVC) ? context.onBehalfOfAccount : msg.sender` (`:1167-1176`) - inside
the permit self-call the signer is the sender.

`authenticateCaller(account, allowOperator, checkLockdown)` (`:758-802`):
1. `s := _msgSender()`; `owner := ownerLookup[prefix(account)].owner`.
2. If `haveCommonOwner(account, s)`: if `owner == 0` → **register `owner := s`** (lazy binding) and
   authenticate; else authenticate iff `owner == s`.
3. Else if `allowOperator ∧ operatorBit(account, s)` → authenticate.
4. If authenticated and `owner ≠ account` and `account.code.length ≠ 0` → **reject** (non-owner
   sub-accounts must be codeless).
5. Not authenticated → `EVC_NotAuthorized`; `checkLockdown ∧ lockdown` → `EVC_LockdownMode`.
The prefix variant (`:812-824`) uses the registered owner or the prefix's id-0 address.

### 4.3 Guarded entry points

| function | guard | effect |
|---|---|---|
| `setLockdownMode(prefix, b)` `:291-303` | owner only (no operator, lockdown not checked) | set; disabling forbidden while `checksDeferred` or in permit self-call |
| `setPermitDisabledMode(prefix, b)` `:306-321` | owner only | set; disabling forbidden while deferred |
| `setNonce(prefix, ns, n)` `:324-338` | owner only; `n > current` | jump nonce forward (invalidate signed permits) |
| `setOperator(prefix, op, bits)` `:343-359` | owner only; `op ≠ EVC`, `op` not one of the owner's 256 accounts; value must change | overwrite whole bitfield |
| `setAccountOperator(account, op, auth)` `:364-401` | owner or operator of `account` (lockdown not checked); an operator may only change **its own** bit | set/clear bit `owner xor account` |
| `enable/disableCollateral`, `reorderCollaterals` `:416-447` | owner-or-operator, lockdown checked, not in checks / controlCollateral | set update; `requireAccountStatusCheck(account)` |
| `enableController(account, vault)` `:462-472` | owner-or-operator, lockdown checked | insert; status check |
| `disableController(account)` `:475-480` | **msg.sender is the controller being removed** (no owner auth) | remove msg.sender; status check |
| `permit(signer, sender, ns, nonce, deadline, value, data, sig)` `:485-548` | not in permit self-call; `sender == 0 ∨ sender == msg.sender`; `signer ≠ 0 ∧ isSignerValid`; prefix not permit-disabled; `nonce == current ∧ current ≠ 2^256-1`; `deadline ≥ block.timestamp`; `data ≠ ∅`; `ecrecover(EIP712) == signer` or ERC-1271 | `nonce := nonce+1`; self-call `callWithContextInternal(EVC, signer, value, data)` |
| `call(target, onBehalfOf, value, data)` `:553-568` | not in checks/controlCollateral; per `callWithAuthenticationInternal` | defer checks; call; run deferred checks if outermost |
| `controlCollateral(collateral, onBehalfOf, value, data)` `:571-597` | `onlyController(onBehalfOf)`: exactly one controller and it is `msg.sender` (`:133-148`); `collateral ∈ accountCollaterals[onBehalfOf]` | context gets `CONTROL_COLLATERAL_IN_PROGRESS`; call collateral vault with onBehalfOf = violator |
| `batch(items)` `:600-614` | each item authenticated as in `call` | |
| `batchRevert/batchSimulation` `:619-681` | as batch; always reverts with results | |
| `requireAccountStatusCheck(a)` `:696-702` | none (anyone may *add* a check) | defer or check now |
| `forgiveAccountStatusCheck(a)` `:705-713` | `onlyController(a)` | remove deferred check |
| `requireVaultStatusCheck()` / `forgiveVaultStatusCheck()` `:723-734` | vault = msg.sender | |

`callWithAuthenticationInternal(target, onBehalfOf, value, data)` (`:882-908`):
* `target == EVC` → require `onBehalfOf == 0 ∧ value == 0`, **delegatecall** self (preserves
  msg.sender for nested authentication).
* else if `target ≠ msg.sender` → `authenticateCaller(onBehalfOf, allowOperator=true,
  checkLockdown=true)`; **if `target == msg.sender` no authentication** (a contract calling EVC to call
  itself may name any `onBehalfOf`).
* then `callWithContextInternal`.

`callWithContextInternal` (`:832-870`): `value == max` → whole EVC balance; set
`onBehalfOfAccount := onBehalfOf`; set `OPERATOR_AUTHENTICATED` iff the caller is not a common-owner
of `onBehalfOf` and `target ≠ msg.sender`, `target ≠ EVC`, not in controlCollateral; `CALL` target;
restore context.

### 4.4 Deferred checks

`call/batch/controlCollateral` set `CHECKS_DEFERRED`; on exit of the outermost frame
`restoreExecutionContext` (`:916-925`) sets `CHECKS_IN_PROGRESS`, clears `onBehalfOf`, and runs
`checkStatusAll(Account)` then `(Vault)`. Account check (`:935-960`): 0 controllers → ok; >1 →
`EVC_ControllerViolation`; else `staticcall(controller.checkAccountStatus(account, collaterals))` must
return its own selector; on success store timestamp. Vault check (`:983-991`): `call(vault.
checkVaultStatus())` must return selector. `nonReentrantChecksAcquireLock` (`:180-192`) prevents
re-entry during checks.

### 4.5 Time / replay

* Permit: sequential nonce per `(prefix, namespace)`; `deadline < block.timestamp` reverts (deadline is
  inclusive). Owner may jump a namespace forward (`setNonce`). `2^256-1` is a dead nonce.
* EIP-712 domain `EIP712Domain(string name,uint256 chainId,address verifyingContract)` with name
  "Ethereum Vault Connector" (`:27, :34-35, :1157-1159`); struct `Permit(address signer,address
  sender,uint256 nonceNamespace,uint256 nonce,uint256 deadline,uint256 value,bytes data)` (`:37-39,
  :1063-1088`). Cached separator recomputed on chain-id change.
* ECDSA: 65-byte only, low-s enforced, `v` not checked beyond ecrecover (`:1098-1129`); ERC-1271 only if
  signer has code (`:1141-1153`); ECDSA tried first.
* `isSignerValid` excludes the 256-address groups of `0x0`, `0x100` (EIP-7587 precompiles) and
  `0x4200..00` predeploys (`:1047-1052`).

### 4.6 Relay behaviour - how vaults authenticate the original principal

The EVC is a relay that **calls** targets with `msg.sender = EVC` and publishes the principal in its
context. Vaults use `EVCUtil` (`utils/EVCUtil.sol`):
* `_msgSender()`: if `msg.sender == evc` → `evc.getCurrentOnBehalfOfAccount(0)` (reverts if none) else
  `msg.sender` (`:104-112`).
* `_msgSenderForBorrow()`: also requires the vault be an enabled controller of that account
  (`:119-134`), via `getCurrentOnBehalfOfAccount(address(this))` (`EVC:206-220`).
* `_authenticateCallerWithStandardContextState(onlyOwner)` (`:204-226`): through EVC, reject if
  `operatorAuthenticated ∨ controlCollateralInProgress ∨ checksInProgress`; optionally require the
  account to be its owner (or owner unregistered).
* `_callThroughEVC()` (`:164-187`): a vault called directly re-enters itself via
  `EVC.call(address(this), msg.sender, msg.value, msg.data)` - target == msg.sender ⇒ no EVC
  authentication; `onBehalfOf = original msg.sender`.
* `_onlyEVCWithChecksInProgress` (`:191-195`) guards `checkAccountStatus/checkVaultStatus`.

### 4.7 Edge cases / pitfalls

1. **Self-target exemption**: any contract X can call `EVC.call(X, victim, ...)` and receive a frame
   whose context says `onBehalfOf = victim` (operatorAuthenticated cleared). Only X observes it, so X
   must never treat such a self-routed context as proof of authority unless X itself set
   `onBehalfOf = its own msg.sender` (as `_callThroughEVC` does).
2. Owner binding is lazy: the first common-prefix address to authenticate becomes owner.
3. Operators set via `setOperator` get a raw bitfield; `setAccountOperator` lets an operator only
   clear/set its own bit.
4. Lockdown blocks operator/owner authentication in `call/batch` and collateral/controller changes,
   but not owner management functions; it cannot be disabled in a deferred or permit context.
5. Controller removal is controller-initiated only (`disableController` uses msg.sender).
6. Sub-account with code is rejected unless it is the owner (`:787-789`); a delegated 7702 EOA as
   *owner* is fine.
7. `value == type(uint256).max` forwards the EVC's entire balance.

### 4.8 Abstract actor model

Each EOA/contract owner controls 256 deterministically derived sub-accounts and can authorise
operators per sub-account (bitfield), freeze itself (lockdown), disable signed permits, and burn nonces.
Principals act through the EVC relay (directly, by operator, or by EIP-712 permit relayed by anyone or a
named sender); the EVC authenticates once, then calls the target with `msg.sender = EVC` while
exposing `(onBehalfOfAccount, flags)` in a context that the target reads back. A single enabled
controller vault obtains a capability to seize the account's collateral via `controlCollateral` and is
the only party that can release itself. Safety invariants (account solvency by controller, vault
caps) are checked once at the end of the outermost relay frame.

---

## 5. ERC-4337 EntryPoint (v0.7 / v0.8) and ERC-7579 accounts

### 5.1 Authority state

* `NonceManager.nonceSequenceNumber[sender][key:uint192] -> uint256` (`EP8 core/NonceManager.sol:14`);
  `nonce = key<<64 | seq`. `incrementNonce(key)` bumps `msg.sender`'s key (`:23-25`).
* `StakeManager` deposits/stakes per address (`core/StakeManager.sol`).
* Account state is account-defined: SimpleAccount `owner` (`accounts/SimpleAccount.sol:23`),
  immutable `_entryPoint`; Simple7702Account has **no** owner storage - the authority is the EOA key
  (`accounts/Simple7702Account.sol:39-41`).

### 5.2 handleOps flow (v0.8, `core/EntryPoint.sol`)

`handleOps(ops, beneficiary)` (`:58-76`, `nonReentrant` transient): validation loop for all ops, then
execution loop, then pay beneficiary.

Per-op validation `_validatePrepayment` (`:747-808`), order:
1. Copy/unpack; `userOpHash = getUserOpHash(op)` (`:761`); all gas fields ≤ `2^120-1` (`AA94`).
2. `requiredPrefund = (vgl + cgl + pmVgl + pmPostOpGl + pvg) * maxFeePerGas` (`:459-471`).
3. `_validateAccountPrepayment` (`:530-560`): `_createSenderIfNeeded` (factory via `SenderCreator`,
   or EIP-7702 init if `initCode` starts with `0x7702` padded to 20 bytes, `:479-518`); if no paymaster,
   `missingAccountFunds = max(0, prefund - deposit)`; **`sender.validateUserOp(op, userOpHash,
   missing)` with `msg.sender = EntryPoint`** and gas `verificationGasLimit` (`:571-601`); return must be
   exactly 32 bytes; then deduct prefund from sender's deposit (`AA21`).
4. `_validateAndUpdateNonce(sender, nonce)`: `nonceSequenceNumber[sender][key]++ == seq` (`AA25`,
   `:785-788`) - **after** account validation.
5. Verification gas ≤ `verificationGasLimit` (`AA26`).
6. Paymaster (`:615-680`): deduct prefund from paymaster deposit (`AA31`), call
   `validatePaymasterUserOp(op, userOpHash, prefund)` with `msg.sender = EntryPoint`, decode
   `(context, validationData)`.
7. `_validateAccountAndPaymasterValidationData` (`:689-716`): account `aggregator` must equal the
   expected aggregator (0 for `handleOps`) else `AA24`; time-range else `AA22`; paymaster
   aggregator field must be 0 (`AA34`) and in range (`AA32`).

`validationData` packing (`core/Helpers.sol:44-53`): `aggregator:160 | validUntil:48 << 160 |
validAfter:48 << 208`; `validUntil == 0 ⇒ ∞`; `aggregator == 1 ⇒ SIG_VALIDATION_FAILED`. Range test
v0.8: `block.timestamp > validUntil ∨ block.timestamp <= validAfter` ⇒ out of range (`:732`);
**v0.7: `< validAfter`** (`EP7 core/EntryPoint.sol:605`).

Execution `_executeUserOp` (`:201-274`) → self-call `innerHandleOp` (`:376-424`, `msg.sender ==
address(this)` only): if callData starts with `executeUserOp.selector`, the account receives
`executeUserOp(userOp, userOpHash)`, else raw `callData`; **`Exec.call(sender, 0, callData,
callGasLimit)` - the account sees `msg.sender = EntryPoint`**. Then `_postExecution` (`:821-885`):
gas accounting with 10% unused-gas penalty above 40k (`:948-957`); paymaster `postOp(mode, context,
actualGasCost, gasPrice)` if context non-empty; refund to sender or paymaster deposit.

`handleAggregatedOps` (`:79-137`): for each group, `aggregator ≠ address(1)`;
`aggregator.validateSignatures(ops, sig)` must not revert; each op's validationData aggregator must
equal the group's aggregator.

### 5.3 userOpHash and replay

* v0.7: `keccak256(abi.encode(hash(userOp), entryPoint, chainid))` (`EP7 core/EntryPoint.sol:363-368`).
* v0.8: EIP-712 `toTypedDataHash(domain("ERC4337","1",chainid,EntryPoint), structHash)` with
  `PackedUserOperation(address sender,uint256 nonce,bytes initCode,bytes callData,bytes32
  accountGasLimits,uint256 preVerificationGas,bytes32 gasFees,bytes paymasterAndData)`
  (`EP8 :140-146, 51-55`, `core/UserOperationLib.sol:32-35`); for 7702 initCode the initCode hash is
  overridden by `keccak(delegate ‖ initData)` read from the sender's delegation designator
  (`core/Eip7702Support.sol:24-34, 64-80`).
* Replay: (sender, key)-sequenced nonce, consumed by the EntryPoint; parallel keys = parallel queues.

### 5.4 Accounts

* `BaseAccount.validateUserOp` (`EP8 core/BaseAccount.sol:80-89`): `msg.sender == entryPoint`;
  `_validateSignature`; `_validateNonce` (no-op by default); pay prefund to msg.sender (failure
  ignored).
* `SimpleAccount` v0.8: signature = `ECDSA.recover(userOpHash, sig) == owner` (EIP-712 hash directly,
  `accounts/SimpleAccount.sol:73-80`); `execute/executeBatch` require `msg.sender ∈ {EntryPoint,
  owner}` (`_requireForExecute` `:68-70`); `withdrawDepositTo` and UUPS upgrade require `msg.sender ∈
  {owner, self}` (`:47-50, 101-108`); `initialize(owner)` once (`initializer`, `:58-65`).
  v0.7 SimpleAccount (`EP7 samples/SimpleAccount.sol`): `_requireFromEntryPointOrOwner` (`:100-102`),
  signature over `toEthSignedMessageHash(userOpHash)` (`:105-110`).
* `Simple7702Account` (`EP8 accounts/Simple7702Account.sol`): hard-coded EntryPoint v0.8
  `0x4337084D9E255Ff0702461CF8895CE9E3b5Ff108` (`:19-21`); valid iff `ECDSA.recover(hash, sig) ==
  address(this)` (the EOA itself, `:39-41`); `execute` requires `msg.sender ∈ {self, EntryPoint}`
  (`:43-49`); ERC-1271 with the same rule (`:35-37`).
* Paymasters (`core/BasePaymaster.sol:35-63, 148-150`): `validatePaymasterUserOp`/`postOp` only from
  EntryPoint; stake functions `onlyOwner`.

### 5.5 ERC-7579 reference account `MSAAdvanced` (`7579 src/MSAAdvanced.sol`)

* Module types (`interfaces/IERC7579Module.sol:9-14`): 1 validator, 2 executor, 3 fallback, 4 hook,
  8/9 pre-validation hooks (1271 / 4337).
* State: ERC-7201 `ModuleManagerStorage{validators (sentinel list), executors (sentinel list),
  fallbacks[selector] = (handler, calltype)}` (`core/ModuleManager.sol:32-49`); single hook slot
  (`core/HookManager.sol:16-23`); optional ERC-7484 `$registry` (`core/RegistryAdapter.sol:16`).
* `entryPoint()` = v0.7 `0x0000000071727De22E5E9d8BAf0edAc6f37da032` (`core/AccountBase.sol:29-31`).
* Guards:
  * `execute(mode, data)` - `onlyEntryPointOrSelf` (`AccountBase.sol:15-20`) + `withHook`
    (`MSAAdvanced.sol:49-88`); supports single/batch CALL and **DELEGATECALL**, default/try.
  * `executeFromExecutor(mode, data)` - `onlyExecutorModule` (`msg.sender ∈ executors`,
    `ModuleManager.sol:58-62`) + `withHook` + `withRegistry(msg.sender, EXECUTOR)` (`:97-148`).
    Executors thus act **as the account** (targets see `msg.sender = account`), including
    delegatecall.
  * `installModule(type, module, init)` - `onlyEntryPointOrSelf`, `withHook`, `withRegistry(module,
    type)`, `module.isModuleType(type)` (`:174-204`). `uninstallModule` - `onlyEntryPointOrSelf`,
    `withHook`, no registry check (`:209-236`). Hence modules are installed only via a validated
    userOp or by the account calling itself (e.g. from `execute` or an executor via
    `executeFromExecutor` → self-call).
  * `executeUserOp` - `onlyEntryPoint`, delegatecalls `callData[4:]` into itself (`:158-169`).
  * `validateUserOp` - `onlyEntryPoint`; **validator selected by `nonce >> 96`** (upper 160 bits of the
    nonce key); if not installed: before initialization accept `ECDSA(ethSigned(userOpHash)) ==
    address(this)` (7702 EOA bootstrap), else fail; installed → optional pre-validation hook may
    rewrite `(hash, sig)` then `validator.validateUserOp` (`:247-286`).
  * `isValidSignature(hash, data)` - validator = `data[0:20]`; same uninitialized-EOA rule;
    `validator.isValidSignatureWithSender(msg.sender, hash, sig)` (`:296-319`).
  * `initializeAccount(data)` - if `msg.sender ≠ self` require transient `INIT_SLOT` set (only set by
    `MSAProxy` constructor, `utils/MSAProxy.sol`, `lib/Initializable.sol:11-28`); then delegatecall a
    bootstrap (`:402-439`).
  * `fallback` (`ModuleManager.sol:296-351`): route `msg.sig` to handler; `CALLTYPE_STATIC` →
    staticcall, `CALLTYPE_SINGLE` → call, both with **`msg.sender` appended as the last 20 bytes of
    calldata** (ERC-2771 style). No hook.
  * `withHook` (`HookManager.sol:28-37`): `preCheck(msg.sender, msg.value, msg.data)` /
    `postCheck(hookData)` around guarded functions.
  * `onRedelegation()` only from self; uninstalls all modules (`core/ERC7779Adapter.sol:58-62`,
    `MSAAdvanced.sol:441-446`).

### 5.6 Relay behaviour summary

* EntryPoint is the relay: account validation authenticates the principal by signature over
  `userOpHash`; execution arrives with `msg.sender = EntryPoint`, and the account trusts it because the
  EntryPoint only executes ops it validated in the same `handleOps`.
* Factories see `msg.sender = SenderCreator` (`core/SenderCreator.sol:22-45`); 7702 init calls see
  `msg.sender = SenderCreator` too (`:47-68`).
* 7579 executors relay through `executeFromExecutor` (account becomes msg.sender downstream);
  fallback handlers authenticate the original caller from the appended 20 bytes, which is meaningful
  only if they also check `msg.sender == account`.

### 5.7 Edge cases / pitfalls

1. Nonce consumption happens after `validateUserOp`; an account must not rely on the nonce being
   already bumped during validation.
2. v0.7 vs v0.8 differ in `validAfter` boundary and userOpHash format (eth-signed vs EIP-712).
3. Paymaster validationData with non-zero aggregator is a hard failure; account `aggregator = 1`
   (sig failed) fails `AA24` under `handleOps`.
4. `MSAAdvanced` uses `nonce` bits as validator selector - non-standard; a validator is chosen by the
   bundled op, so each installed validator is an independent root of authority.
5. Executor modules can delegatecall arbitrary code into the account (full storage authority).
6. `MSAAdvanced.initializeAccount` detects 7702 via `extcodehash(address()) == keccak256(0xef01)`
   (`:412-418`); under the Final EIP-7702 text EXTCODEHASH operates on the 23-byte delegation
   indicator (`eip-7702.md:426-427`), so this branch appears never to fire (observation, not tested).
7. Fallback with a `DELEGATECALL` calltype silently returns success with empty data (no branch).

### 5.8 Abstract actor model

A singleton relay (EntryPoint) runs a two-phase protocol per operation: (1) ask the account (and
optionally a paymaster) to validate a signature over a domain-separated hash, receiving a packed
(authorizer, validUntil, validAfter) verdict, consume a (sender, key)-sequenced nonce and escrow gas
funds; (2) call the account with `msg.sender = relay`, which the account treats as authenticated.
Accounts are capability containers: modular accounts hold typed module sets (validators = authority
roots for signatures, executors = delegated actors that act as the account, hooks = pre/post guards,
fallbacks = selector-routed extensions receiving the original sender appended), and only the relay or
the account itself may change that set.

---

## 6. EIP-7702 (Final)

* Set-code tx type `0x04`, `authorization_list = [[chain_id, address, nonce, y_parity, r, s], ...]`
  (`eip-7702.md:50-69`); non-empty (`:80-82`); null destination invalid (`:73-74`).
* Per tuple (`:104-132`): chain id ∈ {0, current}; `nonce < 2^64-1`; `authority = ecrecover(keccak(0x05
  ‖ rlp([chain_id, address, nonce])))`, low-s; authority code empty **or already delegated**;
  `authority.nonce == nonce`; write `0xef0100 ‖ address` (or clear code if address = 0); `authority.
  nonce += 1`. Invalid tuples are skipped; last valid tuple per authority wins; **not rolled back on
  tx failure**. Processed after the sender's nonce increment ⇒ self-sponsored authorization must use
  `sender_nonce + 1`.
* Execution semantics (`:134-172`): CALL/CALLCODE/DELEGATECALL/STATICCALL and tx destinations load the
  delegate's code and execute it **in the context of the authority** (`address(this) = EOA`, storage
  and balance of the EOA, `msg.sender` = whoever called the EOA). `EXTCODESIZE` = 23, `EXTCODECOPY`/
  `EXTCODEHASH` operate on the indicator (`:151-159, 426-436`); `CODESIZE/CODECOPY` see the delegate
  code. One level only (no chains, `:168-172`); delegation to a precompile = empty code (`:161-166`).
* EIP-3607 relaxation (`:191-199`): an account whose code is a valid delegation indicator may still
  originate transactions.
* The EOA key retains full authority: it signs ordinary transactions, can re-delegate or clear at any
  time, and its ECDSA signatures remain valid wherever `ecrecover` is used.
* Broken invariants (`:481-494, 554-559`): balance may decrease without a tx from the account; nonce may
  increase mid-tx (CREATE); `tx.origin == msg.sender` can occur below the top frame (self-sponsoring:
  the EOA calls itself or its code calls out); multiple calls per tx. `extcodesize(a) == 0` no longer
  identifies "EOA" (delegated EOAs report 23).
* Delegate-contract security requirements (`:498-532`): sign over nonce, value, gas, target/calldata;
  initialization must be authenticated by the EOA key (no initcode ⇒ front-running risk);
  storage-layout collisions across re-delegations (ERC-7201).

### Interactions observed in the other systems

* Permit2 `SignatureVerification.verify` routes on `claimedSigner.code.length == 0`
  (`P2 libraries/SignatureVerification.sol:26-45`): a delegated EOA goes to the **ERC-1271 path only**;
  its plain ECDSA signature works only if the delegate implements `isValidSignature` accepting it
  (Simple7702Account does, `:35-41`).
* EVC tries ECDSA first, then 1271 (`EVC :530-535`) - delegated EOAs unaffected; but sub-accounts that
  are not the owner must be codeless (`:787-789`).
* 4337 v0.8 natively supports 7702 senders (`0x7702` initCode marker; hash includes the delegate).
* `MSAAdvanced` / `Simple7702Account` treat `ecrecover(...) == address(this)` as root authority.
* HSG/Safe signature schemes and Hats are unaffected except that `tx.origin`-style checks are invalid.

### Abstract actor model

An externally owned key becomes the root principal of an account whose behaviour is a mutable pointer to
code; every frame executing at the account runs that code with the account's identity and storage, and
any caller can trigger it. The key can always act directly (txs) and replace the pointer; the
delegate code defines additional, possibly relayed, authority paths (sub-keys, EntryPoint, modules).

---

## 7. Uniswap Permit2

### 7.1 Authority state

* Domain (`P2 EIP712.sol:15-40`): `EIP712Domain(string name,uint256 chainId,address
  verifyingContract)`, name "Permit2" (no version); cached separator recomputed when chain id changes.
* SignatureTransfer: `nonceBitmap[owner][wordPos:uint248] -> uint256` (`SignatureTransfer.sol:19`);
  `nonce → (wordPos = nonce >> 8, bitPos = nonce & 0xff)` (`:142-145`).
* AllowanceTransfer: `allowance[owner][token][spender] = PackedAllowance{amount:uint160,
  expiration:uint48, nonce:uint48}` (`AllowanceTransfer.sol:23`, `interfaces/IAllowanceTransfer.sol:79-86`),
  packed `nonce<<208 | expiration<<160 | amount` (`libraries/Allowance.sol:45-47`).
* Precondition outside Permit2: the owner must have ERC-20-approved Permit2; token transfers are
  `token.transferFrom(owner, to, amt)` with **`msg.sender = Permit2`** at the token
  (`SignatureTransfer.sol:67, 123`; `AllowanceTransfer.sol:93`).

### 7.2 SignatureTransfer (one-shot signed transfers)

`permitTransferFrom(permit{permitted{token,amount}, nonce, deadline}, {to, requestedAmount}, owner, sig)`
(`:22-29, 51-68`), order: `block.timestamp ≤ deadline` (else `SignatureExpired`); `requested ≤
permitted.amount`; `_useUnorderedNonce(owner, nonce)` (flip bit, revert if it was already set,
`:150-156`); verify signature over `hashTypedData(PermitTransferFrom(TokenPermissions permitted,
address spender,uint256 nonce,uint256 deadline))` where **`spender = msg.sender`** is injected by
Permit2 (`libraries/PermitHash.sol:21-23, 57-63`); transfer. Batch (`:71-127`): lengths equal, one
nonce for the whole batch, per-item `requested ≤ permitted`, zero amounts skipped.
Witness variants (`:32-43, 81-92`, `PermitHash.sol:31-36, 85-120`): type string = stub
`"PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,"`
‖ caller-supplied `witnessTypeString`, struct appends `witness` - binds arbitrary integrator data
(e.g. an order) into the owner's signature.
Owner-side invalidation: `invalidateUnorderedNonces(wordPos, mask)`: `bitmap |= mask` (`:130-134`).

### 7.3 AllowanceTransfer (time-bounded budgets)

* `approve(token, spender, amount, expiration)` by owner = msg.sender (`:26-30`): sets amount and
  expiration (`0 ⇒ block.timestamp`, i.e. valid only this block, `Allowance.sol:34-42`); nonce
  untouched.
* `permit(owner, PermitSingle{details{token,amount,expiration,nonce}, spender, sigDeadline}, sig)`
  (`:33-40`), anyone may submit: `block.timestamp ≤ sigDeadline`; signature over
  `PermitSingle(PermitDetails details,address spender,uint256 sigDeadline)PermitDetails(address
  token,uint160 amount,uint48 expiration,uint48 nonce)` (`PermitHash.sol:11-13`); `_updateApproval`
  requires `stored.nonce == details.nonce` then writes `(amount, expiration or now, nonce+1)`
  (`:131-142`, `Allowance.sol:13-30`). Batch: one sigDeadline/spender, per-detail nonces (`:43-56`).
* `transferFrom(from, to, amount, token)` by spender = msg.sender (`:59-94`): `block.timestamp ≤
  expiration` (else `AllowanceExpired`); if `amount_stored ≠ 2^160-1` require `amount ≤ stored` and
  decrement (max = unlimited, not decremented); transfer.
* `lockdown(pairs)` by owner: amount := 0 for each (token, spender) (`:97-110`).
* `invalidateNonces(token, spender, newNonce)` by owner: `newNonce > old`, `newNonce - old ≤ 2^16-1`
  (`:113-126`).

### 7.4 Signature verification (`libraries/SignatureVerification.sol:21-46`)

If `claimedSigner.code.length == 0`: accept 65-byte `(r,s,v)` or 64-byte EIP-2098 `(r, vs)`;
`ecrecover ≠ 0` and `== claimedSigner`. **No low-s check** (malleable sigs accepted; replay is still
prevented by nonces). Else: `IERC1271(claimedSigner).isValidSignature(hash, sig) == 0x1626ba7e`.

### 7.5 Edge cases / pitfalls

1. SignatureTransfer binds the spender to `msg.sender`; AllowanceTransfer `permit` binds the spender in
   the signed struct but can be submitted by anyone (front-running a permit only applies it).
2. Unordered nonces: any unused (word, bit) is valid; order-free replay protection with owner bulk
   cancellation.
3. Allowance nonce is per (owner, token, spender) and only advanced by signed permits or
   `invalidateNonces`; `approve` does not bump it, so an outstanding signed permit stays valid after a
   direct `approve`/`lockdown` (lockdown zeroes amount but not nonce).
4. Expiration `0` means "this block only" in both `approve` and `permit`.
5. EIP-7702 delegated EOAs are routed to ERC-1271 (see §6).

### 7.6 Abstract actor model

A token-agnostic delegation hub: owners pre-approve the hub on each token, then grant spenders either
(a) consumable, expiring budgets per (owner, token, spender) set directly or by signed permit with a
sequential per-triple nonce, or (b) one-shot transfer authorisations signed for a specific spender
(the caller), protected by an unordered nonce bitmap and an optional witness binding. Authority is
established by EIP-712 signatures verified by ECDSA for codeless owners and ERC-1271 for owners with
code; the hub then moves tokens as `msg.sender` at the token.

---

## 8. Minimal abstract primitives

The following primitives suffice to express all of the above (names are suggestions for a formal
model).

1. **Principal resolution ≠ msg.sender.** `principal(frame) = if caller ∈ TrustedRelays(callee) then
   relay.context(frame) else caller`. Instances: EVC `getCurrentOnBehalfOfAccount`; 4337 account
   trusting `msg.sender == EntryPoint` as "already validated"; 7579 fallback appended sender (ERC-2771);
   Permit2/HSG/Agent as acting identity.
2. **Relay frame with scoped context.** A relay sets context `(onBehalfOf, flags)` for exactly the
   duration of a sub-call and restores it (stack discipline); flags include
   operator-authenticated, control-collateral, checks-in-progress, simulation. Includes the
   *self-target exemption* (target == caller ⇒ no authentication, context spoofable only towards self).
3. **Signed authorization object.** `verify(domain(name,[version],chainId,verifyingContract),
   typedStruct, sig, signer)` with verifier = ECDSA (variants: low-s or not, 64/65 bytes) or ERC-1271,
   selected by code-length or try-order; the struct may bind the submitter (`spender = msg.sender`,
   EVC `sender`), an arbitrary witness, value and calldata.
4. **Replay-protection families.** (a) sequential nonce per (principal, key) with owner forward-jump
   (4337 key/seq, EVC prefix/namespace, Permit2 allowance with bounded jump); (b) unordered nonce
   bitmap with owner bulk invalidation (Permit2); (c) protocol account nonce consumed by authorization
   (7702); (d) consumed-once request records (Hats link requests).
5. **Validity windows.** deadline (inclusive), `validAfter/validUntil` packed with `0 = ∞` and
   version-dependent boundary, expiration with `0 = current block`, block-number/timestamp predicates.
6. **Bounded consumable budget with expiry.** `(amount, expiration, nonce)` per (owner, asset,
   spender), `max = unlimited`, decrement on use (Permit2, Aave borrow allowance w/o expiry).
7. **Flat RBAC with admin roles.** `hasRole(r,a)`, `adminOf(r)`, grant/revoke guarded by
   `hasRole(adminOf(r), caller)`, self-renounce, constructor bootstrap (Aave ACLManager).
8. **Parametrised permission predicate.** `Perm(entity|ANY, target, role) → program` where the
   program is an expression DAG over the call's argument vector (truncated words), constants,
   block/time, external fail-closed oracles and AND/OR/XOR/NOT/IF; per-(target, role) manager with
   transfer/remove/burn (Aragon).
9. **External status oracle with fallback policy.** `status = staticcall(module, q)`; validate
   (length, range, magic value); on failure: *fallback to stored value* (Hats), *fail-closed* (Aragon
   oracle, EVC checks), *revert* (Hats `check*`). Must model gas-dependence of failure.
10. **Push-or-pull status slot.** A stored bit writable only by a designated module address
    (EOA "humanistic" push) and also pullable from the same address if it is a contract.
11. **Hierarchical id-encoded admin tree.** `id = domain ‖ level₁ … level₁₄`, `ancestor(id,l) = id &
    mask(l)`, plus inter-tree link pointers (acyclic, request/approve, tippy-root constraints);
    `admin(u,h) ⇔ ∃ strict ancestor a of h. holds(u,a)` (top hat self-admin).
12. **Dynamic membership.** `holds(u,h) = token(u,h) ∧ active(h) ∧ eligible(u,h)` evaluated at use time
    (Hats), used as a guard by other systems (HSG owner hat, signer validity).
13. **Owner / sub-account algebra.** `account ↔ (prefix:bytes19, id:uint8)` by xor; lazily bound owner;
    per-(prefix, operator) bitfield; per-principal modes (lockdown, permit-disabled) that restrict entry
    paths and are not disableable from relayed contexts (EVC).
14. **Deferred end-of-frame invariant checks.** Sets of (account, vault) obligations accumulated during
    the outermost relay frame and discharged by external checkers before returning (EVC), and guard
    pre/post checks around a relayed execution comparing state snapshots (HSG `checkAfterExecution`,
    7579 hooks).
15. **Exclusive capability grant.** Owner enables a controller; the controller alone may act on the
    account's collateral through the relay and alone may release itself (EVC).
16. **Two-phase validate/execute relay with escrow.** validate (signature verdict + time window +
    aggregator), consume nonce, escrow gas from account or sponsor deposit, execute as relay, settle
    and refund (4337); delegated signature verification (aggregators).
17. **Account module capability sets.** Typed sets (validator, executor, fallback-by-selector, hook)
    mutable only by the relay or the account itself; executors act as the account (incl.
    delegatecall); validator chosen by op-supplied selector (7579).
18. **Code-delegated EOA.** account code = pointer to delegate; the key remains root (txs,
    re-delegation, ECDSA signatures); delegated code runs with `address(this) = EOA`; `codesize > 0`
    and `tx.origin == msg.sender` no longer characterise EOAs / top frames (7702).
19. **Registry indirection of authority sources.** Guards resolve the current ACL / configurator /
    module address through a registry at call time (Aave provider, Aragon kernel→ACL, HSG→Hats); the
    registry owner can re-root authority.
20. **Proxy with immutable admin (transparent).** Admin-only upgrade path that is disjoint from the
    user path; initializer guarded by "implementation unset" / versioned initializer (Aave).
21. **Threshold multisig over a dynamic signer set.** Count of signers in a set whose membership is a
    live predicate ≥ threshold, threshold derived from a config function of set size (HSG on Safe).
22. **Forwarder re-rooting.** A forwarder executes a script as itself (delegatecalled executor issuing
    CALLs with value 0), so downstream authority is the forwarder's grants; the originating principal is
    dropped (Aragon Voting/Agent).
23. **Irreversible sentinels / one-way flags.** Burned manager (`address(1)`), HSG `lock()`, Hats
    `makeHatImmutable`, EVC dead nonce `2^256-1`, Permit2 set nonce bits (never cleared).
