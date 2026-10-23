# OpenZeppelin Contracts: actor and authority model (source-grounded spec)

**Source.** `OpenZeppelin/openzeppelin-contracts` tag **v5.7.0** (latest v5 tag on 2026-10-22; commit
`cab19933c33c2ad1d4c7a84864a3601dddfd16f3`). Cloned to `research/src-oz`. All `file:line` references are to
`src-oz/contracts/` at that commit unless they are prefixed.

**Comparison sources.**
- `openzeppelin-contracts-upgradeable` v5.7.0 (`14f52c54`, in `research/src-ozu`), used for the ERC-7201 namespaces.
- `openzeppelin-contracts` v5.0.2 (`research/src-oz50`), used for the changes within 5.x.
- `openzeppelin-contracts` v4.9.6 (`dc44c9f1`, in `research/src-oz4`), used for the 4.x differences.
- Raw `AccessManager.sol` and `AuthorityUtils.sol` files from tags v5.1.0 through v5.6.1 (`research/am-versions`).

**Slot checks.** Every ERC-7201 slot constant quoted here was recomputed with an independent keccak implementation
(`scratchpad/tools/k.js`), and all of them matched. The selectors quoted were also recomputed.

**Notation.**
- `now` = `block.timestamp`. `T()` = `Time.timestamp()` = `SafeCast.toUint48(block.timestamp)` (Time.sol:26-28).
- `S` = `_msgSender()` and `D` = `_msgData()`.
- `pad(x)` = the 32-byte ABI word of `x`. Addresses and uints are left-padded. `bytesN` values are left-aligned and
  right-padded.
- `mapslot(p, k)` = `keccak256(pad(k) ‖ pad(p))`.

**Storage layout in the non-upgradeable package.** It is sequential: variables are laid out in declaration order,
following the C3 linearisation from the most base contract. So absolute slot numbers depend on what the user
inherits. Only the `AccessManager` layout is fixed, because it is a concrete contract.

**Storage layout in the upgradeable package.** Each module keeps its storage in a struct at the ERC-7201 base

`NS(id) = keccak256(abi.encode(uint256(keccak256(id)) - 1)) & ~0xff`.

The struct fields then follow at `NS+0`, `NS+1`, and so on, with normal packing.

**Initializable.** Since 5.5.0, `Initializable` is no longer transpiled. The same namespaced file serves both packages
(CHANGELOG 5.5.0).

---

## 0. Context (the sender abstraction): utils/Context.sol

- `_msgSender() = msg.sender` (Context.sol:17-19).
- `_msgData() = msg.data` (Context.sol:21-23).
- `_contextSuffixLength() = 0` (Context.sol:25-27).

All modules below authenticate through `_msgSender()`. They are therefore ERC-2771-aware whenever they are combined
with `ERC2771Context`. The exceptions are `ERC2771Context` itself and `Multicall`, which inspect the raw `msg.sender`.

---

## 1. Ownable: access/Ownable.sol

**1. State**

| | |
|---|---|
| Variable | `address private _owner` (Ownable.sol:21) |
| Non-upgradeable | one sequential slot (20 bytes, low-order) |
| Upgradeable | `erc7201:openzeppelin.storage.Ownable`, base `0x9016d09d72d40fdae2fd8ceac6b6234c7706214fd39c1cd1e609a0528c199300`; `_owner` at `NS+0` (src-ozu `access/OwnableUpgradeable.sol:22-28`) |

**2. Guards**

`onlyOwner` ≡ `_checkOwner()` (lines 48-51, 63-67). It reverts with `OwnableUnauthorizedAccount(S)` unless
`owner() == S`. `owner()` is virtual (line 56).

**3. Transitions**

| Function | Guard | Effect / events |
|---|---|---|
| `constructor(initialOwner)` (38-43) | `initialOwner ≠ 0`, else `OwnableInvalidOwner(0)` | `_transferOwnership(initialOwner)` |
| `renounceOwnership()` (76-78) | `onlyOwner` | `_owner := 0`. The owner can never be set again through the public API. |
| `transferOwnership(n)` (84-89) | `onlyOwner`, then `n ≠ 0`, else `OwnableInvalidOwner(0)` | `_owner := n` |
| `_transferOwnership(n)` (95-99) | internal, unguarded | `_owner := n`; emits `OwnershipTransferred(old, n)` |

**4. Time.** None.

**5. Relay.** None.

**6. Pitfalls**
- Renouncing is irreversible.
- `onlyOwner` uses `_msgSender()`, so with ERC-2771 the trusted forwarder can act as the owner.
- Upgradeable variant: `__Ownable_init(initialOwner)` is `onlyInitializing` (src-ozu `OwnableUpgradeable.sol:51-60`).
  Whoever first calls the initializer chooses the owner (see §12).

**7. Actor model.** There is a single principal, `owner`, which is an address or ⊥ (= 0). There is one permission,
`P_owner`, held iff `S = owner`. Ownership is transferred by a single owner-signed step, and renouncing it moves the
system to the absorbing state `owner = 0`.

**4.x differences (v4.9.6)**
- The constructor takes no arguments: `_transferOwnership(_msgSender())`, so the deployer becomes owner
  (4.9.6 `access/Ownable.sol:28-30`).
- Errors are require strings rather than custom errors.
- The zero-address check exists only in `transferOwnership`.
- Ownership lives in an ordinary sequential slot, with no namespace.

---

## 2. Ownable2Step: access/Ownable2Step.sol

**1. State**

| | |
|---|---|
| Inherited | `_owner` |
| Variable | `address private _pendingOwner` (line 26). In the non-upgradeable package it takes its own slot (cannot pack with `_owner`, since 20+20 > 32 bytes). |
| Upgradeable | `erc7201:openzeppelin.storage.Ownable2Step`, base `0x237e158222e3e6968b72b9db0d8043aacf074ad9f650f0d1606b4d82ee432c00`. This namespace is separate from Ownable's. |

**2–3. Entry points**

| Function | Guard | Effect / events |
|---|---|---|
| `transferOwnership(n)` (43-46, overrides) | `onlyOwner`, with no zero check | `_pendingOwner := n`; emits `OwnershipTransferStarted(owner(), n)`. `n = 0` is the "cancel" form. It replaces any existing pending owner. |
| `acceptOwnership()` (60-66) | `pendingOwner() == S`, else `OwnableUnauthorizedAccount(S)` | `_transferOwnership(S)` |
| `_transferOwnership(n)` (52-55, overrides) | internal | `delete _pendingOwner`, then `super` (`_owner := n`, `OwnershipTransferred`) |
| `renounceOwnership()` | inherited, `onlyOwner` | single step; also clears `_pendingOwner` via the override |

**4. Time.** None. A pending transfer never expires.

**6. Pitfalls**
- `pendingOwner = 0` can never be accepted, because `S ≠ 0` always holds.
- Renouncing remains a single step.
- Any stale pending owner can accept at any later time until it is overwritten.

**7. Actor model.** There are two principals: `owner` and `pending` (each an address or ⊥).
- `propose(n)` requires `S = owner` and sets `pending := n`.
- `accept()` requires `S = pending` and performs `owner := S; pending := ⊥`.
- `renounce()` requires `S = owner` and performs `owner := ⊥; pending := ⊥`.

**4.x.** The semantics are the same in 4.8 and later; 4.9.6 uses require strings.

---

## 3. AccessControl: access/AccessControl.sol

**1. State**

`struct RoleData { mapping(address => bool) hasRole; bytes32 adminRole; }` (50-53)

`mapping(bytes32 => RoleData) private _roles` (55), stored at slot `p`:

| Item | Slot |
|---|---|
| `hasRole[r][a]` | `mapslot(keccak256(pad(r) ‖ pad(p)), a)`, i.e. RoleData offset 0 |
| `adminRole[r]` | `keccak256(pad(r) ‖ pad(p)) + 1` |

- Upgradeable: `p = NS("openzeppelin.storage.AccessControl") = 0x02dd7bc7dec4dceedda775e58dd541e08a116c6c53815c0bd028192f7b626800`.
- `DEFAULT_ADMIN_ROLE = 0x00` (57) is a constant. Because storage defaults to zero, **every role's admin is
  `0x00` by default, including `0x00` itself**.

**2. Guards**

- `onlyRole(r)` ≡ `_checkRole(r)` ≡ `_checkRole(r, S)` (63-66, 84-96).
- It reverts with `AccessControlUnauthorizedAccount(S, r)` unless `hasRole(r, S)`.
- `hasRole` and `_checkRole` are virtual.

**3. Transitions**

| Function | Guard (in order) | Effect / events |
|---|---|---|
| `grantRole(r, a)` (120-122) | `onlyRole(getRoleAdmin(r))` | `_grantRole(r, a)` |
| `revokeRole(r, a)` (135-137) | `onlyRole(getRoleAdmin(r))` | `_revokeRole(r, a)` |
| `renounceRole(r, c)` (154-160) | `c == S`, else `AccessControlBadConfirmation()` | `_revokeRole(r, c)` |
| `_setRoleAdmin(r, adm)` (167-171) | internal | `adminRole[r] := adm`; emits `RoleAdminChanged(r, prev, adm)` |
| `_grantRole(r, a)` (180-188) | internal | If `¬hasRole(r, a)`: sets it true, emits `RoleGranted(r, a, S)`, returns `true`. Otherwise returns `false`. Idempotent; no event on a no-op. |
| `_revokeRole(r, a)` (197-205) | internal | Symmetric, emits `RoleRevoked(r, a, S)` |

**4. Time.** None.

**5. Relay.** None.

**6. Pitfalls**
- `DEFAULT_ADMIN_ROLE` administers itself (doc 44-47). Any holder can grant it to others or revoke it from co-admins.
- A role whose admin role has no members is frozen with respect to the public API.
- `_setRoleAdmin` can create cycles or self-administration. For example, with `adminRole[r] = r`, members manage
  each other.
- Roles can be granted to `address(0)`; there is no check.
- If the last admin calls `renounceRole(0x00, self)`, the role graph rooted at `0x00` is permanently frozen.
- Internal `_grantRole` in constructors or initializers is the only bootstrap.
- `onlyRole`'s argument `getRoleAdmin(r)` is evaluated when the call enters.

**7. Actor model**
- Principals are addresses.
- Roles are `bytes32`, with a membership predicate `M(r, a)`.
- Each role has an admin role `adm(r)`, which defaults to `0`.
- Permission to call `f` means `M(role_f, S)`.
- Granting or revoking `r` requires `M(adm(r), S)`.
- Self-removal is always allowed.
- Authority composes through the admin graph `r ↦ adm(r)`.

**4.x**
- `renounceRole(r, account)` requires `account == _msgSender()`.
- Internal `_grantRole` and `_revokeRole` return nothing.
- The deprecated `_setupRole` (= `_grantRole`) still exists.
- Reverts use the string `"AccessControl: account 0x.. is missing role 0x.."`.
- There is no namespace.

---

## 4. AccessControlEnumerable: access/extensions/AccessControlEnumerable.sol

**1. State.** `mapping(bytes32 => EnumerableSet.AddressSet) private _roleMembers` (17).
- `AddressSet = { Set{ bytes32[] _values; mapping(bytes32 => uint256) _positions } }` (EnumerableSet.sol:61-67, 448-450).
- Positions are `index + 1`, and 0 means absent.
- Upgradeable: `NS("openzeppelin.storage.AccessControlEnumerable") = 0xc1f6fe24621ce81ec5827caf0253cadb74709b061630e6b55e82371705932000`.

**2–3. Entry points**
- No new guards.
- `_grantRole` and `_revokeRole` are overridden (63-80) to add or remove the account only when the base function
  returns `true`.
- Invariant: `a ∈ _roleMembers[r] ⇔ hasRole(r, a)`, provided all writes go through these hooks.
- Views: `getRoleMember(r, i)` (uses `pos`, line 37), `getRoleMemberCount`, and `getRoleMembers` (added in 5.1).

**6. Pitfalls.** Enumeration order is unstable, because swap-and-pop happens on removal.

**7. Actor model.** Same as AccessControl, plus a derived finite set view of each role.

**4.x.** It uses `at(index)` and has no `getRoleMembers`. 4.x hooked `_grantRole` and `_revokeRole` without return
values, by checking `hasRole` around the call.

---

## 5. AccessControlDefaultAdminRules: access/extensions/AccessControlDefaultAdminRules.sol

**1. State (lines 43-51), packed and declared after AccessControl's `_roles`**

| Slot | Contents |
|---|---|
| s0 | `_pendingDefaultAdmin` (address, bits 0-159) and `_pendingDefaultAdminSchedule` (uint48, bits 160-207; 0 means unset) |
| s1 | `_currentDelay` (uint48, bits 0-47) and `_currentDefaultAdmin` (address, bits 48-207) |
| s2 | `_pendingDelay` (uint48, bits 0-47) and `_pendingDelaySchedule` (uint48, bits 48-95; 0 means unset) |

- Upgradeable: `NS("openzeppelin.storage.AccessControlDefaultAdminRules") = 0xeef3dac4538c82c8ace4063ab0acd2d15cdb5883aa1dff7c2673abb3d8698400`.
  The same three-slot struct sits at `NS+0..2`.
- Constants: `defaultAdminDelayIncreaseWait() = 5 days` (186-188, virtual).

**Helpers**
- `set(s) := s ≠ 0` (362-364).
- `passed(s) := s < block.timestamp` (369-371). **This comparison is strict.** The full `block.timestamp` is
  compared to the uint48 `s`.

**Derived views**
- `defaultAdmin() = _currentDefaultAdmin` (164-166). `owner() = defaultAdmin()` for ERC-5313 (70-72).
- `pendingDefaultAdmin() = (_pendingDefaultAdmin, _pendingDefaultAdminSchedule)` (169-171).
- `defaultAdminDelay() = (set(pds) ∧ passed(pds)) ? _pendingDelay : _currentDelay`, where `pds = _pendingDelaySchedule`
  (174-177). This is a *virtual materialisation*: the pending delay takes effect without any write.
- `pendingDefaultAdminDelay() = (set ∧ ¬passed) ? (_pendingDelay, pds) : (0, 0)` (180-183).

**Invariant.** `_currentDefaultAdmin` is the unique holder of `DEFAULT_ADMIN_ROLE` (or 0 if there is none). This holds
because `_grantRole(0x00, a)` reverts when `defaultAdmin() ≠ 0` (131-139), and `_revokeRole(0x00, defaultAdmin())`
clears it (142-147).

**2–3. Entry points (check order exactly as in source)**

**`constructor(initialDelay, initialDefaultAdmin)`** (56-62)
- Guard: `initialDefaultAdmin ≠ 0`, else `AccessControlInvalidDefaultAdmin(0)`.
- Effect: `_currentDelay := initialDelay`, then `_grantRole(0x00, initialDefaultAdmin)`.

**`grantRole(r, a)` and `revokeRole(r, a)`** (81-96)
- First check: `r == 0x00` reverts `AccessControlEnforcedDefaultAdminRules()`. This happens before any authorisation.
- Then the AccessControl path (`onlyRole(adm(r))`).

**`renounceRole(r, a)`** (111-120)
- If `r == 0x00 ∧ a == defaultAdmin()`:
  - Let `(n, s) = pendingDefaultAdmin()`.
  - It reverts `AccessControlEnforcedDefaultAdminDelay(s)` if `n ≠ 0 ∨ ¬set(s) ∨ ¬passed(s)`.
  - Otherwise it deletes `_pendingDefaultAdminSchedule`.
- Then `super.renounceRole`, which requires `a == S`. Note that the confirmation is checked *after* the delay check.

**`_setRoleAdmin(0x00, ·)`** (152-157) reverts. The admin of the default admin role is permanently `0x00`.

**`beginDefaultAdminTransfer(n)`** (195-208)
- Guard: `onlyRole(0x00)`.
- Computes `sched := toUint48(now) + defaultAdminDelay()`, using the *current* effective delay, fixed at this moment.
- Calls `_setPendingDefaultAdmin(n, sched)`.
- Emits `DefaultAdminTransferScheduled(n, sched)`.
- `n = 0` is allowed; it is the first step of renouncing.

**`_setPendingDefaultAdmin(n, s)`** (320-331)
- Reads `old` (the old schedule), then writes the pair.
- If `set(old)`, it emits `DefaultAdminTransferCanceled()`, before the Scheduled event.

**`cancelDefaultAdminTransfer()`** (211-222)
- Guard: `onlyRole(0x00)`.
- Effect: `_setPendingDefaultAdmin(0, 0)`, which emits Canceled iff a schedule was set.

**`acceptDefaultAdminTransfer()`** (225-248)
- Guard 1: `S == pendingDefaultAdmin().newAdmin`, else `AccessControlInvalidDefaultAdmin(S)`.
- Guard 2: `set(s) ∧ passed(s)`, else `AccessControlEnforcedDefaultAdminDelay(s)`.
- Effect, in order:
  1. `_revokeRole(0x00, defaultAdmin())` (emits RoleRevoked).
  2. `_grantRole(0x00, newAdmin)` (sets `_currentDefaultAdmin`, emits RoleGranted).
  3. Delete the pending admin and its schedule.

**`changeDefaultAdminDelay(d)`** (255-268)
- Guard: `onlyRole(0x00)`.
- Computes `sched := toUint48(now) + wait(d)`.
- Calls `_setPendingDelay(d, sched)`.
- Emits `DefaultAdminDelayChangeScheduled(d, sched)`.

**`wait(d)`** (`_delayChangeWait`, 293-309)
- Let `cur = defaultAdminDelay()`.
- `wait(d) = d > cur ? min(d, 5 days) : cur − d`.

**`_setPendingDelay(d, s)`** (338-353)
- If `set(old)`:
  - If `passed(old)`, it materialises: `_currentDelay := _pendingDelay`.
  - Otherwise it emits `DefaultAdminDelayChangeCanceled()`.
- Then `(_pendingDelay, _pendingDelaySchedule) := (d, s)`.

**`rollbackDefaultAdminDelay()`** (271-282)
- Guard: `onlyRole(0x00)`.
- Effect: `_setPendingDelay(0, 0)`.

**4. Time**
- The clock is `block.timestamp`, with uint48 schedules.
- "Passed" is **strict** (`s < now`). Even with delay 0, accepting requires a strictly later block timestamp.
  Contrast this with AccessManager's `≤` (§7).
- A pending admin transfer **never expires**.
- The delay used for a transfer is fixed at `begin`. Later delay changes do not reschedule it.
- Delay-change guarantee: after a decrease scheduled at time t, no transfer begun at or after t can complete before
  `t + cur`.

**6. Pitfalls**
- **The default-admin quorum is exactly 1.** Other roles can still default to admin `0x00`, so the single default
  admin controls them.
- Renouncing takes two steps: `begin(0)`, wait, then `renounceRole(0x00, self)`.
- Exposing internal `_grantRole(0x00, ·)` after a renounce would re-open the role (doc 128-129).
- A stale accepted-but-unused pending admin remains valid until it is cancelled or overwritten.

**7. Actor model.** This is AccessControl with a distinguished singleton principal `defaultAdmin`, which can only be
replaced by a two-phase handover:
1. Propose `(n, τ = now + δ)`.
2. `n` accepts when `τ < now`.

Here `δ` is a self-delayed parameter: a pending value with an activation time, where increases wait `min(new, 5d)`
and decreases wait `old − new`.

**4.x (4.9.0+).** The logic is identical, using require strings. `_grantRole` and `_revokeRole` return nothing. The
contract lives at `access/AccessControlDefaultAdminRules.sol`.

---

## 6. Time library (the clock used by AccessManager): utils/types/Time.sol

**Types and clock**
- `timestamp() = toUint48(block.timestamp)`. It reverts if the timestamp is ≥ 2^48 (26-28).
- `type Delay is uint112` (61). The packing (49-56, 117-132) is `raw = effect<<64 | valueBefore<<32 | valueAfter`:
  - `effect`: uint48, bits 64-111
  - `before`: uint32, bits 32-63
  - `after`: uint32, bits 0-31

**Functions**
- `toDelay(d) = wrap(d)` (66-68), i.e. `(before=0, after=d, effect=0)`.
- `_getFullAt(self, t)` (74-80): `effect ≤ t ? (after, 0, 0) : (before, after, effect)`.
- `getFull(self) = _getFullAt(self, T())` (86-88). `get(self) = getFull(self).0` (93-96).
  - So **`get` = `after` if `effect ≤ now`, else `before`**.
  - `effect = 0` means it is always `after`.
- `withUpdate(self, new, minSetback)` (103-112):
  - `v := get(self)` (the currently effective value).
  - `setback := max(minSetback, v > new ? v − new : 0)`.
  - `effect := T() + setback`.
  - It returns `(pack(before=v, after=new, effect), effect)`.

**Consequences**
- Any previously pending value is **discarded and overwritten**. The new "before" is the value effective now.
- Increases (`new ≥ v`) take effect after `minSetback`. With `minSetback = 0` they are immediate (`effect = now`, and
  `effect ≤ now`).
- Decreases take effect after `max(minSetback, v − new)`. This guarantees that for any time `t ≥ update time`,
  `t + get@t ≥ update time + v`. In words: shrinking a delay never lets an operation complete earlier than the old
  delay would have allowed, counted from the update.
- Arithmetic is checked: `T() + setback` overflows only near 2^48.

---

## 7. AccessManager: access/manager/AccessManager.sol

`contract AccessManager is Context, Multicall, IAccessManager` (62). Its sender is `Context` (`msg.sender`), so it is
not ERC-2771-aware unless a derived contract makes it so.

### 7.1 State (lines 66-118)

```
struct TargetConfig { mapping(bytes4 => uint64) allowedRoles; Time.Delay adminDelay; bool closed; }
struct Access       { uint48 since; Time.Delay delay; }                            // 1 slot
struct Role         { mapping(address => Access) members; uint64 admin; uint64 guardian; Time.Delay grantDelay; }
struct Schedule     { uint48 timepoint; uint32 nonce; }                            // 1 slot
uint64 constant ADMIN_ROLE  = 0;            // line 105
uint64 constant PUBLIC_ROLE = 2**64 - 1;    // line 110
mapping(address => TargetConfig) _targets;  // slot 0
mapping(uint64  => Role)         _roles;    // slot 1
mapping(bytes32 => Schedule)     _schedules;// slot 2
bytes32 _executionId;                       // slot 3 (plain storage, not transient)
```

The slot numbers above are exact for the non-upgradeable contract, which has no other storage. For the upgradeable
variant, replace slot `i` with `NS + i`, where
`NS("openzeppelin.storage.AccessManager") = 0x40c6c8c28789853c7efd823ab20824bbd71718a8a5915e855f6f288c9a26ad00`
(src-ozu `AccessManagerUpgradeable.sol:113-125`).

**Per-target slots.** Let `bt = mapslot(0, target)`.

| Item | Slot | Bits |
|---|---|---|
| `allowedRoles[target][sel]` | `keccak256(pad(sel) ‖ bt)`, with `sel` left-aligned | uint64 at bits 0-63 |
| `adminDelay` | `bt+1` | Delay at bits 0-111 |
| `closed` | `bt+1` | bool at bits 112-119 |

**Per-role slots.** Let `br = mapslot(1, roleId)`.

| Item | Slot | Bits |
|---|---|---|
| `members[a]` | `mapslot(br, a)` | `since` at 0-47, `delay` at 48-159 |
| `admin` | `br+1` | 0-63 |
| `guardian` | `br+1` | 64-127 |
| `grantDelay` | `br+1` | 128-239 |

**Schedules.** Slot `mapslot(2, id)`, with `timepoint` at bits 0-47 and `nonce` at bits 48-79.

**Defaults, which follow from zero storage**
- Every `(target, selector)` requires role 0, i.e. ADMIN.
- Every role's `admin` and `guardian` are 0 (ADMIN).
- All delays are 0.
- No target is closed.

**Constants (virtual)**
- `expiration() = 1 weeks` (164-166).
- `minSetback() = 5 days` (169-171).

### 7.2 Membership predicate

`hasRole(r, a)` (217-227):
- `r == PUBLIC_ROLE` gives `(true, 0)`.
- Otherwise `(since ≠ 0 ∧ since ≤ T(), members[r][a].delay.get())`.

Membership becomes active at `since`, which is inclusive. The second component is the caller's current *execution
delay* in that role.

### 7.3 `canCall(caller, target, sel)` (140-161), the IAuthority-compatible policy (view)

The branches are evaluated in this order:
1. `isTargetClosed(target)` gives `(false, 0)`.
2. `caller == address(this)` gives `(_isExecuting(target, sel), 0)`. This is the **relay branch**.
3. `sel == setAuthority.selector (0x7a9e5e4b)` gives:
   - `(isAdmin ? (d == 0, d) : (false, 0))`,
   - where `d = max(execDelay_ADMIN(caller), getTargetAdminDelay(target))`.
   - This branch is **new in 5.7.0**; it is absent in 5.0.2 through 5.6.1.
4. Otherwise, with `r = allowedRoles[target][sel]` and `(m, d) = hasRole(r, caller)`, it gives
   `m ? (d == 0, d) : (false, 0)`.

Output space: `(true, 0)` means immediate; `(false, d > 0)` means allowed only after scheduling; `(false, 0)` means
denied.

### 7.4 Self-administration: `_getAdminRestrictions(data)` (625-665) and `_canCallSelf(caller, data)` (691-717)

**`_getAdminRestrictions(data)`** returns `(adminRestricted, role, opDelay)`:
- `|data| < 4` gives `(false, 0, 0)`.
- `labelRole`, `setRoleAdmin`, `setRoleGuardian`, `setGrantDelay`, `setTargetAdminDelay` give `(true, ADMIN_ROLE, 0)`.
- `updateAuthority`, `setTargetClosed`, `setTargetFunctionRole` give `(true, ADMIN_ROLE, getTargetAdminDelay(t))`,
  where `t = abi.decode(data[4:36], address)` is the first argument.
- `grantRole`, `revokeRole` give `(true, getRoleAdmin(r), 0)`, where `r = abi.decode(data[4:36], uint64)`.
  The decode reverts on a dirty word or on short data.
- Any other selector gives `(false, allowedRoles[address(this)][sel], 0)`. Since 5.1 this lets functions that a
  derived contract adds under `onlyAuthorized` be configured; 5.0 returned `(false, 0, 0)`.

**`_canCallSelf(caller, data)`**:
1. `|data| < 4` gives `(false, 0)`.
2. `caller == this` gives `(_isExecuting(this, sel), 0)`.
3. Compute `(adm, r, od)` with `_getAdminRestrictions`.
4. `¬adm ∧ closed(this)` gives `(false, 0)`. Closing the manager never blocks its admin functions.
5. `(in, ed) = hasRole(r, caller)`. If `¬in`, the result is `(false, 0)`.
6. Let `d = max(od, ed)`. The result is `(d == 0, d)`.

**`_canCallExtended(caller, target, data)`** (676-686):
- `target == this` gives `_canCallSelf`.
- Otherwise `|data| < 4` gives `(false, 0)`, and anything else gives `canCall(caller, target, data[0:4])`.

### 7.5 The `onlyAuthorized` guard ≡ `_checkAuthorized()` (124-127, 604-615)

- Let `c = S`. Compute `(imm, d) = _canCallSelf(c, D)`.
- If `imm`, the call proceeds.
- Else if `d == 0`, it reverts `AccessManagerUnauthorizedAccount(c, requiredRole)`.
- Else it calls `_consumeScheduledOp(hashOperation(c, address(this), D))`. A delayed admin operation can therefore be
  run either by calling the function directly after it was scheduled, or through `execute`.

### 7.6 Entry points (each guard listed in check order)

#### Role and target configuration

**`labelRole(r, label)`** (231-236)
- Guard: `onlyAuthorized` (ADMIN, opDelay 0).
- Then `r ∈ {ADMIN, PUBLIC}` reverts `AccessManagerLockedRole`.
- Effect: emits `RoleLabel` only.

**`grantRole(r, a, execDelay)`** (239-241, 276-303)
- Guard: `onlyAuthorized` (role `admin(r)`, opDelay 0).
- `r == PUBLIC` reverts `LockedRole`.
- If the account is new (`since == 0`):
  - `since := T() + grantDelay(r).get()`, using the current grant delay.
  - `delay := toDelay(execDelay)`, effective immediately.
- Otherwise (an existing member, **including a pending member whose `since > now`**):
  - `since` is unchanged.
  - `(delay, eff) := delay.withUpdate(execDelay, 0)`. Increases are immediate; decreases wait `old − new`.
- Emits `RoleGranted(r, a, execDelay, since_or_eff, newMember)`. For an existing member the 4th field is the delay
  effect time.

**`revokeRole(r, a)`** (244-246, 311-324)
- Guard: `onlyAuthorized` (role `admin(r)`).
- `r == PUBLIC` reverts `LockedRole`.
- If `since == 0`, it is a no-op returning false, with no event.
- Otherwise it deletes `members[r][a]` (both since and delay) and emits `RoleRevoked`.

**`renounceRole(r, c)`** (249-254)
- Guard: no authorisation, but `c == S` is required, else `AccessManagerBadConfirmation`.
- Effect: `_revokeRole(r, c)`. ADMIN_ROLE can be renounced.

**`setRoleAdmin(r, adm)`** (257-259, 334-342)
- Guard: `onlyAuthorized` (ADMIN, 0).
- `r ∈ {ADMIN, PUBLIC}` reverts `LockedRole`.
- Effect: `admin := adm`; emits `RoleAdminChanged`.

**`setRoleGuardian(r, g)`** (262-264, 352-360)
- Same guard and lock as `setRoleAdmin`.
- Effect: `guardian := g`; emits `RoleGuardianChanged`.

**`setGrantDelay(r, d)`** (267-269, 367-376)
- Guard: `onlyAuthorized` (ADMIN, 0).
- `r == PUBLIC` reverts. Note that ADMIN_ROLE's grant delay *is* settable.
- Effect: `grantDelay.withUpdate(d, minSetback())`. Every change, including an increase, waits at least 5 days.
- Emits `RoleGrantDelayChanged(r, d, effect)`.

**`setTargetFunctionRole(t, sels[], r)`** (380-403)
- Guard: `onlyAuthorized` (ADMIN, opDelay `adminDelay(t)`).
- For each selector: `sel == setAuthority.selector` reverts `AccessManagerLockedFunction` (new in 5.7).
- Effect: `allowedRoles[t][sel] := r`; emits `TargetFunctionRoleUpdated` once per selector.
- `t == address(this)` is allowed.

**`setTargetAdminDelay(t, d)`** (406-420)
- Guard: `onlyAuthorized` (ADMIN, opDelay 0).
- Effect: `adminDelay.withUpdate(d, minSetback())`; emits `TargetAdminDelayUpdated(t, d, effect)`.

**`setTargetClosed(t, b)`** (424-436)
- Guard: `onlyAuthorized` (ADMIN, `adminDelay(t)`).
- Effect: `closed := b`; emits `TargetClosed`.
- In 5.0.x, `t == this` reverted `AccessManagerLockedAccount`. This was removed in 5.1.

**`updateAuthority(t, n)`** (594-596)
- Guard: `onlyAuthorized` (ADMIN, `adminDelay(t)`).
- Relay: **CALL** `t.setAuthority(n)` with `msg.sender = manager` and value 0.

#### Delayed operations

**`schedule(t, data, when)`** (451-485). Let `c = S`.
- Compute `(_, sb) = _canCallExtended(c, t, data)` (the `immediate` flag is ignored) and `minWhen = T() + sb`.
- It reverts `AccessManagerUnauthorizedCall(c, t, data[0:4])` if `sb == 0 ∨ (when > 0 ∧ when < minWhen)`.
  An immediate caller **cannot** schedule.
- Then `when := max(when, minWhen)`. `when = 0` means "as early as possible", and any later `when` (up to 2^48) is
  allowed.
- Compute `id = hashOperation(c, t, data) = keccak256(abi.encode(c, t, data))` (588-590).
- `_checkNotScheduled(id)` (492-497) reverts `AlreadyScheduled` if `tp ≠ 0 ∧ ¬expired(tp)`.
- Effect: `nonce := old + 1` (unchecked uint32, so it wraps); `timepoint := when`.
- Emits `OperationScheduled(id, nonce, when, c, t, data)`.

**`execute(t, data)` payable** (503-534). Let `c = S`.
- Compute `(imm, sb) = _canCallExtended(c, t, data)`.
- If `¬imm ∧ sb == 0`, it reverts `UnauthorizedCall`.
- Compute `id = hash(c, t, data)`.
- If `sb ≠ 0 ∨ getSchedule(id) ≠ 0`, it calls `nonce := _consumeScheduledOp(id)`. An immediate caller with a live
  schedule for the same id also consumes it.
- Let `prev := _executionId`. Set `_executionId := H(t, data[0:4])`.
- **CALL** `t` with `data` and `msg.value` (`Address.functionCallWithValue`: bubbles reverts; reverts if `t` has no
  code and returns nothing).
- Restore `_executionId := prev`.
- Return `nonce`, which is 0 if nothing was consumed.

**`_consumeScheduledOp(id)`** (569-585). Let `tp = timepoint`.
- `tp == 0` reverts `NotScheduled`.
- `tp > T()` reverts `NotReady`.
- `expired(tp)` reverts `Expired`.
- Effect: `timepoint := 0`, keeping the nonce. Emits `OperationExecuted(id, nonce)`.

**`cancel(c, t, data)`** (537-553). Let `m = S`.
- `data[0:4]` reverts if `|data| < 4`.
- `id = hash(c, t, data)`.
- Raw `timepoint == 0` reverts `NotScheduled`. An **expired-but-uncleared** operation can still be cancelled.
- `¬_canCancel(c, t, data)` reverts `UnauthorizedCancel(m, c, t, sel)`.
- Effect: `timepoint := 0` (nonce kept); emits `OperationCanceled(id, nonce)`.

**`_canCancel(c, t, data)`** (722-748), evaluated in order:
1. `c == m` (the proposer) is allowed.
2. `hasRole(ADMIN, m)` or `hasRole(guardian(allowedRoles[t][sel]), m)` is allowed.
3. If `t == this`, `adminRestricted`, and `r ≠ ADMIN`, the result is `hasRole(r, m)`. This means a role's admin can
   cancel scheduled grant/revoke operations for that role. This branch is **new in 5.7.0**.
4. Otherwise it is denied.

Note: for `t == this` the guardian is looked up using `allowedRoles[this][sel]`, which defaults to 0, so the guardian
of ADMIN_ROLE, which is locked at 0.

**`consumeScheduledOp(c, data)`** (556-562). Let `t = S`.
- Requires `IAccessManaged(t).isConsumingScheduledOp() == 0x8fb36037`, a STATICCALL since the function is declared
  view. Otherwise it reverts `AccessManagerUnauthorizedConsume(t)`.
- Effect: `_consumeScheduledOp(hash(c, t, data))`.
- **A contract can consume only operations whose target is itself.**

**`multicall(bytes[])`** (inherited, §10)
- A DELEGATECALL to self for each item. `msg.sender` is preserved, so each item is authorised independently against
  `_msgData() = data[i]`.
- `multicall` is non-payable, so a batched `execute` always sees `msg.value = 0`.

#### Constructor and helpers

**`constructor(initialAdmin)`** (129-136)
- Guard: `initialAdmin ≠ 0`.
- Effect: `_grantRole(ADMIN, initialAdmin, 0, 0)`, active immediately with no execution delay.
- The upgradeable variant has `__AccessManager_init` and a public initializer (5.1+).

**Helpers**
- `_isExecuting(t, s) = (_executionId == H(t, s))`, where `H(t, s) = keccak256(pad(t) ‖ s‖0^28)` (753-755, 774-776).
  This equals the 5.0 `keccak256(abi.encode(t, s))`.
- `_isExpired(tp) = tp + expiration() ≤ T()` (760-762). The arithmetic is checked uint48.
- `getSchedule(id) = expired(tp) ? 0 : tp` (440-443).
- `getNonce(id) = nonce` (446-448).

### 7.7 Time semantics (exact)

- The clock is `T()`, a uint48 seconds timestamp. Durations are uint32.
- **Membership**: active iff `since ≠ 0 ∧ since ≤ T()`. Here `since = grantTime + grantDelay(r)` evaluated at the
  grant.
- **Operation window**: an operation scheduled at `τ` is executable iff `τ ≤ T() < τ + 604800`, i.e. **[τ, τ + 1 week)**.
  - Before `τ` it reverts `NotReady`; at or after `τ + 1w` it reverts `Expired`.
  - It is consumed at most once. Only one live schedule may exist per id. Expired operations may be re-scheduled
    without cancelling.
  - The nonce is incremented on each schedule, not on execute or cancel.
- **Delays are evaluated at different times**:
  - The scheduling delay `sb` is the caller's delay **at schedule time**.
  - At execute time, authorisation is re-checked (the caller must still be a member, and the target must still be
    open), but the stored `τ` is *not* re-validated against a new delay. Increasing a delay later does not postpone
    already-scheduled operations; revoking membership does block them.
- **Delay updates**:

  | Delay | Update rule | Notes |
  |---|---|---|
  | execution delay | `withUpdate(new, 0)` | increase is immediate; decrease takes `old − new` |
  | grantDelay | `withUpdate(new, minSetback = 5d)` | even an increase takes ≥ 5 days |
  | target adminDelay | `withUpdate(new, minSetback = 5d)` | even an increase takes ≥ 5 days |

  - A new member's execution delay is set immediately, with no setback.
  - Revoking and re-granting resets the execution delay immediately, but re-granting incurs the role's grant delay.
    IAccessManager.sol:130-133 notes this.
- **Overflow edge**: if `when > 2^48 − 1 − 1 week`, then `_isExpired` overflows (a Panic). The id is then stuck:
  scheduling it again and executing it both panic; only `cancel`, which never calls `_isExpired`, clears it.

### 7.8 Relay behaviour

| Call site | Opcode | `msg.sender` / value | How the callee authenticates |
|---|---|---|---|
| `execute` → `t` | CALL | manager / `msg.value` | If `t` is AccessManaged: `restricted` → `canCall(manager, t, sel)` → relay branch → `_executionId == H(t, sel)`. If `t` is Ownable/AccessControl-owned by the manager: `owner()==manager` / `hasRole(r, manager)`. |
| `execute(this, …)` → self | CALL | manager / `msg.value` | `onlyAuthorized` → `_canCallSelf(this, D)` → `_isExecuting(this, sel)` |
| `updateAuthority` → `t.setAuthority(n)` | CALL | manager / 0 | `AccessManaged.setAuthority`: `S == authority()` and `n.code.length > 0` |
| `consumeScheduledOp` → `t.isConsumingScheduledOp()` | STATICCALL | manager | It returns the magic value only while the `_consumingSchedule` flag is set |
| `multicall` → self | DELEGATECALL | original sender / original value | per-item `onlyAuthorized` |

`_executionId` binds only `(target, selector)`, not caller, arguments or depth. It is saved and restored, so nested
`execute`s are well-bracketed. Only the manager can appear as `caller == manager`, so the relay branch can be used
only by calls that the manager itself issues while that id is set:
- Nested `execute(this, execute(...))` fails unless the inner call's `(t, sel)` matches.
- `execute(this, multicall(...))` makes the sub-items fail, because each sub-item's selector differs from
  `multicall.selector`.

### 7.9 Pitfalls and edge cases

- **ADMIN_ROLE = 0** is the default value of every `allowedRoles` entry, every role admin and every guardian, so an
  unconfigured function is admin-only.
- ADMIN_ROLE's admin is locked to 0, so ADMIN is self-administered: any admin can grant or revoke admins.
- An admin with an execution delay must schedule every admin operation.
- The last admin can `renounceRole(ADMIN)`, which bricks the manager.
- **PUBLIC_ROLE = 2^64 − 1**:
  - Everyone is a member, with delay 0.
  - It cannot be granted, revoked, labelled, have a grant delay, or have its admin or guardian set.
  - It *can* be used as a target function role (anyone may call), as another role's admin (anyone can grant or revoke
    that role), or as a guardian (anyone may cancel that role's operations).
- **Closed targets**: `canCall` returns false for everyone, including the relay branch, so neither direct calls nor
  `execute` nor `schedule` work. Closing the manager itself blocks only its non-admin functions.
- **setAuthority** (5.7):
  - It cannot be assigned through `setTargetFunctionRole`.
  - Through `execute` it requires ADMIN plus `max(execDelay, targetAdminDelay)`.
  - Before 5.7, `allowedRoles[t][setAuthority]` defaulted to ADMIN with *no target admin delay*. An admin could then
    `execute(t, setAuthority(x))` and bypass the `updateAuthority` admin delay, and a non-admin could be granted that
    selector.
- **Same-operation-id rule**: `id = keccak256(abi.encode(caller, target, data))`. The caller is part of the id, so
  operations are not transferable between callers. There is at most one live schedule per id; to run concurrent
  copies, append a salt to `data` (IAccessManager.sol schedule NOTE).
- **`canCall(c, manager, sel)` misreports** the manager's own admin functions, because it consults `allowedRoles`, not
  `_getAdminRestrictions`.
- **Ownable or AccessControl contracts owned by the manager**: `renounceOwnership` and `renounceRole` become callable
  through `execute` by whoever holds the role mapped to those selectors (doc 55-58).
- **`hasRole` for a pending member** returns `(false, currentDelay)`. Re-granting a pending member only updates the
  delay; it does not reset `since`.
- **`execute` is payable but the manager has no `receive`.** ETH sent to `execute` is forwarded to the target.

### 7.10 Actor model

- **Principals**: addresses, plus the manager itself as a relay principal.
- **Roles**: `uint64`, with two distinguished values: ADMIN = 0, which is self-administered, and PUBLIC = max, which
  is universal.
- **Membership**: a time-activated relation `since(r, a)`, carrying a per-member execution delay that is a
  deferred-update `Delay`.
- **Permissions**:
  - Each target carries a table `(target, selector) ↦ role` (default ADMIN), a `closed` flag, and an `adminDelay`
    (a `Delay` with 5-day minimum setback).
  - Each role carries an `admin` role (who may grant and revoke it), a `guardian` role (who may cancel its
    operations), and a `grantDelay`.
- **Authorisation of `(caller, target, sel)`** yields one of: immediate, delayed by `d`, or denied, where
  `d = max(member exec delay, operation-specific admin delay)`.
- **Delayed calls** are mediated by a single-use schedule keyed by `hash(caller, target, data)` with window
  `[τ, τ + 1w)`. The schedule is consumed either by the manager (`execute`, then CALL with `msg.sender = manager`) or
  by the target itself (`consumeScheduledOp` while its flag is set).
- **The manager's own configuration** is the same model applied to the target `address(this)`, with a hard-coded
  selector→role and delay map (`_getAdminRestrictions`).
- **Composition**: managed contracts delegate *all* decisions to the manager through `canCall`, and fully trust calls
  coming from the manager while `_executionId` matches.

---

## 8. AccessManaged, AuthorityUtils and IAuthority

### State: access/manager/AccessManaged.sol:20-22

- `address _authority` and `bool _consumingSchedule` share one slot: authority in bits 0-159, flag in bits 160-167.
- Upgradeable: `NS("openzeppelin.storage.AccessManaged") = 0xf3177357ab46d8af007ab3fdb9af81da189e1068fefdc0073dca88a2cab40a00`.

### Guard: `restricted` (55-58) ≡ `_checkCanCall(S, D)` (95-111)

1. Compute `(imm, d) = AuthorityUtils.canCallWithDelay(authority(), S, address(this), bytes4(D[0:4]))`.
   `D[0:4]` reverts if `|D| < 4`. Using `restricted` on `receive` always reverts, and on `fallback` it depends on the
   calldata (doc 44-53).
2. If `imm`, the call proceeds.
3. Else if `d > 0`:
   - `_consumingSchedule := true`.
   - **CALL** `authority.consumeScheduledOp(S, D)` with `msg.sender = this`.
   - `_consumingSchedule := false`.
4. Else it reverts `AccessManagedUnauthorized(S)`.

The permission is determined by the **entry** selector of the current call frame. For this reason the modifier must
not be placed on internal functions, or on public functions that are also called internally (doc 35-42).

### `canCallWithDelay` (AuthorityUtils.sol:14-35)

- It STATICCALLs `canCall(caller, target, sel)` (selector `0xb7009613`) and copies at most 64 bytes of return data
  into zeroed scratch space.
- On failure it returns `(false, 0)`.
- On success:
  - `immediate := word0`. Any nonzero word counts as true.
  - `delay := word1`, but 0 if `word1 ≥ 2^32`.
- A 32-byte (plain IAuthority) return gives `delay = 0`. An authority with no code gives `(false, 0)`.
- 5.0 through 5.2 used `abi.decode` and checked the return length (reverts on dirty values). The assembly version is
  in 5.3+.

### Transitions

**`setAuthority(n)`** (66-75)
- Guard 1: `S == authority()`, else `AccessManagedUnauthorized(S)`.
- Guard 2: `n.code.length > 0`, else `AccessManagedInvalidAuthority(n)`.
- Effect: `_setAuthority(n)`, which emits `AuthorityUpdated(n)`.
- **This is not `restricted`; it authenticates the *current authority address* directly.**

**`constructor(initialAuthority)`** (27-29) has **no checks**.
- With `initialAuthority = 0` or an EOA, every `restricted` function is denied forever, and `setAuthority` can never
  be called because `S ≠ 0`.

**`isConsumingScheduledOp()`** (78-80) returns `0x8fb36037` iff the flag is set, else 0.
- This prevents a target that makes attacker-controlled calls from being made to consume its own schedules outside
  `restricted` (IAccessManaged.sol:26-31).
- The flag is ordinary storage, not transient.

### IAuthority (IAuthority.sol:9-14)

`canCall(address caller, address target, bytes4 sel) → bool` is the Dappsys interface. AccessManager returns
`(bool, uint32)`, which is ABI-compatible with it in the first word.

### Actor model

A managed contract has one authority principal.
- Every restricted entry `(this, sel)` asks the authority `canCall(S, this, sel)`. Delayed permissions are honoured by
  consuming the manager's schedule for `hash(S, this, D)`.
- Only the authority can replace itself.
- When the authority is an AccessManager, the manager calling in via `execute` is treated as immediately allowed iff
  the manager's execution context is `(this, sel)`.

**4.x.** None of this exists in 4.x; it was introduced in 5.0.

---

## 9. ERC2771Context: metatx/ERC2771Context.sol

**1. State.** `address private immutable _trustedForwarder` (23). It lives in code, not storage, in both packages
(the upgradeable variant also uses an immutable with `unsafe-allow`). `trustedForwarder()` and
`isTrustedForwarder(f) = (f == trustedForwarder())` are virtual (39-48).

**2. Sender semantics.** Let `L = msg.data.length`. The suffix length is `_contextSuffixLength() = 20` (87-89).
- `_msgSender()` = `L ≥ 20 ∧ isTrustedForwarder(msg.sender) ? address(bytes20(msg.data[L−20:])) : msg.sender`
  (55-65).
- `_msgData()` = under the same condition, `msg.data[:L−20]`; otherwise `msg.data` (72-82).

**5. Relay.** It makes no calls. It *consumes* the relay convention: the forwarder CALLs with `data ‖ from`.

**6. Pitfalls**
- **The trusted forwarder is a super-principal**: it can impersonate any address in every `_msgSender()`-based check
  (Ownable, AccessControl, AccessManaged.restricted, and so on).
- The appended 20 bytes change `msg.data.length`, which can trigger `fallback` instead of `receive`.
- A **self-DELEGATECALL loses the context**: inside a delegatecall to self, `msg.sender` is still the forwarder but
  `msg.data` is attacker-chosen, so the "last 20 bytes" are attacker-chosen (doc 17-19). Multicall now handles this
  (§10).
- When the forwarder itself calls with fewer than 20 bytes, the sender is the forwarder.

**7. Actor model.** `effectiveSender = (rawSender == F ∧ |cd| ≥ 20) ? suffix(cd) : rawSender`, where `F` is a fixed,
fully trusted principal.

**4.x.**
- In 4.9.3 and later, the semantics are the same (`isTrustedForwarder(msg.sender) && L ≥ 20`).
- **Before 4.9.3** there was no length check (CHANGELOG 4.9.3, #4481/#4484). Per those changelog entries, short
  calldata from the forwarder did not yield the forwarder address, and `_msgData()` reverted.
- In 4.x the variable was immutable from 4.4 (#2917) and in storage in 4.1-4.3.

---

## 10. Multicall: utils/Multicall.sol

**`multicall(bytes[] data)`** (26-36). It is `public`, non-payable, and unguarded.
- `ctx := (msg.sender == _msgSender()) ? "" : msg.data[L − _contextSuffixLength():]`.
- For each `i`: `results[i] = Address.functionDelegateCall(address(this), data[i] ‖ ctx)`.
- **DELEGATECALL** to self preserves `msg.sender` and `msg.value`. Reverts bubble up, and the batch is atomic.

**Sender in a sub-call**
- If the outer call came from the trusted forwarder with signer `s`, then `ctx = s`, so the last 20 bytes of the
  sub-calldata are `s` and `_msgSender() = s`. This is sound.
- Otherwise `ctx = ""`, and `_msgSender() = msg.sender` in the sub-call, unless the outer `msg.sender` is the
  forwarder, which is the canonical-context-detection case.

**Pitfalls**
- **Pre-fix (OZ < 4.9.4 / < 5.0.1, CHANGELOG 5.0.1)**: `ctx` was always empty. Anyone could route
  `multicall([f(args)‖victim])` through a trusted forwarder, and each sub-call then saw `_msgSender() = victim`. This
  is the December 2023 ERC-2771 + Multicall address-spoofing class.
- The current detection is by **equality** `msg.sender == _msgSender()`, not by `isTrustedForwarder`. If a trusted
  forwarder could ever append its *own* address, `ctx` would be empty and the sub-calls spoofable. ERC2771Forwarder
  cannot do this, because `from` must be a recovered ECDSA signer.
- Relays that filter selectors do not see nested selectors (doc 12-14).
- Every sub-call sees the same `msg.value`, which is harmless here because `multicall` is non-payable.

**4.x.** 4.9.4 and later contain the same fix, but `multicall` is `external` (src-oz4 `utils/Multicall.sol`).

---

## 11. ERC2771Forwarder: metatx/ERC2771Forwarder.sol (MinimalForwarder in 4.x)

**1. State**
- `Nonces._nonces: mapping(address => uint256)`. Upgradeable: `NS("openzeppelin.storage.Nonces") =
  0x5ab42ced628888259c08ac98db1eb0cf702fc1501344311d8b100cd1bfe4bb00`.
- EIP712 immutables: name, version `"1"`, cached domain, chain id and `this`. Upgradeable:
  `NS("openzeppelin.storage.EIP712") = 0xa16a46d94261c7517cc8ff89f61c0ce93598e3c849801011dee649a6a557d100`.

**Request and digest**
- `ForwardRequestData{from, to, value, gas, uint48 deadline, data, signature}` (54-62).
- The signed struct is
  `ForwardRequest(address from,address to,uint256 value,uint256 gas,uint256 nonce,uint48 deadline,bytes data)`
  (64-67). The `nonce` is implicit: it is `nonces(from)`.
- `digest = _hashTypedDataV4(keccak256(abi.encode(TYPEHASH, from, to, value, gas, nonces(from), deadline, keccak256(data))))`
  (223-242).

**Validity** (`_validate`, 204-215). A request is valid iff all of these hold:
- `_isTrustedByTarget(to)`: a STATICCALL of `to.isTrustedForwarder(this)` (`0x572b6c05`) succeeds, returns at least
  32 bytes, and returns a nonzero word (313-331).
- `deadline ≥ block.timestamp`. This is inclusive: the request is still valid at the deadline second.
- The ECDSA signature is valid and `recovered == from`. `tryRecoverCalldata` accepts only 65-byte signatures with
  low `s` and a nonzero recovered address (ECDSA.sol:85-104, 185-191).

**Entry points** (all permissionless; anyone can relay)

**`execute(req)` payable** (132-143)
1. `msg.value == req.value`, else `ERC2771ForwarderMismatchedValue`.
2. `_execute(req, true)`, which reverts in order with:
   - `ERC2771UntrustfulTarget`
   - `ERC2771ForwarderExpiredRequest`
   - `ERC2771ForwarderInvalidSigner`
3. If the call fails, it reverts `Errors.FailedCall()`. Because the whole transaction reverts, the nonce is not
   consumed.

**`executeBatch(reqs, refundReceiver)` payable** (165-198)
- `requireValid := (refundReceiver == 0)`.
- For each request:
  - `requestsValue += value`.
  - `ok = _execute(req, requireValid)`. Invalid requests are skipped (returning false) when `¬requireValid`, and
    revert otherwise.
  - If `¬ok`, then `refundValue += value`.
- After the loop: `requestsValue ≠ msg.value` reverts.
- If `refundValue ≠ 0`:
  - If `requireValid`, it reverts `ERC2771ForwarderNoRefundReceiver`. This is new in 5.7: a failed value-carrying call
    reverts an atomic batch.
  - Otherwise it calls `sendValue(refundReceiver, refundValue)`.
- In a batch, a *failed call* still consumes its nonce.

**`_execute`** (259-302). If the request is valid:
1. `n = _useNonce(signer)` (post-increment), *before* the call, which prevents reentrancy replay.
2. **CALL** `to` with `gas = req.gas`, `value = req.value`, and calldata `req.data ‖ req.from` (20 bytes).
3. `_checkForwardedGas`: if `gasleft < req.gas/63`, it executes `INVALID`, consuming all gas (345-375).
4. Emit `ExecutedForwardRequest(signer, n, success)`.

**Relay authentication.** The target sees `msg.sender = forwarder`, and `ERC2771Context` takes `from` from the
suffix. The forwarder authenticates the user by signature plus nonce plus deadline. The target authenticates the
forwarder by address.

**Actor model.**
- A signed-intent relay: a user `u` authorises the exact tuple `(to, value, gas, data, deadline)` at nonce `nonces[u]`.
- Any relayer submits it.
- The forwarder re-issues it as a CALL whose effective sender, for trusting targets, is `u`.
- Nonces are sequential per user and single-use.

**4.x (MinimalForwarder, 4.9.6 `metatx/MinimalForwarder.sol`)**
- The nonce is explicit in the request, with no deadline and no `isTrustedForwarder` check on the target.
- `execute` does not revert when the call fails; it returns `(success, returndata)`.
- There is no batching.
- Gas check: `gasleft() <= req.gas/63` triggers `invalid`.
- It was replaced by ERC2771Forwarder in 5.0.

---

## 12. Initializable: proxy/utils/Initializable.sol (initialisation as an authority mechanism)

**1. State.** `struct InitializableStorage { uint64 _initialized; bool _initializing; }` (65-74).
- Both fields share one slot at `0xf0c57e16840df040f15088dc2f81fe391c3923bec73e23a9662efc9c229c6a00`
  (`erc7201:openzeppelin.storage.Initializable`, line 77). `_initialized` is in bits 0-63 and `_initializing` in
  bits 64-71.
- The slot can be overridden with `_initializableStorageSlot()` (224-226, added in 5.3).

**2. Guards.** Let `v = _initialized` and `top = ¬_initializing`.

**`initializer`** (104-132)
- The call is allowed iff `(v == 0 ∧ top) ∨ (v == 1 ∧ address(this).code.length == 0)`, else
  `InvalidInitialization()`.
- Effect:
  1. `_initialized := 1`.
  2. If `top`, set `_initializing := true`.
  3. Run the body.
  4. If `top`, set `_initializing := false` and emit `Initialized(1)`.
- Nested `initializer` calls are allowed only during construction.

**`reinitializer(k)`** (152-164)
- It reverts if `_initializing ∨ v ≥ k`.
- Effect: `_initialized := k; _initializing := true`, then the body, then `_initializing := false` and emit
  `Initialized(k)`.
- Versions may skip numbers. Reinitializers cannot nest. `k = 2^64 − 1` locks the contract forever.

**`onlyInitializing`** (170-182) requires `_initializing`.

**`_disableInitializers()`** (192-203)
- It reverts if `_initializing`.
- If `v ≠ max`, it sets `v := 2^64 − 1` and emits `Initialized(max)`.

**3–5. Authority.** **The guard does not depend on the sender**: the first caller of an initializer wins. In practice,
initializers assign the owner, admin or authority (`__Ownable_init(initialOwner)`, `__AccessManager_init(admin)`,
`__AccessManaged_init(authority)`, `__AccessControlDefaultAdminRules_init(delay, admin)` in src-ozu; all are
`onlyInitializing`). Initialisation is therefore a **one-shot, first-come authority assignment**, with versioned
re-assignment through `reinitializer(k)` that is itself guarded only by the version counter. In practice a
reinitializer is gated behind an upgrade, which is admin-controlled.

**6. Pitfalls**
- **Front-running**: if the proxy is deployed and initialised in separate transactions, anyone can initialise first
  and seize ownership. The documented mitigation is to pass the initialiser calldata to the `ERC1967Proxy`
  constructor (doc 26-27).
- **Uninitialised implementation contracts** can be taken over. The mitigation is `_disableInitializers()` in the
  constructor (doc 32-46).
- The `code.length == 0` construction escape hatch allows repeated `initializer` calls inside a constructor.
- A reverted initializer rolls back.
- Parent initializers can be invoked twice by mistake (doc 29-30).
- A non-reverting call path can leave the proxy uninitialised.

**7. Actor model.** A monotone version counter `v ∈ ℕ64` with a transient "initializing" bit.
- The transition `v → k` is allowed for any principal iff `k > v` (or `v = 0` and `k = 1` for `initializer`) and no
  initialisation is in progress.
- Functions guarded by `onlyInitializing` are callable only inside such a transition.
- Authority assignments made inside the transition are therefore granted to whoever wins the race to the transition.

**4.x (4.9.6)**
- `uint8 _initialized; bool _initializing;` are *sequential*, normally in slot 0 at byte offsets 0 and 1.
- The guard is the same:
  `(top ∧ v < 1) ∨ (¬Address.isContract(this) ∧ v == 1)`.
- `reinitializer(uint8)` has a maximum of 255.
- `_disableInitializers` sets 255.
- The ERC-7201 namespace arrived in 5.0 (CHANGELOG 5.0.0, #4460).

---

## 13. Summary of the "sender" used per check

| Module / check | Sender |
|---|---|
| Ownable `_checkOwner`, Ownable2Step `acceptOwnership` | `_msgSender()` |
| AccessControl `_checkRole(r)`, `renounceRole`, event `sender` field | `_msgSender()` |
| DefaultAdminRules `acceptDefaultAdminTransfer` | `_msgSender()` |
| AccessManager `schedule`/`execute`/`cancel`/`_canCancel`/`renounceRole`/`_checkAuthorized`/`consumeScheduledOp` | `_msgSender()` (= `msg.sender`; Context only) and `_msgData()` |
| AccessManager `canCall` relay branch | raw `caller` argument compared to `address(this)` |
| AccessManaged `restricted`, `setAuthority` | `_msgSender()`, `_msgData()` |
| ERC2771Context forwarder test | raw `msg.sender` |
| Multicall context detection | `msg.sender` vs `_msgSender()` |
| ERC2771Forwarder | none (signature-based); `msg.value` |
| Initializable | none |

---

## 14. Minimal abstract primitives for a formal model

**P1. Principal and caller.** `Addr` (20 bytes) with a distinguished `⊥ = 0`. Every frame has
`(rawSender, value, calldata, self)`.

**P2. Effective-sender function.** `eff : Frame → Addr`, a projection.
- The default is `eff = rawSender`.
- The ERC-2771 instance, for a fixed trusted `F` and suffix length `k = 20`:
  `eff = (rawSender = F ∧ |cd| ≥ k) ? last_k(cd) : rawSender`.
- The paired `effData` strips the suffix.

**P3. Singleton holder.** `owner : State → Addr ∪ {⊥}`. The predicate is `isOwner(s, a) := owner = a ≠ ⊥`.

**P4. Two-phase handover.**
- `pending : Addr ∪ {⊥}`, optionally with an activation time `τ` (uint48, where 0 means unset).
- `propose` is guarded by holder; `accept` is guarded by `eff = pending` (and `τ < now` in the strict variant).
- `⊥` is absorbing for renounce.

**P5. Role membership predicate.**
- `M : Role × Addr × Time → Bool`.
- Untimed form (AccessControl): `M(r, a) := bit[r][a]`.
- Timed form (AccessManager): `M(r, a, t) := since(r, a) ≠ 0 ∧ since(r, a) ≤ t`.
- A universal role `PUBLIC` with `M ≡ true`.

**P6. Role administration graph.**
- `adm : Role → Role`, with default value `0`.
- `grant(r, a)` and `revoke(r, a)` are guarded by `M(adm(r), eff)`.
- `renounce(r)` is guarded by `a = eff`.
- Some roles are locked: their `adm` is constant (ADMIN, PUBLIC, DEFAULT_ADMIN under DefaultAdminRules).
- A guardian map `grd : Role → Role` gives cancel-rights.

**P7. Permission table.**
- `perm : (Target × Selector) → Role`, with default ADMIN.
- A per-target `closed : Target → Bool`, which overrides everything.
- Reserved selectors with fixed rules (setAuthority).
- The manager's own hard-coded table `selfPerm : Selector × Args → (Role, opDelay)`, which can depend on the first
  argument (target or roleId).

**P8. Deferred-update delay cell (`Time.Delay`).** A triple `(before, after, effect)`.
- `get(t) = effect ≤ t ? after : before`.
- `update(new, minSetback, now) = (get(now), new, now + max(minSetback, get(now) ∸ new))`. A pending value is
  overwritten.
- It is instantiated as:
  - per-member execution delay, with `minSetback = 0`;
  - per-role grant delay, with 5 days;
  - per-target admin delay, with 5 days;
  - the DefaultAdminRules delay, a variant: `wait = new > cur ? min(new, 5d) : cur − new`, with strict `<`
    activation and lazy materialisation.

**P9. Three-valued authorisation decision.**
- `canCall(c, t, sel, now) ∈ {Immediate, Delayed(d > 0), Denied}`.
- Here `d = max(execDelay(c, role), opDelay)`.

**P10. Single-use scheduled operation.**
- `id = H(caller, target, data)`.
- The store is `id ↦ (τ : uint48, nonce : uint32)`.
- `schedule` is allowed iff `Delayed(d)`; it sets `τ = max(when, now + d)`, requires no live entry, and does
  `nonce++`.
- `consume` is allowed iff `τ ≠ 0 ∧ τ ≤ now < τ + E`, with `E = 1 week`; it sets `τ := 0`.
- `cancel` is guarded by (proposer ∨ ADMIN ∨ guardian(perm(t, sel)) ∨ admin-of-role for grant/revoke operations); it
  sets `τ := 0`.
- At execution, authorisation is re-checked; `τ` is not re-validated.

**P11. Authority delegation (managed target).** `authority : Addr`.
- A restricted entry `(self, sel)` evaluates `authority.canCall(eff, self, sel)`. This is a STATICCALL; a failure or a
  short return is read as Denied, or as delay 0.
- On `Delayed`, the target calls `authority.consumeScheduledOp(eff, data)`, and the authority authenticates the target
  by `rawSender` plus a callback flag (`isConsumingScheduledOp`).
- Only `authority` may set a new authority, and the new authority must have code.

**P12. Relay (privileged call-through).**
- The manager performs `CALL(target, data, value)` with `rawSender = manager`.
- It sets a scoped execution token `exec := H(target, sel)`, saved and restored around the call.
- The target's authority check treats `caller = manager` as authorised iff `exec = H(target, sel)` and the target is
  not closed.
- The manager also relays `setAuthority` through `updateAuthority`.

**P13. Self-batching (DELEGATECALL to self).**
- Each item runs with the same `(rawSender, value)` and calldata `item ‖ ctx`.
- Here `ctx = (rawSender = eff) ? ε : suffix`.
- Each item is authorised independently. The batch is atomic.

**P14. Signed-intent forwarding.**
- A request `(from, to, value, gas, deadline, data)` signed by `from` under EIP-712, with a sequential nonce
  `nonce[from]`.
- It is valid iff `sig ok ∧ recovered = from ∧ deadline ≥ now ∧ to.trusts(forwarder)`.
- Effect: `nonce[from]++`, then `CALL(to, data ‖ from, value, gas)` with `rawSender = forwarder`.
- Under P2 the target sees `eff = from`.

**P15. One-shot versioned initialisation.**
- A monotone counter `v` plus an `initializing` bit.
- The transition to `k > v` is allowed for **any** principal (the first caller wins). `initializer` is `k = 1`, with
  a construction-time exception when `code.length = 0`.
- Authority-assigning functions (`onlyInitializing`) are enabled only during the transition.
- `disable` sets `v := max`.

**P16. Clock.**
- `now = block.timestamp`, cast to uint48 (the cast reverts if it is ≥ 2^48).
- The comparisons used are:

  | Check | Comparison |
  |---|---|
  | AccessManager membership active | `since ≤ now` |
  | AccessManager operation ready | `τ ≤ now` |
  | AccessManager operation expired | `τ + E ≤ now` |
  | DefaultAdminRules schedule passed | `s < now` (strict) |
  | Forwarder deadline still valid | `deadline ≥ now` |
