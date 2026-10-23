# Actor / authority models: Solmate, Solady, DappHub, MakerDAO, Compound

Source-grounded specification. Every claim cites `file:line` at the commit listed below.
I read the code only; I built and ran nothing. Storage slots for ordinary Solidity state are
derived from declaration order and the standard mapping formula. I did not check them with
`solc --storage-layout`. Where a slot is defined in assembly (Solady), the formula is quoted
from the code.

| Repo | Path read | Commit (date) |
|---|---|---|
| transmissions11/solmate (main) | `src/auth/*` | `89365b880c4f` (2025-07-21) |
| Vectorized/solady (latest tag **v0.1.26**) | `src/auth/*` | `acd959aa4bd0` (tag). `main@258f67cc` differs only in formatting in EnumerableRoles/TimedRoles |
| dapphub/ds-auth | `src/auth.sol` | `a51e7caa1f03` |
| dapphub/ds-guard | `src/guard.sol` | `af05632249f9` |
| dapphub/ds-roles | `src/roles.sol` | `53d56949c0f9` |
| makerdao/dss (master) | `src/vat.sol` | `fa4f6630afb0` |
| dapphub/ds-pause | `src/pause.sol` | `0763eafcf926` |
| dapphub/ds-chief | `src/chief.sol` | `4a833cdaeb66` |
| dapphub/ds-token (master, used for IOU semantics) | `src/token.sol` | `16f187acc15d`. ds-chief pins `c3a1cebee1ae`, which I did not read |
| compound-finance/compound-protocol (master) | `contracts/Timelock.sol`, `Governance/GovernorBravo*.sol`, `Comptroller*.sol`, `Unitroller.sol` | `a3214f67b733` |

Notation: `sender = msg.sender` (CALLER), `self = address(this)`, `sig = msg.sig` (the first
4 calldata bytes of the *outer* external call, also when the check runs inside an internal
call), `now = block.timestamp`, `bn = block.number`. "Revert" means the whole frame reverts.
`M[k]@s` means the Solidity mapping slot `keccak256(pad32(k) ++ pad32(s))`, where `bytes4`/`bytesN`
keys are left-aligned and zero-padded on the right, and address/uint keys are left-padded.

General compiler fact used below: since solc 0.5.0, a high-level call to an external
`view`/`pure` function compiles to **STATICCALL**. Before that it compiled to CALL. With ABI
coder v2 (the default in 0.8), a `bool` return word other than 0 or 1, or returndata shorter
than 32 bytes, makes the caller revert. In solc 0.8.10 and later, the `extcodesize` pre-check
is skipped when return data is decoded. A call to a code-less address still reverts, because
decoding the empty returndata fails.

---

## 1. Solmate `Owned` (`src/auth/Owned.sol`)

**1. State.** `address owner` in slot 0 of the mixin (`Owned.sol:17`). It is shifted by any
preceding bases in the inheriting contract.

**2. Guarded entry points.** `onlyOwner`: `require(sender == owner, "UNAUTHORIZED")`
(`:19-23`).

**3. Authority mutations.**
- `constructor(_owner)`: `owner := _owner`, with no zero check (`:29-33`).
- `transferOwnership(newOwner)` `onlyOwner`: `owner := newOwner` (`:39-43`). It is one-step,
  with no zero check, so `newOwner = 0` renounces ownership irrevocably.

**4. Time.** None. **5. Relay.** None.

**6. Pitfalls.** A typo in `newOwner` loses ownership permanently, and there is no two-step
transfer.

**7. Actor model.** There is one principal `owner : Address`. A guarded function is allowed
iff `sender = owner`. The owner can replace itself with any address, including 0, which
locks every guarded function forever.

---

## 2. Solmate `Auth` (`src/auth/Auth.sol`)

**1. State.** `address owner` in slot 0 (`:12`) and `Authority authority` in slot 1 (`:14`).
They are not packed, because 20+20 bytes exceed 32. The interface is
`Authority.canCall(address user, address target, bytes4 functionSig) external view returns (bool)`
(`:58-64`).

**2. Guarded entry points.** `requiresAuth` = `require(isAuthorized(sender, sig), "UNAUTHORIZED")`
(`:24-28`), where (`:30-36`):
```
isAuthorized(user, s) = (authority != 0 && authority.canCall(user, self, s)) || user == owner
```
The checks run in this order:
1. Read `authority` from storage.
2. If it is nonzero, make an external STATICCALL to `canCall(user, self, s)`. If that call
   reverts, the whole call reverts, even when `user == owner`.
3. If the result is false, test `user == owner`.

The comment at `:33-34` states this design choice explicitly.

**3. Authority mutations.**
- `setAuthority(newAuthority)` (`:38-46`) is guarded **not** by `requiresAuth` but by
  `require(sender == owner || authority.canCall(sender, self, sig))`. It checks the owner
  first, so the owner can always replace a reverting or gas-burning authority. There is no
  `authority != 0` test. A non-owner calling while `authority == 0` reverts, because the
  call goes to an address with no code (empty-returndata decode failure). Effect:
  `authority := newAuthority`, any value including 0 or an EOA.
- `transferOwnership(newOwner)` is `requiresAuth` (`:48-52`). The authority can therefore
  grant ownership transfer to non-owners. Effect: `owner := newOwner`, with no zero check.
- `constructor(_owner, _authority)` sets both (`:16-22`).

**4. Time.** None in `Auth`. An authority may consult `block.timestamp` in its view logic.

**5. Relay.**
- `canCall` is an external STATICCALL, because the interface method is `view` and the
  pragma is `>=0.8.0`. It forwards all but 1/64 of the remaining gas.
- Inside the authority, `msg.sender = self` (the protected contract), and `user` is passed
  explicitly.

What an untrusted authority can do:
- **Grant.** It can return true for any `(user, sig)`, including `transferOwnership.selector`
  and `setAuthority.selector`. It can therefore take over ownership and replace itself.
- **Deny.** It can return false, which leaves the owner fallback.
- **DoS.** It can revert or burn gas. This blocks every `requiresAuth` function for
  everyone, the owner included, but it does not block the owner's `setAuthority`.
- **Branch on observable state.** It can base its answer on any state it can read: its own
  storage, the target's view functions (reentrant read-only calls), `tx.origin`, time, and
  gas left.
- **Not mutate state.** It cannot change state, emit logs, or move ETH, because it runs
  under STATICCALL and any SSTORE, LOG, CALL-with-value, CREATE, or SELFDESTRUCT inside it
  reverts the authority frame. If the authority returns a malformed bool, the caller
  reverts.

**6. Pitfalls.**
1. The authority can be any contract, and its decision is consulted **before** the owner
   fallback.
2. `setAuthority` uses a different rule: `owner || canCall(..., setAuthority.selector)`.
3. `sig` is the outer selector. If a public function `f` internally calls a
   `requiresAuth` function `g`, the authority sees `f.selector`.
4. Setting `owner = 0` and `authority = 0` bricks the contract permanently.
5. A self-referential setup is possible (for example `RolesAuthority` with
   `authority = this`, see §3).

**7. Actor model.** There are two principals: an `owner` address and an `authority` oracle
`A : (user, target, sig) → Bool | ⊥`, where ⊥ means revert or out-of-gas. A guarded call by
`u` with selector `s` succeeds iff `(A ≠ 0 ∧ A(u, self, s) = true) ∨ u = owner`. If A
returns ⊥, the call reverts. Replacing `A` requires `u = owner ∨ A(u, self, setAuthority.selector)`,
with the owner test evaluated first, so A is never queried for the owner. Ownership
transfer is an ordinary authority-gated capability.

---

## 3. Solmate `RolesAuthority` (`src/auth/authorities/RolesAuthority.sol`)

**1. State.** It extends `Auth`, so `owner` is in slot 0 and `authority` in slot 1. It adds:
- `getUserRoles : address → bytes32` in slot 2 (`:30`)
- `isCapabilityPublic : address → bytes4 → bool` in slot 3 (`:32`)
- `getRolesWithCapability : address → bytes4 → bytes32` in slot 4 (`:34`)

Role `r ∈ [0,255]` is bit `r` (LSB = role 0). `1 << role` is computed in uint256, because
the left operand is a literal (`:83, :101`).

**2. Decision function** (`canCall`, `:52-60`):
```
canCall(user, target, s) = isCapabilityPublic[target][s] || (getUserRoles[user] & getRolesWithCapability[target][s]) != 0
```
This is any-of semantics: one shared role is enough. It is pure storage reads with no
external calls.

**3. Authority mutations.** All three are `requiresAuth` on the RolesAuthority itself, which
means its own `authority` or `owner`.
- `setPublicCapability(target, s, en)`: `isCapabilityPublic[target][s] := en` (`:66-74`).
- `setRoleCapability(r, target, s, en)`: sets or clears bit r of
  `getRolesWithCapability[target][s]` (`:76-89`).
- `setUserRole(user, r, en)`: sets or clears bit r of `getUserRoles[user]` (`:95-107`).
- The inherited `transferOwnership` and `setAuthority` follow §2.

**4. Time.** None. **5. Relay.** None inside `canCall`. It is queried by STATICCALL from
`Auth` instances.

**6. Pitfalls.**
1. Public capabilities bypass roles entirely.
2. There is no role hierarchy and no admin role. Whoever passes `requiresAuth` on the
   authority can grant itself any role on any target.
3. If `authority = this`, the authority's own configuration is governed by its own roles.
   Capabilities whose target is the RolesAuthority itself then become admin rights.
4. Capabilities are keyed by `(target, sig)`. Deploying the same code at a new address
   needs reconfiguration.

**7. Actor model.** This is a static RBAC relation: users map to a role set `R(u) ⊆ [0,256)`,
capabilities `(target, sig)` map to a role set `C(t, s)`, and a public flag `P(t, s)`
exists. `allow(u, t, s) ⇔ P(t, s) ∨ R(u) ∩ C(t, s) ≠ ∅`. Configuration is governed by an
`Auth` instance (owner plus an optional upstream authority).

---

## 4. Solmate `MultiRolesAuthority` (`src/auth/authorities/MultiRolesAuthority.sol`)

**1. State.** `owner` in slot 0 and `authority` in slot 1 (from Auth), plus:
- `getTargetCustomAuthority : address → Authority` in slot 2 (`:31`)
- `getUserRoles : address → bytes32` in slot 3 (`:37`)
- `isCapabilityPublic : bytes4 → bool` in slot 4 (`:39`)
- `getRolesWithCapability : bytes4 → bytes32` in slot 5 (`:41`)

Capabilities do **not** depend on the target.

**2. Decision** (`:55-66`):
```
canCall(u, t, s) = if custom[t] != 0 then custom[t].canCall(u, t, s)   // external STATICCALL, result returned verbatim
                   else isCapabilityPublic[s] || (getUserRoles[u] & getRolesWithCapability[s]) != 0
```
**3. Authority mutations.** All are `requiresAuth`:
- `setTargetCustomAuthority(t, a)` (`:72-76`)
- `setPublicCapability(s, en)` (`:82-86`)
- `setUserRole(u, r, en)` (`:92-104`)
- `setRoleCapability(r, s, en)` (`:110-122`)

**5. Relay.** It delegates to the custom authority by a nested STATICCALL. A
reverting custom authority makes `canCall` revert, which the target then sees as a revert.

**6. Pitfalls.**
1. A custom authority **replaces** the role check for that target rather than adding to it.
2. Selector-only capabilities apply to *every* target that uses this authority. Two
   unrelated contracts sharing a selector, such as `mint(address,uint256)`, share the
   capability.
3. Chains of authorities can form cycles. A STATICCALL cycle recurses until gas runs out
   and then reverts.

**7. Actor model.** This is RBAC keyed by selector, with a per-target override oracle:
`allow(u, t, s) = O_t(u, t, s)` if an override `O_t` exists, else `P(s) ∨ R(u) ∩ C(s) ≠ ∅`.

---

## 5. Solady `Ownable` (`src/auth/Ownable.sol`, v0.1.26)

**1. State.** All slots are defined in assembly.
- Owner slot: `_OWNER_SLOT = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff74873927`,
  which equals `not(0x8b78c6d8)` (`:63-70`). It holds the owner in the low 160 bits. In
  guarded mode it also holds a bit-255 sentinel, described below.
- Handover expiry per `pendingOwner`: `sload(keccak256(bytes32((uint256(uint160(p)) << 96) | 0x389a75e1)))`,
  that is keccak of the 32 bytes `p(20) ‖ 0x00×8 ‖ 0x389a75e1(4)` (`:72-78`). This is
  implemented by `mstore(0x0c, SEED); mstore(0x00, p); keccak256(0x0c, 0x20)` (`:198-200`,
  `:226-228`). The value is a uint256 expiry timestamp, with 0 meaning none.
- Constants: `_HANDOVER_SLOT_SEED = 0x389a75e1` (`:78`). Event topics are at `:47-57`.

**2. Guarded entry points.** `onlyOwner` calls `_checkOwner`:
`if caller() != sload(_OWNER_SLOT) revert Unauthorized()` (`:150-160, :274-277`). This
compares the full 256-bit word, so in guarded mode, once the bit-255 sentinel is set, no
caller can match. Every public mutator is `payable`.

**3. Authority mutations.**
- `_initializeOwner(newOwner)` is internal and unguarded (`:94-121`).
  - If `_guardInitializeOwner()` (`:85`, which returns false by default unless overridden)
    returns true: the call reverts with `AlreadyInitialized()` if `sload(_OWNER_SLOT) != 0`.
    Otherwise it stores `newOwner | (newOwner == 0 ? 1 << 255 : 0)`.
  - If it returns false: the call stores `newOwner` unconditionally, so it can be invoked
    again.
  - It logs `OwnershipTransferred(0, newOwner)`.
- `_setOwner(newOwner)` is internal. It logs `OwnershipTransferred(sload(slot), newOwner)`.
  The old-owner topic is the raw word, which may carry the sentinel. It stores the same
  sentinel form when guarded (`:124-148`).
- `transferOwnership(newOwner)` is `onlyOwner` and `payable`. It reverts with
  `NewOwnerIsZeroAddress` if `shl(96, newOwner) == 0`, then calls `_setOwner` (`:174-183`).
- `renounceOwnership()` is `onlyOwner` and calls `_setOwner(0)`. In guarded mode the
  stored word becomes `1 << 255` (`:186-188`).
- `requestOwnershipHandover()` can be called by **anyone**:
  `slot(sender) := now + _ownershipHandoverValidFor()`. The addition is unchecked, the
  default validity is `48*3600 = 172800` seconds (overridable, `:165-167`), and an
  existing request is overwritten (`:192-205`).
- `cancelOwnershipHandover()` can be called by anyone, for their own slot:
  `slot(sender) := 0` (`:208-218`).
- `completeOwnershipHandover(p)` is `onlyOwner`. It reverts with `NoHandoverRequest` if
  `now > slot(p)`, then sets `slot(p) := 0` and calls `_setOwner(p)` (`:222-238`).

**4. Time.** A handover is valid iff `now ≤ expires`, where `expires = t_request + 172800`.
The revert uses strict `gt(timestamp(), expires)` at `:230`. A missing request (`expires = 0`)
always fails, because `now > 0`.

**5. Relay.** None.

**6. Pitfalls.**
1. The owner is **not** auto-initialized. If `_initializeOwner` is never called, the owner
   is 0 and every `onlyOwner` function is dead.
2. Without the `_guardInitializeOwner` override, an exposed initializer can be re-run.
3. In guarded mode the sentinel makes a renounced contract non-reinitializable. `owner()`
   (`:245-250`) returns the raw slot as an `address`. ABI encoding masks it to 160 bits, so
   callers see 0, but a log topic can show `0x8000…`.
4. Handover requests are keyed only by the requester. They survive owner changes, so a
   *new* owner may complete a request made while an earlier owner was in control. A
   request lasts until it expires or is cancelled.
5. `completeOwnershipHandover` is the only path that needs consent from the new owner.
   `transferOwnership` is one-step.

**7. Actor model.** There is one principal `owner`, plus a set of time-stamped handover
offers `H : Address → Timestamp`. Any account `p` can post or refresh `H(p) := now + Δ`
(Δ = 48 h) and withdraw it. The owner can transfer ownership directly to any nonzero
address, renounce it, or accept a live offer (`now ≤ H(p)`), which consumes that offer.

---

## 6. Solady `OwnableRoles` (`src/auth/OwnableRoles.sol`)

**1. State.** It has the Ownable owner slot plus a roles bitmap per user (uint256):
`roleSlot(u) = keccak256(bytes32((uint256(uint160(u)) << 96) | 0x8b78c6d8))` (`:33-42`). The
code computes it as `mstore(0x0c, 0x8b78c6d8); mstore(0x00, u); keccak256(0x0c, 0x20)`, which
ignores any dirty upper bits of `u`. Note that `_OWNER_SLOT == not(_ROLE_SLOT_SEED)`
(`:41, :120-121`). The bitmap covers 256 roles, and the constants `_ROLE_i = 1 << i` are at
`:279`.

**2. Guards.**
- `onlyRoles(roles)` calls `_checkRoles`: revert `Unauthorized` iff
  `sload(roleSlot(sender)) & roles == 0` (`:98-111, :254-257`). This is **any-of**.
  `roles = 0` never passes, and the owner gets **no** implicit pass.
- `onlyOwnerOrRoles(roles)` calls `_checkOwnerOrRoles`. It checks first
  `caller == sload(_OWNER_SLOT)`, and if that fails it applies the any-of role check
  (`:116-133, :261-264`).
- `onlyRolesOrOwner(roles)` (`:138-155, :268-271`) is the same predicate with the role
  check evaluated first, a gas-order difference only.
- `hasAnyRole` (`:240-242`) returns `rolesOf(u) & roles != 0`. `hasAllRoles` (`:245-247`)
  returns `rolesOf(u) & roles == roles`.

**3. Mutations.**
- `grantRoles(u, roles)` is `onlyOwner`: `R(u) := R(u) | roles` (`:207-209`, via
  `_updateRoles` `:64-83`).
- `revokeRoles(u, roles)` is `onlyOwner`: `R(u) := R(u) & ~roles`. The code implements this
  as `xor(cur, and(cur, roles))` (`:213-215`, `:77`).
- `renounceRoles(roles)` can be called by anyone, for themselves: `R(sender) &= ~roles`
  (`:219-221`).
- `_setRoles(u, roles)` is an internal overwrite (`:49-59`).
- Each of these emits `RolesUpdated(u, newRoles)`, using the cleaned address.
- Ownership transitions follow §5.

**4. Time.** None, apart from Ownable handover. **5. Relay.** None.

**6. Pitfalls.**
1. Roles cannot administer roles. Only the owner can grant, unless the derived contract
   wraps `_grantRoles`.
2. Passing several roles to `onlyRoles` means OR, not AND.
3. Roles persist across ownership transfer and renounce.
4. After `renounceOwnership`, role holders keep their powers but nobody can grant roles.

**7. Actor model.** The model has an owner and a bitmap relation `R : Address → 2^256`.
A guard with mask `m` admits `u` iff `R(u) ∩ m ≠ ∅` (or `u = owner` in the OwnerOr
variants). Only the owner can add or remove roles from others, and each holder can drop
their own roles.

---

## 7. Solady `EnumerableRoles` (`src/auth/EnumerableRoles.sol`)

**1. State.** The seed is `0xee9853bb`. The code does `mstore(0x18, holder); mstore(0x04, seed); mstore(0x00, role)`
(`:58-69`). In this layout `role` occupies 32 bytes, followed by 4 seed bytes, followed by
20 holder bytes.
- `rootSlot(role) = keccak256(role ‖ seed)` over 36 bytes. Its upper 160 bits hold holder #0
  and its low 96 bits hold `length`.
- `positionSlot(role, h) = keccak256(role ‖ seed ‖ h)` over 56 bytes. It holds a 1-based
  index, where 0 means "does not hold the role".
- Holder #i (i ≥ 1) is stored in the upper 160 bits of `rootSlot + i`.
- Roles are arbitrary `uint256`, not a bitmask.

**2. Guards.**
- `onlyRole(r)` checks `hasRole(sender, r)`, which means `positionSlot != 0` (`:86-94, :237-239, :262-265`).
- `onlyRoles(bytes encodedRoles)` checks any-of over an `abi.encode`d list of words
  (`:216-234, :242-244`). The length is rounded down to a multiple of 32.
- `onlyOwnerOrRole` and `onlyOwnerOrRoles` (`:247-255, :275-287`) use an **owner test by
  self-STATICCALL**: `_enumerableRolesSenderIsContractOwner` (`:295-305`) runs
  `staticcall(gas(), self, owner.selector 0x8da5cb5b)`.
  - It is true iff the call succeeded, `returndatasize ≥ 32`, and
    `caller == returned word[0]` as a full 256-bit equality.
  - Yul evaluates arguments right to left, so the staticcall executes first.
  - A contract without `owner()` yields false.

**3. Mutations.** `setRole(holder, role, active)` is public and `payable` (`:76-79`). It runs
these steps in order:
1. `_authorizeSetRole`, which by default reverts with `EnumerableRolesUnauthorized` unless
   `sender == owner()` via the self-staticcall (`:208-212`).
2. `_validateRole(role)`. This makes a self-staticcall to `MAX_ROLE()` (0xd24f19d5) and
   reverts with `InvalidRole` iff the call succeeded, `returndatasize ≥ 32`, and
   `role > MAX_ROLE` (`:193-205`). If `MAX_ROLE()` is missing, the check is skipped.
3. Revert with `RoleHolderIsZeroAddress` if `holder == 0` (`:153-156`).
4. Update the set:
   - Add: only if the holder is absent, append at index n (`:179-183`).
   - Remove: swap-and-pop. The last holder moves to the vacated index and its position
     slot is rewritten (`:165-177`).
5. Emit `RoleSet(holder, role, active)`, even when nothing changed.

**4. Time.** None. **5. Relay.** It makes self-STATICCALLs to `owner()` and `MAX_ROLE()`,
with `msg.sender = self` inside them. A contract whose `owner()` reverts or returns fewer
than 32 bytes disables owner authority silently.

**6. Pitfalls.**
1. It is incompatible with OwnableRoles, as noted at `:25`.
2. It is designed to work with any `owner()`, for example OpenZeppelin's Ownable.
3. `_authorizeSetRole` is virtual, so a derived contract defines the real admin rule.
4. A stale holder word stays in storage beyond `length` after a pop, but it is never read.

**7. Actor model.** This is a set-valued relation `Holders : Role → Set Address` with an
O(1) membership test. Mutation needs `sender = self.owner()`, or a derived rule. Guards
check membership for one role, for any of several roles, or owner-or-role.

---

## 8. Solady `TimedRoles` (`src/auth/TimedRoles.sol`)

**1. State.** The seed is `0x28900261`. `slot(h, r) = keccak256(r ‖ seed ‖ h)` over 56 bytes
(`:66-76`). Bits [0..39] hold `expires` (uint40) and bits [216..255] hold `start` (uint40).

**2. Guards.**
- `onlyTimedRole(r)` (`:203-206, :229-232`) checks `timedRoleActive(sender, r).isActive`.
  `timedRoleActive` is defined at `:98-114`:
  ```
  active(h, r) = !(now < start || now > expires) = start ≤ now ≤ expires   (both inclusive)
  ```
  An unset slot has `start = expires = 0`, so it is never active, because `now > 0`.
- `onlyTimedRoles(encoded)` is the any-of version (`:181-200, :236-239`).
- `onlyOwnerOrTimedRole(s)` (`:214-222, :242-254`) uses the same self-staticcall owner test
  as EnumerableRoles (`:262-272`).

**3. Mutations.** `setTimedRole(h, r, start, expires)` is public and payable (`:84-91`). It
runs these steps in order:
1. Owner-only, through the self-staticcall `owner()` test (`:170-177`).
2. `_validateTimedRole` against `MAX_TIMED_ROLE()` (0x32bc6439) (`:155-167`).
3. Revert if `h == 0`.
4. Mask `start` and `expires` to 40 bits, then revert with `InvalidTimedRoleRange` if
   `expires < start`.
5. Store `start << 216 | expires` and emit an event (`:121-151`).

Revocation sets `start = expires = 0`. Equal bounds are allowed, which gives a single-second
window.

**4. Time.** The role is active on the closed interval `[start, expires]` of
`block.timestamp`, with uint40 bounds. There is no implicit renewal.

**5. Relay.** It makes self-STATICCALLs only.

**6. Pitfalls.**
1. A role can be scheduled to start in the future.
2. Changes take effect immediately, with no delay.
3. The owner can rewrite any window at any time.

**7. Actor model.** This is a time-indexed relation
`Grant : Address × Role → Interval(uint40)`, where `u` holds `r` at time t iff `t ∈ Grant(u, r)`.
Only `owner()` can edit it.

---

## 9. DappHub `DSAuth` / `DSAuthority` (`ds-auth/src/auth.sol`)

**1. State.** `DSAuthority authority` in slot 0 and `address owner` in slot 1 (`:29-30`).
Note that this order is the reverse of Solmate's. The interface
`DSAuthority.canCall(src, dst, sig) external view` is at `:17-21`.

**2. Guard.** `auth` = `require(isAuthorized(sender, sig), "ds-auth-unauthorized")`
(`:53-56`). The checks run in this order (`:58-68`):
1. `src == self`: allow. A self-call is always authorized.
2. `src == owner`: allow.
3. `authority == 0`: deny.
4. Otherwise return `authority.canCall(src, self, sig)` as an external call.

**3. Mutations.**
- The constructor sets `owner := msg.sender` (`:32-35`).
- `setOwner(o)` (`:37-43`) and `setAuthority(a)` (`:45-51`) are both `auth`. They give
  unconditional replacement, and the authority can grant either power.

**4. Time.** None.

**5. Relay.** The `canCall` call is a STATICCALL when compiled with solc ≥ 0.5.0. The pragma
is `>=0.4.23`, and older (0.4.x) builds emit CALL, which gives a state-mutating authority
with reentrancy. The owner short-circuits **before** the authority, so a broken authority
cannot DoS the owner. A malicious authority can grant anything, including `setOwner`.

**6. Pitfalls.**
1. The `src == self` rule means any generic "execute arbitrary call" feature on the
   contract becomes full admin.
2. `sig` is the outer selector.
3. The owner check comes first here, but after the authority in Solmate `Auth`.
4. Here `setAuthority` is plain `auth`, whereas Solmate uses a separate rule.

**7. Actor model.** There are three implicit principals: `self`, `owner`, and an oracle
`authority(src, self, sig)`. A guarded call is allowed iff
`src = self ∨ src = owner ∨ (authority ≠ 0 ∧ authority(src, self, sig))`. Replacing the
owner or the authority is itself a guarded capability.

---

## 10. DappHub `DSGuard` (`ds-guard/src/guard.sol`)

**1. State.** It extends DSAuth (authority in slot 0, owner in slot 1). It adds
`acl : bytes32 → bytes32 → bytes32 → bool` in slot 2 (`:39`) and the constant
`ANY = bytes32(uint(-1)) = 0xff…ff` (`:37`).
- Addresses are keyed as `bytes32(bytes20(a))`, left-aligned with 12 zero bytes.
- The sig is keyed as `bytes32(bytes4)`, left-aligned with 28 zero bytes.
- So no real address or sig can equal ANY.

**2. Decision** (`:41-55`): `canCall(src, dst, sig)` is the 8-way disjunction over
`{src, ANY} × {dst, ANY} × {sig, ANY}` of `acl[·][·][·]`. It has no side effects.

**3. Mutations.**
- `permit(bytes32 src, bytes32 dst, bytes32 sig)` (`auth`): `acl[src][dst][sig] := true`
  (`:57-60`).
- `forbid(…)` (`auth`): `acl[src][dst][sig] := false` (`:62-65`).
- The address overloads (`:67-72`) are **not** `auth` themselves. They call the `auth`
  internal version, so `isAuthorized` sees `msg.sig` = the *address-overload* selector.
- `DSGuardFactory.newGuard()` makes `msg.sender` the owner (`:79-83`).

**4–5.** There is no time logic and no external call in `canCall`.

**6. Pitfalls.**
1. `forbid` only clears an exact triple. There are no negative rules, so a wildcard permit
   cannot be overridden by a specific forbid.
2. `acl[ANY][ANY][ANY]` makes everything public.
3. `permit` takes the sig as a left-aligned `bytes32`. Passing a right-aligned value
   silently grants nothing.
4. Permissions on `(src, guard, permit-selector)` let `src` administer the guard, but only
   if the guard is its own authority.

**7. Actor model.** This is a positive ACL relation `ACL ⊆ (Addr+*) × (Addr+*) × (Sig+*)`,
with `allow(s, d, f) ⇔ ∃ (a, b, c) ∈ ACL` such that each component equals the query value
or `*`. Administration is through DSAuth.

---

## 11. DappHub `DSRoles` (`ds-roles/src/roles.sol`)

**1. State.** It has DSAuth's slots 0-1, plus:
- `_root_users : address → bool` in slot 2
- `_user_roles : address → bytes32` in slot 3
- `_capability_roles : address → bytes4 → bytes32` in slot 4
- `_public_capabilities : address → bytes4 → bool` in slot 5

These are at `:24-27`. Role r is bit `2**r` (`:67, :101, :121`).

**2. Decision** (`:71-83`):
```
canCall(caller, code, sig) = isUserRoot(caller) || isCapabilityPublic(code, sig) || (user_roles[caller] & capability_roles[code][sig]) != 0
```
`isUserRoot` and the other getters are `public` and can be overridden. `DSChief` overrides
`isUserRoot`. Root grants everything on every target.

**3. Mutations.** All are `auth`:
- `setRootUser(who, en)` (`:89-94`)
- `setUserRole(who, r, en)` (`:96-107`)
- `setPublicCapability(code, sig, en)` (`:109-114`)
- `setRoleCapability(r, code, sig, en)` (`:116-128`)

**4–5.** None. The pragma is `>=0.4.23`, and `uint(-1)` in BITNOT requires solc < 0.8.

**6. Pitfalls.**
1. Root is unconditional, including over DSRoles itself when DSRoles is its own authority.
2. It emits no events (no `note`), so off-chain reconstruction needs traces.

**7. Actor model.** The model is RBAC with superusers:
`allow(u, t, s) ⇔ Root(u) ∨ Pub(t, s) ∨ R(u) ∩ C(t, s) ≠ ∅`.

---

## 12. MakerDAO `Vat` (`dss/src/vat.sol`, master; LibNote removed, see `:22-24`)

**1. State.** In declaration order:

| Slot | Variable | Location |
|---|---|---|
| 0 | `wards : address → uint` | `:28` |
| 1 | `can : address → address → uint` | `:36` |
| 2 | `ilks` | |
| 3 | `urns` | |
| 4 | `gem` | |
| 5 | `dai` | |
| 6 | `sin` | |
| 7 | `debt` | |
| 8 | `vice` | |
| 9 | `Line` | |
| 10 | `live : uint` | `:56-65` |

For example `wards[u]` lives at `keccak256(pad(u) ‖ 0)` and `can[a][b]` at
`keccak256(pad(b) ‖ keccak256(pad(a) ‖ 1))`. The constructor sets `wards[deployer] = 1`
and `live = 1` (`:68-71`).

**2. Guards.**
- `auth`: `require(wards[sender] == 1)` (`:31-34`). The test is equality with 1, so other
  nonzero values do not authorize.
- `wish(bit, usr) = (bit == usr) || can[bit][usr] == 1` (`:39-41`). Consent is required
  from `bit` for `usr = sender`.

The guarded entry points (`auth`), in check order:
- `rely` / `deny`: auth, then `live == 1` (`:29-30`).
- `init(ilk)`: auth, then `rate == 0` (`:100-103`).
- `file(what, data)` and `file(ilk, what, data)`: auth, then live (`:104-115`).
- `cage()`: auth, then `live := 0` (`:116-118`).
- `slip`: auth (`:121-123`).
- `grab`: auth, with no live check (`:207-220`).
- `suck`: auth, with no live check (`:230-235`).
- `fold`: auth, then live (`:238-245`).

The consent-guarded entry points:
- `flux` (`:124-128`) and `move` (`:129-133`): `wish(src, sender)`.
- `frob(i, u, v, w, dink, dart)` (`:143-180`) checks, in order:
  1. `live == 1`
  2. ilk initialized
  3. arithmetic
  4. ceilings, if `dart > 0`
  5. safety, unless `dart ≤ 0 ∧ dink ≥ 0`
  6. `wish(u, sender)`, unless `dart ≤ 0 ∧ dink ≥ 0` (`:166`)
  7. `wish(v, sender)` if `dink > 0` (`:168`)
  8. `wish(w, sender)` if `dart < 0` (`:170`)
  9. dust
- `fork` (`:182-205`): arithmetic first, then `wish(src) ∧ wish(dst)`, then safety and
  dust. There is no live check.
- `heal` (`:223-229`) acts on the sender's own balances.

**3. Authority mutations.**
- `rely(usr)`: `wards[usr] := 1`. `deny(usr)`: `wards[usr] := 0`. Both need a ward and
  `live == 1`.
- `hope(usr)`: `can[sender][usr] := 1` (`:37`). `nope(usr)`: `can[sender][usr] := 0`
  (`:38`). Both are unguarded and apply to the caller's own row.
- `cage()`: `live := 0`, which is irreversible because there is no un-cage.

**4. Time.** None. Rates are pushed by `fold` from Jug, outside the Vat.

**5. Relay.** None. The Vat makes no external calls.

**6. Pitfalls.**
1. **Wards are flat and self-propagating.** Any ward can `rely` any address, including new
   wards, and can `deny` any other ward, including itself. There is no hierarchy or quorum.
   If every ward is removed, the Vat's admin powers are gone forever.
2. After `cage`, the ward set is frozen, because `rely`/`deny` require live. `grab`,
   `suck`, and `slip` still work for wards, and End uses them for settlement.
3. **`can` is unscoped.** `hope(x)` gives `x` authority over *all* of the caller's `gem`
   (every ilk), `dai`, and urns (all ilks) for `frob`, `fork`, `flux`, and `move`. It has
   no amount, ilk, or expiry limit. It is **not transitive**: `can[a][b] ∧ can[b][c]` does
   not give `c` access to `a`. It also cannot be delegated further. A ward is **not**
   automatically `wish`-authorized, but wards have `slip`, `grab`, and `suck`, which bypass
   consent entirely.
4. `frob` lets anyone improve someone else's urn using their *own* `v` and `w` resources
   without `u`'s consent.
5. `wards[x] == 1` is an exact test.

**7. Actor model.** There are two independent authority layers.
1. **Ward set** `W ⊆ Addr`. Its members have full administrative and confiscatory powers,
   and any member can add or remove any member while `live`.
2. **Per-account delegation** `can ⊆ Addr × Addr`. It is set unilaterally by the
   delegator and grants all-or-nothing control over that account's balances and urns.

A monotone kill flag `live: 1 → 0` freezes `W` and blocks risk-increasing user actions.

---

## 13. DappHub `DSPause` / `DSPauseProxy` (`ds-pause/src/pause.sol`)

**1. State.** The base is `DSAuth` + `DSNote`, and DSNote has no storage.

| Slot | Variable | Location |
|---|---|---|
| 0 | `authority` | |
| 1 | `owner` | |
| 2 | `plans : bytes32 → bool` | `:48` |
| 3 | `proxy : DSPauseProxy` | `:49` |
| 4 | `delay : uint` | `:50` |

`DSPauseProxy` has `owner` in slot 0 (`:110`). The constructor `(delay_, owner_, authority_)`
sets them and deploys a proxy whose `owner` is the pause (`:54-59, :112`). In the
integration test deployment the call is `new DSPause(delay, address(0x0), chief)`
(`src/integration.t.sol:167`). So **owner = 0 and authority = chief**. The chief is the
authority, not the owner.

Plan id (`:63-68`): `keccak256(abi.encode(usr, tag, fax, eta))`, where `tag` is the
expected `extcodehash(usr)` (`:70-75`). In ABI head/tail form the encoded tuple is
`usr ‖ tag ‖ 0x80 ‖ eta ‖ len(fax) ‖ fax‖pad`.

**2. Guarded entry points.**
- `plot(usr, tag, fax, eta)` is `note auth`. Here `auth` is DSAuth's: self, owner (= 0),
  then `authority.canCall(sender, pause, plot.selector)`. It then requires
  `eta >= add(now, delay)`, overflow-checked (`:79-84`). Effect: `plans[id] := true`.
- `drop(...)` is `note auth`. Effect: `plans[id] := false` (`:86-90`). It has no other
  checks, so dropping an unplotted id is a no-op.
- `exec(...)` can be called by **anyone** (`:92-104`). It checks, in order:
  1. `plans[id]`
  2. `extcodehash(usr) == tag`
  3. `now >= eta`

  It then clears the plan, calls `proxy.exec(usr, fax)`, and finally requires
  `proxy.owner() == self`.
- `wait` is `require(sender == proxy)` (`:25`). It guards `setOwner`, `setAuthority`, and
  `setDelay` (`:27-37`), which override DSAuth's `auth` versions.

**3. Authority mutations.** `owner`, `authority`, and `delay` can change **only** through a
plan whose delegatecalled code calls back into `pause.setX`, so that `msg.sender = proxy`.
That means every admin change is itself delayed. `plans` changes only through `plot`,
`drop`, and `exec`.

**4. Time.** Plotting requires `eta ≥ now + delay` (`:82`), and execution requires
`now ≥ eta` (`:98`). There is **no expiry or grace period**: a plotted plan stays executable
forever until it is dropped or executed. Changing `delay` does not affect plans that were
already plotted.

**5. Relay.** `pause.exec` makes a **CALL** to `proxy.exec`. `proxy.exec` checks
`sender == owner (pause)` and then **DELEGATECALL**s `usr` with `fax` (`:114-121`).
- Inside the plan code, `address(this) = proxy`, `msg.sender = pause`, and `msg.value = 0`.
- Calls issued by the plan reach their targets with `msg.sender = proxy`.
- A revert in the plan reverts the whole call (`"ds-pause-delegatecall-error"`).
- The authority query is a STATICCALL (pragma `>=0.5.0 <0.6.0`), and the post-check
  `proxy.owner()` is also a STATICCALL.

**6. Pitfalls.**
1. **The plan runs arbitrary code as the proxy.** It can write any proxy storage slot,
   since only slot 0 (`owner`) is checked afterwards. It can call any contract with
   proxy authority; on Maker the proxy is the ward of the core contracts. It can call back
   into `pause.setDelay`/`setOwner`/`setAuthority` via `wait`, and it can call
   `pause.exec` for other ready plans. It cannot re-execute itself, because the plan is
   cleared before the call.
2. `plot` from inside a plan requires the proxy to be authorized by the chief or to be the
   owner.
3. Before Cancun, a plan could SELFDESTRUCT the proxy. The post-check still passes inside
   the transaction, the proxy then disappears, and the pause is bricked. After EIP-6780 this
   only clears ETH.
4. `tag` pins the code hash at execution time, which defends against CREATE2 redeploy and
   metamorphic contracts. For an empty `usr`, `extcodehash` is 0 for an absent account and
   `keccak("")` for an existing code-less account, and the delegatecall is a no-op success.
5. A hat that can `plot` can also `drop` other plans.
6. The `note` modifier logs `msg.data` (anonymous `LogNote`).

**7. Actor model.** There is a scheduler holding a set of commitments
`Plans ⊆ H(usr, tag, fax, eta)`.
- An *authorized proposer* (decided by the DSAuth oracle, in practice the chief's hat) can
  insert a commitment with `eta ≥ now + delay` or remove one.
- *Anyone* can fire a commitment once `now ≥ eta`, provided `codehash(usr) = tag`.
- Firing is one-shot and executes `usr`'s code by DELEGATECALL inside an isolated executor
  identity (the proxy). All downstream authority is granted to that executor.
- The scheduler's own parameters can only be changed by the executor, which means by a
  delayed plan.

---

## 14. DappHub `DSChief` (`ds-chief/src/chief.sol`)

**1. State.** This is a C3 linearization I derived by hand, not compiler-checked:
`DSChief, DSChiefApprovals, DSThing, DSMath, DSNote, DSRoles, DSAuthority, DSAuth`. It gives
the slots below.

| Slot | Variable | Location |
|---|---|---|
| 0 | `authority` | |
| 1 | `owner` | |
| 2 | `_root_users` | |
| 3 | `_user_roles` | |
| 4 | `_capability_roles` | |
| 5 | `_public_capabilities` | |
| 6 | `slates : bytes32 → address[]` | `:28` |
| 7 | `votes : address → bytes32` | `:29` |
| 8 | `approvals : address → uint` | `:30` |
| 9 | `deposits : address → uint` | `:31` |
| 10 | `GOV` | |
| 11 | `IOU` | |
| 12 | `hat` | `:34` |
| 13 | `MAX_YAYS` | `:36` |

The constructor sets `authority = this` and `owner = 0` (`:154-156`).

**2. Entry points.** None of these have access control. They are all `note`.
- `lock(wad)`: `GOV.pull(sender, wad)`, which is a `transferFrom` and needs approval. Then
  `IOU.mint(sender, wad)`, `deposits += wad`, and `addWeight(wad, votes[sender])`
  (`:49-57`).
- `free(wad)`: `deposits -= wad` (checked), `subWeight`, then `IOU.burn(sender, wad)`. The
  burn needs the user's IOU allowance to the chief, because DSToken `burn(guy)` with
  `guy ≠ msg.sender` checks the allowance (`ds-token/src/token.sol:112-122`). Finally
  `GOV.push(sender, wad)` (`:59-67`).
- `etch(yays)`: requires `len ≤ MAX_YAYS` and strictly increasing addresses, then sets
  `slates[keccak256(abi.encodePacked(yays))] := yays` (`:69-81`).
- `vote(address[])` calls `etch` and then `vote(bytes32)` (`:83-89`).
- `vote(slate)` requires `slates[slate].length > 0` or
  `slate == keccak256("") = 0xc5d2…a470`. It then moves the sender's full deposit weight
  from the old slate to the new one (`:91-101`). This check is the fix for "slate camping",
  per `chief-exploits.t.sol:86-230`.
- `lift(whom)` can be called by **anyone**. It requires `approvals[whom] > approvals[hat]`
  (strict) and sets `hat := whom` (`:104-110`).

**DSAuthority role.** The chief inherits `canCall` from DSRoles, with `isUserRoot(who) := (who == hat)`
(`:168-173`). So:
```
chief.canCall(u, t, s) = (u == hat) || _public_capabilities[t][s] || (_user_roles[u] & _capability_roles[t][s]) != 0
```
**3. Authority mutations.**
- `hat` changes only via `lift`.
- `setOwner`, `setAuthority`, and `setRootUser` always revert (`:158-166, :174-177`).
- `setUserRole`, `setPublicCapability`, and `setRoleCapability` are DSRoles `auth`, with
  `authority = this`. `isAuthorized(u)` is therefore `u == chief` (self) `|| u == 0`
  (impossible) `|| chief.canCall(u, chief, sig)`. In practice the **hat** decides
  (`chief.t.sol:326-391`).

**4. Time.** There is no time dependence and no snapshot. Weight is the current deposit.
`lock → vote → lift → free` can all run in **one transaction**, which enables flash-loaned
election of the hat. This version has no same-block lock/free restriction. Maker's later
chief v1.2 (makerdao/ds-chief) reportedly adds one; I did not verify that here.

**5. Relay.** The chief makes external CALLs to the GOV and IOU tokens. When it is the
authority of DSPause, the pause queries it with a STATICCALL.

**6. Pitfalls.**
1. The hat is a **root user over every contract whose authority is the chief**. That
   includes `pause.plot` and `drop`, and the chief's own role and capability tables. A hat
   can therefore call `setPublicCapability(pause, plot.selector, true)` to let *anyone*
   plot, or assign roles that outlive its tenure.
2. The hat stays in place when its approvals drop. Removing it needs an explicit `lift` of
   a strictly higher candidate.
3. Initially `hat = 0` with `approvals[0] = 0`.
4. Moving IOU tokens away blocks `free` for the depositor.
5. `addWeight` and `subWeight` loop over the slate, so their gas cost is bounded by
   `MAX_YAYS`.

**7. Actor model.** This is approval voting with an elected root user. Token holders escrow
weight `D(u)` and point it at a slate `S(u) ⊆ Candidates`, so that
`approvals(c) = Σ{D(u) | c ∈ S(u)}`. Anyone can promote any candidate whose approvals strictly
exceed the incumbent's. The elected `hat` acts as a DSRoles superuser, so the chief as a
DSAuthority grants the hat every capability, plus whatever role and public capabilities the
hat configured.

---

## 15. Compound `Timelock` (`contracts/Timelock.sol`, ^0.8.10)

**1. State.**
- `admin` in slot 0
- `pendingAdmin` in slot 1
- `delay : uint` in slot 2
- `queuedTransactions : bytes32 → bool` in slot 3 (`:20-24`)
- Constants: `GRACE_PERIOD = 14 days`, `MINIMUM_DELAY = 2 days`, `MAXIMUM_DELAY = 30 days`
  (`:16-18`)

`txHash = keccak256(abi.encode(target, value, signature, data, eta))` (`:65, :75, :84`).

**2. Guarded entry points.**
- `setDelay(d)`: `sender == self`, then `d ≥ MIN`, then `d ≤ MAX` (`:37-44`).
- `acceptAdmin()`: `sender == pendingAdmin`. Effect: `admin := sender`, `pendingAdmin := 0`
  (`:46-52`).
- `setPendingAdmin(p)`: `sender == self` (`:54-59`).
- `queueTransaction(...)`: `sender == admin`, then `eta >= now.add(delay)`. Effect:
  `queued[h] := true` (`:61-70`).
- `cancelTransaction(...)`: `sender == admin`. Effect: `queued[h] := false` (`:72-79`).
- `executeTransaction(...)` is `payable`. It checks, in order (`:81-106`):
  1. `sender == admin`
  2. `queued[h]`
  3. `now >= eta`
  4. `now <= eta.add(GRACE_PERIOD)`

  It then sets `queued[h] := false` and calls. The calldata is `data` if `signature` is
  empty, otherwise `bytes4(keccak(signature)) ‖ data`. The call is
  `target.call{value: value}(callData)` and must succeed.
- The constructor checks `MIN ≤ delay_ ≤ MAX` and sets `admin := admin_`, with no zero
  check (`:27-33`). `fallback() payable` accepts ETH (`:35`).

**3. Authority mutations.** Changing `delay` or `pendingAdmin` requires a self-call, which
means a queued and executed transaction targeting the timelock. `admin` changes only via
`acceptAdmin` by the pending admin.

**4. Time.** A transaction becomes executable at `eta` and expires after `eta + 14 days`.
The window is the closed interval `[eta, eta + GRACE]`. Queueing needs
`eta ≥ now + delay` with `delay ∈ [2 d, 30 d]`.

**5. Relay.** Execution is a **CALL** with `msg.sender = Timelock` and `value` taken from
the Timelock balance (not necessarily `msg.value`). The return data is passed back. The
timelock self-calls for `setDelay` and `setPendingAdmin` through `executeTransaction` with
`target = self`.

**6. Pitfalls.**
1. `txHash` has no nonce, so identical actions with the same `eta` collide. GovernorBravo
   guards against this.
2. Only the admin can execute, and execution is one-shot.
3. A stale transaction is never auto-cleared and simply stays true but unexecutable.
4. `pendingAdmin` is not cleared on cancel. Overwriting it is the only way to revoke it.
5. The deployed mainnet timelock (0.5.x) may differ in syntax and initialization. This
   description covers the repo version only.

**7. Actor model.** There is a single `admin` principal that can commit to calls
`H(target, value, sig, data, eta)` with `eta ≥ now + delay`, cancel them, and fire them in
`[eta, eta + 14 d]`. Fired calls run as the timelock. The timelock's own parameters,
including the admin handoff, can only be changed by the timelock calling itself, which
means through the same delayed path. Admin rotation is two-step, through pendingAdmin.

---

## 16. Compound `GovernorBravoDelegate` (`contracts/Governance/GovernorBravoDelegate.sol`)

**1. State.** The delegate runs through `GovernorBravoDelegator`, a DELEGATECALL proxy
(`GovernorBravoDelegator.sol:66-78`), so the storage belongs to the delegator
(`GovernorBravoInterfaces.sol`).

| Slot | Variable |
|---|---|
| 0 | `admin` |
| 1 | `pendingAdmin` |
| 2 | `implementation` |
| 3 | `votingDelay` |
| 4 | `votingPeriod` |
| 5 | `proposalThreshold` |
| 6 | `initialProposalId` |
| 7 | `proposalCount` |
| 8 | `timelock` |
| 9 | `comp` |
| 10 | `proposals` |
| 11 | `latestProposalIds` |
| 12 | `whitelistAccountExpirations` |
| 13 | `whitelistGuardian` |

The `Proposal` struct has the fields `id`, `proposer`, `eta`, `targets[]`, `values[]`,
`signatures[]`, `calldatas[]`, `startBlock`, `endBlock`, `forVotes`, `againstVotes`,
`abstainVotes`, `canceled`, `executed`, and `receipts`.

Constants (`:12-33`):

| Constant | Value |
|---|---|
| `MIN_PROPOSAL_THRESHOLD` | 1 000e18 |
| `MAX_PROPOSAL_THRESHOLD` | 100 000e18 |
| `MIN_VOTING_PERIOD` | 5760 blocks |
| `MAX_VOTING_PERIOD` | 80640 blocks |
| `MIN_VOTING_DELAY` | 1 block |
| `MAX_VOTING_DELAY` | 40320 blocks |
| `quorumVotes` | 400 000e18 |
| `proposalMaxOperations` | 10 |

**State function** (`state`, `:209-229`). It requires
`initialProposalId < id ≤ proposalCount` and then evaluates:
```
canceled                                       → Canceled
bn ≤ startBlock                                → Pending
bn ≤ endBlock                                  → Active
forVotes ≤ againstVotes ∨ forVotes < quorum    → Defeated
eta == 0                                       → Succeeded
executed                                       → Executed
now ≥ eta + timelock.GRACE_PERIOD()            → Expired      // external STATICCALL to timelock
otherwise                                      → Queued
```
**2. Guarded entry points.**
- `initialize(...)` (`:49-63`) checks, in order:
  1. `timelock == 0`
  2. `sender == admin`
  3. nonzero addresses
  4. parameter ranges
- `propose(...)` (`:74-117`) checks, in order:
  1. `initialProposalId != 0`
  2. `comp.getPriorVotes(sender, bn - 1) > proposalThreshold` (strict) `|| isWhitelisted(sender)`
  3. equal array lengths
  4. `len != 0`
  5. `len ≤ 10`
  6. the proposer's latest proposal is neither Active nor Pending

  It then sets `startBlock = bn + votingDelay` and `endBlock = startBlock + votingPeriod`.
- `queue(id)` (`:123-132`) can be called by anyone. It requires `state == Succeeded` and
  sets `eta = now + timelock.delay()`. For each action it requires
  `!timelock.queuedTransactions(h)` and then calls `timelock.queueTransaction`.
- `execute(id)` (`:143-151`) can be called by anyone and is payable. It requires
  `state == Queued` and sets `executed = true`. For each action it calls
  `timelock.executeTransaction{value: values[i]}`, paid from the governor's balance or the
  attached `msg.value`.
- `cancel(id)` (`:157-179`) requires `state != Executed`. If `sender ≠ proposer`:
  - If the proposer is whitelisted, it requires
    `getPriorVotes(proposer, bn - 1) < threshold ∧ sender == whitelistGuardian`.
  - Otherwise it requires `getPriorVotes(proposer, bn - 1) < threshold`, so anyone may
    cancel.

  It then sets `canceled = true` and calls `timelock.cancelTransaction(..., eta)` for each
  action, which is harmless when `eta = 0`.
- `castVote`, `castVoteWithReason`, and `castVoteBySig` (`:236-261`) use EIP-712 with
  `ecrecover ≠ 0`. They have no nonce and are replay-protected only by `hasVoted`.
  `castVoteInternal` (`:270-291`) requires `state == Active`, `support ≤ 2`, and
  `!hasVoted`. Its weight is `comp.getPriorVotes(voter, startBlock)`.
- `isWhitelisted(a) = whitelistAccountExpirations[a] > now` (`:298-300`).
- The admin-only setters are `_setVotingDelay`, `_setVotingPeriod`, and
  `_setProposalThreshold`, each with range checks (`:306-340`), plus
  `_setWhitelistGuardian` (`:358-364`) and `_initiate` (`:371-377`). `_initiate` requires
  `initialProposalId == 0`, copies `proposalCount` from GovernorAlpha, and calls
  `timelock.acceptAdmin()`.
- `_setWhitelistAccountExpiration(a, exp)` accepts `admin || whitelistGuardian` (`:347-352`).
- `_setPendingAdmin(p)`: admin only (`:384-396`).
- `_acceptAdmin()` requires `sender == pendingAdmin ∧ sender ≠ 0` (`:402-418`).
- On the delegator, `_setImplementation(impl)` requires admin and `impl ≠ 0`
  (`GovernorBravoDelegator.sol:36-44`).

**"Proposal guardian".** This repo has **no** `proposalGuardian`. `grep` finds no matches.
The only guardian is `whitelistGuardian`, and it can only:
1. set whitelist expirations, including for itself, which lets it whitelist itself and
   propose with no threshold, and
2. cancel whitelisted proposers' proposals once they are below threshold.

A "proposalGuardian" exists in Compound's newer governor, which is a separate repo and out
of scope here.

**3. Authority mutations.** Parameter, whitelist, and admin changes need `admin`. In
production the admin is the Timelock, so these changes are proposal-gated. Implementation
upgrade also needs `admin`. Admin rotation is two-step.

**4. Time.** Voting runs on block numbers: Pending while `bn ≤ start` and Active while
`start < bn ≤ end`. Voting weight is snapshotted at `startBlock`, and the proposer's weight
at `bn - 1`. `Comp.getPriorVotes` requires `blockNumber < block.number`
(`Comp.sol:189-190`). The timelock stage runs on timestamps.
- **Boundary mismatch.** Bravo says `Expired` when `now ≥ eta + GRACE` (`:224`), but the
  Timelock still accepts at `now == eta + GRACE` (`Timelock.sol:87`). Bravo is stricter by
  one second.
- `queue` sets `eta = now + delay`, which meets the timelock's `≥` with equality.

**5. Relay.**
1. EOA → Delegator: CALL.
2. Delegator → implementation: DELEGATECALL, preserving `msg.sender` and storage.
3. Delegator, as identity, → Timelock: CALL, so the timelock sees `msg.sender = Delegator`,
   which must be its `admin`.
4. Timelock → target: CALL, with `msg.sender = Timelock`.
5. The reads `timelock.delay()`, `GRACE_PERIOD()`, `queuedTransactions()`, and
   `comp.getPriorVotes()` are STATICCALLs.

**6. Pitfalls.**
1. A proposal with two identical `(target, value, sig, data)` actions cannot be queued.
   The duplicate check at `:135` rejects the second.
2. The propose threshold is strict `>` and the cancel threshold strict `<`. At exactly the
   threshold, a proposer can neither propose nor be cancelled.
3. A whitelisted proposer cannot be cancelled by the public, only by the whitelist
   guardian.
4. `execute` and `queue` are permissionless.
5. `castVoteBySig` uses `ecrecover` without a malleability check, but `hasVoted` makes this
   irrelevant.
6. `cancel` can be called on Canceled, Defeated, or Expired proposals.

**7. Actor model.** This is token-weighted governance driving a timelock.
- **Proposal.** An account with snapshot weight above threshold, or a whitelisted account,
  proposes up to 10 calls.
- **Vote.** After `votingDelay` blocks, holders vote with weight snapshotted at
  `startBlock` for `votingPeriod` blocks.
- **Success.** A proposal succeeds iff `for > against ∧ for ≥ quorum`.
- **Queue and execute.** Anyone may queue a successful proposal. The governor, as timelock
  admin, commits the calls at `eta = now + delay`, and anyone may then execute in
  `[eta, eta + GRACE)`.
- **Cancel.** The proposer may cancel, and so may anyone once the proposer's weight drops
  below threshold. For whitelisted proposers, only the whitelist guardian may cancel.
- **Admin.** The governor's admin, normally the timelock, controls the parameters.

---

## 17. Compound `Comptroller` pause guardian (`contracts/Comptroller.sol`, `ComptrollerStorage.sol`, `Unitroller.sol`)

**1. State.** These derive from the storage contract order:

| Slot | Variable | Location |
|---|---|---|
| 0 | `admin` | `ComptrollerStorage.sol:11` |
| 1 | `pendingAdmin` | `:16` |
| 2 | `comptrollerImplementation` | `:21` |
| 3 | `pendingComptrollerImplementation` | `:26` |
| 9 | `markets` | |
| 10 | `pauseGuardian`, packed with `_mintGuardianPaused`, `_borrowGuardianPaused` (legacy, unused), `transferGuardianPaused` and `seizeGuardianPaused` as bytes 20–23 | `:87-91` |
| 11 | `mintGuardianPaused : address → bool` | `:92` |
| 12 | `borrowGuardianPaused : address → bool` | `:93` |
| — | `borrowCapGuardian` | `:132` |

The Comptroller runs by DELEGATECALL through the Unitroller (`Unitroller.sol:138`), so
`msg.sender` is the original caller.

**2. Guarded entry points.**
- `_setPauseGuardian(g)` (`:1032-1047`). If `sender ≠ admin` it **returns** an error code
  (`fail(UNAUTHORIZED, …)` with a `Failure` event) **without reverting**. Otherwise it sets
  `pauseGuardian := g`.
- `_setMintPaused(c, st)` (`:1049-1057`) and `_setBorrowPaused(c, st)` (`:1059-1067`) check,
  in order:
  1. `markets[c].isListed`
  2. `sender == pauseGuardian || sender == admin`
  3. `sender == admin || st == true`

  They then write the per-market flag.
- `_setTransferPaused(st)` (`:1069-1076`) and `_setSeizePaused(st)` (`:1078-1085`) apply the
  same two checks to the global flags. These four functions *revert* on failure.
- The pause flags are enforced by `require` in the hooks:
  - `mintAllowed` (`:236`)
  - `borrowAllowed` (`:342`)
  - `seizeAllowed` (`:555`)
  - `transferAllowed` (`:613`)

  Redeem, repay, and liquidate-borrow have no pause flag. Liquidation is blocked
  indirectly through `seize`.
- Other admin functions mostly use the `if (sender != admin) return fail(...)` pattern.
  Some use `require`, for example `_setCloseFactor` (`:851`) and `_setMarketBorrowCaps`
  (`admin || borrowCapGuardian`, `:996-997`). `adminOrInitializing()` (`:1143-1145`) means
  `admin || comptrollerImplementation`.
- Unitroller's two-step admin (`:86-125`) and implementation handover (`:39-77`) use
  error-code returns.

**3. Authority mutations.** Only `admin` sets `pauseGuardian`, and it may set it to 0. The
guardian's powers are **monotone restricting**: it can move each flag `false → true` (or
`true → true`) only. `admin` can set either value.

**4. Time.** None. Pauses take effect immediately and have no expiry.

**5. Relay.** No external calls are involved in the guard. In production the admin is the
Timelock, so unpausing goes through governance with a delay, while pausing by the guardian
is instant.

**6. Pitfalls.**
1. This is **negative authority**: a principal that can only shrink the set of allowed
   user actions. It is a liveness risk, not a safety risk.
2. A compromised guardian can freeze mint, borrow, transfer, and seize, which also freezes
   liquidations, until governance replaces it.
3. Admin-failure functions *do not revert*, so a model must treat "unauthorized" as a
   successful no-op returning a nonzero code with a `Failure` log.
4. A market must be listed before it can be paused.

**7. Actor model.**
- `admin` (the Timelock) holds full bidirectional control over a vector of pause flags.
- `pauseGuardian` can only set flags to `true`.
- User-facing hooks require the corresponding flag to be `false`.

---

## 18. Cross-cutting comparison

| Aspect | Solmate Auth | DSAuth | Solady Ownable(Roles) | Vat | DSPause | Compound Timelock |
|---|---|---|---|---|---|---|
| Owner checked | after authority | before authority | n/a (owner only / roles) | n/a (ward set) | owner = 0 in MCD | admin |
| Self-call authorized | no | **yes** (`src == self`) | no | no | via proxy (`wait`) | **yes** (`setDelay`, `setPendingAdmin`) |
| External oracle | STATICCALL `canCall` | STATICCALL (≥0.5) / CALL (<0.5) | self-STATICCALL `owner()` (Enumerable/Timed only) | none | chief STATICCALL | none |
| Two-step transfer | no | no | yes, 48 h expiry | no | n/a | yes (pendingAdmin) |
| Delay / expiry | – | – | handover ≤ expires; timed roles [start, expires] | – | eta ≥ now + delay; no expiry | [eta, eta + 14 d]; delay ∈ [2 d, 30 d] |
| Relay | – | – | – | – | CALL → DELEGATECALL | CALL with value |
| Failure mode | revert | revert | custom-error revert | revert | revert | revert (Comptroller: error code) |

---

## 19. Minimal abstract primitives

These are enough to state every model above formally, for example in Lean over `EvmLean`
states.

1. **Call context** `Ctx = {sender, self, sig : Bytes4, args, value, now : Timestamp, bn : BlockNumber, origin}`.
   `sig` is the outer selector, carried unchanged through internal calls.
2. **Guard** `Guard := Ctx → State → Outcome`, where `Outcome ∈ {Allow, Revert(reason), SoftFail(code)}`.
   Checks are an *ordered* list. The first failing check decides the outcome, and checks
   that involve external calls can themselves revert. This is needed for check order, for
   Solmate's authority-before-owner rule, and for Compound's error-code returns.
3. **Principal slots.** `owner/admin : Option Address`, and `pending : Option Address`,
   optionally with an `expiry : Timestamp` per candidate (Solady `H : Address → Timestamp`).
   Transitions are direct set, propose/accept, and renounce. Renounce may use a sentinel,
   so a "never initialized" flag is needed.
4. **Membership set** `W : Set Address`, with flat self-administration (`rely`/`deny`).
5. **Role relations.**
   - (a) Bitmap `R : Address → BitVec 256`, with `anyOf(m) := R(u) &&& m ≠ 0` and
     `allOf(m) := R(u) &&& m = m`.
   - (b) Capability map `C : Target × Sig → BitVec 256` (or `Sig → …`) plus a public flag
     `P`, and a root predicate.
   - (c) An enumerable set `Holders : Role → List Address` with a no-duplicates invariant
     and an index map.
   - (d) Time-ranged grants `G : Address × Role → (start, expires)`, active iff
     `start ≤ now ≤ expires`.
6. **Wildcard ACL** `ACL ⊆ (Addr ⊎ *) × (Addr ⊎ *) × (Sig ⊎ *)` with pattern-match lookup.
7. **Delegation relation** `can : Address → Address → Bool`. It is set only by the first
   argument, is non-transitive, and is unscoped: `wish(a, s) := a = s ∨ can a s`.
8. **External authority oracle** `canCall : Address(authority) → (user, target, sig) → State → Bool ⊎ ⊥`.
   It is evaluated by **STATICCALL**: read-only, any computable function of world state,
   possibly ⊥ (revert or out-of-gas). It covers self-staticcalls such as Solady
   `owner()`/`MAX_ROLE()`, with their returndata-size checks.
9. **Liveness and kill flags.** A monotone `live : 1 → 0` that freezes the authority
   tables, and **one-directional capabilities**: a principal allowed only `flag := true`
   (negative or restricting authority) next to a principal allowed both directions.
10. **Commitment queue** `Q : Hash → Bool`, keyed by `H(action, eta)` with an exact
    encoding (`abi.encode`). Its operations are:
    - insert, guarded by `eta ≥ now + delay`
    - cancel
    - fire, guarded by `eta ≤ now ≤ eta + grace`, where grace is `∞` for DSPause
    - clear before running, so firing is one-shot

    It also carries `delay` bounds and the rule that parameters can only change by
    self-call.
11. **Code identity** `codehash : Address → Bytes32`, used to pin plans (`tag`).
12. **Relays**:
    - `CALL(target, value, data)`, where the callee sees `sender = relayer`.
    - `DELEGATECALL(code, data)`, which runs foreign code with the relayer's storage,
      balance, and identity, so all its outbound calls have `sender = relayer`.
    - `STATICCALL`, which is read-only.
    - Post-condition checks after a relay (`proxy.owner() == pause`).
    - Upgradeable indirection, a proxy that DELEGATECALLs an `implementation` pointer
      (Bravo Delegator, Unitroller), with shared storage layout.
13. **Elections**:
    - (a) Snapshot weight oracle `votes(u, block)`, defined only for `block < bn`, with
      tallies, `quorum`, strict thresholds, and a proposal state machine over `(bn, now)`.
    - (b) Approval voting with escrowed deposits and slates:
      `approvals(c) = Σ deposit(u) · [c ∈ slate(u)]`, and `lift` when strictly greater.
      There is no snapshot, so same-transaction manipulation is possible.
14. **Storage-slot model** to connect to bytecode:
    - the Solidity mapping formula `keccak256(pad(k) ‖ pad(slot))` with bytesN
      left-alignment, and nesting
    - Solady seed-packed slots: `keccak256(addr << 96 | seed)` over 32 bytes, and
      `keccak256(role ‖ seed4 ‖ addr20)` over 36 or 56 bytes
    - constant high slots (`_OWNER_SLOT`)
    - bit-packing (`start << 216 | expires`, length in the low 96 bits, packed bool bytes)
15. **Authority graph / reachability.** A derived relation `controls(a, b)`: "a can, through
    some sequence of permitted calls (including via relays and self-administration), make
    b's guard admit an arbitrary principal". It is needed to state properties such as "only
    the PauseProxy, after the delay, can rely on Vat" or "the hat can grant public plot".
