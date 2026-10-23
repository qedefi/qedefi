# OpenZeppelin Contracts: actor and authority model for governance and proxies

**Source.** OpenZeppelin Contracts **v5.7.0**, the latest stable v5 tag (later tags are only `-rc`). Tag commit
`cab19933c33c2ad1d4c7a84864a3601dddfd16f3`, committed 2026-07-29. It was cloned to
`research/src-oz-gov/`, and every `file:line` below refers to that tree unless marked otherwise.

**4.x comparison.** v4.9.6, commit `dc44c9f1a4c3b10af99492eed84f83ed244203f6`, in `research/src-oz-gov-v4/`.
Differences between v5 releases (5.0, 5.3, 5.4, 5.5 against 5.7) were checked with `git show <tag>:<path>` on
fetched tags.

**Method.** Source reading only. Nothing from the repository was built or run. Slot constants and selectors were
recomputed with a small pure-Python Keccak written by me. It reproduces the in-source constants
`IMPLEMENTATION_SLOT`, `ADMIN_SLOT`, `BEACON_SLOT` and `INITIALIZABLE_STORAGE`.

**Paths.** Paths are relative to `contracts/`.

Notation:

- `S` is the caller (`msg.sender`). In these non-meta-tx contracts `_msgSender()` equals `msg.sender`, because
  `Context` is the identity.
- `now_ts` is `block.timestamp`, and `now_bn` is `block.number`.
- `clock()` is the ERC-6372 clock.
- A guard is listed as an ordered sequence of `check → revert error`.

---

## 0. Shared building blocks

### 0.1 AccessControl (`access/AccessControl.sol`)

**Storage** (non-upgradeable): `mapping(bytes32 role => RoleData) _roles` at slot `p` (slot 0 in TimelockController).
`RoleData { mapping(address=>bool) hasRole; bytes32 adminRole; }`.

- `hasRole[role][a]` is at `keccak(a . keccak(role . p))`.
- `adminRole(role)` is at `keccak(role . p) + 1`.
- `DEFAULT_ADMIN_ROLE = 0x00` (line 57). Every role's admin defaults to `0x00` unless `_setRoleAdmin` is called.

**Entry points:**

| function | guard (in order) | effect / events |
|---|---|---|
| `grantRole(role,a)` (120) | `hasRole(getRoleAdmin(role), S)` else `AccessControlUnauthorizedAccount(S, adminRole)` | `_grantRole`: if not already set, set true and emit `RoleGranted(role,a,S)` (180-188) |
| `revokeRole(role,a)` (135) | same | `_revokeRole`: if set, set false and emit `RoleRevoked(role,a,S)` (197-205) |
| `renounceRole(role,c)` (154) | `c == S` else `AccessControlBadConfirmation` | `_revokeRole(role,S)` |

`grantRole` and `revokeRole` on an account that already has (or lacks) the role are silent no-ops.

### 0.2 Ownable (`access/Ownable.sol`)

**Storage:** `address _owner` (slot 0 when it comes first).

- The constructor reverts `OwnableInvalidOwner(0)` if `initialOwner == 0` (38-43).
- `onlyOwner`: `owner() == S` else `OwnableUnauthorizedAccount(S)` (48-67).
- `transferOwnership(n)`: `onlyOwner`, then `n != 0`, then `_owner = n` and emit `OwnershipTransferred(old,n)` (84-99).
- `renounceOwnership()`: `onlyOwner`, then `_owner = 0` (76-78). This is irreversible.

### 0.3 Address helpers (`utils/Address.sol`)

- `verifyCallResult(success, ret)` (158-166): bubbles the callee's revert data, or reverts `Errors.FailedCall()` if
  that data is empty. It does **not** check that the target has code, so a CALL to an EOA "succeeds".
- `functionDelegateCall(target, data)` (116-127): DELEGATECALL. On success with empty returndata and no code at
  `target`, it reverts `AddressEmptyCode(target)`.

### 0.4 DoubleEndedQueue.Bytes32Deque (`utils/structs/DoubleEndedQueue.sol:31-35`)

`{uint128 _begin; uint128 _end; mapping(uint128=>bytes32) _data}`. `_begin` and `_end` share one slot.

- `popFront` on an empty queue: `Panic(0x31)` (120-124).
- `clear()` sets `_begin = _end = 0` (260-263).

### 0.5 Checkpoints.Trace208 (`utils/structs/Checkpoints.sol:452-459`)

`Checkpoint208[] _checkpoints`, where `Checkpoint208 {uint48 _key; uint208 _value}` is packed into one slot.

`push(key, v)`:
- if the last key is greater than `key`: revert `CheckpointUnorderedInsertion`;
- if the last key equals `key`: overwrite the value;
- otherwise append.

`upperLookupRecent(k)` returns the value of the **last** checkpoint with `_key <= k`, or 0 if there is none. Before
the binary search it probes the window `len - sqrt(len)`.

`latest()` is the last value, or 0.

### 0.6 ERC-6372 clocks (`utils/types/Time.sol`, `utils/ERC6372Utils.sol`)

- `Time.blockNumber() = toUint48(block.number)` and `Time.timestamp() = toUint48(block.timestamp)` (Time.sol:26-35).
- `ERC6372Utils.blockNumberClockMode(clock)` reverts `ERC6372InconsistentClock` if `clock() != block.number`.
  Otherwise it returns `"mode=blocknumber&from=default"` (ERC6372Utils.sol:27-33). This is new in 5.7; in 5.5 the
  check was inline in `Votes`.

### 0.7 ERC-7201 namespaces

These apply to the separate `openzeppelin-contracts-upgradeable` package, which is not in this repository.

The formula is `slot(id) = keccak256(abi.encode(uint256(keccak256(id)) - 1)) & ~bytes32(uint256(0xff))`.

- **Verified in source:** `openzeppelin.storage.Initializable = 0xf0c57e16840df040f15088dc2f81fe391c3923bec73e23a9662efc9c229c6a00`
  (`proxy/utils/Initializable.sol:76-77`).
- **Computed by the `openzeppelin.storage.<Contract>` naming convention** (to be cross-checked against the
  upgradeable repository):

| namespace | slot |
|---|---|
| AccessControl | `0x02dd7bc7dec4dceedda775e58dd541e08a116c6c53815c0bd028192f7b626800` |
| Ownable | `0x9016d09d72d40fdae2fd8ceac6b6234c7706214fd39c1cd1e609a0528c199300` |
| TimelockController | `0x9a37c2aa9d186a0969ff8a8267bf4e07e864c2f2768f5040949e28a624fb3600` |
| Governor | `0x7c712897014dbe49c045ef1299aa2d5f9e67e48eea4403efa21f1e0f3ac0cb00` |
| GovernorTimelockControl | `0x0d5829787b8befdbc6044ef7457d8a95c2a04bc99235349f1a212c063e59d400` |
| GovernorVotes | `0x3ba4977254e415696610a40ebf2258dbfa0ec6a2ff64e84bfe715ff16977cc00` |
| GovernorVotesQuorumFraction | `0xe770710421fd2cad75ad828c61aa98f2d77d423a440b67872d0f65554148e000` |
| GovernorCountingSimple | `0xa1cefa0f43667ef127a258e673c94202a79b656e62899531c4376d87a7f39800` |
| GovernorSettings | `0x00d7616c8fe29c6c2fbe1d0c5bc8f2faa4c35b43746e70b24b4d532752affd00` |
| GovernorPreventLateQuorum | `0x042f525fd47e44d02e065dd7bb464f47b4f926fbd05b5e087891ebd756adf100` |
| GovernorProposalGuardian | `0x2953e0c334ced07e397f02d0e9b450dbfd92be015e93a9c249855132826e0300` |
| Votes | `0xe8b26c30fad74198956032a3533d903385d56dd795af560196f9c78d4af40d00` |
| Nonces | `0x5ab42ced628888259c08ac98db1eb0cf702fc1501344311d8b100cd1bfe4bb00` |
| EIP712 | `0xa16a46d94261c7517cc8ff89f61c0ce93598e3c849801011dee649a6a557d100` |
| ERC20 | `0x52c63247e1f47db19d5ce0460030c497f067ca4cebf71ba98eeadabe20bace00` |

The non-upgradeable contracts in this repository use plain sequential slots (layouts below).

### 0.8 Selectors (computed)

| function | selector |
|---|---|
| `upgradeToAndCall(address,bytes)` | `0x4f1ef286` |
| `upgradeAndCall(address,address,bytes)` | `0x9623609d` |
| `proxiableUUID()` | `0x52d1902d` |
| `upgradeTo(address)` | `0x3659cfe6` |
| `implementation()` | `0x5c60da1b` |
| `updateDelay(uint256)` | `0x64d62353` |
| `relay(address,uint256,bytes)` | `0xc28bc2fa` |
| `updateTimelock(address)` | `0xa890c910` |
| `schedule(...)` | `0x01d5062a` |
| `scheduleBatch(...)` | `0x8f2a0bb0` |
| `execute(address,uint256,bytes,bytes32,bytes32)` | `0x134008d3` |
| `executeBatch(...)` | `0xe38335e5` |
| `cancel(bytes32)` | `0xc4d252f5` |
| `grantRole` | `0x2f2ff15d` |

---

## 1. TimelockController (`governance/TimelockController.sol`, last updated v5.6.0)

`contract TimelockController is AccessControl, ERC721Holder, ERC1155Holder` (line 24).

### 1.1 Authority state

| slot | variable | meaning |
|---|---|---|
| 0 | `AccessControl._roles` | role membership and admin roles |
| 1 | `mapping(bytes32 id => uint256) _timestamps` (30) | operation readiness timestamp. 0 = Unset, 1 = Done, otherwise the ETA |
| 2 | `uint256 _minDelay` (31) | minimum scheduling delay, in **seconds** |

The two Holder bases add no storage.

**Role constants:**

| role | value |
|---|---|
| `PROPOSER_ROLE` | `keccak256("PROPOSER_ROLE") = 0xb09aa5ae…19cc1` |
| `EXECUTOR_ROLE` | `0xd8aa0f31…469e63` |
| `CANCELLER_ROLE` | `0xfd643c72…26f783` |
| `DEFAULT_ADMIN_ROLE` | `0x00` |

`DONE_TIMESTAMP = 1` (25-28). There is no `_setRoleAdmin` call, so **every role is administered by
`DEFAULT_ADMIN_ROLE`**.

**Operation state** (`getOperationState`, 205-216), with `t = _timestamps[id]`:
- `t == 0` gives `Unset`;
- `t == 1` gives `Done`;
- `t > now_ts` gives `Waiting`;
- otherwise (`1 < t <= now_ts`) gives `Ready`.

Derived predicates:
- `isOperation = state ≠ Unset`;
- `isOperationPending = Waiting ∨ Ready` (note that Ready counts as pending);
- `isOperationReady = Ready`;
- `isOperationDone = Done` (168-192).

**Operation ids:**
- single call: `id = keccak256(abi.encode(target, value, data, predecessor, salt))` (231-239);
- batch: `idB = keccak256(abi.encode(targets[], values[], payloads[], predecessor, salt))` (245-253).

A one-element batch and a single call have different ids.

### 1.2 Constructor (115-137)

`constructor(minDelay, proposers[], executors[], admin)`:
1. `_grantRole(DEFAULT_ADMIN_ROLE, address(this))`, which is self-administration.
2. If `admin != 0`: `_grantRole(DEFAULT_ADMIN_ROLE, admin)`.
3. For each proposer `p`: grant `PROPOSER_ROLE` **and** `CANCELLER_ROLE`. Proposer and canceller are equal by
   construction.
4. For each executor `e`: grant `EXECUTOR_ROLE`. Passing `address(0)` here opens the role.
5. `_minDelay = minDelay` and emit `MinDelayChange(0, minDelay)`.

`RoleGranted` events carry sender = deployer.

### 1.3 Guards

- **`onlyRole(r)`**: `hasRole(r, S)` else `AccessControlUnauthorizedAccount(S, r)`.
- **`onlyRoleOrOpenRole(r)`** (145-150): if `hasRole(r, address(0))` **the check is skipped**. Otherwise it behaves
  like `onlyRole(r)`. It is applied only to `EXECUTOR_ROLE` (execute and executeBatch). Granting `PROPOSER_ROLE` or
  `CANCELLER_ROLE` to `address(0)` has no effect, because those functions use plain `onlyRole`.

### 1.4 Entry points and transitions

| entry | guard (in order) | effect | events |
|---|---|---|---|
| `schedule(target,value,data,pred,salt,delay)` (264-278) | ① `onlyRole(PROPOSER)`; ② `_schedule`: `isOperation(id)` → `TimelockUnexpectedOperationState(id, bit(Unset))`; ③ `delay < getMinDelay()` → `TimelockInsufficientDelay(delay,min)`; ④ `now_ts + delay` overflow → Panic | `_timestamps[id] = now_ts + delay` (322) | `CallScheduled(id,0,target,value,data,pred,delay)`, then `CallSalt(id,salt)` if `salt ≠ 0` |
| `scheduleBatch(...)` (289-309) | ① `onlyRole(PROPOSER)`; ② lengths equal, else `TimelockInvalidOperationLength(t,p,v)`; ③ as `_schedule` | same | one `CallScheduled(id,i,…)` per element, then optional `CallSalt` |
| `cancel(id)` (332-342) | ① `onlyRole(CANCELLER)`; ② `!isOperationPending(id)` → `TimelockUnexpectedOperationState(id, bit(Waiting)\|bit(Ready))` | `delete _timestamps[id]`, which returns it to **Unset**, so the id can be re-scheduled | `Cancelled(id)` |
| `execute(target,value,payload,pred,salt)` payable (356-369) | ① `onlyRoleOrOpenRole(EXECUTOR)`; ② `_beforeCall`: `!Ready(id)` → `TimelockUnexpectedOperationState(id,bit(Ready))`; ③ `pred ≠ 0 ∧ !Done(pred)` → `TimelockUnexecutedPredecessor(pred)` | `target.call{value}(payload)` with the revert bubbled (`_execute` 410-413); then `_afterCall`: `!Ready(id)` → revert, else `_timestamps[id] = 1` (430-435) | `CallExecuted(id,0,…)`, emitted after the call and before `_afterCall` |
| `executeBatch(...)` payable (383-405) | ① `onlyRoleOrOpenRole(EXECUTOR)`; ② lengths; ③ `_beforeCall` | sequential CALLs; then `_afterCall` | one `CallExecuted` per call |
| `updateDelay(newDelay)` (447-454) | `S == address(this)` else `TimelockUnauthorizedCaller(S)` | `_minDelay = newDelay` (any value, including 0) | `MinDelayChange(old,new)` |
| `grantRole`/`revokeRole` (inherited) | `hasRole(0x00, S)`, which holds for the timelock itself and the optional admin | as in 0.1 | |
| `renounceRole` | `c == S` | | |
| `receive()` (155) | none | accepts ETH | |
| `onERC721Received` / `onERC1155*Received` | none | accept NFTs | |

### 1.5 Semantics notes

- **`execute` and value.** `msg.value` is not compared with `value`. Calls spend the timelock's balance, and
  `msg.value` is just added to it.
- **Predecessor rule.** The predecessor is checked **only at execute time**, and only as `Done`. Its scheduling
  state at schedule time is irrelevant.
- **Reentrancy.** During the external call the operation is still `Ready`. A reentrant execute of the same id
  finishes and sets it to Done, and so does a reentrant `cancel`, which sets it to Unset. Either way the outer
  `_afterCall` sees "not Ready" and the whole call reverts.
- **Self-administration.** All role changes and `updateDelay` require `S = timelock` (or the optional admin for role
  changes). That means a scheduled operation `(target = timelock, data = grantRole/revokeRole/updateDelay…)` that
  goes through Unset → Waiting → Ready → Done. A `minDelay` change applies only to **future** `schedule` calls;
  already-stored ETAs are unchanged.
- **No expiry.** A Ready operation stays executable forever.
- **msg.sender seen by targets** is the timelock, via CALL.

### 1.6 Time semantics

- Ready iff `now_ts >= scheduledAt + delay`. The comparison `t > now_ts` gives Waiting, so the operation is ready
  **at** the ETA second.
- With `minDelay = 0` and `delay = 0`, an operation is Ready in the same block it was scheduled.
- Units are always seconds (`block.timestamp`), independent of any governor clock.

### 1.7 v4.9 differences

- Separate `TIMELOCK_ADMIN_ROLE = keccak("TIMELOCK_ADMIN_ROLE")`, set as the admin of all roles (v4
  TimelockController.sol:82-85). In v5 this is `DEFAULT_ADMIN_ROLE`.
- No `OperationState` enum: `isOperationPending = t > 1` and `isOperationReady = t > 1 ∧ t <= now_ts`. These are
  semantically identical.
- `require` strings instead of custom errors.
- `_execute` swallows revert data ("underlying transaction reverted").
- `updateDelay` uses `msg.sender`.
- v4 implements the ERC721/1155 receivers directly; behaviour is the same.

### 1.8 Abstract model

A timelock is a map `id ↦ {Unset | ETA(t) | Done}` plus a role relation `R ⊆ Role × Addr`.

- PROPOSER moves `Unset → ETA(now + d)` for `d ≥ minDelay`.
- CANCELLER moves `ETA → Unset`.
- EXECUTOR, or anyone if `(EXECUTOR, 0) ∈ R`, moves `ETA(t) → Done` when `now ≥ t` and the predecessor is Done,
  atomically with performing the call list as `msg.sender = timelock`.
- Authority mutations (`R`, `minDelay`) are themselves calls whose sender must be the timelock, apart from the
  optional bypass admin. The timelock is therefore a self-governing delayed relay.

---

## 2. Governor core (`governance/Governor.sol`, last updated v5.7.0)

`abstract contract Governor is Context, ERC165, EIP712, Nonces, IGovernor, IERC721Receiver, IERC1155Receiver` (28).

### 2.1 Authority state

The layout is sequential and base-first. Extension slots follow in the concrete contract's C3 order.

| slot | variable |
|---|---|
| 0, 1 | `EIP712._nameFallback`, `_versionFallback` (strings; usually empty because ShortStrings are immutable) |
| 2 | `Nonces._nonces` (`mapping(address=>uint256)`) |
| 3 | `string _name` (48) |
| 4 | `mapping(uint256 => ProposalCore) _proposals` (50) |
| 5, 6 | `DoubleEndedQueue.Bytes32Deque _governanceCall` (56): `_begin\|_end` in slot 5, `_data` in slot 6 |

`ProposalCore` (38-45) sits at `keccak(pid . 4)`:
- word 0 = `proposer` (bytes 0-19) | `voteStart uint48` (20-25) | `voteDuration uint32` (26-29) | `executed` (30) |
  `canceled` (31);
- word 1 = `etaSeconds uint48`.

**Proposal id** (121-128, 131-138):
`pid = uint256(keccak256(abi.encode(targets, values, calldatas, keccak256(bytes(description)))))`. The chain id and
the governor address are **not** included. `getProposalId` is virtual; `GovernorSequentialProposalId` overrides it.

**ProposalState enum** (IGovernor.sol:16-25): Pending 0, Active 1, Canceled 2, Defeated 3, Succeeded 4, Queued 5,
Expired 6, Executed 7.

### 2.2 `state(pid)` (141-178), with exact check order

1. `executed` → **Executed**
2. `canceled` → **Canceled**
3. `snapshot = voteStart`; if `snapshot == 0`: revert `GovernorNonexistentProposal(pid)`
4. `c = clock()`; if `snapshot >= c` → **Pending**
5. `deadline = proposalDeadline(pid)` (base: `voteStart + voteDuration`, computed in uint48); if `deadline >= c` →
   **Active**
6. else if `!_quorumReached(pid) ∨ !_voteSucceeded(pid)` → **Defeated**
7. else if `proposalEta(pid) == 0` → **Succeeded**
8. else → **Queued**

The core never returns **Expired**. Only `GovernorTimelockCompound` does, through its grace period.

**Time windows:**
- Pending for `c ∈ [created, snapshot]`.
- Active for `c ∈ [snapshot+1, deadline]`.
- Final (Defeated, Succeeded or Queued) for `c ≥ deadline + 1`.

### 2.3 The `onlyGovernance` modifier and the `_governanceCall` queue

`_checkGovernance()` (215-224):
1. `_executor() != S` → `GovernorOnlyExecutor(S)`.
2. If `_executor() != address(this)`: let `h = keccak256(msg.data)`. Then `while (_governanceCall.popFront() != h) {}`.
   An empty queue gives `Panic(0x31)`. Entries in front of the match are **discarded**.

The queue is filled in `execute` (413-419): if `_executor() ≠ this`, then for every `i` with
`targets[i] == address(this)` it does `pushBack(keccak256(calldatas[i]))`. It is cleared after
`_executeOperations` if it is non-empty (424-426).

Consequences:
- With the executor equal to the governor (base, GovernorTimelockAccess), `onlyGovernance` ≡ `S == governor`. It is
  reachable only by the governor calling itself during `_executeOperations`.
- With an external executor (a timelock), the call must come from the executor **and** its exact calldata must have
  been whitelisted by the governor's own `execute` in the same transaction. Another timelock proposer that schedules
  `governor.setX()` directly on the timelock fails, because the queue is empty and the call panics. This protection
  has existed since v4.6.
- Order matters: calls are consumed FIFO by hash, and skipped entries are lost.

`_executor()` (671-673) is `address(this)` in the base and is overridden by the timelock extensions.

Governance-only setters in the extensions include:
- `setVotingDelay`, `setVotingPeriod`, `setProposalThreshold`;
- `updateQuorumNumerator`;
- `updateTimelock`;
- `setLateQuorumVoteExtension`;
- `setProposalGuardian`;
- `setBaseDelaySeconds`, `setAccessManagerIgnored`;
- `relay`.

### 2.4 Entry points

| entry | guard (in order) | effect | events |
|---|---|---|---|
| `propose(targets,values,calldatas,description)` (274-297) | ① `_isValidDescriptionForProposer(S, description)`, else `GovernorRestrictedProposer(S)`; ② `thr = proposalThreshold()`; **if `thr > 0`**: `getVotes(S, clock()-1) < thr` → `GovernorInsufficientProposerVotes(S, votes, thr)`; then `_propose`: ③ `len(t) ≠ len(v) ∨ len(t) ≠ len(c) ∨ len(t) == 0` → `GovernorInvalidProposalLength`; ④ `voteStart(pid) ≠ 0` → `GovernorUnexpectedProposalState(pid, state, 0)` | `proposer = S`, `voteStart = toUint48(clock() + votingDelay())`, `voteDuration = toUint32(votingPeriod())` (320-326) | `ProposalCreated(pid, S, targets, values, string[](n), calldatas, snapshot, snapshot+duration, description)` |
| `queue(t,v,c,dh)` (344-369) | ① `state == Succeeded`, else `GovernorUnexpectedProposalState`; ② `proposalNeedsQueuing(pid)`, else `GovernorProposalQueueingNotRequired` (5.7); ③ `eta = _queueOperations(...)`; `eta == 0` → `GovernorProposalQueueingFailed` | `etaSeconds = eta` | `ProposalQueued(pid, eta)` |
| `execute(t,v,c,dh)` payable (395-431) | ① `state == (needsQueuing ? Queued : Succeeded)`, else `GovernorUnexpectedProposalState` (**5.7**; ≤5.6 accepted `Succeeded ∨ Queued`) | `executed = true` **before** the calls; fill `_governanceCall`; `_executeOperations` (base: `targets[i].call{value: values[i]}(calldatas[i])`, bubbling reverts, 440-451); clear the queue | `ProposalExecuted(pid)`, after the calls |
| `cancel(t,v,c,dh)` (454-469) | ① `_validateCancel(pid, S)`, else `GovernorUnableToCancel(pid,S)`. Base (793-795): `state == Pending ∧ S == proposer`; ② `_cancel`: `state ∈ {Pending, Active, Defeated, Succeeded, Queued}`, i.e. not Canceled, Expired or Executed (485-491), else `GovernorUnexpectedProposalState` | `canceled = true` | `ProposalCanceled(pid)` |
| `castVote` / `castVoteWithReason` / `castVoteWithReasonAndParams` (514-538) | voter = `S`; `_castVote`: ① `state == Active` (640); ② `w = _getVotes(voter, proposalSnapshot(pid), params)`; ③ `_countVote` (module checks such as hasVoted and support) | tally; `_tallyUpdated(pid)` hook | `VoteCast(voter,pid,support,weight,reason)` if `params` is empty, else `VoteCastWithParams` |
| `castVoteBySig(pid,support,voter,sig)` (541-551) | `SignatureChecker.isValidSignatureNow(voter, EIP712(Ballot(pid,support,voter,_useNonce(voter))), sig)` (ECDSA or ERC-1271), else `GovernorInvalidSignature(voter)`. **The nonce is consumed during the check.** Then as `_castVote` | | |
| `castVoteWithReasonAndParamsBySig` (554-566) | ExtendedBallot(pid, support, voter, nonce, keccak(reason), keccak(params)) | | |
| `relay(target,value,data)` payable (662-665) | `onlyGovernance` | `target.call{value}(data)` from the governor, with revert bubbling | |
| `receive()` (83-87) | `_executor() == this`, else `GovernorDisabledDeposit` | | |
| `onERC721Received` / `onERC1155Received` / `onERC1155BatchReceived` (679-712) | `_executor() == this`, else `GovernorDisabledDeposit` | | |

**Proposer-suffix front-running protection** (`_isValidDescriptionForProposer`, 762-786):
- Let `L = len(description)`.
- If `L < 52`: unrestricted.
- If `bytes10(desc[L-52 .. L-42]) ≠ "#proposer="`: unrestricted.
- Otherwise `Strings.tryParseAddress(desc, L-42, L)`. This needs exactly a `"0x"` prefix (lower-case `x`) plus 40 hex
  digits of either case (Strings.sol:413-431).
  - Parse failure: unrestricted.
  - Parse success: allowed only if `recovered == proposer`.

Because the suffix is part of `descriptionHash` and so of `pid`, a front-runner who strips it creates a different
proposal.

**Value flow.** `execute` is payable. In the base, calls spend the governor's balance; `msg.value` is not matched to
`sum(values)`.

### 2.5 v4.9 differences (v4 Governor.sol)

- `ProposalCore {uint64 voteStart; address proposer; …; uint64 voteEnd; …; bool executed; bool canceled}`. The
  deadline is stored, with no duration and no `etaSeconds`.
- `queue` lives only in the timelock modules.
- `state` has no Queued branch in the core (the timelock module maps it).
- The threshold is always checked as `getVotes(proposer, clock()-1) >= proposalThreshold()` (279).
- `cancel` is proposer-only and Pending-only (355-356). There is no `_validateCancel` (added in v5.3) and no guardian
  (added in v5.4).
- `execute` emits `ProposalExecuted` **before** the calls and accepts `Succeeded ∨ Queued`. Queue fill and clear
  happen in `_beforeExecute` / `_afterExecute`.
- `castVoteBySig(pid, support, v, r, s)` has **no voter field and no nonce**; `ECDSA.recover` derives the voter.
  Replay is stopped only by `hasVoted`.
- The suffix parser looks for `"#proposer=0x"` plus 40 hex digits.
- In v4 `onlyGovernance` is a `require` string. `onERC721Received` and the other receivers accept unconditionally.

---

## 3. Governor extensions

### 3.1 GovernorVotes (`extensions/GovernorVotes.sol`, v5.7.0)

- **State:** `IERC5805 immutable _token` (17). It lives in code, not storage.
- `clock()` (34-40) is `try token.clock()`, falling back to `Time.blockNumber()` if that reverts. `CLOCK_MODE()`
  (46-52) is `try token.CLOCK_MODE()`, falling back to `ERC6372Utils.blockNumberClockMode(clock)`.
- `_getVotes(a, tp, _) = token.getPastVotes(a, tp)` (57-63). This reverts `ERC5805FutureLookup` unless
  `tp < token.clock()`.
- **Weight:** `getVotes(account, snapshot)`. During voting (Active means `snapshot < clock`) the lookup is always in
  the past. For proposing, `clock()-1` is in the past.

### 3.2 GovernorVotesQuorumFraction (v5.5.0)

- **State:** `Checkpoints.Trace208 _quorumNumeratorHistory` (18). Denominator is 100 (55-57).
- `quorum(tp) = mulDiv(token.getPastTotalSupply(tp), quorumNumerator(tp), 100)` (62-64). The numerator at `tp` comes
  from `_optimisticUpperLookupRecent` (104-112): if the latest key is `<= tp` use the latest value, otherwise
  `upperLookupRecent`.
- `updateQuorumNumerator(n)`: `onlyGovernance`. `_updateQuorumNumerator` (89-99):
  1. `n > 100` → `GovernorInvalidQuorumFraction(n, 100)`.
  2. Otherwise push `(clock(), n)`.
  3. Emit `QuorumNumeratorUpdated(old, n)`.
- **Effect:** proposals with `snapshot < updateClock` keep the old numerator, and those with
  `snapshot >= updateClock` use the new one. The constructor sets the initial value at the deploy clock.
- `_quorumReached` is evaluated lazily in `state()`, so it is `quorum(snapshot)` read **at view time**. Total supply
  at the snapshot is fixed, so the value is stable.
- v4.9: a `Trace224` history plus a deprecated `_quorumNumerator` fallback.

### 3.3 GovernorCountingSimple (v5.4.0)

- **State:** `mapping(pid => ProposalVote{against, for, abstain, mapping hasVoted})` (21-28).
- `_countVote` (70-95):
  1. `hasVoted[a]` → `GovernorAlreadyCastVote(a)`.
  2. Set `hasVoted[a] = true`.
  3. Branch on `support`: 0 → against, 1 → for, 2 → abstain. Anything else → `GovernorInvalidVoteType`, which
     reverts everything.
  4. Return `totalWeight`.
- `_quorumReached`: `quorum(snapshot) <= for + abstain` (52-56).
- `_voteSucceeded`: `for > against`, strictly (61-65).
- A zero-weight vote is allowed. It marks the account as voted and adds 0.

### 3.4 GovernorSettings (v5.4.0)

- **State:** `uint256 _proposalThreshold`; `uint48 _votingDelay`; `uint32 _votingPeriod` (13-17). The last two share
  a slot.
- Setters, all `onlyGovernance` (52-72):
  - `setVotingDelay(uint48)` emits `VotingDelaySet`;
  - `setVotingPeriod(uint32)` reverts `GovernorInvalidVotingPeriod(0)` if 0, then emits `VotingPeriodSet`;
  - `setProposalThreshold(uint256)` emits `ProposalThresholdSet`.
- They take effect for **new** proposals only, because snapshot and duration are frozen in `ProposalCore`. The
  exception is the threshold, which is read at propose time.

### 3.5 GovernorPreventLateQuorum (v5.7.0)

- **State:** `uint48 _voteExtension`; `mapping(pid => uint48) _extendedDeadlines` (19-21).
- `proposalDeadline = max(voteStart + voteDuration, _extendedDeadlines[pid])` (45-47).
- `_tallyUpdated` (58-69) runs after each vote. If `_extendedDeadlines[pid] == 0 ∧ _quorumReached(pid)`:
  - `ext = clock() + voteExtension` (uint48);
  - emit `ProposalExtended` **only if** `ext > proposalDeadline`;
  - **always** store `_extendedDeadlines[pid] = ext`.
  This happens once per proposal, at the first vote that reaches quorum.
- `setLateQuorumVoteExtension(uint48)`: `onlyGovernance`. 5.7 adds a bound: `> _maxLateQuorumVoteExtension()`
  (default `votingPeriod()`) reverts `GovernorPreventLateQuorumVoteExtensionTooLarge` (108-115).

### 3.6 GovernorProposalGuardian (v5.5.0; first appeared in v5.4.0)

- **State:** `address _proposalGuardian` (14).
- `setProposalGuardian(a)`: `onlyGovernance`; emits `ProposalGuardianSet(old, new)` (30-42).
- `_validateCancel(pid, c)` (51-58) is the disjunction of:
  - `c == guardian`;
  - `guardian == 0 ∧ c == proposer`;
  - the base rule (`Pending ∧ c == proposer`).
- Combined with `_cancel`'s state filter: the guardian can cancel in Pending, Active, Defeated, Succeeded or Queued.
  If no guardian is set, the proposer gets that same power for their own proposals.

### 3.7 GovernorTimelockControl (v5.5.0)

**State:** `TimelockController _timelock` (25); `mapping(pid => bytes32) _timelockIds` (26).

- **Constructor:** `_updateTimelock(t)`, which emits `TimelockChange(0, t)`.
- `_executor() = address(_timelock)` (139-141). `onlyGovernance` therefore needs `S == timelock` plus a queue match.
- `proposalNeedsQueuing = true` (70-72).
- **Salt:** `salt = bytes20(address(this)) ^ descriptionHash` (164-166). `bytes20` is left-aligned in the bytes32, so
  the governor address is XORed into the high 20 bytes. This avoids collisions between governors sharing a timelock.

**`_queueOperations`** (77-91):
1. `delay = timelock.getMinDelay()`.
2. `_timelockIds[pid] = timelock.hashOperationBatch(t, v, c, 0, salt)`.
3. `timelock.scheduleBatch(t, v, c, predecessor = 0, salt, delay)`. The governor needs **PROPOSER_ROLE**.
4. Return `toUint48(now_ts + delay)`, so the ETA is in seconds.

**`_executeOperations`** (97-108): `timelock.executeBatch{value: msg.value}(t, v, c, 0, salt)`, then
`delete _timelockIds[pid]`. The governor needs **EXECUTOR_ROLE**, or the role must be open. Targets see
`msg.sender = timelock`.

**`_cancel`** (117-134): `super._cancel`; then, if `_timelockIds[pid] ≠ 0`, `timelock.cancel(id)` (the governor needs
**CANCELLER_ROLE**) and delete the id.

**`state`** (43-60): if the core result is `Queued`, consult the timelock:
- `isOperationPending(id)` → Queued;
- `isOperationDone(id)` → **Executed** (executed directly on the timelock);
- otherwise → **Canceled** (cancelled on the timelock, or the timelock was swapped).

**`updateTimelock(newTL)`:** `onlyGovernance`; emits `TimelockChange` (149-156).

v4.9 differences:
- salt = `descriptionHash`, without the governor XOR;
- `queue` is defined in the module;
- `proposalEta` is read from `timelock.getTimestamp`, mapping 1 to 0;
- `state` maps `Succeeded` plus an id to Executed, Queued or Canceled;
- `_timelockIds` is not deleted on execute.

### 3.8 GovernorTimelockAccess (v5.4.0)

**State:**
- `mapping(target => mapping(bytes4 => bool)) _ignoreToggle` (59);
- `mapping(pid => ExecutionPlan{uint16 length; uint32 delay; mapping(bucket => uint32[8]) managerData})` (45-61);
- `uint32 _baseDelay` (63);
- `IAccessManager immutable _manager` (65).

**Executor.** `_executor()` is not overridden, so the **governor itself** is the executor. The governor holds the
assets and the AccessManager roles.

**`isAccessManagerIgnored(t, sel)`** is `_ignoreToggle[t][sel] != (t == this)` (121-124). By default the governor's
own functions ignore the manager, and other targets use it.

**`setAccessManagerIgnored`** is `onlyGovernance`. It reverts `GovernorLockedIgnore` if
`(t == this ∧ sel == setAccessManagerIgnored.selector)` (130-150).

**`propose` override** (180-215). For each call with `len(calldata) ≥ 4`:
- `(immediate, delay) = AuthorityUtils.canCallWithDelay(manager, governor, target, sel)`.
- If `(immediate ∨ delay > 0) ∧ !ignored`, mark it controlled; mark `withDelay = !immediate`.
- `plan.delay = max(baseDelay, delays)`.

The plan is frozen at propose time.

**`proposalNeedsQueuing = plan.delay > 0`** (175-177).

**`_queueOperations`** (223-245): `eta = Time.timestamp() + plan.delay`, in seconds regardless of the clock mode. For
each `withDelay` call, `manager.schedule(target, data, eta)` and record `nonce + 2`.

**`_executeOperations`** (250-276):
1. `now_ts < eta` → `GovernorUnmetDelay`.
2. For each call: if it is controlled, `manager.execute{value}(target, data)`. The target sees
   `msg.sender = manager`. The manager returns a nonce, and a mismatch on a delayed call reverts
   `GovernorMismatchedNonce`.
3. Otherwise a direct CALL from the governor.

**`_cancel`** (279-314): if `eta ≠ 0`, then for each delayed call whose nonce equals `manager.getNonce(opId)`, run
`try manager.cancel(this, target, data)` and ignore failures.

**`setBaseDelaySeconds(uint32)`:** `onlyGovernance`; emits `BaseDelaySet`.

### 3.9 Other v5.7 extensions present (not detailed)

GovernorCountingFractional, GovernorCountingOverridable, GovernorCrosschain, GovernorNoncesKeyed,
GovernorSequentialProposalId, GovernorStorage, GovernorSuperQuorum, GovernorTimelockCompound (the only source of
`Expired`), GovernorVotesSuperQuorumFraction.

---

## 4. Votes and ERC20Votes

### 4.1 Votes (`governance/utils/Votes.sol`, v5.7.0)

`abstract contract Votes is Context, EIP712, Nonces, IERC5805` (34).

**State:**
- `mapping(address => address) _delegatee` (40);
- `mapping(address => Trace208) _delegateCheckpoints` (42);
- `Trace208 _totalCheckpoints` (44);
- the EIP712 fallback strings and `Nonces` come first in the C3 order.

**Clock:** `clock() = Time.blockNumber()` (55-57) and `CLOCK_MODE() = blockNumberClockMode(clock)` (63-65). Both are
virtual. A timestamp token overrides both, for example
`clock() = Time.timestamp(); CLOCK_MODE() = "mode=timestamp"`. Overriding only `clock()` makes `CLOCK_MODE()` revert
`ERC6372InconsistentClock`.

**Views:**
- `_validateTimepoint(tp)`: `tp >= clock()` → `ERC5805FutureLookup(tp, clock)` (70-74). The lookup must be strictly
  in the past.
- `getVotes(a)` is the latest checkpoint.
- `getPastVotes(a, tp)` is `upperLookupRecent(tp)`, the value at the **end** of timepoint `tp` (91-93).
- `getPastTotalSupply(tp)` is the same over the total (107-109).

**Delegation transitions:**

| entry | guard | effect | events |
|---|---|---|---|
| `delegate(d)` (128-131) | none | `_delegate(S, d)` | |
| `delegateBySig(d, nonce, expiry, v, r, s)` (136-155) | ① `now_ts > expiry` → `VotesExpiredSignature`; ② `signer = ECDSA.recover(EIP712(Delegation(d, nonce, expiry)))` (reverts on malformed signatures); ③ `_useCheckedNonce(signer, nonce)` → `InvalidAccountNonce` | `_delegate(signer, d)` | |
| `_delegate(a, d)` (162-168) | internal | `old = delegatee[a]`; `delegatee[a] = d`; `_moveDelegateVotes(old, d, _getVotingUnits(a))` | `DelegateChanged(a, old, d)` |
| `_transferVotingUnits(from, to, amt)` (174-182) | internal, called by the token on mint, burn and transfer | `from == 0` adds `amt` to total; `to == 0` subtracts it; `_moveDelegateVotes(delegatee[from], delegatee[to], amt)` | |
| `_moveDelegateVotes(f, t, amt)` (187-206) | applies if `f ≠ t ∧ amt > 0` | if `f ≠ 0`, push `(clock(), latest(f) - amt)`; if `t ≠ 0`, push `(clock(), latest(t) + amt)` | `DelegateVotesChanged(f\|t, old, new)` |

Every push uses key `clock()` (225-231), so several changes in one timepoint overwrite each other. Units are
counted **only** when delegated. Delegating to `address(0)` removes the account's weight from every delegate. Votes
are not counted for undelegated holders, and a holder must self-delegate to vote.

### 4.2 ERC20Votes (`token/ERC20/extensions/ERC20Votes.sol`, v5.5.0)

- `_maxSupply() = type(uint208).max` (39-41).
- `_update(from, to, v)` (48-58): `super._update`. If `from == 0` (a mint) and `totalSupply > cap`, revert
  `ERC20ExceededSafeSupply`. Then `_transferVotingUnits(from, to, v)`.
- `_getVotingUnits(a) = balanceOf(a)` (66-68).
- `numCheckpoints` and `checkpoints(a, pos)` expose the trace.
- Layout for `contract T is ERC20, ERC20Votes`:
  - ERC20 slots 0-4 (`_balances`, `_allowances`, `_totalSupply`, `_name`, `_symbol`);
  - EIP712 slots 5-6;
  - Nonces slot 7;
  - `_delegatee` slot 8;
  - `_delegateCheckpoints` slot 9;
  - `_totalCheckpoints` slot 10.
  Composition with `ERC20Permit` reorders this, so confirm per concrete contract.

**v4.9:** a standalone `ERC20Votes is ERC20Permit, IERC5805` with `Checkpoint{uint32 fromBlock; uint224 votes}`,
`_maxSupply = uint224.max`, a block-number clock, and the "ERC20Votes: future lookup" `require` (v4 ERC20Votes.sol).

---

## 5. Proxies

### 5.1 ERC1967Utils (`proxy/ERC1967/ERC1967Utils.sol`, v5.6.0)

**Slots**, each `keccak256(label) - 1`:

| label | slot |
|---|---|
| `IMPLEMENTATION_SLOT` = "eip1967.proxy.implementation" | `0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc` (21) |
| `ADMIN_SLOT` = "eip1967.proxy.admin" | `0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103` (83) |
| `BEACON_SLOT` = "eip1967.proxy.beacon" | `0xa3f0ad74e5423aebfd80d3ef4346578335a9a72aeaee59ff6cb3582b35133d50` (121) |
| v4 only: `_ROLLBACK_SLOT` = "eip1967.proxy.rollback" | `0x4910fdfa16fed3260ed0e7147f7cc6da11a60208b5b9406d12a635614ffd9143` |

**`upgradeToAndCall(impl, data)`** (67-76):
1. `impl.code.length == 0` → `ERC1967InvalidImplementation`.
2. Set the slot.
3. Emit `Upgraded(impl)`.
4. If `len(data) > 0`, `Address.functionDelegateCall(impl, data)`, which runs in proxy storage with the original
   `msg.sender` and `msg.value`. Otherwise `msg.value > 0` → `ERC1967NonPayable`.

**`changeAdmin(a)`** (111-114): emit `AdminChanged(old, a)` **before** `_setAdmin`. `a == 0` →
`ERC1967InvalidAdmin(0)`.

**`upgradeBeaconToAndCall(b, data)`** (157-166) applies these checks in order:
1. `b.code.length == 0` → `ERC1967InvalidBeacon`.
2. Store the slot.
3. `IBeacon(b).implementation().code.length == 0` → `ERC1967InvalidImplementation`.
4. Emit `BeaconUpgraded`.
5. If `data` is non-empty, DELEGATECALL `b.implementation()`. Otherwise run the non-payable check.

These are internal library functions. Any authority comes from the caller.

### 5.2 Proxy (`proxy/Proxy.sol`)

`fallback() payable` → `_delegate(_implementation())` (66-68, 22-45). It copies the full calldata, DELEGATECALLs with
all gas, and returns or reverts with the raw returndata. There is no `receive`, so empty calldata also reaches the
fallback.

A DELEGATECALL to an address with no code succeeds with empty output.

### 5.3 ERC1967Proxy (v5.6.0)

**Constructor** (34-39), payable:
- If `!_unsafeAllowUninitialized() ∧ len(_data) == 0` → `ERC1967ProxyUninitialized`. This is **new in 5.6**: an
  empty initializer is rejected by default (59-61).
- Then `upgradeToAndCall(impl, _data)`. The init DELEGATECALL sees `msg.sender = deployer`.

**Routing:** `_implementation() = sload(IMPLEMENTATION_SLOT)` (48-50). The proxy itself has **no** upgrade function.
Upgradeability comes from the implementation (UUPS).

### 5.4 TransparentUpgradeableProxy (`proxy/transparent/TransparentUpgradeableProxy.sol`, v5.5.0)

**State:**
- `address immutable _admin` (67), in code;
- the ERC-1967 implementation slot;
- the ERC-1967 admin slot, which is informational only.

**Constructor `(_logic, initialOwner, _data)`** (79-83):
1. `ERC1967Proxy(_logic, _data)` runs **first**: it sets the implementation and the init DELEGATECALL runs with
   `msg.sender = deployer`. `_data` must be non-empty in 5.6+.
2. `_admin = address(new ProxyAdmin(initialOwner))`, a CREATE from the proxy. The address is
   `keccak(rlp(proxy, nonce = 1))`. It reverts if `initialOwner == 0` (Ownable).
3. `ERC1967Utils.changeAdmin(_admin)` emits `AdminChanged(0, _admin)` and writes the slot.

**`_fallback()` routing** (95-105):
- If `msg.sender == _admin` (the immutable value, **not** the slot):
  - `msg.sig == 0x4f1ef286` (`upgradeToAndCall(address,bytes)`): `_dispatchUpgradeToAndCall()` (114-117), which
    ABI-decodes `msg.data[4:]` as `(address, bytes)` and calls `ERC1967Utils.upgradeToAndCall`. That includes the
    msg.value check and the init DELEGATECALL with `msg.sender = ProxyAdmin`.
  - Any other selector, including empty calldata: revert `ProxyDeniedAdminAccess()`. **The admin cannot fall
    through.**
- Otherwise DELEGATECALL the implementation, even when the selector is `0x4f1ef286`. That is transparency.

**Authority.** Only the ProxyAdmin contract can upgrade. The admin can **never** change, because there is no
`changeAdmin` in v5. Writing `ADMIN_SLOT` from implementation code desynchronises the slot from the immutable, and
routing follows the immutable.

### 5.5 ProxyAdmin (`proxy/transparent/ProxyAdmin.sol`, v5.2.0)

`contract ProxyAdmin is Ownable` (13). **State:** `_owner` at slot 0.

- `UPGRADE_INTERFACE_VERSION = "5.0.0"` (22).
- `upgradeAndCall(proxy, impl, data)` payable, `onlyOwner` (38-44): `proxy.upgradeToAndCall{value: msg.value}(impl,
  data)`. This is a CALL in which the proxy sees `msg.sender = ProxyAdmin`. It works only on proxies whose immutable
  admin is this ProxyAdmin; for any other proxy the call falls through to that proxy's implementation.
- Ownership:
  - `transferOwnership` changes who can upgrade.
  - `renounceOwnership` permanently freezes every proxy administered by this ProxyAdmin.

### 5.6 UUPSUpgradeable (`proxy/utils/UUPSUpgradeable.sol`, v5.5.0)

This code lives in the **implementation**. It has no storage (`@custom:stateless`); `address immutable __self =
address(this)` (23) is in code.

- **`onlyProxy`** (`_checkProxy`, 97-104): `address(this) == __self` (not a delegatecall) **or**
  `sload_proxy(IMPLEMENTATION_SLOT) != __self` (not the active implementation) → `UUPSUnauthorizedCallContext`.
- **`notDelegated`** (110-115): `address(this) != __self` → `UUPSUnauthorizedCallContext`.
- **`proxiableUUID()`** (74-76): `notDelegated`; returns `IMPLEMENTATION_SLOT`.
- **`upgradeToAndCall(newImpl, data)`** payable, `onlyProxy` (88-91):
  1. `_checkProxy`.
  2. `_authorizeUpgrade(newImpl)`: abstract, user-defined, and expected to revert if `S` is unauthorized. Typically
     `onlyOwner`, using proxy storage and `S` equal to the original caller, because this code runs under DELEGATECALL
     from the proxy.
  3. `_upgradeToAndCallUUPS` (137-147):
     - `try IERC1822Proxiable(newImpl).proxiableUUID()`. This is an external view call, so a STATICCALL from the proxy
       to `newImpl`.
     - On success with `slot ≠ IMPLEMENTATION_SLOT`: `UUPSUnsupportedProxiableUUID(slot)`. This revert is inside the
       success branch and is not caught.
     - On success with the right slot: `ERC1967Utils.upgradeToAndCall(newImpl, data)`.
     - Any failure, including no code, a revert, or `newImpl` being a proxy whose `proxiableUUID` hits
       `notDelegated`: `ERC1967InvalidImplementation(newImpl)`.

v4.9 differences:
- `upgradeTo(address)` also exists.
- `forceCall`: `upgradeToAndCall` with empty data still delegatecalls, which hits `receive` or fallback.
- `ERC1967Upgrade._upgradeToAndCallUUPS` honours `_ROLLBACK_SLOT`: if it is set, the implementation is set without
  the UUID check.
- `onlyProxy` was added in 4.3.2, fixing the uninitialized-implementation and selfdestruct vulnerability.

### 5.7 BeaconProxy (`proxy/beacon/BeaconProxy.sol`, v5.2.0)

**State:** `address immutable _beacon` (25), plus the `BEACON_SLOT`, which is informational only.

**Constructor `(beacon, data)`** payable (39-42): `upgradeBeaconToAndCall(beacon, data)`, then `_beacon = beacon`.
An empty `data` is allowed, with no msg.value.

**Routing:** `_implementation() = IBeacon(_beacon).implementation()` (47-49). That is a STATICCALL to the beacon on
**every** call, then a DELEGATECALL.

**Authority.** The proxy exposes no administrative function at all; every selector falls through. The beacon
**cannot change** (it is immutable), and writing `BEACON_SLOT` has no effect on routing. Authority equals the
beacon's owner.

v4.9 differences: the beacon is read from `BEACON_SLOT`, and an internal `_setBeacon` lets a subclass or the
implementation change it.

### 5.8 UpgradeableBeacon (`proxy/beacon/UpgradeableBeacon.sol`, v5.0.0)

`contract UpgradeableBeacon is IBeacon, Ownable`. **State:** slot 0 is `_owner` and slot 1 is `address
_implementation` (16).

- **Constructor** `(impl, initialOwner)`: `Ownable(initialOwner)`, which reverts on 0, then `_setImplementation`.
- `implementation()` is a view.
- `upgradeTo(n)`: `onlyOwner`. Then `n.code.length == 0` → `BeaconInvalidImplementation(n)`. Then
  `_implementation = n` and emit `Upgraded(n)` (52-69).
- There is **no init call** on a beacon upgrade. A single transaction upgrades every BeaconProxy that points at the
  beacon.

### 5.9 Initializable (context for the uninitialized-implementation pitfall)

ERC-7201 slot `0xf0c5…6a00` holds `{uint64 _initialized; bool _initializing}`.

- **`initializer`** (104-132) is allowed if either:
  - `_initialized == 0 ∧ top-level call`; or
  - `_initialized == 1 ∧ address(this).code.length == 0` (during construction).
  It then sets `_initialized = 1` and emits `Initialized(1)`.
- **`reinitializer(v)`** needs `!_initializing ∧ _initialized < v`.
- **`_disableInitializers()`** sets `_initialized = uint64.max`.

---

## 6. Relay behaviour summary

| path | opcode | callee sees `msg.sender` | value source | storage context |
|---|---|---|---|---|
| Timelock `execute`/`executeBatch` → target | CALL | timelock | timelock balance (`values[i]`) | target |
| Governor (base or TimelockAccess) `_executeOperations` → target | CALL | governor | governor balance | target |
| Governor+TimelockControl `execute` → `timelock.executeBatch{value: msg.value}` → target | CALL, CALL | the timelock is called by the governor; targets see the timelock | `msg.value` is forwarded to the timelock, then the timelock balance is used | target |
| …target == governor (`onlyGovernance` fn) | CALL | timelock, so `_executor()` matches and the hash is popped from the queue | | governor |
| `Governor.relay(target, value, data)` | CALL | governor | governor balance | target |
| TimelockAccess controlled call: `manager.execute{value}(t, d)` | CALL, CALL | the manager calls the target | governor balance, via the manager | target |
| ProxyAdmin `upgradeAndCall` → proxy | CALL | ProxyAdmin, which matches the immutable `_admin` | `msg.value` forwarded | proxy |
| …proxy init `data` → newImpl | DELEGATECALL | ProxyAdmin (the msg.sender is preserved) | same msg.value | proxy |
| User → Transparent/ERC1967/Beacon proxy → implementation | DELEGATECALL | user | user msg.value | proxy |
| UUPS `upgradeToAndCall` (in proxy context) → `newImpl.proxiableUUID()` | STATICCALL | proxy | none | newImpl |
| …then the init `data` → newImpl | DELEGATECALL | original caller | msg.value | proxy |
| BeaconProxy → `beacon.implementation()` | STATICCALL | proxy | none | beacon |

---

## 7. Edge cases and pitfalls

1. **Vote checkpoints at the snapshot.**
   - Weight is `getPastVotes(voter, voteStart)`, the delegated balance at the **end** of timepoint `voteStart`.
   - Votes can only be cast for `clock ∈ (voteStart, deadline]`, so the snapshot is always strictly in the past and
     immutable.
   - Transfers or delegation changes after the snapshot do not change any weight. Moving tokens to a fresh account
     after voting gives that account zero snapshot weight, so double voting is impossible.
   - Undelegated tokens count in `getPastTotalSupply` (the quorum denominator) but in nobody's votes.
2. **Flash-loan resistance.**
   - Both the proposal threshold (`clock()-1`) and vote weight (snapshot `< clock`) read past checkpoints.
   - A flash loan that opens and closes within one transaction leaves the end-of-timepoint value unchanged.
   - With `votingDelay = 0`, the snapshot is the proposal's own timepoint. Capital held across the end of that block
     (or second) counts, which is not a flash loan but is a same-block acquisition. A non-zero delay is recommended.
   - Timestamp-mode tokens key checkpoints by second. Several blocks cannot share a second post-merge, but L2s may
     have this.
3. **Delegate changes.** Delegation moves the *current* balance. Re-delegating in the same timepoint overwrites the
   checkpoint (same key). Delegating to 0 burns the account's voting weight until it re-delegates.
4. **Clock mode mismatch.**
   - The Governor clock is taken from the token. `votingDelay`, `votingPeriod` and the late-quorum extension are in
     the clock's units (blocks or seconds).
   - Timelock delays, `etaSeconds` and the TimelockAccess `baseDelay` are **always seconds**.
   - A token that overrides `clock()` but not `CLOCK_MODE()` makes `CLOCK_MODE()` revert.
5. **Timelock admin left set.** The constructor's optional `admin` holds `DEFAULT_ADMIN_ROLE` with no delay. It can
   grant itself PROPOSER and EXECUTOR and bypass governance, and it must be renounced. (In v4 it was
   `TIMELOCK_ADMIN_ROLE`, and very old versions auto-granted it to the deployer.)
6. **Proposer = canceller.** The constructor gives each proposer both roles. Any extra timelock proposer can:
   - schedule arbitrary self-calls (`grantRole`, `updateDelay`, …) without a vote;
   - cancel governor-queued operations, a DoS that the governor reports as `Canceled`.
   The governor itself needs PROPOSER, CANCELLER and EXECUTOR (or an open executor).
7. **Open executor role.** With `hasRole(EXECUTOR, 0)`, anyone can call `timelock.executeBatch` with the governor's
   salt once the operation is Ready. The governor's `state()` then reports Executed, while the core `executed` flag
   stays false.
   - If such a batch calls governor `onlyGovernance` functions, it panics (queue empty), so those proposals can only
     execute through `Governor.execute`.
   - Execution on the timelock is otherwise permitted.
8. **`updateTimelock` with queued proposals.** Stored `_timelockIds` refer to the old timelock. The new timelock
   reports them Unset, so `state` gives **Canceled**, and the old operations remain executable on the old timelock by
   its executors.
9. **`execute` state strictness (5.7).** Proposals that need queueing must be `Queued`, and those that do not must
   be `Succeeded`. In ≤5.6 `Succeeded ∨ Queued` was accepted; with TimelockControl that path then failed inside the
   timelock.
10. **Governor holds no assets under TimelockControl.**
    - ETH and NFT deposits revert (`GovernorDisabledDeposit`).
    - Tokens pushed via plain `transfer` are recoverable only with `relay` (a governance call).
    - Under the base governor or TimelockAccess, the governor itself is the treasury.
11. **Proposal id is not chain- or governor-bound.** The same description on two governors gives the same `pid`. The
    salt in TimelockControl XORs in the governor address to avoid timelock id collisions. Re-proposing an identical
    proposal requires a new description.
12. **Cancel scope.**
    - Base: only the proposer, only while Pending.
    - Guardian: any non-final state.
    - With no guardian set, ProposalGuardian lets the proposer cancel through Queued.
    - With TimelockControl, cancelling a Queued proposal also cancels the timelock operation (the governor needs
      CANCELLER).
13. **Late quorum.** At most one extension per proposal, triggered by the first vote that reaches quorum. The extended
    deadline is stored even when it is not later (so it cannot trigger again). The extension keeps the proposal
    Active past its original deadline, so opponents can still vote.
14. **Signature votes.**
    - v5 nonces are per voter and consumed only on successful validation, because a failure reverts everything.
    - ERC-1271 wallets are supported.
    - v4 had no nonce, and `hasVoted` was the only replay guard.
15. **Transparent proxy.**
    - The admin is immutable, a ProxyAdmin created in the constructor.
    - The ProxyAdmin **owner** (an EOA) interacts with the dapp normally, because it is not the admin. The ProxyAdmin
      contract cannot use the dapp through the proxy.
    - Renouncing ProxyAdmin ownership freezes the proxy.
    - Adding external functions to a subclass risks selector clashes with `0x4f1ef286`.
    - In v4 the admin was mutable (`changeAdmin`) and could be an EOA that could then never use the dapp; the
      `ifAdmin` modifier exposed `admin()`, `implementation()`, `upgradeTo` and `changeAdmin`.
16. **UUPS upgrade to a non-UUPS implementation.**
    - The `proxiableUUID` check rejects implementations without it.
    - An implementation that has it but drops `upgradeToAndCall`, or makes `_authorizeUpgrade` unsatisfiable
      (renounced owner), **bricks** upgradeability permanently.
    - A storage-layout mismatch corrupts state.
    - UUPS functions are also reachable through a Transparent proxy by non-admins, so `_authorizeUpgrade` is the only
      guard.
17. **Uninitialized implementation or proxy.**
    - Anyone can call `initialize` on the bare implementation contract, which is why `_disableInitializers()` belongs
      in the implementation constructor. In v5, `onlyProxy` prevents upgrading the bare implementation. The pre-4.3.2
      attack initialized the implementation, upgraded it and selfdestructed it via delegatecall, bricking every proxy.
    - A proxy deployed with empty `_data` can have its initializer front-run. v5.6+ `ERC1967Proxy` rejects empty data
      by default.
    - Post-Cancun `SELFDESTRUCT` no longer removes code except in the creation transaction, but DELEGATECALL to a
      code-less implementation would silently succeed.
18. **Beacon.**
    - One owner key controls every BeaconProxy.
    - There is no init call on `upgradeTo`, and the beacon is immutable per proxy (v5).
    - Each call performs an extra STATICCALL, and a reverting `implementation()` bricks all proxies.
19. **The governance queue discards unmatched entries.** If a proposal's calls to the governor are reordered through
    the executor, for example by a custom timelock that executes out of order, earlier whitelisted hashes are popped
    and lost, and later calls fail.
20. **Threshold 0 shortcut (5.x).** When `proposalThreshold() == 0`, `getVotes` is not called at all, so propose works
    even if the token's `getPastVotes` would revert. In v4 it was always called.

---

## 8. Abstract actor models (one paragraph each)

**TimelockController.**
- Actors are addresses holding roles in a relation `R`; `address(0)` in EXECUTOR means "everyone".
- The state is `minDelay` plus a total map `ops: Id → Unset | Pending(eta) | Done`, where Pending splits into
  Waiting and Ready by `eta > now`.
- PROPOSER does `schedule(id = H(calls, pred, salt), d)` with `d ≥ minDelay`, giving `Pending(now + d)`.
- CANCELLER does `Pending → Unset`.
- EXECUTOR does `Pending(eta) → Done` iff `now ≥ eta ∧ (pred = 0 ∨ ops(pred) = Done)`, atomically with performing
  `calls` as principal *timelock*. The call is reverted if `ops(id)` changed during them.
- Mutations of `R` need `(ADMIN, S) ∈ R`, and ADMIN is held by the timelock itself and an optional bootstrap admin.
  Mutations of `minDelay` need `S = timelock`. So after the bootstrap admin renounces, every authority change is a
  delayed self-call.

**Governor (with GovernorVotes, QuorumFraction, CountingSimple, Settings, and optionally TimelockControl).**
- Actors are token holders with delegated weight `w(a, t) = getPastVotes(a, t)`.
- Any actor with `w(a, clock-1) ≥ threshold` (when the threshold is greater than 0), and matching any
  `#proposer=` suffix, creates a proposal `pid = H(calls, H(desc))` with `snapshot = clock + votingDelay` and
  `deadline = snapshot + votingPeriod` (possibly extended once by late quorum).
- During `(snapshot, deadline]` each account votes once with weight `w(a, snapshot)`.
- After the deadline the outcome is Succeeded iff `for > against ∧ for + abstain ≥ ⌊supply(snapshot) ·
  num(snapshot) / 100⌋`.
- A succeeded proposal is queued (with a timelock: scheduled under salt `gov ⊕ H(desc)`, `eta = now + minDelay`) and
  then executed by anyone. The calls are performed by the *executor* principal: the governor itself, or the timelock.
- The proposer may cancel while Pending, and the guardian at any non-final state.
- Governance parameters are guarded by `onlyGovernance`: `S = executor`, plus, if the executor is external, a
  one-shot whitelist of `H(msg.data)` populated by the governor's own `execute` in the same transaction. The
  governor's authority is thus exactly "a successful vote, relayed through the executor".

**Votes/ERC20Votes.**
- Each holder chooses a delegate.
- Each delegate's weight is a checkpointed function of time equal to the sum of the delegators' balances, and the
  total supply is checkpointed alongside.
- All reads are restricted to strictly-past timepoints, which makes them immutable facts.

**Proxies.**
- A proxy is a principal whose code is `impl(state)`, where `impl` is read from:
  - `IMPLEMENTATION_SLOT` (ERC1967, Transparent, UUPS); or
  - `beacon.implementation()` (Beacon).
- Every non-admin call executes `impl` in the proxy's storage with the caller's identity.
- Authority to change `impl`:
  - **Transparent:** exactly one immutable principal, a ProxyAdmin whose Ownable owner is the human or governance
    actor. It is the only one allowed to invoke `upgradeToAndCall`, and it is denied everything else.
  - **UUPS:** whatever predicate the *current* implementation's `_authorizeUpgrade` encodes, with the new
    implementation required to self-certify via `proxiableUUID` as a directly called (non-proxied) UUPS contract.
  - **Beacon:** the beacon's Ownable owner, atomically for all proxies.
- Every upgrade is a code-change effect that also replaces the guard functions themselves. It may carry an
  initialization DELEGATECALL running as the upgrader's caller context.

---

## 9. Minimal abstract primitives

1. **Principals and call context.** An `Addr` type, plus a call frame `⟨self, sender, value, data⟩`. Two call kinds:
   - **CALL**: a new frame `self := target`, `sender := caller.self`, value transferred.
   - **DELEGATECALL**: frame `self` and `sender` preserved, code taken from the target, storage of `self`.
   STATICCALL is CALL with no state change. A failing frame reverts atomically, including all nested effects.
2. **Role relation with admin hierarchy.**
   - `R ⊆ Role × Addr` and `adminOf: Role → Role` (default `0x00`).
   - Grant and revoke are guarded by `(adminOf r, sender) ∈ R`; renounce is self-only.
   - An *open role* predicate: `(r, 0) ∈ R ⇒ ∀a. authorized(r, a)`.
3. **Single-owner authority.** `owner: Addr` (0 means renounced or frozen); `onlyOwner` means `sender = owner`; a
   transfer is guarded and has a non-zero target.
4. **Self-call authority.** The guard `sender = self`, possibly with the executor as an indirection
   (`sender = executor(self)`), so authority changes are only reachable as effects of the contract's own relayed
   operations.
5. **Timelocked operation.** A content-addressed id `H(calls, pred, salt)` and a state machine
   `Unset → Pending(eta) → Done` (`Pending → Unset` on cancel), with readiness `now ≥ eta`, a predecessor
   precondition `pred = 0 ∨ Done(pred)`, `eta ≥ now + minDelay` at creation, no expiry, and execution atomic with a
   call batch and re-checked after it.
6. **Relay or batch execution.** Perform the list `[(target, value, data)]` as principal P with CALL, bubbling the
   first revert. Variants: through an intermediary principal (timelock or AccessManager), and the generic
   `relay(target, value, data)` guarded by `onlyGovernance`.
7. **Proposal lifecycle state machine.**
   - The state is derived from the stored `{proposer, snapshot, duration, eta, executed, canceled}`, the clock and the
     tally.
   - Order of precedence: Executed > Canceled > (nonexistent: revert) > Pending (`snapshot ≥ clock`) > Active
     (`deadline ≥ clock`) > Defeated/Succeeded (`quorum ∧ succeeded`) > Queued (`eta ≠ 0`), plus an external-oracle
     refinement from the timelock operation state.
   - Transitions: propose, queue, execute and cancel, each with an allowed-state bitmap.
8. **Checkpointed history (time-indexed map).** `Trace: (key: uint48 ↦ value)`, push-only with non-decreasing keys
   and same-key overwrite. A lookup `v(t)` gives the last value with `key ≤ t`. A *strictly-past* read guard is
   `t < clock`.
9. **Delegated weighted authority.** `delegate: Addr → Addr`, `units: Addr → ℕ`,
   `w(d, t) = Σ_{a: delegate_t(a) = d} units_t(a)` (realised as a checkpoint trace), and `supply(t)`. Authority
   predicates:
   - **threshold:** `w(proposer, clock-1) ≥ θ`;
   - **one-shot vote:** `w(voter, snapshot)` per (proposal, voter);
   - **quorum:** `Σ(for, abstain) ≥ ⌊supply(snapshot) · num(snapshot) / den⌋`, with `for > against`.
10. **Abstract clock.** ERC-6372: `clock ∈ {block.number, block.timestamp}` (uint48) together with a separate
    wall-clock `now = block.timestamp` for timelock ETAs. Exact comparisons are `≥` and `>` as listed in the sections
    above.
11. **One-shot call whitelist (authorization token).** A FIFO multiset of `H(calldata)` that the governor's `execute`
    fills and that is consumed (pop-until-match, panic when empty) by guarded entry points. It is cleared at the end
    of the transaction scope.
12. **Content-addressed identity with bound salt.** `pid = H(calls, H(desc))`, a timelock salt `gov ⊕ H(desc)`, and a
    signature or nonce-bound ballot (EIP-712 with a per-account monotone nonce).
13. **Proposer binding predicate.** A description suffix `#proposer=0x<40hex>` restricts `propose` to that address.
14. **Code-indirection (upgrade) effect.** A mutable pointer `impl` (a storage slot, or the beacon's state) that
    decides which code, *including the guard functions*, runs for every future call. An upgrade has three parts:
    - the authority predicate (immutable admin, current code's `_authorizeUpgrade`, or beacon owner);
    - well-formedness (`code(new) ≠ ∅`; for UUPS, `new.proxiableUUID() = IMPLEMENTATION_SLOT` evaluated
      non-delegated);
    - an optional init DELEGATECALL, together with a non-payable rule when there is no init.
15. **Routing by caller identity (transparency).** A dispatch predicate on `sender = admin` that selects an
    admin-only interface (exactly one selector, everything else reverts) and otherwise the delegated
    implementation.
16. **Immutables versus storage.** A distinction between authority fixed in code (TUP `_admin`, BeaconProxy `_beacon`,
    UUPS `__self`, GovernorVotes `_token`, TimelockAccess `_manager`) and authority in storage that implementation
    code may overwrite, with the resulting desynchronisation (the ERC-1967 admin and beacon slots become
    informational).
17. **Initialization latch.** `initialized: uint64` with `initializing: bool`: a one-time (or versioned) privileged
    entry point that anyone may call first, and a disable operation (`max`).
