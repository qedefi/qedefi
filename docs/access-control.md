# Access control: the actor model (`QEDefi.Actor`)

Who can cause an effect, through roles, contracts that hold roles, thresholds, stored approvals,
configuration changes and delays, stated so that it is checked rather than assumed. The library
is EVM-independent (`qedefi/QEDefi/Actor/`), works on the model level like the rest of `QEDefi`,
and transfers to bytecode through `QEDefi.Trace.Lift`. Three worked examples are in
`qedefi/Examples/Actor/`, reusable components in `qedefi/QEDefi/Actor/Lib/` (§6); the bytecode
results are in [actor-bytecode.md](actor-bytecode.md).

## 1. What it gives you

For a model `step : S → O → Option S`, the operations' **consenters** (`consent op`: sender,
signers) and **authority rules** `R`:

| Statement | Lean | Reads |
|---|---|---|
| Until a controller acts | `Guards.exec_keep` | along any operation sequence by keys `T`, if `T` derives no capability in `Q` initially, the protected state is kept |
| Who did it | `Guards.derives_of_not_keep` | if the protected state changed, the trace's consenters could derive a capability in `Q` |
| Trust policy | `Exercises.invariant` | an invariant holds when every step able to exercise `Q` follows a policy `π` (e.g. "the admin only upgrades to audited code") |
| Notice | `Delayed.notice` | a timelocked effect at time `τ` was scheduled at `t` with `t + delay ≤ τ`, the delay being the one in force then, or was pending at the start |
| On bytecode | `Guards.lift`, `ExecAll.lift_invariant` | the same along any concrete trace, for any `System.Refinement` |

The first form needs no trust hypothesis at all: it says exactly whose action can break the
property. This is the form for "only the admin can change the implementation, and that is
acceptable": the theorem names the admin's controllers, and nothing else can do it.

## 2. The model

**Capabilities.** `(a, p)`: principal `a` can be made to perform action `p`. The standard
vocabulary (`Action`) mirrors EVM frames:

- `call t m`: `a` sends `m` to `t` (`msg.sender = a` at `t`);
- `delegate t m`: `a` delegatecalls `t`, so `t`'s code runs with `a`'s storage and authority;
- `sign h`: `a` approves digest `h`, by a signature or a stored approval;
- `act m`: `a` runs `m` past its access check, i.e. performs its effect.

A message that acts on behalf of an account other than the sender (ERC-2771, EVC, ERC-4337)
carries that account in `m`.

**Rules and keys.** `Rules S A P`: in state `s`, `R s q X` says capability `q` follows from all
of `X`. `Derives R s T q` is the least set containing every action of the keys `T` and closed
under the rules (`Derive.lean`). Thresholds, weighted quorums and "any of these holders" are
rules whose premise is a set. Stored consent and open functions are rules with an empty premise.
Non-derivability is proved by exhibiting a closed set (`Derives.le_of_closed`).

**Configurations and escalation.** Authority reads a configuration `cfg s` (owners, role
tables, pointers to role managers, thresholds, modules, approved hashes, scheduled operations).
Changing it is an action: `chg e c c'`. `close chg R` (`Config.lean`) adds every escalation rule
mechanically: `q` follows from `Y` plus changes `es` when some path of changes `es` leads to a
configuration where `R` gives `q ← Y`. Whoever can make a ProxyAdmin transfer its ownership can
upgrade; whoever can grant a role holds it; whoever can repoint an oracle holds every role it
answers for. None of these rules is written by hand, so none can be forgotten.

**The two obligations** a model discharges (`Trace.lean`):

- `Stable`: a step can add authority only through its own consenters. With `close` this is
  `stable_of_cfg`: each step either keeps the configuration or performs changes its consenters
  could derive. In practice this follows from one soundness lemma per model ("every successful
  call is authorised"), proved by induction on messages (`run_sound` in the examples).
- `Guards Q Keep`: a step whose consenters derive nothing in `Q` keeps `Keep`, a preorder:
  "unchanged" (`Same f`), or a quantitative relation such as "decreases by at most the
  allowance".

**Soundness: rules cannot under-approximate.** If a model's rules miss a path to authority (an
escalation, an open initialiser, a relay, a stored approval), `Stable` or `Guards` fails to be
provable. For example, a Safe rule set without a rule for executing an approved hash that
transfers ProxyAdmin ownership fails `Stable`, and the gap is real: anyone can execute such a
hash, and the new owner can then upgrade. Rules may *over*-approximate
(ignore delays, ignore which digest a signature is for): the theorems stay sound, only less
precise.

**What `consent` means.** Senders are top-level transaction senders (EIP-3607 makes them keys).
Signers are the addresses that `ecrecover` returns for signatures the operation carries. A
signer counts as having acted, which is accurate when only the key holder produces its
signatures (`SigUnforgeable`, `Examples/Solmate/ERC20/Permit.lean`). A replayed signature counts
as its signer acting, so a theorem's `T` must include every key whose signatures appear.

## 3. Modelling a system: the recipe

1. **Messages** `M`: the functions involved, as an inductive (relayed calls nest: `exec t m`).
2. **Configuration** `Cfg`: every piece of state that any access check reads.
3. **Semantics** `run`: one call, recursive through relays, with `none` for reverts. Pass along
   the identity each callee sees (`msg.sender`, or the context account).
4. **Base rules** `Base : Cfg → A × Act → Set (A × Act) → Prop`, one constructor per check:
   `endpoint`, `relay`, `quorum` and `facts` are the four shapes (`Action.lean`). Use an
   inductive, as the examples do.
5. **Changes** `Chg`: one constructor per configuration-changing function, labelled with the
   capability that performs it (`(t, act m)`, or `(b, call t m)` when the change records `b`'s
   own consent, as `approveHash` and `renounceRole` do).
6. **`run_sound`**: each successful call either keeps the configuration and makes only effects
   derivable from its caller's capability, or makes one derivable change. `stable` and `guards`
   then take ten lines each.
7. **Who can**: the closed set `D` of what the keys `T` can do, and an invariant `Inv` of the
   configurations they can reach (`close_le_of_closed`). One case per rule.
8. **Not vacuous**: show that the intended controllers can do it, by an execution
   (`upgrade_by_owners`) or a derivation (`owner_can_pause`).
9. **Bytecode**: per-call refinement as for ERC-4626 (`OpRefinesAt`), then `Guards.lift`.

## 4. Worked examples (`qedefi/Examples/Actor/`)

| File | System | Headline |
|---|---|---|
| `SafeProxyAdmin.lean` | OZ v5 transparent proxy ← `ProxyAdmin` (`Ownable`) ← Safe (owners, threshold, modules, `approveHash`, self-administration, sender-as-signer) | `impl_kept`: whatever keys `T` do, the implementation is unchanged when fewer than `thr` owners are in `T` or hold an approved hash and no module acts; `upgrade_by_owners`: `thr` owners do upgrade |
| `RoleOracle.lean` | target with `onlyRole` answered by a replaceable role manager (OZ `AccessControl`, admin hierarchy), `Ownable2Step` owner, renounce | `paused_kept`: holders of no role on `PAUSER`'s admin chain, neither owner nor pending owner, cannot change the flag; `owner_can_pause`: the owner holds `PAUSER`, derived through `setAcm` |
| `Timelock.lean` | OZ `TimelockController` (content-addressed ids, proposers, executors, cancellers, `updateDelay` through the timelock) | `value_notice`: every change was scheduled at least `minDelay` (as of scheduling) before it ran, or was pending at the start |

All three are model-level. Only the three standard axioms are used (`propext`,
`Classical.choice`, `Quot.sound`), and `scripts/check-trust.sh` passes.

## 5. Catalogue: each system in the model

The semantics are those of the upstream sources at the versions named. "Rules" lists base rules, "Changes" configuration changes, "Facts" empty-premise rules, and "Delayed" the
uses of `Delayed`.

| System | Rules | Changes / Facts / Delayed | Sharp edges the model must keep |
|---|---|---|---|
| Ownable, ERC-173, Solmate `Owned`, Solady `Ownable` | `(t, act m) ← {(owner, call t m)}` | `transferOwnership`, `renounce` (owner := none) | renounce is irreversible; Solady's renounce sentinel under `_guardInitializeOwner` |
| `Ownable2Step`, Chainlink `ConfirmedOwner` | the above + `accept ← {(pending, call)}` | `transfer` sets pending; `accept` (by the pending owner) | pending owner is a controller; v5 `renounce` clears pending |
| Solady ownership handover | `complete ← {(owner, call)}` with a request fact | request (by the requester), complete; Delayed for the 48 h expiry window | valid iff `now ≤ request + 172800` |
| OZ `AccessControl` (+`Enumerable`) | `(t, act m) ← {(b, call)}` for holders of `role(m)`; `grant/revoke r ← {(b, call)}` for holders of `adminOf r` | grant, revoke, renounce (by the holder: `(b, call)` change) | `DEFAULT_ADMIN_ROLE` administers itself; enumeration is only needed to report, not to prove |
| `AccessControlDefaultAdminRules` | the above; begin/accept transfer | Delayed: acceptance strictly after `schedule` (`<`), never expires | delay 0 still needs a later block |
| OZ `AccessManager` + `AccessManaged` | `(t, act m) ← {(b, call t m)}` for active members of `role(t, selector)`; manager admin functions by `ADMIN_ROLE`/role admins | grant (with grant delay), `setTargetFunctionRole`, `setTargetClosed`, `setAuthority`; schedule as a fact; Delayed for execution delays (`Time.Delay` deferred updates) | membership active iff `since ≤ now`; ops executable in `[τ, τ+1 week)`; guardian cancels only (negative authority); 5.7.0 closes the `execute(setAuthority)` bypass of the target admin delay; `AccessManaged(0)` bricks |
| Solmate `Auth` + `RolesAuthority`/`MultiRolesAuthority` | `(t, act m) ← {(b, call)}` when `authority.canCall(b, t, sig)` (authority state in the configuration) or `b = owner` | `setAuthority` (owner or authority-approved), capability and role changes | `canCall` runs before the owner check: a reverting authority blocks the owner on `requiresAuth` but not on `setAuthority`; a malicious authority can approve `transferOwnership` |
| Solady `OwnableRoles` | holders of any role in the mask | grant/revoke by owner; Delayed for `TimedRoles` | `onlyRoles` gives the owner no pass |
| DSAuth / DSGuard / DSRoles | self, then owner, then `authority.canCall`; DSGuard ACL on `(src, dst, sig)` with wildcards; DSRoles root users and public capabilities | ACL and role edits | self-calls are always authorised; DSAuth's order differs from Solmate's |
| Maker `wards` (`rely`/`deny`), `can` (`hope`) | `(t, act m) ← {(w, call)}` for wards; per-user operator rule | rely/deny by any ward (flat, self-administered); hope by the user | any ward adds or removes anyone, itself included; `cage` freezes |
| DSPause + DSChief | `exec` by anyone for a plotted plan (fact); `plot` by the authority (the chief's hat) | plot, drop; Delayed (`eta ≥ now + delay`, no expiry); relay through the pause proxy by `delegatecall` | the chief has no snapshot: lock → vote → lift → free fits in one transaction (a flash election), so a weighted rule over *current* balances fails `Stable` unless lenders are modelled as relays |
| Compound Timelock + GovernorBravo | queue/execute by the admin (the governor) | queue, cancel; Delayed with grace window `[eta, eta + 14 d]`; votes as a weighted quorum at the proposal's snapshot | propose threshold strict `>`, cancel `<`; `Expired` one second stricter in Bravo than in the Timelock |
| OZ `Governor` + `TimelockController` | proposal success as a quorum over delegated votes at the snapshot; timelock roles as `AccessControl` | schedule, cancel; Delayed (`minDelay`, changed only by the timelock itself); open executor via `address(0)` = anyone | votes are read strictly in the past; 5.7.0 `execute` requires exactly Queued; the governor needs proposer, executor and canceller roles |
| Comptroller pause guardian, `Pausable` | pause by the guardian, unpause by the admin only | flag changes | negative authority: `Guards` with `Keep` = "flags only set to true" |
| Safe 1.3 to 1.5 | quorum of `sign h` over the owners; sender-as-signer; `execTransactionFromModule ← {(module, call)}`; self-calls for administration | owners, threshold, modules, guard; approved hashes (`(o, call)` changes); delegatecall operations as an over-approximation (`(sf, act any) ← {(sf, delegate …)}`) | modules bypass signatures, and before 1.5 the guard; 1.5 adds the module guard (a veto, never authority); ERC-1271 owners are relays; the domain binds chainId, address and nonce |
| Zodiac Roles v2 | `(sf, call t m) ← {(member, call roles (execWithRole t m))}` for clearances and conditions matching `m`; budgets as quantitative `Keep` | role, scope and allowance edits by the owner | the June 2026 exploit (Roles < 2.1.1, Delay < 1.1.1): an ERC-1271 check that ignored the staticcall success flag accepted revert data as a signature, so a contract signer is a relay whose answer must be modelled, not trusted |
| Zodiac Delay | executes the queue head after the cooldown (anyone) | Delayed (`txCooldown`, optional expiry); owner vetoes a queue prefix | cooldown changes apply to queued transactions; a failing head blocks the queue |
| Hats Protocol | wearer ∧ active ∧ eligible: a rule whose premise includes the toggle and eligibility modules' answers (in the configuration) | mint, transfer, renounce; status pushed by modules; admin tree by id | view paths silently fall back to the stored status when the module call fails, and a caller may force that with gas |
| Aragon ACL (Lido) | `(app, act role) ← {(entity, call)}` with parameter predicates, `ANY_ENTITY` | permission grants by the permission manager; burn | under `ANY_ENTITY`, parameters see `ANY_ENTITY` and not the caller; arguments are compared on 240 bits |
| Aave v3 `ACLManager` + `PoolAddressesProvider` | role rules (`AccessControl`) queried by the pool | the provider owner swaps the ACL manager and every implementation (a change granting everything) | the ACL admin is fixed at construction; the provider owner is the root |
| Transparent proxy (OZ v5) | `upgrade ← {(admin, call)}`, admin immutable (a `ProxyAdmin`) | implementation change (the protected effect) | the admin cannot reach the implementation; v5 has no `changeAdmin` |
| UUPS | `upgrade ← _authorizeUpgrade` of the *current* implementation | implementation change replaces the rules: state theorems "until upgrade" or "for implementations satisfying a spec" | upgrading to a non-UUPS implementation bricks upgrades |
| Beacon | `upgrade ← {(beacon owner, call)}` for every proxy at once | beacon implementation change | one key, many proxies |
| Initializers | `initialize ← ∅` while uninitialised (anyone) | the initialised flag | open initialisers make *everyone* a controller; the model surfaces this |
| ERC-2771 forwarder | `(t, act (m on behalf of a)) ← {(fwd, call t (m ‖ a))}`, `(fwd, call …) ← {(a, sign req)}` | nonces | OZ authenticates through `_msgSender()` everywhere, so a trusted forwarder acts as anyone it can sign for; Multicall with delegatecall had a spoofing bug, fixed in 4.9.4 / 5.0.1 |
| EIP-2612 `permit`, Permit2 | `(token, act spend) ← {(owner, sign permit)}` with nonce and deadline | allowances (quantitative), nonces, the unordered nonce bitmap | Permit2 picks ECDSA or ERC-1271 by `code.length`; `approve` and `lockdown` do not bump the nonce, so an outstanding permit stays valid |
| ERC-4337, ERC-7579 accounts | `(acct, call t m) ← {(owner, sign userOp)}` through the EntryPoint; executors as relays | module installation by the account itself | v0.7 and v0.8 differ on `validAfter` and on the hash; MSAAdvanced selects the validator from the nonce |
| EIP-7702 | a delegated EOA is a key *and* a relay: both its key rule and its code's rules | delegation designator changes (by the key) | `tx.origin == msg.sender` no longer means "no code" |
| Euler EVC | `(vault, act (m on behalf of a)) ← {(evc, call vault …)}`, `(evc, call …) ← {(owner or operator of a, call evc …)}` | operators, lockdown, permit nonces | a contract calling itself through the EVC may pass any `onBehalfOf` |
| Replaceable role oracle (`AccessControlled`; seen in Strata) | `onlyRole ← {(b, call)}` for holders at `cfg.acm` | `setAcm` by the owner (escalation derived), two-step ownership | the owner holds every role the oracle answers for (`owner_can_pause`); roles shared across targets |

**Not modelled as authority** (outside this model): a reverting or gas-starved oracle denies
service but grants nothing. Off-chain identity (whether five signers are five people), custody,
and cross-chain message endpoints enter as hypotheses about who acts, or as assumed relay rules.

## 6. Components and the bytecode bridge

**Components** (`qedefi/QEDefi/Actor/Lib/`): `Ownable`, `Ownable2Step`, `AccessControl`, `Safe`
and `Timelock` (TimelockController). Each provides its configuration fragment, `Base`/`Chg`
constructors parameterised by the contract address and an embedding into the host system's
messages (`Sys`), its `run_sound`, and a "who can" lemma (`no_act`, `no_call`), together with
the converse (`owner_can`, `admin_can`, `owners_can`). `Examples/Actor/SafeProxyAdminLib.lean`
re-derives the Safe example from the components with the same headline statement.

**On bytecode** ([actor-bytecode.md](actor-bytecode.md)). `EvmLogic/Program/Nested/Relay.lean`
and `Guard.lean` prove, for any transaction, that every call a relay issues satisfies its
issuance predicate and that a world invariant over the relays' storage survives when some
principals do not act; `EvmLogic/AbsInt/Guard/` decides which branch an access check takes. The
instances:

| Theorem | System | Statement |
|---|---|---|
| `Examples.Actor.ProxyGuard.Dep.impl_kept` | OZ v5.7.0 transparent proxy and `ProxyAdmin`, owned by an EOA | no transaction not sent by the owner changes the implementation slot or ProxyAdmin's owner (any calldata, depth, reentrancy); `Dep.trace_impl_kept` (`ProxyGuardTrace.lean`) along any sequence of transactions. Ownable's `no_act` with `T = {sender}` |
| `Examples.Actor.SafeGuard.Dep.impl_kept` | the same, owned by `MiniSafe` (ECDSA threshold multisig) | no transaction signed by fewer than `threshold` owners changes the implementation, the owner, or the Safe's owners and threshold. `Safe`'s `Closes.outsider` |
| `Examples.Safe.Guard.Dep.impl_kept` | the same, owned by Safe v1.5.0 (mainnet bytecode) | as above, for the Safe's whole configuration, every entry point and all four signature kinds |
