# Actor models on bytecode: relays

`QEDefi.Actor` (see [access-control.md](access-control.md)) proves who can cause an effect in a
model of a system of contracts. `Guards.lift` moves such a theorem to bytecode for one contract,
through `System.Refinement`. A system with **relays** (a ProxyAdmin calling its proxy, a Safe
executing a transaction, a timelock executing an operation) needs one more fact: each relay's
frames issue calls only as its model rules say. This document describes that fact, proved in
`EvmLogic/Program/Nested/Relay.lean` (core and Std only), its instances, and how it connects to
`QEDefi.Actor.Derives`.

## 1. The frame condition

**Setting.** `Rl : Address → Prop` is the set of relays, `C r` is the code of relay `r`, and
`Iss r : Machine → Message → Prop` is its **issuance predicate**. `Iss r m c` says that the
frame executing at machine `m` (before the instruction runs) may request the child message `c`.
`Requests m c` says that the instruction at `m` requests `c` (`CALL`, `CALLCODE`, `DELEGATECALL`,
`STATICCALL`, or a creation). It is defined from `exec`, so it holds exactly when the
instruction requests that child.

**Which frames are covered.** `Danger Rl f` (from `Run.lean`) means a non-static frame at a
relay. This covers every frame that runs *as* `r`: `r`'s own code, and also code that `r`
delegatecalls into (that code acts with `r`'s authority, so its calls count as `r`'s). Static
frames are not covered: they can only issue static calls, and static calls change nothing.

**Per-relay obligation** (`RelayInv Rl C Iss r J`): `J` is an invariant of `r`'s non-static
frames, with four fields:

| Field | Statement |
|---|---|
| `start` | `RelayStart Rl C Iss r m → J m` |
| `issue` | `J m → RelayCode Rl C m.world → Requests m c → Iss r m c` |
| `next` | `J m →` the instruction at `m` continues with `m'` `→ J m'` |
| `resume` | `J m →` the instruction at `m` requests a child `→ ∀ M res, M.frame = m'.frame → M.parents = m.parents → M.ctx = m.ctx → M.precompiles = m.precompiles → J (resume M res)` |

`resume` holds **whatever the child did** (`M` and `res` are arbitrary): reentrancy, changed
storage, any return data. The only thing assumed about other contracts is the EVM itself.
These are the obligations of `EvmLogic.AbsInt.exit_frame_ind`, and the abstract
interpreter's `InCert` already discharges `next` and `resume` (`inCert_within`,
`inCert_resume`).

`RelayStart Rl C Iss r m` is what an invariant may assume when a frame starts:

- it is a fresh call frame at `r`, and it is non-static;
- `entry`: it runs `C r` with `codeAddress = some r`, **or** it was requested by a non-static
  frame at `r` itself (a `DELEGATECALL`, a `CALLCODE` or a call to itself), with `Requests mp
  msg ∧ Iss r mp msg` for the requesting machine `mp`. So an `Iss r` that pins the code that
  `r` delegatecalls into (for example "`DELEGATECALL` only to library `L`") gives the child
  frame's invariant its code;
- relays hold their code (`RelayCode`), and the precompiles are the standard ones.

**Theorem** (`processMessageCall_issues`):

```lean
theorem processMessageCall_issues (hC : RelayCodeOk Rl C)
    (hJ : ∀ r, Rl r → RelayInv Rl C Iss r (J r)) (hw : RelayCode Rl C w)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hmsg : TopOk Rl w msg)
    (hm : Reaches ctx w tr msg m) (hd : Danger Rl m.frame) (hc : Requests m c) :
    Iss m.frame.msg.currentTarget m c
```

In words: start from a world where every relay `r` holds `C r`, which is not empty and is not
an EIP-7702 designator (`RelayCodeOk`). Take a top-level message whose sender is not a relay and
which runs a relay's own code when it calls one (`TopOk`, as for `processMessageCall_good`).
Then every message requested by a non-static frame at a relay, at any depth of the call, satisfies
that relay's `Iss`. `processMessageCall_issues_call` restates this for non-static calls requested
by *any* frame at a relay: only non-static frames can request non-static calls.

**Proof.** A forward simulation with the invariant `RelayTxInv`, preserved by `step`
(`relayTxInv_step`):

- relays keep their code, in the current world and in every rollback snapshot. No instruction
  changes code (`exec_code`), and no creation frame targets a relay, since the target of a
  creation has no code (`CreateOk.code`);
- the executing frame, if it is a non-static relay frame, satisfies its `J`;
- every suspended non-static relay frame satisfies `J` when it resumes after any child
  (`Suspended`). This is recorded when the child is pushed, from `resume`.

When a child frame is pushed at relay `r`, it satisfies `RelayStart`. Either the parent runs at
`r` (then the parent is a covered frame and `issue` gives `Iss r`), or `CallOk.nonstatic` makes
it a `CALL` that runs `r`'s code. The proof needs no frame summary and no termination, unlike
`processMessageCall_good`. Only the standard axioms are used; `scripts/check-trust.sh` passes.

**What `Iss` should read.** The frame's message (`m.frame.msg`: caller, calldata, value), its
entry world (`m.frame.snapshot.1`), the stack and memory at the call, and the current world.
Because `J` must survive any child, a fact checked before an external call (an owner read from
storage) holds after it only if `J` records it about frame-constant data. This matches what the
contract actually guarantees: a check made before a reentrant call is stale after it.

## 2. Guarded relays: protected state, and principals that do not act

`EvmLogic/Program/Nested/Guard.lean` extends the same step-local simulation with two things a
theorem about protected state needs:

- a **world invariant** `G` (it may depend only on the relays' storage) held by the current world
  and every rollback snapshot of every machine. Frames that are not at a relay cannot change it
  (the frame condition); each relay's invariant must show that the relay's own instructions keep
  it (`GuardInv.good`);
- **idle principals** `X`: accounts with no code and a nonzero nonce (`IdleW`), for example an
  owner EOA that has sent at least one transaction. The simulation keeps "no frame is sent by an
  idle account" (`GuardTxInv.callers`): a frame at an idle account runs no code, so it requests
  nothing, and no creation lands on an account with a nonzero nonce (`execCreate_ids`). Nonces
  never decrease (`exec_nonce`, `Idle.lean`).

`GuardStart`, what a relay's invariant may assume when its frame starts, adds to `RelayStart`:
`G` held, the sender is not idle, and `origin`. The origin is either the top-level frame (whose
sender is no relay) or a request by a non-static machine `mp`, under that relay's `Iss` if `mp`
runs at a relay, with the sender being `mp`'s account or (for `DELEGATECALL`) `mp`'s sender
(`exec_ids`).

Two refinements serve relays whose safety depends on cryptography (§5):

- **The context.** `GuardStartK K`, `GuardInvK K` and `GuardTxInvK K` carry a predicate `K` on
  the transaction's context (`ctx : K m.ctx`, kept by every step since no step changes it), so a
  frame invariant may use hypotheses about `ctx.crypto` or the chain id; the top-level theorems
  take `hK : K ctx`. `GuardStart`, `GuardInv` and `GuardTxInv` are the case `K = True` (and
  `hK` is then discharged automatically).
- **Precompile results.** `GuardInv.resume` holds for any `M res` as before, but may assume
  that a precompile answered as `launchCall` makes it answer (`resume M res = launchCall m' req`
  when the request is a precompile's). So a frame invariant may know `ecrecover`'s output.

**Theorems.** `processMessageCall_guard` (the final world satisfies `G`) and
`processMessageCall_guard_issues` (every relay request satisfies `Iss`), under
`RelayCodeOk`, `G` local to the relays, `G` and `IdleW` initially, no EIP-7702 authorizations
(or a fork before Prague), and `GuardTop` (the `TopOk` of `Run.lean`, an active sender, no code
when calling an idle account).

## 3. Path-sensitive frame invariants (`EvmLogic/AbsInt/Guard/`)

A relay's invariant has to know which branch an access check takes. `EvmLogic.AbsInt` explores
both branches of every `JUMPI`, so it cannot see that `onlyOwner` reverts for a non-owner.
The guarded analyzer adds:

- **atoms**, address values fixed for the frame: the sender (`CALLER`) and the address held in a
  pinned storage slot (`SLOAD` of a listed constant key). Immutables are `sym k` as before.
- **distinctness**: pairs of atoms or immutables known to denote different addresses. Then `EQ`
  of the two is `0`, `SUB` is `nz` (nonzero), and `ISZERO` folds.
- **`JUMPI` pruning**: a known condition gives one successor, so code behind a decided guard is
  never explored.
- **checks**: allowed call targets (abstractly), allowed `SSTORE` keys, no creations.

Soundness (`gsucc_next`, `gcertify_sound`) holds for machines satisfying the configuration's
facts (`EnvOk`). In a guarded relay those facts come from `G` (pinned slots) and from the frame's
identity (the sender, and how it differs from the owner or admin). `Guard/Frame.lean` turns a
certificate into the relay obligations: `ginCert_init`, `ginCert_next`, `ginCert_resume`,
`ginCert_call`, `ginCert_no_create`, `ginCert_sstore`. `Storage.lean` adds `exec_slot`: no
instruction but `SSTORE` writes the storage of an account holding code.

## 4. The upgrade guard on bytecode (`qedefi/Verified/OpenZeppelin/Proxy/`)

The OpenZeppelin v5.7.0 contracts built by `scripts/build-contracts.sh` (`OzTransparentProxy`
with its admin immutable, `OzProxyAdmin`, and the implementation `ActorImpl`):

- `Certify.lean`: kernel certificates of the guarded analyzer.
  - ProxyAdmin when the sender is not the owner: nothing requested, nothing written.
  - The proxy when the sender is not its admin: only the `DELEGATECALL` to the implementation
    slot's address, nothing written.
  - `ActorImpl`: writes slot `0` only.
- `Proxy/Guard.lean`: the instance of `processMessageCall_guard`.
  - **Relays:** the proxy, ProxyAdmin and the implementation.
  - **World invariant `G`:** the implementation slot holds `ia`, and ProxyAdmin's slot `0` holds
    the owner `o`.
  - **Idle principals:** `X = {o}`.
  - **Frame invariants:** read off the certificates. A ProxyAdmin frame's sender is not idle,
    hence not the owner. A proxy frame's sender is not ProxyAdmin: by `origin`, it was requested
    by the top-level sender, by a non-ProxyAdmin frame, or by the proxy itself under its `Iss`,
    which runs the implementation's code, not the proxy's.

**`Dep.impl_kept`:**

> From a world where the three contracts are deployed, the implementation slot holds `ia`, and
> ProxyAdmin is owned by an EOA `o` that has sent a transaction: every top-level message call
> whose sender is neither `o` nor one of the contracts leaves the implementation slot and the
> owner unchanged.

This covers any calldata, any value, calls at any depth, reentrancy, and reverts. Only the
standard axioms are used.

In the terms of `QEDefi.Actor`, this is Ownable's `no_act` with `T = {sender}`, now a fact about
every reachable EVM machine. `Proxy/GuardTrace.lean` lifts it to traces: along every sequence of
transactions not sent by the owner, interleaved with environment steps that leave the deployment
alone (a transaction's nonce increment and fee payment among them), the implementation and the
owner never change (`Dep.trace_impl_kept`), and the owner's first transaction starts from the
original ones (`Dep.trace_impl_until_owner`).

**Limits.**

- The owner is an EOA. §5 replaces it with a threshold multisig, a further relay.
- The implementation is part of the trusted code. Its certificate says it never writes the
  implementation slot. An implementation that could would itself be an upgrade path.

## 5. A Safe owner: threshold signatures on bytecode

`qedefi/Verified/Safe/MiniSafe/Guard.lean` makes the ProxyAdmin's owner a threshold
multisig, `MiniSafe` (`contracts/src/MiniSafe.sol`, 1,303 bytes): owners, a threshold and a nonce
in storage, and `execTransaction(to, value, data, signatures)` that calls `to` once `threshold`
owners signed the transaction digest, checked as Safe 1.5.0's `checkNSignatures` does for ECDSA
signatures (65-byte `r ‖ s ‖ v`, signers recovered by `ecrecover`, strictly increasing, each an
owner). The digest is `keccak256(abi.encode(chainid, this, to, value, keccak256(data), nonce))`.

MiniSafe leaves out what makes Safe 1.5.0 harder (§6): `simulateAndRevert`, the fallback
handler, modules, guards, and EIP-1271 and `approveHash` signatures.

**Frames that end safely (`EvmLogic/Program/Nested/Own.lean`).** The Safe's frame invariant must
know that the final `CALL` of `execTransaction` is unreachable when fewer than `threshold` owners
sign. `Own S C m` says: every path of the frame from `m`, by its own instructions, ends the frame;
every instruction satisfies `S` (here: an `SSTORE` writes slot `1`, the nonce); every requested
call is answered by a precompile and satisfies `C` (here: it targets `1`, `ecrecover`); nothing
is created. It is inductive and universal over the outcomes of `exec`, so exceptional halts (out
of gas, bad jumps) need no argument and it holds for any gas. It is kept by `next` and by a
precompile's resumption, so `J := Own S C` is a relay invariant. Rules per instruction shape
(`Own.binOp`, `Own.mload`, `Own.staticcallPre`, …) work on a tracked state `Fr` (pc, stack,
memory, world of an otherwise unknown machine); the tactic `own_explore [pcs] using [lemmas]`
(`EvmLogic/Tactic/OwnStep.lean`) runs them over literal code, splits every `JUMPI` (the
condition is `hc<pc>`), closes decided branches and stops at the given pcs.

**The Safe's frames (`MiniSafeLoop.lean`, `MiniSafeFrame.lean`).**

- `loop`: the signature loop (pc `604`). With `cnt (O ∩ T) x` the owners among the signers `T`
  up to address `x`, the invariant `i ≤ cnt (O ∩ T) last` holds: each iteration recovers `cur`
  with `ecrecover` (the precompile's output, through the memory `returnMemory` writes), requires
  `cur > last` and `isOwner[cur]`, so `cur` is an owner, hence a signer (`Signers`), and
  `cnt (O ∩ T) cur > cnt (O ∩ T) last`. Since `cnt ≤ |O ∩ T| < threshold`, the exit test
  `i < threshold` never fails: every path reverts. The proof is induction on
  `|O ∩ T| - cnt last`, one symbolic iteration per step.
- `hashFn`: the digest function returns a MiniSafe digest (`Digest`: `keccak256` of 192 bytes
  starting with the chain id and the Safe's address), with the free memory pointer at `0x160`.
- `frame`: from the start of any MiniSafe frame (any calldata, value and gas), `Own S C`. The
  dispatcher, the view functions and the decoders are explored to the end; `execTransaction`
  reaches the loop after `hashFn` and the nonce increment.

**Hypotheses** (`FrameCtx`, and in `Dep.impl_kept`):

| Hypothesis | Meaning |
|---|---|
| `Signers crypto chainId ms O T` | every owner `ecrecover` recovers from a digest of this Safe on this chain is in `T` (style of `SigUnforgeable`) |
| `(O ∩ T).card < thr` | fewer than `thr` owners sign |
| `w.sload ms 0 = thr`, `isOwner[a] ≠ 0 → a ∈ O` | the Safe's configuration (kept by `G`) |
| `ownerSlot crypto a ≠ 1` | no owner slot is the nonce slot (keccak avoids `1`) |
| from Prague: address `1` has no code, a nonzero nonce, and does not send | `1` never holds a delegation designator, so `ecrecover` is the precompile (a designator there would let any code answer `ecrecover`) |

**`Verified.Safe.MiniSafe.Guard.Dep.impl_kept`:**

> From a world where the proxy, its ProxyAdmin, the implementation and the Safe are deployed,
> the implementation slot holds `ia`, ProxyAdmin is owned by the Safe, and the Safe has threshold
> `thr` and owners `O`: every top-level message call (before Prague or without EIP-7702
> authorizations) whose signers `T` include fewer than `thr` owners leaves the implementation, the
> owner of ProxyAdmin, and the Safe's threshold and owners unchanged.

Relays: the proxy, ProxyAdmin, the implementation and the Safe. `Iss`: the proxy runs only the
implementation's code; the Safe calls only `1`. A ProxyAdmin frame's sender is not the Safe (by
`origin`: the Safe calls only `1`, and ProxyAdmin is not `1`), so the certificate of §4 applies.
The context predicate is `K c := c = ctx`, so the Safe's frames may use the hypotheses about
`ctx.crypto`. `MiniSafe.Guard.Example` instantiates every hypothesis (three owners, threshold `2`, one
signer, a stand-in `Crypto`). Only the standard axioms are used.

In the terms of `QEDefi.Actor.Lib.Safe` (`Examples.Actor.SafeProxyAdminLib`): `Closes.outsider`
with fewer than `thr` owners among the keys and no module (MiniSafe has none), on bytecode.

**Limits.** The signature hypothesis is about digests of 192 bytes starting with the chain id and the Safe; the theorem says nothing about
transactions that do reach `thr` signatures (the converse, that `thr` owners can upgrade, is
`upgrade_by_owners` in the model only).

## 6. Safe 1.5.0 on bytecode (`qedefi/Verified/Safe/Bytecode/`)

`qedefi/Verified/Safe/Bytecode/` replaces MiniSafe by the real Safe: `SafeProxy` and the
v1.5.0 singleton (`SafeSingleton`), compiled byte for byte from `safe-global/safe-smart-account`
tag `v1.5.0` with its pinned settings (`contracts/README.md`). The deployment `Dep` has five
relays: the OZ transparent proxy `px`, its ProxyAdmin `pa`, the implementation `ia`, the Safe
`sf` (a `SafeProxy`) and the singleton `sg`.

**Doomed frames (`EvmLogic/Program/Nested/Sandbox.lean`).** `simulateAndRevert` `DELEGATECALL`s
caller-chosen code from a Safe frame, then always reverts. The step-local simulation of
`Guard.lean` cannot follow that code, so `Sandbox.lean` adds *doomed* frames: a frame (and every
frame below it) whose parent is known to revert after it returns. Inside them anything may
happen; `G` is only required again at the parent's revert, which rolls the world back.
`GuardInvD` extends `GuardInvK` with the obligations `doom` (a request the judgment marks as
doomed: the parent's continuation is `Doomed`) and `doomCreate`; `GuardInvK.toD` lifts the old
certificates, and `processMessageCall_guardD` is the transaction theorem. The statements of
`Guard.lean` and `Relay.lean` are unchanged.

**Frame judgments with loops (`EvmLogic/Program/Nested/OwnG.lean`).** `Own` is inductive, which
needs a termination argument for every loop. Safe's loops include `getStorageAt`, whose
unchecked `length * 32` can wrap memory, so `OwnG` is coinductive: `OwnB` explores a bounded
piece of a frame (ending in `leaf`s), and `OwnG.coind` closes a loop by an invariant `L` whose
states step back into `L`. `OwnG` adds the run predicate `R` (what holds of every machine of
the transaction, e.g. `G` and idle accounts: `sloadR`, `extcodesizeR` hand it to the proof) and
the doomed-call obligation. `own_explore` (`Tactic/OwnStep.lean`) handles both judgments.

**The singleton's frames (`Singleton/*.lean`).** Every entry point of the dispatcher (33
functions plus `receive` and `fallback`) is explored on the bytecode (`sg_frame`):

| Function(s) | Why it keeps `G` |
|---|---|
| views, `getStorageAt`, `getOwners`, `getModulesPaginated`, `checkSignatures`, `checkNSignatures` | no `SSTORE`; requests are static (`ecrecover`, `isValidSignature`); loops by coinduction (`Lists.lean`, `SigView.lean`, `CopyLoop.lean`) |
| `addOwnerWithThreshold`, `removeOwner`, `swapOwner`, `changeThreshold`, `enableModule`, `disableModule`, `setGuard`, `setModuleGuard`, `setFallbackHandler`, `setup` | `authorized`: the sender must be the Safe itself, which is not the sender of any frame (`SgCtx.caller`); `setup` reverts once the threshold is set |
| `approveHash` | writes `approvedHashes[msg.sender][h]`, a `Kw` key; the sender is active (not an owner outside `T`) |
| `execTransactionFromModule(ReturnData)` | the sender must be an enabled module; only the sentinel is |
| `simulateAndRevert` | the `DELEGATECALL` is doomed (`Dsim`): the frame reverts after it |
| `fallback` | calls the handler `h₀`, which is unset or not a relay |
| `execTransaction` | the nonce write (`Kw`); `getTransactionHash` returns a digest of this Safe (`Digest.lean`); the signature loop never exits (`SigTx*.lean`) |

**The signature loop of `execTransaction` (`SigTx.lean`, `SigTxEcdsa.lean`, `SigTxContract.lean`,
`SigTxLoop.lean`).** The invariant `TxL` at the loop head (pc `6820`): the counter `i` is at most
`cnt (O ∩ T) lastOwner`, the free memory pointer `p` grows by at most 256 bytes per pass, and
the signatures' length word is kept. Each pass that comes back to the head counted an owner of
`T` strictly above `lastOwner`:
- `v = 0`, a contract signature: the copy into the `isValidSignature` calldata is bounded by the
  signatures' length (`contract_bounds`, `copy_17648`); `EXTCODESIZE` of the owner is nonzero
  (else the call reverts), and idle owners have no code, so the owner is in `T`;
- `v = 1`, an approved hash: by `msg.sender` (active, `executor_T`) or recorded before
  (`SafeOk.approvals`: no owner outside `T` approved a digest of this Safe, `approval_T`);
- `v > 30`, `eth_sign`, and otherwise plain ECDSA: `ecrecover` on the (wrapped) digest, then
  `Signers` (`tx_ethSign`, `tx_ecdsa`).
So `i ≤ |O ∩ T| < thr`, and the exit `i ≥ thr` is never taken: every path reverts before the
call.

**Hypotheses of `Verified.Safe.Guard.Dep.impl_kept`:**

| Hypothesis | Meaning |
|---|---|
| codes of `px pa ia sf sg`; `himpl`, `howner` | the deployment: the proxy points at `ia`, ProxyAdmin is owned by the Safe |
| `SafeOk` (kept by `G`) | singleton `sg` in slot `0`; threshold `thr`; owners within `O`; only the sentinel module; no guard, no module guard; fallback handler `h₀`; no approval by an owner outside `T` of a digest of this Safe |
| `hh : h₀ = 0 ∨ ¬ Rl h₀` | the fallback handler is unset or not one of the five relays (e.g. the CompatibilityFallbackHandler) |
| `hthr`, `hcard : (O ∩ T).card < thr` | fewer than `thr` owners sign |
| `Signers` | every owner `ecrecover` recovers from a digest of this Safe on this chain, plain or `eth_sign`-wrapped, is in `T` |
| `hidle`, `hcaller`, `hcode` | owners outside `T` are EOAs with a nonzero nonce, are not the sender, and run no code; from Prague on, likewise address `1` |
| `hdeleg`, `htop` | before Prague or no EIP-7702 authorizations; the top-level frame is not a relay frame with the wrong code |
| `hR : Rw` (run-level, hashing) | during the transaction, every `SSTORE` the singleton's code performs at the Safe to the nonce (slot `5`) or to an approval key (`approvedHashes[a][h]`) misses every key `G` protects |

**Hashing.** No injectivity or disjointness of keccak is assumed. Where the proof needs that two
keccak-derived slots differ, it takes a run-level hypothesis about this transaction only, or a
fact of the initial state kept by `G`:
- `Rw` (above): the approval slots (and the nonce slot) the Safe writes during the transaction
  lie outside the protected slots. A collision of an approval slot with a protected slot
  (threshold, an owner, module, guard or handler slot) would let `approveHash` change the
  configuration; `Rw` excludes exactly that.
- Owners read as nonzero are in `O`: not a separate hypothesis but derived. `SafeOk.owners`
  (every nonzero `owners[a]` has `a ∈ O`) is part of `G`, holds initially, and is kept at every
  step because, by `Rw`, the only Safe writes that happen (nonce, approvals) miss the owner
  slots. The signature loop reads `owners[cur]` at a machine of the run, where `G` holds
  (`owner_mem`).
- Approvals read as nonzero: `SafeOk.approvals` (no owner outside `T` has approved a digest of
  this Safe) is likewise part of `G`, an initial-state hypothesis kept by `Rw`.

These three are exactly where a keccak collision would break the guard: an owner or approval
slot colliding with another protected slot, or an approval written over one.

**What `impl_kept` says.** From a world with the deployment above (proxy at `ia`, ProxyAdmin
owned by the Safe, the Safe configured as `SafeOk`), every top-level message call (before
Prague or without EIP-7702 authorizations) whose signers `T` include fewer than `thr` owners
ends with the same implementation, the same ProxyAdmin owner and the same Safe configuration.
Only the standard axioms are used.

**How it is checked.** `own_explore`/`sg_explore` run the bytecode symbolically. The
`ecrecover` continuations are tactic scripts (`tx_ecdsa_close`, `tx_ethSign_close`) run on the
explored states rather than lemmas: restating those states (kilobytes of memory terms) as
hypotheses makes `exact` unify terms that differ in instance arguments (`Word` against
`BitVec 256`), which is slow. `tx_contract` instead states its stack and memory as variables.

**Limits.** The fallback handler is assumed unset or not a relay (CompatibilityFallbackHandler
qualifies), and modules, guard and module guard unset; the theorem says nothing about Safes with
modules. Owners outside `T` are EOAs. Contract owners in `T` may be anything (their
`isValidSignature` call is static). As in §5, the converse (that `thr` owners can upgrade) is
proved only in the model.

## 7. Connecting to `QEDefi.Actor.Derives`

Open. The vocabulary `call/delegate/sign/act` matches frames, so the goal is to prove, on
bytecode, that every capability a transaction *exercises* is derivable in the model from the
transaction's keys; `Guards`-style theorems then hold on the concrete system. The route:

1. **Observed actions.** In `qedefi/QEDefi/Actor/Bytecode.lean` (Mathlib side), define the
   actions of a reached frame from its message and its parent:
   - a `CALL`/`STATICCALL` frame gives `(caller, call t (dec data))` with `t = currentTarget`;
   - a `DELEGATECALL` frame requested by a frame at `b` gives `(b, delegate codeAddress (dec data))`;
   - a frame that gets past its access check gives `(t, act (dec data))`.

   Here `dec : ByteArray → Option M` decodes ABI calldata into the model's messages; undecodable
   calldata maps to an opaque message that no rule mentions.
2. **Relay predicates from rules.** For a relay `r` with model rules `relay r out` and
   `endpoint r may`, take `Iss r mp c := ∃ m, dec mp.frame.msg.data = some m ∧ may s
   mp.frame.msg.caller m ∧ out s m (act_of c)`, where `act_of c` is `call`/`delegate` by the
   kind of `c` and `s = abs mp.frame.snapshot.1`. Then each request is a two-step derivation,
   `(caller, call r m) ⟹ (r, act m)` (endpoint) `⟹ (r, act_of c)` (relay). `quorum` relays
   (Safe thresholds) put the signature condition in `may`, with signers recovered by `ecrecover`
   from calldata, as `consent` does today.
3. **Induction along the frame stack** (`derives_of_reaches`): every observed `(b, call t m)`
   satisfies `Derives R s₀ T (b, call t m)` with `T = {sender} ∪ {non-relay accounts}`. Any
   unmodelled contract is a key, which is the conservative choice: a derivation that reaches
   `Q` must then pass through the relays' rules. The top-level frame is the sender (a key). A
   child of a non-relay frame comes from a key. A child of a relay frame comes from step 2,
   using the derivation for the parent frame's own message. This needs a small EvmLogic lemma,
   `Reaches.frame_origin`: every frame on the stack was pushed by its parent's `Requests`, or
   is the top-level frame.
4. **The state of the rules.** `Iss` reads the configuration at the frame's entry world, which
   is not the transaction's initial world when an earlier frame of the same transaction changed
   the configuration (a Safe running `addOwner` and then a call). Handle this with `close chg R`:
   maintain, across the transaction, that the configuration at every snapshot is reachable from
   `cfg s₀` by changes derivable from `T`. Then a derivation at an intermediate configuration is
   a derivation in `close chg R` at `s₀`. That invariant is a `Good` predicate for
   `processMessageCall_good`, since only protected frames write the configuration.
5. **Guards on the system.** With the effect contract (the proxy) verified per call as today
   (`OpRefinesAt`: "`upgradeTo` changes the slot only when `caller = admin`"), a change of the
   protected state in a transaction gives an observed `(proxy, act (upgradeTo x))`. Step 3 makes
   it derivable from `T`. This is the bytecode form of `Guards.derives_of_not_keep`, for
   multi-contract systems.

A good order: the `EvmLogic` lemma `Reaches.frame_origin`; steps 1–3 on a toy two-contract
system (an `Ownable` relay calling a guarded counter); the configuration invariant (step 4); then
`SafeProxyAdmin`, whose ProxyAdmin is a `relay` and whose Safe is a `quorum`.

## 8. Limits

- Before Prague, or without EIP-7702 authorizations (the same condition as
  `processMessageCall_good`). Relays must not hold designators.
- Relay code is fixed for the whole transaction (`RelayCode`). Upgradeable relays (a Safe
  proxy) are modelled by taking the proxy as the relay and its `DELEGATECALL` to the singleton
  as an issued message whose `Iss` pins the singleton's code.
- `J` must hold after an arbitrary child, so a relay whose safety depends on a reentrancy guard
  needs the guard's storage in `J` together with the fact that only `r`'s own frames can change
  it. That fact comes from the `Danger` simulation, not from this module.
