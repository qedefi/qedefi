# Safe smart account and Zodiac Roles / Delay: actor and authority model, from source

## 0. Sources (read-only clones)

All paths below are relative to `SCRATCH=`.

| Clone | Repo | Ref | Commit |
|---|---|---|---|
| `src-safe150` | safe-global/safe-smart-account | tag `v1.5.0` | `dc437e8fba8b4805d76bcbd1c668c9fd3d1e83be` |
| `src-safe141` | safe-global/safe-smart-account | tag `v1.4.1` | `bf943f80fec5ac647159d26161446ac5d716a294` |
| `src-safe130` | safe-global/safe-smart-account | tag `v1.3.0` | `186a21a74b327f17fc41217a927dea7064f74604` |
| `src-roles-v2` | gnosisguild/zodiac-modifier-roles (worktree) | `05f2ca83` (2024-08-21; last contract change before the 2025 refactor; package `2.1.0`) | `05f2ca83` |
| `src-roles` | same repo, HEAD (now v3, BUSL) | `main` | `59bfd9b6c21d799e53b3b99c1338bf5483d4a2f6` |
| `src-delay` | gnosisguild/zodiac-modifier-delay | tag `v1.1.0` (read via `git show v1.1.0:…`) | `515737f67bb704d0ce14d45cd6f7cc8e6b4655d1` |
| `src-zodiac341` | gnosisguild/zodiac (Module/Modifier base) | tag `v3.4.1` | `0312a26fd0c3138da996fb84c50106e798137d04` |
| `src-zcore400` | gnosisguild/zodiac-core | tag `v4.0.0` (contains the ERC-1271 fix) | — |
| `src-ozu500` | OpenZeppelin/openzeppelin-contracts-upgradeable | tag `v5.0.0` | — |

Why these Zodiac refs:
- The Roles v2.1.0 mastercopy is `0x9646fDAD06d3e24444381f44362a3B0eB343D337` (`packages/evm/mastercopies.json` @ `69c8c167`). That commit was built against `@gnosis.pm/zodiac` 3.4.1 (`package.json` @ `a19c0ebd`, 2023-11-29).
- The contract changes between `a19c0ebd` and `05f2ca83` are only an import-path switch to zodiac-core. The 2025 commits (`557b17d5…69c8c167`) rewrote the decoder and are not what was deployed as 2.1.0.
- Delay v1.1.0 is likewise built on `@gnosis.pm/zodiac` 3.4.1 (`git show v1.1.0:package.json`).

The PermissionBuilder/Checker/Loader file names you asked about exist only in v2. HEAD is a v3 rewrite (`core/…`).

Constants checked with a local Keccak-256 (`scratchpad/tools/keccak.py`); every value matched the source:
- `keccak("guard_manager.guard.address") = 0x4a204f62…3c34c8`
- `keccak("fallback_manager.handler.address") = 0x6c9a6c4a…9918d5`
- `keccak("module_manager.module_guard.address") = 0xb104e0b9…289947`
- `EIP712Domain(uint256 chainId,address verifyingContract) = 0x47e79534…469218`
- `SafeTx(...) = 0xbb8310d4…1286d8`
- `SafeMessage(bytes message) = 0x60b3cbf8…50fbca`
- `ModuleTx(bytes data,bytes32 salt) = 0x2939aeed…6d91d4`
- `masterCopy() = 0xa619486e`
- `isValidSignature(bytes32,bytes) = 0x1626ba7e`
- `isValidSignature(bytes,bytes) = 0x20c13b0b`

Unless a version is named, file paths in sections 1–7 are under `src-safe150/contracts/`.

---

## 1. Safe v1.5.0

### 1.1 Authority state (storage layout)

The inheritance order is `Safe is Singleton, NativeCurrencyPaymentFallback, ModuleManager, GuardManager, OwnerManager, SignatureDecoder, SecuredTokenTransfer, ISignatureValidatorConstants, FallbackManager, StorageAccessible, ISafe` (`Safe.sol:37-49`). Only these contribute sequential slots:

| Slot | Variable | Declared at |
|---|---|---|
| 0 | `address singleton` | `common/Singleton.sol:12` (must equal `SafeProxy.singleton`, `proxies/SafeProxy.sol:21`) |
| 1 | `mapping(address=>address) modules` (linked list; `SENTINEL_MODULES = 0x1`) | `base/ModuleManager.sol:62,67` |
| 2 | `mapping(address=>address) owners` (linked list; `SENTINEL_OWNERS = 0x1`) | `base/OwnerManager.sol:17,19` |
| 3 | `uint256 ownerCount` | `base/OwnerManager.sol:20` |
| 4 | `uint256 threshold` | `base/OwnerManager.sol:21` |
| 5 | `uint256 nonce` | `Safe.sol:64` |
| 6 | `bytes32 _deprecatedDomainSeparator` (unused since 1.3.0) | `Safe.sol:65` |
| 7 | `mapping(bytes32=>uint256) signedMessages` | `Safe.sol:67` |
| 8 | `mapping(address=>mapping(bytes32=>uint256)) approvedHashes` | `Safe.sol:69` |
| `0x4a204f62…3c34c8` | transaction guard address | `base/GuardManager.sol:66` |
| `0x6c9a6c4a…9918d5` | fallback handler address | `base/FallbackManager.sol:13` (also `handler/HandlerContext.sol:18`) |
| `0xb104e0b9…289947` | module guard address (**new in 1.5.0**) | `base/ModuleManager.sol:65` |

The same layout is mirrored in `libraries/SafeStorage.sol:9-24`, which delegatecall libraries use.

Derived predicates:
- `isOwner(o) ≡ o ≠ 0x1 ∧ owners[o] ≠ 0` (`OwnerManager.sol:127-129`).
- `isModuleEnabled(m) ≡ m ≠ 0x1 ∧ modules[m] ≠ 0` (`ModuleManager.sol:196-198`).
- "Initialised" means `threshold > 0`. The singleton's constructor sets `threshold = 1` (`Safe.sol:72-79`), so `setup` on the singleton is impossible (GS200).
- Well-formed list invariant: `owners[0x1]` starts a chain that returns to `0x1` and has exactly `ownerCount` elements, with `1 ≤ threshold ≤ ownerCount`. Only `authorized` functions maintain this; a DelegateCall can break it.

### 1.2 Guarded entry points (check order and revert codes)

Reverts use `revertWithError(bytes5)`, which ABI-encodes `Error(string)` with a 5-byte reason (`libraries/ErrorMessage.sol:16-28`). In 1.3.0 and 1.4.1 the same codes come from `require(..., "GSxxx")`.

**`execTransaction(to,value,data,operation,safeTxGas,baseGas,gasPrice,gasToken,refundReceiver,signatures)`** (`Safe.sol:115-207`; payable; no caller restriction)
1. `onBeforeExecTransaction` hook (`:127`). This is empty in Safe; in SafeL2 it emits `SafeMultiSigTransaction` (`SafeL2.sol:37-66`).
2. `txHash = getTransactionHash(..., nonce++)` (`:131-146`). This is a post-increment, so the current nonce is hashed and storage is bumped before the signatures are checked. Any later revert rolls it back.
3. `checkSignatures(msg.sender, txHash, signatures)` (`:147`). This yields GS001, GS020–GS026 (§1.4).
4. If `guard ≠ 0`: `ITransactionGuard(guard).checkTransaction(to,value,data,operation,safeTxGas,baseGas,gasPrice,gasToken,refundReceiver,signatures,msg.sender)` (`:149-169`). A revert vetoes the transaction.
5. `gasleft() < max((safeTxGas<<6)/63, safeTxGas+2500) + 500` → **GS010** (`:174`).
6. `success = execute(to,value,data,operation, gasPrice==0 ? gasleft()-2500 : safeTxGas)` (`:180`).
7. If `!success ∧ safeTxGas==0 ∧ gasPrice==0`, the inner revert data is bubbled (`:184-193`). In 1.3.0/1.4.1 this was `require(..., "GS013")`.
8. If `gasPrice > 0`, `handlePayment` runs (`:196-198`, `:217-235`). The refund goes to `refundReceiver`, or to `tx.origin` if that is 0. For ETH the amount is `(gasUsed+baseGas)*min(gasPrice,tx.gasprice)` paid via `call` (**GS011** on failure). For tokens it is `(gasUsed+baseGas)*gasPrice` via `transferToken` (**GS012**).
9. Emits `ExecutionSuccess(txHash,payment)` or `ExecutionFailure(txHash,payment)` (`:199-200`).
10. If `guard ≠ 0`: `checkAfterExecution(txHash, success)` (`:203-205`). A revert undoes everything, including the nonce bump.

So a failed inner call with `safeTxGas>0` or `gasPrice>0` still **consumes the nonce** and pays the refund.

**`execTransactionFromModule(to,value,data,operation)`** and **`…ReturnData`** (`ModuleManager.sol:154-191`)
1. `onBeforeExecTransactionFromModule` hook (`:100`). This emits `SafeModuleTransaction` in SafeL2 (`SafeL2.sol:71-73`); it fires before the module check, but a revert discards it.
2. `guard = getModuleGuard()` (`:101`).
3. `msg.sender == 0x1 ∨ modules[msg.sender] == 0` → **GS104** (`:104`).
4. If the module guard is set: `guardHash = IModuleGuard(guard).checkModuleTransaction(to,value,data,operation,msg.sender)` (`:106-108`).
5. `execute(to,value,data,operation, type(uint256).max)` (`:161`, `:175`). There is no nonce, no signature and no transaction guard.
6. If the module guard is set: `checkAfterModuleExecution(guardHash, success)`. Then it emits `ExecutionFromModuleSuccess(module)` or `ExecutionFromModuleFailure(module)` (`:118-124`).
7. The return value carries `success`; the call does **not** revert on inner failure.

**`authorized` (SelfAuthorized)**: `msg.sender ≠ address(this)` → **GS031** (`common/SelfAuthorized.sol:11-19`). Every owner, module, guard and fallback mutator uses it. The only ways to satisfy it are:
- a CALL from the Safe to itself, made through `execTransaction` (threshold signatures) or `execTransactionFromModule` (any enabled module); or
- code running in the Safe's context via DelegateCall that calls the function internally, or that writes the slots directly.

**`approveHash(h)`** (`Safe.sol:380-384`): `owners[msg.sender] == 0` → **GS030**. The check is `owners[msg.sender]==0`; `msg.sender==0x1` cannot occur. Effect: `approvedHashes[msg.sender][h] = 1` and emit `ApproveHash(h, msg.sender)`. There is no revocation.

**`setup(...)`** (`Safe.sol:84-110`; external; **no caller restriction**)
1. Emits `SafeSetup(msg.sender,_owners,_threshold,to,fallbackHandler)` first (in 1.3.0/1.4.1 this came last).
2. `setupOwners` (`OwnerManager.sol:28-52`) checks, in order:
   - `threshold>0` → **GS200**
   - `_threshold > len` → **GS201**
   - `_threshold==0` → **GS202**
   - for each owner: `owner ∈ {0, 0x1, this} ∨ owner == previous` → **GS203**; `owners[owner]≠0` (duplicate) → **GS204**
   - then writes the list, `ownerCount` and `threshold`.
3. If `fallbackHandler≠0`: `internalSetFallbackHandler` (GS400 if it equals self). No event.
4. `setupModules(to,data)` (`ModuleManager.sol:75-83`):
   - `modules[0x1]≠0` → **GS100**
   - sets `modules[0x1]=0x1`
   - if `to≠0`: `!isContract(to)` → **GS002**; then `execute(to,0,data,DelegateCall,max)`, and failure → **GS000**.
5. If `payment>0`: `handlePayment(payment,0,1,paymentToken,paymentReceiver)` pays from the new Safe.

**Views and simulation**
- `checkSignatures(executor,h,sigs)` and `checkNSignatures(executor,h,sigs,n)` are public views (`Safe.sol:276-342`).
- The legacy overloads `checkSignatures(h,data,sigs)` and `checkNSignatures(h,data,sigs,n)` use `executor = msg.sender` (`:355-375`). The source warns that an owner calling these gets a free approved-hash signature.
- `simulateAndRevert(target,payload)` (`common/StorageAccessible.sol:34-47`) does an **unrestricted DELEGATECALL** to any target and then always reverts. It has no persistent effect, but during the call arbitrary code runs as the Safe.
- `getStorageAt` (`:16-29`) reads storage.

**`fallback()`** (`base/FallbackManager.sol:55-87`; non-payable):
- If `handler==0`, it returns empty with success.
- Otherwise it does `call(gas, handler, 0, calldata ‖ bytes20(caller()))`, then returns or **reverts with the handler's returndata verbatim**.
- `receive()` accepts ETH with empty calldata and emits `SafeReceived` (`common/NativeCurrencyPaymentFallback.sol:14-16`).

### 1.3 Authority-mutating transitions

All of these are `authorized` (msg.sender == Safe). Events are declared in `interfaces/I*Manager.sol`.

| Function | Checks (in order) | Effect | Events |
|---|---|---|---|
| `addOwnerWithThreshold(o,t)` `OwnerManager.sol:57-68` | `o∈{0,0x1,this}`→GS203; `owners[o]≠0`→GS204 | `owners[o]=owners[0x1]; owners[0x1]=o; ++ownerCount` (insert at head); if `threshold≠t`, `changeThreshold(t)` | `AddedOwner(o)` [+`ChangedThreshold(t)`] |
| `removeOwner(prev,o,t)` `:73-85` | `--ownerCount < t`→GS201 (decrements first; restored on revert); `o∈{0,0x1}`→GS203; `owners[prev]≠o`→GS205 | `owners[prev]=owners[o]; owners[o]=0`; if `threshold≠t`, `changeThreshold(t)` (which re-checks `t≤ownerCount`, `t≥1`) | `RemovedOwner(o)` [+`ChangedThreshold`] |
| `swapOwner(prev,old,new)` `:90-103` | `new∈{0,0x1,this}`→GS203; `owners[new]≠0`→GS204; `old∈{0,0x1}`→GS203; `owners[prev]≠old`→GS205 | `owners[new]=owners[old]; owners[prev]=new; owners[old]=0`; threshold unchanged | `RemovedOwner(old)`, `AddedOwner(new)` |
| `changeThreshold(t)` `:108-115` | `t>ownerCount`→GS201; `t==0`→GS202 | `threshold=t` | `ChangedThreshold(t)` (1.4.1 emitted the same value via `threshold`) |
| `enableModule(m)` `ModuleManager.sol:129-137` | `m∈{0,0x1}`→GS101; `modules[m]≠0`→GS102 | insert at head | `EnabledModule(m)` |
| `disableModule(prev,m)` `:142-149` | `m∈{0,0x1}`→GS101; `modules[prev]≠m`→GS103 | unlink | `DisabledModule(m)` |
| `setModuleGuard(g)` `:258-270` (**1.5.0 only**) | `g≠0 ∧ ¬g.supportsInterface(0x58401ed8)`→GS301 | `sstore(MODULE_GUARD_SLOT,g)` | `ChangedModuleGuard(g)` |
| `setGuard(g)` `GuardManager.sol:71-81` | `g≠0 ∧ ¬g.supportsInterface(0xe6d7a83a)`→GS300 | `sstore(GUARD_SLOT,g)` | `ChangedGuard(g)` |
| `setFallbackHandler(h)` `FallbackManager.sol:46-49` | `h==this`→GS400 (`:33`) | `sstore(FALLBACK_SLOT,h)` | `ChangedFallbackHandler(h)` |
| `approveHash(h)` (owner, not `authorized`) | GS030 | `approvedHashes[sender][h]=1` | `ApproveHash` |
| `nonce` | only via `execTransaction` | `+1` per successful (non-reverting) call | — |
| `signedMessages[h]` | **no setter in Safe**; written only by DelegateCall into `SignMessageLib.signMessage` (`libraries/SignMessageLib.sol:22-26`) | `=1` | `SignMsg(h)` |
| `singleton` (slot 0) | **no setter**; written only by DelegateCall (e.g. `SafeMigration.migrate*` `libraries/SafeMigration.sol:71-97`, `SafeToL2Setup.setupToL2` `libraries/SafeToL2Setup.sol:64-66`, which requires `nonce==0`) | changes the implementation | `ChangedMasterCopy` (library event) |

Note that ownership checks are about **list membership, not usability**. There is no check that an owner can sign (it could be a contract that never returns the magic value). The Safe cannot become an owner of itself through the API (GS203).

### 1.4 Signature semantics

**What is signed.** `txHash` is computed by `getTransactionHash` (`Safe.sol:404-473`):

```
txHash = keccak256(0x19 ‖ 0x01 ‖ domainSeparator ‖ keccak256(abi.encode(
           SAFE_TX_TYPEHASH, to, value, keccak256(data), operation,
           safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, nonce)))
domainSeparator = keccak256(abi.encode(0x47e7…9218, block.chainid, address(this)))   // Safe.sol:389-399
```

The domain separator is recomputed on every call, so after a hard fork that changes the chain ID, old signatures are invalid. In 1.5.0 this is inline assembly over calldata; the source warns there is no dirty-bit cleaning of addresses or the enum (`:421-424`). 1.4.1 and 1.3.0 use `encodeTransactionData` with `abi.encode`, which is the same value.

**Message hashes** (EIP-1271 for the Safe as a signer): `keccak256(0x1901 ‖ domainSeparator ‖ keccak256(abi.encode(SAFE_MSG_TYPEHASH, keccak256(message))))` (`handler/CompatibilityFallbackHandler.sol:51-64`; `SignMessageLib.sol:33-36`).

**`checkNSignatures(executor, h, sigs, n)`** (`Safe.sol:287-342`):
- `sigs.length < 65n` → **GS020**.
- `lastOwner = 0`. For `i < n`, read `(v,r,s)` at `65i` (`common/SignatureDecoder.sol:21-31`; layout `r(32) s(32) v(1)`) and branch on `v`:

| v | Type | Recovered `currentOwner` | Validity condition | Revert |
|---|---|---|---|---|
| 0 | contract (EIP-1271) | `address(uint160(r))` | `s ≥ 65n` (GS021); `s+32 ≤ len` (GS022); `s+32+len_s ≤ len` (GS023); `ISignatureValidator(currentOwner).isValidSignature(h, sigs[s+32 .. s+32+len_s]) == 0x1626ba7e` (GS024), via `checkContractSignature` `:246-271` | GS021–GS024 |
| 1 | approved hash / caller | `address(uint160(r))` | `executor == currentOwner ∨ approvedHashes[currentOwner][h] ≠ 0` | GS025 (`:328`) |
| >30 | eth_sign | `ecrecover(keccak256("\x19Ethereum Signed Message:\n32" ‖ h), v-4, r, s)` | — | — |
| else | raw ECDSA | `ecrecover(h, v, r, s)` | — | — |

- Then, for every type: `currentOwner ≤ lastOwner ∨ owners[currentOwner]==0 ∨ currentOwner == 0x1` → **GS026** (`:338-339`). Then `lastOwner = currentOwner`.
- `checkSignatures` adds `threshold == 0` → **GS001** and uses `n = threshold` (`:276-282`). Bytes beyond the first `n` slots are only reachable as dynamic contract-signature data. Extra signatures are ignored.

**Meaning of "owner `o` approved hash `h`"**, at the moment of the check:
- **ECDSA (v ∈ {27,28})**: someone holding `o`'s secp256k1 key produced `(r,s,v)` over `h`. Assumptions: EUF-CMA of ECDSA over secp256k1, keccak collision resistance, and that `ecrecover` returns 0 for invalid input. A 0 result fails GS026 because `0 ≤ lastOwner`. High-s malleability is accepted (`:300-303`); it is harmless because distinctness is by address and the nonce prevents replay. A `v` outside {0,1,27,28,31,32} leads to `ecrecover` returning 0 and then GS026.
- **eth_sign (v ∈ {31,32})**: the same, over the EIP-191 prefixed hash.
- **Approved hash (v = 1)**: either (a) `o` is the caller (`executor == msg.sender` of `execTransaction`), meaning the act of submitting is an approval; or (b) at some earlier time `o` called `approveHash(h)` **while it was an owner**. That entry is stored forever (slot 8) and is never cleared, including after `o` is removed and later re-added.
- **Contract (v = 0)**: the contract at `o` answered the magic value to `isValidSignature(h, blob)`. The callback is a `view` external call (STATICCALL), so it cannot change state, but it is arbitrary code that can read state, time, or anything else. Its "approval" is whatever predicate that contract implements. Two points matter:
  - The callback is made **before** the GS026 owner check. Any address placed in `r` gets called, owner or not. If it reverts, the revert data propagates out of `checkNSignatures`, and out of the Safe if the call came through a fallback.
  - The `blob` pointer is only checked against the static region. Several contract signatures may share or overlap dynamic data.
- **Threshold semantics**: `checkSignatures` succeeds iff there exist `threshold` addresses `o_1 < o_2 < … < o_k`, each currently in `owners`, each approving `h` by one of the four mechanisms. Strict ordering gives distinctness; there is no other de-duplication.

**Replay protection**:
- `nonce` is bound in the hash and incremented per executed transaction. Ordering is strict: only `nonce == current` can execute.
- `chainId` and `verifyingContract = address(this)` are bound through the domain separator. This prevents replay across chains and across Safes, including same-address Safes on different chains.
- Not covered: messages verified through EIP-1271 have **no nonce**. Once valid, a message stays valid. If it was validated via `signedMessages`, it stays valid forever, because nothing unsets it except another DelegateCall.

**Version differences in signatures**:
- **1.4.1** (`src-safe141/contracts/Safe.sol:257-334`):
  - The signature is `checkSignatures(bytes32 dataHash, bytes data, bytes signatures)`. The executor is implicitly `msg.sender` (`:321`).
  - Contract signatures call the **legacy** `isValidSignature(bytes data, bytes sig)` with magic `0x20c13b0b` (`src-safe141/contracts/interfaces/ISignatureValidator.sol:6,19`) on the full EIP-712 **preimage** `data`. It first requires `keccak256(data) == dataHash` → **GS027** (`:287`).
- **1.3.0** (`src-safe130/contracts/GnosisSafe.sol:240-305`):
  - Same as 1.4.1 but **without GS027**. When reached via the `CompatibilityFallbackHandler` (`src-safe130/contracts/handler/CompatibilityFallbackHandler.sol:28-38`), the contract signer is asked about the raw message `_data` while `dataHash` is the Safe-domain message hash. The two are not bound to each other.
  - Also present: `requiredTxGas` (`:315-327`), an unrestricted `execute` that always reverts.
- **1.5.0**:
  - Has an explicit `executor` parameter (`Safe.sol:276,287`). `CompatibilityFallbackHandler.isValidSignature(bytes32,bytes)` passes `executor = address(0)`, so v=1 counts only `approvedHashes` (`handler/CompatibilityFallbackHandler.sol:73-86`).
  - Contract signatures use the standard `isValidSignature(bytes32,bytes)` / `0x1626ba7e`.
  - `encodeTransactionData` was removed from the Safe and moved to the handler (CHANGELOG 1.5.0).

### 1.5 Relay behaviour

`Executor.execute` (`base/Executor.sol:21-43`):
- `operation == DelegateCall` → `delegatecall(txGas, to, data)`; otherwise `call(txGas, to, value, data)`.
- There is no code-existence check.
- `Enum.Operation {Call, DelegateCall}`.

Every relay path issues `(to, value, data, operation)` with **msg.sender = the Safe** (for Call) or **runs `to`'s code against the Safe's storage and balance** (for DelegateCall):

| Path | Who may trigger | Pre-checks | Post-checks |
|---|---|---|---|
| `execTransaction` | anyone holding a threshold signature set for the current nonce | signatures + tx guard `checkTransaction` | `checkAfterExecution` |
| `execTransactionFromModule*` | any enabled module | membership in `modules`; in **1.5.0 only**, module guard `checkModuleTransaction` | module guard `checkAfterModuleExecution` (1.5.0) |
| `setup` → `setupModules` | anyone, while uninitialised | `isContract(to)` (1.4.1+) | must succeed (GS000) |
| `simulateAndRevert` | anyone | none | always reverts, so no persistent effect |
| `fallback` → handler | anyone | none; this is a CALL **to** the handler, not from the Safe | the handler's return/revert data becomes the Safe's |

A **DelegateCall** can write every slot in §1.1:
- `singleton` (slot 0), which replaces all code;
- `owners`, `ownerCount`, `threshold` (including inconsistent values such as threshold 0, which bricks the Safe via GS001, or `owners[this]`);
- `modules`, `nonce`, `signedMessages`, `approvedHashes`;
- guard, fallback handler and module guard slots.

It bypasses every `authorized` check and every Safe-level event. **Module transactions bypass signatures entirely**, and before 1.5.0 they also bypass every guard. In 1.5.0 they bypass the transaction guard but are subject to the module guard, if one is set.

### 1.6 Edge cases and pitfalls

1. **Threshold bypass via modules.** Any enabled module is a 1-of-1 principal with full power. It can call `addOwnerWithThreshold`, `enableModule` or `setGuard(0)` on the Safe through a Call to `address(this)`, or DelegateCall anything. The effective authority of a Safe is `threshold-of-owners ∨ (any module)`, closed transitively over each module's own authority. A module that is itself a Safe or Roles modifier inherits that structure.
2. **Guard bricking.** A guard whose `checkTransaction` or `checkAfterExecution` always reverts makes `execTransaction` unusable, including the `setGuard(0)` transaction. Recovery is possible only through a module (pre-1.5: always; 1.5: unless the module guard also blocks). The 1.3.0 `setGuard` has no ERC-165 check (`src-safe130/contracts/base/GuardManager.sol:34-38`), so any address can be set as the guard, including an EOA. Solidity 0.7.6 inserts an `extcodesize` check before high-level external calls, so a codeless guard makes `Guard(guard).checkTransaction(...)` revert and bricks the signature path.
3. **Fallback handler `msg.sender` appending.** The handler sees `msg.sender = Safe` and the original caller in the last 20 bytes of calldata (`HandlerContext._msgSender`, `handler/HandlerContext.sol:51-60`). Calling a handler directly lets anyone forge that suffix, so handler state must be keyed by `msg.sender` (the manager). This is the case for `ExtensibleBase.onlySelf`, which requires `_msgSender() == _manager()` (`handler/extensible/ExtensibleBase.sol:35-41`).
   - GS400 forbids `handler == this`. Otherwise a calldata-plus-20-byte suffix could synthesise a 4-byte selector of an `authorized` function, with `msg.sender == this` (`FallbackManager.sol:20-33`). **1.3.0 lacks GS400.**
   - The handler is the Safe's **EIP-1271 oracle**. Whatever it returns is the Safe's answer, and **revert data passes through verbatim** (`FallbackManager.sol:80-83`). This is the Zodiac exploit ingredient; see §3.6.
4. **ERC-1271 owners as relays.**
   - A contract owner can approve via (a) its `isValidSignature` predicate (v=0); (b) its own executions calling `approveHash` (v=1 stored); or (c) being the `executor` of `execTransaction` (v=1 by caller).
   - If the owner is a Safe, then that Safe's modules, guard-free paths and fallback handler all become part of the outer Safe's authority. For example, a module of the inner Safe can make the inner Safe call `outer.approveHash` or `outer.execTransaction`.
   - The contract-signature callback runs before the owner check, so any contract named in `r` is invoked.
5. **approvedHashes as earlier-transaction authority.** Approval is a write by `o` at time `t₀`, consumed at time `t₁ > t₀`. It is permanent, and it is honoured at `t₁` only if `o` is an owner at `t₁`; it need not still be an owner after `t₀`. For transactions it is effectively single-use, because the hash binds the nonce. For EIP-1271 messages it is reusable forever.
6. **owner == address(this).** This is forbidden by `setupOwners`, `addOwnerWithThreshold` and `swapOwner` (GS203) in all three versions. It is reachable only by DelegateCall. If it happened, a module-originated self-call `execTransaction` would have `executor = this`, giving a v=1 free signature.
7. **SENTINEL (0x1).**
   - Owner and module lists use `0x1` as head and tail. `0x1` is never an owner or module: it is excluded by the GS101/GS203 checks, explicitly by GS026 (`currentOwner == SENTINEL`), and GS104 rejects `msg.sender == 0x1`.
   - `owners[0x1]≠0` always holds after setup, which is why GS026 needs the explicit exclusion.
   - `prevOwner`/`prevModule` arguments must point exactly to the predecessor (GS205/GS103), so list operations commit to the current list structure. A concurrent change invalidates pre-signed removals.
8. **Setup front-running.**
   - `setup` is permissionless while `threshold == 0` (GS200 guard only). Any proxy that is deployed and initialised in separate transactions can be captured by whoever calls `setup` first. Cases: `new SafeProxy(singleton)`; 1.3.0 `GnosisSafeProxyFactory.createProxy(singleton, "")`, which uses CREATE with no salt binding (`src-safe130/contracts/proxies/GnosisSafeProxyFactory.sol:15-25`); or any factory call with an empty initializer.
   - With `createProxyWithNonce(singleton, initializer, saltNonce)`, `salt = keccak(keccak(initializer) ‖ saltNonce)` (`proxies/SafeProxyFactory.sol:59-64`). The address commits to the full initial configuration: owners, threshold, setup delegatecall, fallback handler and payment. Front-running only reproduces the identical Safe.
   - The same initializer can be replayed on other chains to the same address, unless `createChainSpecificProxyWithNonce` adds `chainid` (`:86-95`).
   - 1.4.1 `createProxyWithCallback` (`src-safe141/contracts/proxies/SafeProxyFactory.sol:86-95`) was removed in 1.5.0.
   - The setup DelegateCall can arbitrarily configure the Safe before first use, including changing the singleton via `SafeToL2Setup`.
9. **Nonce.** A failed inner call still increments the nonce when `safeTxGas>0 ∨ gasPrice>0`. Signers cannot partially fill or skip; only one transaction exists per nonce. `execTransaction` is not reentrancy-locked: the inner call can call `execTransaction` again, but it needs signatures for `nonce+1`.
10. **Refunds.** `refundReceiver = 0` pays `tx.origin`, i.e. whoever relays. The amount and token are signed. 1.5.0 uses `call`, while ≤1.4.1 used `send`, so in 1.5.0 the refund receiver can re-enter.
11. **MultiSend.** `libraries/MultiSend.sol:30-75` is a DelegateCall-only batch (`require(address(this) != MULTISEND_SINGLETON)`) containing per-item Call or DelegateCall. `MultiSendCallOnly` reverts on items with `operation == 1`. **In 1.5.0 both map `to == 0` to `address(this)`** (`MultiSend.sol:50`, `MultiSendCallOnly.sol:44`); this is new, and absent in 1.4.1 and 1.3.0.
12. **Legacy `checkSignatures(h,data,sigs)`.** The `executor` is `msg.sender`. Any contract using it as an oracle grants the calling owner one free signature (warning at `Safe.sol:349,365`).
13. **No events in non-L2 Safe** for executions beyond `ExecutionSuccess`/`ExecutionFailure`; L2 adds traces. DelegateCall writes produce no Safe events.

### 1.7 v1.4.1 and v1.3.0 differences (summary)

| Aspect | 1.3.0 | 1.4.1 | 1.5.0 |
|---|---|---|---|
| Module guard | — | — | `setModuleGuard`, slot `0xb104…` |
| `setGuard` ERC-165 check (GS300) | no | yes | yes |
| `handler == this` ban (GS400) | no | yes | yes |
| `setupModules` `isContract(to)` (GS002) | no | yes | yes |
| Contract signature interface | `isValidSignature(bytes,bytes)`/`0x20c13b0b`, no GS027 | same + GS027 | `isValidSignature(bytes32,bytes)`/`0x1626ba7e` |
| Executor for v=1 | `msg.sender` | `msg.sender` | explicit parameter (+ legacy overloads) |
| Inner-fail with 0/0 gas | GS013 | GS013 | bubble revert data |
| `SafeSetup` event | after setup | after setup | before setup |
| `requiredTxGas` | yes | no | no |
| Refund transfer | `send` | `send` | `call` |
| MultiSend `to=0 → self` | no | no | yes |
| Factory | `createProxy` (CREATE), `createProxyWithNonce`, `…WithCallback` | `createProxyWithNonce`, `createChainSpecific…`, `…WithCallback` | `createProxyWithNonce(L2)`, `createChainSpecific…(L2)` |
| Storage layout | same | same | same + module-guard slot |

---

## 2. Zodiac base: Module and Modifier (`@gnosis.pm/zodiac` 3.4.1)

Paths in this section are under `src-zodiac341/contracts/`.

- `Module is FactoryFriendly` and `FactoryFriendly is OwnableUpgradeable` (OZ **v5**, `package.json:91-92`). The owner and the initializer state live in ERC-7201 namespaced slots:
  - `OwnableStorageLocation = 0x9016d09d72d40fdae2fd8ceac6b6234c7706214fd39c1cd1e609a0528c199300` (`src-ozu500/contracts/access/OwnableUpgradeable.sol:28`)
  - `INITIALIZABLE_STORAGE = 0xf0c57e16…6a00` (`src-ozu500/contracts/proxy/utils/Initializable.sol:77`)
- `Module`: `avatar` (slot 0), `target` (slot 1) (`core/Module.sol:12,14`).
  - `setAvatar` and `setTarget` are `onlyOwner` (`:23-35`) and emit `AvatarSet`/`TargetSet`.
  - `exec` and `execAndReturnData` call `IAvatar(target).execTransactionFromModule(…ReturnData)` (`:43-72`). Transactions go to **target**, not avatar.
- `ExecutionTracker`: `consumed[signer][hash]` (slot 2). `invalidate(h)` lets anyone set `consumed[msg.sender][h] = true` (`signature/ExecutionTracker.sol:11-16`).
- `Modifier is Module, ExecutionTracker, SignatureChecker, IAvatar`: `modules` linked list (slot 3), sentinel `0x1` (`core/Modifier.sol:17-19`).
  - `enableModule` reverts `InvalidModule` for 0 or 0x1 and `AlreadyEnabledModule` for a duplicate (`:131-138`).
  - `disableModule` reverts `InvalidModule` and `AlreadyDisabledModule` if `modules[prev]≠m` (`:116-126`).
  - Both are `onlyOwner` (OZ `OwnableUnauthorizedAccount`) and emit `EnabledModule`/`DisabledModule`.
  - `transferOwnership` and `renounceOwnership` are `onlyOwner` (OZ).
- **`moduleOnly`** (`core/Modifier.sol:78-97`):
  1. If `modules[msg.sender] ≠ 0`, it passes.
  2. Otherwise `(hash, signer) = moduleTxSignedBy()`.
  3. `modules[signer]==0` → `NotAuthorized(msg.sender)`.
  4. `consumed[signer][hash]` → `HashAlreadyConsumed`.
  5. Sets `consumed[signer][hash]=true` and emits `HashExecuted(hash)`.
- `sentOrSignedByModule()` (`:99-110`) returns `msg.sender` if it is a module, else the signer if that is a module, else 0.
- **`moduleTxSignedBy()`** (`signature/SignatureChecker.sol:14-66`): this is a signature appended to the calldata.
  - It takes `msg.data` (whole), and needs at least `4+32+65` bytes.
  - The last 65 bytes are `r ‖ s ‖ v` and the 32 bytes before them are `salt`.
  - If `v == 0` (contract signature): `start = uint256(s)` must be in `[4, end]`; `signer = address(r)`; `hash = moduleTxHash(data[:start], salt)`; the result is valid iff `_isValidContractSignature(signer, hash, data[start:end])`.
  - Otherwise: `hash = moduleTxHash(data[:end], salt)` and `signer = ecrecover(hash, v, r, s)`.
  - `moduleTxHash = keccak(0x1901 ‖ keccak(abi.encode(DOMAIN_TYPEHASH, chainid, this)) ‖ keccak(abi.encode(MODULE_TX_TYPEHASH, keccak(data), salt)))` (`:75-89`). It is bound to the chain and the modifier instance, and replay is prevented by `consumed`.
  - **`_isValidContractSignature`** (`:113-136`) is the ERC-1271 bug:

```solidity
(, bytes memory returnData) = signer.staticcall(abi.encodeWithSelector(IERC1271.isValidSignature.selector, hash, signature));
return bytes4(returnData) == EIP1271_MAGIC_VALUE;          // success flag IGNORED
```

  Revert data counts as an answer. This is fixed in zodiac-core `v4.0.0-alpha.0` (`11708ac`) as `return success && bytes4(returnData) == EIP1271_MAGIC_VALUE;` (`src-zcore400/contracts/signature/SignatureChecker.sol:112-120`).

---

## 3. Zodiac Roles Modifier v2 (2.1.0 source, `src-roles-v2/packages/evm/contracts/`)

### 3.1 Authority state

- **Owner**: the OZ v5 namespaced `_owner` (§2), set in `setUp` via `_transferOwnership(_owner)` (`Roles.sol:51-63`). `setUp` is `initializer`. The constructor calls `setUp` (`:43-46`), so the mastercopy is initialised; proxies are initialised by the factory.
- **avatar / target / consumed / modules**: slots 0–3 (from Modifier).
- **Roles storage**: I derived this from the C3 linearisation; confirm with `solc --storage-layout` before relying on slot numbers.

| Slot | Variable | Location |
|---|---|---|
| 4 | `mapping(bytes32 => Role) roles` | `Core.sol:13` |
| 5 | `mapping(bytes32 => Allowance) allowances` | `Core.sol:14` |
| 6 | `mapping(bytes32 => ITransactionUnwrapper) unwrappers` | `Periphery.sol:19`; key `bytes20(to) ‖ bytes4(selector)` |
| 7 | `mapping(address => bytes32) defaultRoles` | `Roles.sol:24` |

- `Role { mapping(address=>bool) members; mapping(address=>TargetAddress) targets; mapping(bytes32=>bytes32) scopeConfig; }` (`Types.sol:120-124`).
  - **Membership is a plain bool. There is no start/end time in v2.**
  - Time-bound, usage-limited membership (`start:64 | end:64 | usesLeft:128`) exists only in **v3** at HEAD (`src-roles/packages/evm/contracts/core/Membership.sol:26-73`).
- `TargetAddress { Clearance clearance; ExecutionOptions options; }`:
  - `Clearance {None, Target, Function}`
  - `ExecutionOptions {None, Send, DelegateCall, Both}` (`Types.sol:80-91,115-118`)
- `scopeConfig[key(to,selector)]`, where `key = bytes20(to) | bytes4(sel)>>160` (`Core.sol:33-42`), is a 32-byte header (`packers/BufferPacker.sol:14-24`): `count:16 | options:8 | isWildcarded:8 | unused:64 | pointer:160`.
  - `pointer` is an SSTORE2-style contract whose code holds the packed condition list. It is deployed through the singleton factory `0xce0042B868300000d44A59004Da54A005ffdcf9f` with salt 0 (`WriteOnce.sol:9-48`), so it is content-addressed and immutable.
  - Each condition is 2 bytes: `parent:8 | paramType:3 | operator:5`, followed by compValues.
- `Allowance { uint128 refill; uint128 maxRefill; uint64 period; uint128 balance; uint64 timestamp; }` (`Types.sol:132-138`).
- `ParameterType {None, Static, Dynamic, Tuple, Array, Calldata, AbiEncoded}` (`Types.sol:11-19`).
- `Operator` (`Types.sol:21-78`):
  - 0 Pass
  - 1 And, 2 Or, 3 Nor
  - 5 Matches, 6 ArraySome, 7 ArrayEvery, 8 ArraySubset
  - 15 EqualToAvatar
  - 16 EqualTo, 17 GreaterThan, 18 LessThan, 19 SignedIntGreaterThan, 20 SignedIntLessThan, 21 Bitmask, 22 Custom
  - 28 WithinAllowance, 29 EtherWithinAllowance, 30 CallWithinAllowance
  - The other values are placeholders.

### 3.2 Guarded entry points

**Owner-only** (`onlyOwner` → OZ `OwnableUnauthorizedAccount(sender)`):

| Function | Location | Effect | Event |
|---|---|---|---|
| `assignRoles(module, roleKeys[], memberOf[])` | `Roles.sol:69-84` | length mismatch → `ArraysDifferentLength`; sets `roles[k].members[module] = b`; **auto-enables `module` as a Modifier module** if not enabled; revocation does not disable it | `AssignRoles` |
| `setDefaultRole(module, roleKey)` | `:89-95` | sets the default role | `SetDefaultRole` |
| `allowTarget(role,to,opts)` | `PermissionBuilder.sol:57-67` | `targets[to] = {Target, opts}` | `AllowTarget` |
| `revokeTarget` | `:72-81` | `{None, None}` | `RevokeTarget` |
| `scopeTarget` | `:86-95` | `{Function, None}` | `ScopeTarget` |
| `allowFunction(role,to,sel,opts)` | `:102-112` | header = wildcarded with opts | `AllowFunction` |
| `revokeFunction` | `:118-125` | deletes the header | `RevokeFunction` |
| `scopeFunction(role,to,sel,conds[],opts)` | `:133-156` | `Integrity.enforce(conds)` (`Integrity.sol:28-34`), then `_store` (`PermissionLoader.sol:19-33`) | `ScopeFunction` |
| `setAllowance(key,balance,maxRefill,refill,period,timestamp)` | `:158-177` | `maxRefill=0 → uint128.max`; `timestamp=0 → now` | `SetAllowance` |
| `setTransactionUnwrapper(to,sel,adapter)` | `Periphery.sol:21-28` | sets the unwrapper | `SetUnwrapAdapter` |
| `enableModule`, `disableModule`, `setAvatar`, `setTarget`, `transferOwnership`, `renounceOwnership` | §2 | — | — |

**Module-only execution**: `execTransactionFromModule`, `…ReturnData`, `execTransactionWithRole(…, roleKey, shouldRevert)` and `…ReturnData` (`Roles.sol:103-205`). They all call `_authorize(roleKey, to, value, data, operation)` (`PermissionChecker.sol:21-70`). The default-role entry points use `roleKey = defaultRoles[msg.sender]`. Check order:
1. `moduleOnly` (§2). `msg.sender` must be an enabled module, or the trailing signature must recover to one (replay-marked via `consumed`).
2. `roleKey == 0` → `NoMembership`.
3. `!roles[roleKey].members[sentOrSignedByModule()]` → `NoMembership`.
4. `adapter = unwrappers[to‖bytes4(data)]`:
   - If set: `_multiEntrypoint` calls `adapter.unwrap(to,value,data,operation)` (a view). A revert → `MalformedMultiEntrypoint`. Each unwrapped `(to_i, value_i, data[loc_i:loc_i+size_i], op_i)` goes through `_transaction` and **the first non-Ok status is returned**. **The outer `(to, operation)` is not itself checked against the role.**
   - If not set: `_transaction(role,to,value,data,operation)`.
5. A status other than `Ok` → `ConditionViolation(status, info)`.

**`_transaction`** (`PermissionChecker.sol:114-182`):
- `0 < data.length < 4` → `FunctionSignatureTooShort`.
- `targets[to].clearance == Function`:
  - `header = scopeConfig[key(to, bytes4(data))]`. Note that an empty `data` gives `selector = 0x00000000`, so plain ETH sends need `allowFunction(to, 0x00000000, Send)`.
  - `header == 0` → `FunctionNotAllowed(info = selector)`.
  - `_executionOptions(value, op, options)` (`:188-212`): `value>0 ∧ opts∉{Send,Both}` → `SendNotAllowed`; `op==DelegateCall ∧ opts∉{DelegateCall,Both}` → `DelegateCallNotAllowed`.
  - If wildcarded → `Ok`. Otherwise `_scopedFunction` loads the tree (`PermissionLoader._load`, `:35-84`; it patches `EqualToAvatar` into `EqualTo keccak(abi.encode(avatar))` at `:59-64`), decodes the calldata (`Decoder.inspect`) and walks the tree (`_walk`, `:233-290`).
- `clearance == Target` → only `_executionOptions(value, op, targets[to].options)`. **Any function and any calldata is allowed.**
- `None` → `TargetAddressNotAllowed`.

**Condition semantics** (`PermissionChecker.sol`):

| Operator | Semantics |
|---|---|
| Pass | Ok |
| Matches `:292-331` | `|children| == |payload.children|`, and every child passes on the corresponding sub-payload, threading the consumptions |
| And / Or / Nor `:333-425` | over children on the **same** payload; Nor ignores the consumptions of its children |
| ArraySome `:427-459` | **as written, loops `i < condition.children.length`, which Integrity forces to be 1 (`Integrity.sol:218-223`), and tests `payload.children[i]`.** Only element 0 is ever examined; an empty array indexes out of bounds and panics. In other words it implements "first element passes", which is stricter than the documented intent. The test `test/operators/06ArraySome.spec.ts` does not cover a match at index ≥1. Fails safe, but it is a semantics gap to model precisely. |
| ArrayEvery `:461-492` | every element passes child[0] |
| ArraySubset `:494-542` | `1 ≤ |payload| ≤ |children|`; each element is greedily matched to a distinct child (bitmask `taken`; up to 256 children) |
| EqualTo / GreaterThan / LessThan `:544-564` | EqualTo compares `keccak(bytes of the param encoding)` with compValue (Integrity stores the keccak); GT/LT are unsigned word comparisons |
| SignedInt GT/LT `:566-584` | signed word comparisons |
| Bitmask `:593-621` | `compValue = shift:16 | mask:120 | expected:120` over the param bytes (the Dynamic length word is skipped); `shift ≥ len` → `BitmaskOverflow` |
| Custom `:623-649` | `ICustomCondition(compValue[0:20]).check(to,value,data,op,location,size,extra12)`, an external view; trust is delegated to that contract |
| WithinAllowance / EtherWithinAllowance / CallWithinAllowance `:651-713` | `__consume(amount, key)` with amount = the param word, `value`, or `1` respectively; fails if `amount + consumed > balance` |

Integrity (`Integrity.sol`) enforces:
- a single root at index 0 with BFS order;
- per-operator paramType and compValue shape;
- Ether/Call allowances must be children of the Calldata node;
- child-count rules and type-tree compatibility for siblings;
- the root type must be `Calldata`.

### 3.3 Budgets (Consumptions)

- Accrual (`AllowanceTracker.sol:20-45`): if `period == 0` or the current period is not yet over, the balance is unchanged. Otherwise `n = ⌊(now−timestamp)/period⌋`; if `balance < maxRefill`, `balance = min(balance + n·refill, maxRefill)`; and `timestamp += n·period`.
- Consumptions for the whole (possibly multi-send) transaction are accumulated in memory and merged across entries (`Consumptions.sol:48-91`).
- `_flushPrepare` writes `balance − consumed` before execution, asserting the accrued balance is unchanged (`AllowanceTracker.sol:53-80`). This protects against reentrancy: a nested call sees the reduced balance.
- `_flushCommit` emits `ConsumeAllowance` on success. On failure it restores `balance` (`:90-111`), while keeping the advanced `timestamp`.
- If `execTransactionWithRole(…, shouldRevert=true)` fails, it reverts with `ModuleTransactionFailed` (`Roles.sol:170-172`). Otherwise the call returns `false`.
- Allowance keys are global across roles: two roles that reference the same key share the budget.

### 3.4 Relay behaviour

After `_authorize`, Roles calls `exec`, i.e. `IAvatar(target).execTransactionFromModule(to, value, data, operation)` (`Roles.sol:117,141,169,200`; `src-zodiac341/contracts/core/Module.sol:43-72`). Roles must itself be an enabled module of the target Safe. The Safe then executes with msg.sender = Safe. The Safe 1.5.0 module guard, if any, also applies; signatures and the transaction guard do not.

A role with `DelegateCall` permission on a target gives that target's code full control of Safe storage (§1.5). The same is true of an unwrapper-registered address under operation DelegateCall, as in the MultiSend pattern.

### 3.5 MultiSend unwrapping

`adapters/MultiSendUnwrapper.sol:13-119`:
- It requires `value == 0` and `operation == DelegateCall` (`UnsupportedMode`).
- The header must be selector `multiSend(bytes)`, offset `0x20`, and `4 + ceil32(64 + len) == data.length` (`MalformedHeader`).
- Each entry is `op:1 | to:20 | value:32 | len:32 | data`, with `op ≤ 1` and the entry in bounds (`MalformedBody`), and there must be at least one entry.
- Entries are returned as calldata slices, and each is checked as an independent transaction, including DelegateCall entries, which need the `DelegateCall` option on their target.

Model obligations:
- (a) **Owner trust**: registering `unwrappers[(to, multiSend.selector)]` asserts that `to` is code which executes exactly the decoded list. The outer DelegateCall is *not* permission-checked.
- (b) **`to == 0`**: Safe **1.5.0** MultiSend rewrites `to == 0` to `address(this)` (`src-safe150/contracts/libraries/MultiSend.sol:50`), but the unwrapper reports `to = 0`. Checks are therefore against `targets[0x0]` while execution hits the Safe itself. This only matters if a role grants clearance on `address(0)`; with the 1.3.0/1.4.1 MultiSend there is no divergence.
- (c) **Parser divergence (needs confirmation)**: `_validateEntries` lets the last entry's data run into the ABI padding (`offset + 85 + len ≤ data.length`, `:72`). MultiSend iterates over the ABI-decoded `bytes` (exact length), which solc zero-fills beyond its length. So, as far as I can tell from reading, the ≤31 bytes the checker sees may be attacker-chosen padding while the executed bytes are zeros. I did not test this; treat it as something to confirm.

### 3.6 Edge cases

1. **Advisory: ERC-1271 authorisation bypass** (exploited 1 June 2026; fixed mastercopies Roles 2.1.1 `0xF2964CE6161ce0e75964Fe7927cE114cb0B283D5` and Delay 1.1.1 `0x824175b9…df01`, released 19 June 2026; the faulty versions stay in zodiac's `FAULTY` registry). Root cause is `_isValidContractSignature` ignoring `success` (§2). Mechanism, reconstructed from source:
   1. A role member (Roles) or enabled module (Delay) is a **Safe whose fallback handler is `CompatibilityFallbackHandler`**.
   2. The attacker calls `execTransactionWithRole(...)` (or Delay `execTransactionFromModule`) with a trailing `salt ‖ r=memberSafe ‖ s=offset ‖ v=0` and a crafted inner blob.
   3. Zodiac STATICCALLs `memberSafe.isValidSignature(bytes32,bytes)`. This goes to the Safe fallback (`FallbackManager.sol:55-87`), then to CFH `isValidSignature`.
   4. Depending on the version, CFH calls `safe.checkSignatures(...)` (1.5.0 `:83`, 1.4.1 `:36`) or `safe.isValidSignature(bytes,bytes)` → CFH → `checkSignatures` (1.3.0/1.4.1 bytes32 shim). The blob contains a v=0 signature whose `r` is an attacker contract.
   5. `checkNSignatures` calls the attacker's `isValidSignature` **before** the GS026 owner check (§1.4). The attacker contract reverts with data beginning `0x1626ba7e`.
   6. The revert bubbles through the Safe's `checkNSignatures`, the CFH, and the Safe fallback (`revert(ptr, returndatasize())`) back to Zodiac. Zodiac sees `success = false` and `returnData[0:4] = 0x1626ba7e`, and accepts `signer = memberSafe`.

   EOA-only members were not affected (`extcodesize == 0 → false`), and neither were Safes without a handler (empty return data). Sources: [Safe help article](https://help.safe.global/articles/3569845223-zodiac-module-vulnerability); [Zodiac security docs](https://docs.zodiac.eco/developers/security); [Verichains analysis](https://blog.verichains.io/p/gnosis-pay-exploit-the-devs-discovered); [Gnosis post-mortem](https://www.gnosis.io/blog/post-mortem-gnosis-pay-vulnerability-exploit).
2. **Default role and signed path.** `execTransactionFromModule` uses `defaultRoles[msg.sender]`. On the signed (relayer) path that is the relayer's default role, while membership is checked for the signer. In practice signed transactions need `execTransactionWithRole`.
3. **`assignRoles` enables the module** as a side effect, and revoking all roles does not disable it. The module can still pass `moduleOnly`, but without roles it fails `NoMembership`.
4. **Clearance.Target** is all-functions on that address (subject only to the Send/DelegateCall options). Clearance.Function with `allowFunction` is wildcarded per selector. Only `scopeFunction` inspects parameters.
5. **Owner and avatar typically coincide** (the Safe owns its Roles modifier). Permission changes then need a Safe transaction at threshold, or any Safe module, including Roles itself if a role is allowed to call Roles' admin functions.
6. **The zero role key is never authorised.**
7. **Custom conditions and unwrappers are external trust delegations.** They are view calls, but can return anything.
8. **Allowances**: `period == 0` means one-shot; `maxRefill = 0` is stored as unlimited; refill is bounded by `maxRefill`. Failure restores the balance.

---

## 4. Zodiac Delay modifier v1.1.0 (`git show v1.1.0:contracts/Delay.sol`, built on zodiac 3.4.1)

### 4.1 State

| Slot | Variable |
|---|---|
| 0–3 | Modifier (`avatar`, `target`, `consumed`, `modules`) |
| 4 | `txCooldown` |
| 5 | `txExpiration` |
| 6 | `txNonce` (next to execute) |
| 7 | `queueNonce` (next free index) |
| 8 | `txHash[nonce]` |
| 9 | `txCreatedAt[nonce]` |

Declared at `Delay.sol:25-32`. The owner is in the OZ namespaced slot. Invariant: `txNonce ≤ queueNonce`.

### 4.2 Entry points

**Setup**: `setUp(abi.encode(owner,avatar,target,cooldown,expiration))` is `initializer` (`:57-85`) and requires:
- avatar ≠ 0;
- target ≠ 0;
- `expiration == 0 ∨ expiration ≥ 60`.

**Owner-only**:
- `setTxCooldown(c)` (`:90-93`, `TxCooldownSet`). It applies **retroactively** to queued transactions, because the check uses the current `txCooldown`.
- `setTxExpiration(e)` (`:99-106`; `e == 0 ∨ e ≥ 60`; `TxExpirationSet`).
- **`setTxNonce(n)`** (`:111-119`), the veto: requires `n > txNonce` and `n ≤ queueNonce`, and emits `TxNonceSet`. This skips (vetoes) every queued transaction with index `< n`. Vetoing is prefix-only: you cannot veto index *k* without also vetoing everything before it.
- Plus the Modifier/Ownable admin functions.

**Module-only (`moduleOnly`, including the signed path in §2)**:
- `execTransactionFromModule` and `…ReturnData` (`:128-168`) store `txHash[queueNonce] = keccak256(abi.encodePacked(to, value, data, operation))` (`:214-221`) and `txCreatedAt[queueNonce] = now`, emit `TransactionAdded(queueNonce, hash, to, value, data, operation)`, and do `queueNonce++`.
- It returns `true` and executes nothing.
- The hash has no chain ID, no instance address, and no nonce in its preimage; the queue index provides uniqueness.

**Permissionless**:
- `executeNextTx(to,value,data,operation)` (`:176-201`):
  1. `txNonce < queueNonce`, else "Transaction queue is empty";
  2. `now − createdAt ≥ txCooldown`, else "Transaction is still in cooldown";
  3. if `txExpiration ≠ 0`: `createdAt + cooldown + expiration ≥ now`, else "Transaction expired";
  4. the hash must match, else "Transaction hashes do not match";
  5. `txNonce++` happens before `exec`;
  6. `require(exec(...))`, else "Module transaction failed". A failure reverts everything, including the nonce bump.
- `skipExpired()` (`:203-212`) advances `txNonce` over expired head entries. It does nothing when `txExpiration == 0`.

### 4.3 Semantics and pitfalls

- **Queue order is strict FIFO.** A head transaction that always fails blocks the queue. If `txExpiration == 0`, this lasts until the owner vetoes it with `setTxNonce`; otherwise until it expires and someone calls `skipExpired`.
- Any enabled Delay module, or anyone holding a module's signature, can **queue arbitrarily many** transactions, including **DelegateCall**. These execute against the target Safe after the cooldown unless the owner vetoes.
- The owner's protection is a **timed veto**: approval by inaction for `txCooldown`, with the window `[createdAt+cooldown, createdAt+cooldown+expiration]`.
- Lowering the cooldown, or `setTxNonce`, are owner actions. If the owner is the avatar Safe, these need Safe-level authority.
- The v1.1.0 `moduleOnly` inherits the ERC-1271 bypass (§3.6.1). It is exploitable when an **enabled Delay module is a Safe with CFH**: the attacker queues arbitrary transactions as that module, and they become executable after the cooldown unless vetoed. This is the Gnosis Pay incident; per the Verichains analysis, the queued USDC.e withdrawals were executed after the delay.
- **HEAD** (`221382ea`, 2026-06-05) rebuilds on zodiac-core 4.0.0-alpha.2 (fixed checker) and adds `execTransactionWithSignature(…, salt, signature)` with `moduleOnlySigned` (`src-delay/contracts/Delay.sol:154-163`).

---

## 5. Abstract actor models (one paragraph each)

**Safe.** A Safe is an account `A` with balance and storage, controlled by a mutable configuration:
- an ordered owner set `O` with threshold `k`, where `1 ≤ k ≤ |O|`;
- a module set `M`;
- an optional transaction-guard veto `G_tx`, and in 1.5.0 a module-guard veto `G_mod`;
- an optional fallback oracle `F`;
- a strictly increasing nonce `n`;
- persistent approval sets `approved[o]` and `signed`.

`A` acts in exactly two ways: it relays a Call (as `msg.sender = A`) or a DelegateCall (arbitrary code over `A`'s entire state, including its code pointer), with arguments `(to, value, data, op)`. A relay is authorised either by:
- (i) a transaction hash `H(chainid, A, to, value, data, op, gas params, n)` approved by `≥ k` distinct current owners, where each owner approves by an ECDSA or eth_sign signature, a stored prior `approveHash`, being the submitter, or (for contract owners) an arbitrary view predicate; subject to `G_tx` not vetoing, and consuming `n`; or
- (ii) a call from any `m ∈ M`, with no signatures or nonce, subject only to `G_mod` (1.5.0).

All configuration changes are relays by `A` to itself. So the authority of `A` is the least fixpoint of "≥k-of-O approvals ∨ any module ∨ any code run via DelegateCall", closed under owners and modules that are themselves such accounts. `F` answers queries on `A`'s behalf (EIP-1271) and passes through `F`'s reverts.

**Zodiac Roles (v2).** A Roles modifier is an owner-administered policy engine `R` that is itself a module of a target account `T`. Principals are `R`'s modules, authenticated by `msg.sender` or by an appended, replay-tracked ECDSA or ERC-1271 signature. Each principal holds a set of role keys. A principal presenting role `r` may relay `(to, value, data, op)` to `T`'s module entry point iff the policy `P_r` accepts it. `P_r` checks: the target clearance (None, Target, or Function); the Send/DelegateCall options; and, for scoped functions, a typed calldata condition tree (logical, comparison, bitmask, array, custom-oracle, allowance nodes). Allowance nodes consume global refilling budgets, debited atomically on success. Owner-registered unwrappers split batched calls into independently checked parts.

**Zodiac Delay.** A Delay modifier is a module of `T` that converts module requests into a FIFO queue of hashed transactions. Any entry may be executed by anyone after `cooldown`, within an optional expiry window. The owner can prefix-veto by advancing the execute pointer, and can change timing parameters retroactively.

---

## 6. Minimal abstract primitives

Each item lists what it models and where it occurs.

**P1. Principal**
- An address-identified actor with kind `EOA(key) | Contract(code)`.
- Contracts may implement view predicates (EIP-1271) and may relay.

**P2. Threshold set approval**: `Thr(O, k, h) ≡ ∃ S ⊆ O, |S| ≥ k, ∀o ∈ S. Approves(o, h)`.
- Distinctness is via a strict order on addresses (GS026).

**P3. Approval modes** (a disjunction for `Approves(o, h)`):
- (a) cryptographic signature: `ECDSA_o(h)` or `ECDSA_o(EIP191(h))`;
- (b) caller-approval: `o = executor` of the current entry point;
- (c) **stored prior approval**: `approved[o] ∋ h`, written earlier by an action of `o` while `o ∈ O`; permanent; re-checked against the current `O`;
- (d) **contract-principal callback**: `isValidSignature_o(h, blob) = MAGIC` under STATICCALL. This needs an explicit treatment of revert data, the ordering "callback before membership check", and the success-flag discipline. Fixed: `success ∧ magic`; buggy Zodiac: `magic(returndata)`.

**P4. Domain-bound one-shot hash**:
- `h = H(chainid, verifier, payload, nonce)`, with a strictly increasing nonce (Safe) or a consumed-set (Zodiac `consumed[signer][h]`, salt).
- Its absence (EIP-1271 messages, `signedMessages`, Delay's hash) is a separate, non-replay-protected approval.

**P5. Relay**:
- `Call(A → to, value, data)`, which carries the identity `msg.sender = A`; and
- **`DelegateCall(A ⇐ code(to), data)`**, which gives arbitrary read/write over all of `A`'s state, including the code pointer (`singleton`) and every authority slot.
- `simulateAndRevert`: DelegateCall with forced revert, so no persistent effect.

**P6. Self-authorisation**:
- Configuration mutators guarded by `caller = A`. Authority over configuration therefore reduces to authority to make `A` relay to itself.

**P7. Module set (bypass capability)**:
- A set `M` such that `m ∈ M` may relay without P2/P4.
- Closed transitively: modules and owners that are themselves accounts contribute their own authority.

**P8. Veto predicate (guard)**:
- Arbitrary external pre-hooks (and post-hooks) over the relay parameters and caller. A revert vetoes.
- It can brick its own removal path.
- Separate hooks per path: transaction guard on the signature path, module guard on the module path (1.5.0+).

**P9. Delegated oracle and forwarder (fallback handler)**:
- Unknown selectors go to `F` via CALL with `caller ‖ calldata`, returning or reverting with `F`'s data verbatim.
- `F` acts as `A`'s EIP-1271 answer.

**P10. Uninitialised-account capture**:
- One-shot `setup` by the first caller while `k = 0`.
- Address commitment to the initializer via CREATE2 salt; optional chain binding.

**P11. Role-based parameter-level calldata policy**:
- `member(r, p)`.
- `clearance(r, to) ∈ {None, Target(opts), Function}`.
- `scope(r, to, sel) ∈ {absent, wildcard(opts), tree(opts)}`.
- A typed ABI decoder (Static, Dynamic, Tuple, Array, Calldata, AbiEncoded).
- Condition algebra: Pass, And, Or, Nor, Matches, ArraySome (v2 as implemented: element 0 only), ArrayEvery, ArraySubset, EqualTo (keccak of the encoding), unsigned and signed comparisons, Bitmask, Custom(oracle), EqualToAvatar.
- Options lattice `{None, Send, DelegateCall, Both}`.

**P12. Budgets**:
- Global keyed allowances `(balance, refill, maxRefill, period, timestamp)` with lazy accrual.
- Per-transaction consumption accumulated across batch entries, debited before execution, restored on inner failure.
- Consumption sources: a parameter word, `msg.value`, or a call count.

**P13. Batch unwrapping**:
- Trusted per-`(to, selector)` decoders that map one call to a list of sub-calls, each checked by P11/P12. The outer call is not checked.
- Obligation: decoder ≡ executor semantics (the `to = 0` and padding cases in §3.5).

**P14. Timelock queue with owner veto**:
- FIFO queue of hashes; `executable(i) ≡ i = head ∧ cooldown ≤ now − t_i ≤ cooldown + expiry`; permissionless execution.
- Owner prefix-veto (`head := n`, with `head < n ≤ tail`), retroactive parameter changes, and head-of-line blocking.

**P15. Ownership (single admin)**:
- An OZ `Ownable` owner of a modifier, holding all admin mutators. Typically the owner is the avatar account itself, which feeds back into P2/P7.
