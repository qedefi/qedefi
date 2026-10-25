# ERC-4626 verification: technical notes

Notes per component of the Solmate verification ([README](README.md)). Paths are under
`qedefi/Verified/Solmate/` unless stated; theorem names are in the namespace of their
directory (`Verified.Solmate.ERC4626.…`, `Verified.Solmate.ERC20.…`). Every theorem holds
for every `Crypto`, every fork the hypotheses allow, and arbitrary immutables.

## 1. Abstraction (`ERC4626/Abstraction.lean`)

- `Deployed w vault asset`: `w.code vault = SolmateVault.runtimeCodeWith i` with
  `i.asset = asset`, `w.code asset = SolmateAsset.runtimeCodeWith ia`, neither a precompile.
  The canonical deployment is an instance (`deployed_canonical`); neither code is an
  EIP-7702 designator.
- `abs crypto w vault asset : Solmate.State Address`: share and asset ledgers via
  `ERC20.view` (supply slot 2, `balanceOf[a]` at `keccak(a ‖ 3)`, `allowance[o][s]` at
  `keccak(s ‖ keccak(o ‖ 4))`), hook counters at slots 7 and 6. `Address` is finite, so the
  balances form a `Finsupp` with no assumption.
- `Refines crypto w vault asset s` (both ledgers represented as `QEDefi.ERC20.Rep`, counters
  equal) and `refines_iff : Refines … s ↔ s = abs …`. After writes, `RepOn P` keeps
  allowances only for entries whose slot was not written.
- Reading needs **no** hash hypothesis: `abs` is by definition what the code reads. Writes need
  pointwise freshness (`ERC20.BalanceSlotOk`, `ERC20.AllowanceSlotOk`).

## 2. Per-function refinement

Every bytecode theorem is a `WP`/`Halts` statement about **any** machine whose frame has the
stated shape (any parents, depth, world), so it is both a top-level theorem (via
`processMessageCall_of_halts`, the `*_call` theorems: `∃ n, ∀ fuel ≥ n, …`) and a callee
summary (`WP.call`/`WP.staticcall`).

| Component | Theorems |
|---|---|
| Solmate `mulDiv` (internal, `0x0e62`/`0x0e7d`) | `mulDivDown_wp`, `mulDivUp_wp`: result as the model's `mulDivDown`, or `revert(0,0)` exactly when the model returns `none` |
| asset as callee | `balanceOf_halts`, `transfer_halts_ok`/`_revert`, `transferFrom_halts_ok`/`_revert` (exact worlds, gas bounds) |
| internal `totalAssets` and conversions | `totalAssets_wp` (its `STATICCALL` to the asset via `WP.staticcall` + `balanceOf_halts`), `convertToShares_wp`, `convertToAssets_wp`, `previewMint_wp`, `previewWithdraw_wp` |
| the twelve ERC-4626 views | `*_halts` (`Nat` level), `*_refines` (any frame), `*_call` (top level) in `Views.lean`, `ViewsSpec.lean` |
| `deposit`, `mint`, `withdraw`, `redeem` | `deposit_refines`, `mint_refines`, `withdraw_refines`, `redeem_refines` (`Deposit.lean`, `Withdraw.lean`; internals in `SafeTransfer*.lean`, `WithdrawInternal.lean`) |
| share token | `sharesTransfer_refines`, `sharesTransferFrom_refines`, `sharesApprove_refines` and views (`SharesFrame.lean`) |
| asset functions | `assetTransfer_refines`, `assetTransferFrom_refines`, `assetApprove_refines`, `assetMint_refines`, `assetBurn_refines` (`ERC20/`) |

Model relation: each operation of `QEDefi.ERC4626.Solmate` is an `Option` chain whose steps map
one-to-one to these summaries; `some s'` ⇒ the bytecode succeeds and the final storage
represents `s'`, `none` ⇒ the whole call reverts. Hypotheses: `BalanceSlotOk` for every
balance written (caller, receiver, owner, the vault in the asset), `AllowanceSlotOk` for
spent allowances, `Inv` for unchecked additions, `caller ≠ vault` where the model needs it;
views need `60000 ≤ gas < 2⁶⁴`, no value, depth below 1024.

Proof technique: `pwp_steps` on `runtimeCodeWith i` with `Shares.jumpDestsAgree i` in
context and `readBytes_code_asset*` lemmas for the six `PUSH32`s of the `asset` immutable;
internal functions composed with `WP.bind_mono`; asset calls via `WP.call` with the callee
summaries, then `wp_generalize_gas` before continuing.

## 3. Traces of top-level calls (`ERC4626/Invariants/`, `QEDefi/Trace/Lift.lean`)

- `QEDefi.Trace.Lift` is EVM-independent: a `System` packs model `step`, `abs`, concrete call
  and environment transitions, `Inv`, an agreement `Agree` and per-operation side conditions.
  `System.Refinement` lists the per-call obligations (`OpRefines`: `match step (abs w) op with
  | some s' => abs w' ≈ s' | none => w' = w`); `Refinement.lift`, `Refinement.invariant`,
  `Refinement.lift_step` follow by induction on traces.
- `Trace crypto vault asset minGas w₀ cs w` (`System.lean`): modelled calls (`VCall`, twelve
  kinds: vault `deposit`/`mint`/`withdraw`/`redeem`/`transfer`/`transferFrom`/`approve`, asset
  `transfer`/`transferFrom`/`approve`/`mint`/`burn`, arbitrary arguments and callers,
  terminating, successful or reverting) and environment steps (`EnvStep`: anything leaving
  the vault's and asset's storage and code unchanged, including every view call,
  `envStep_of_world_eq`).
- `RefinesFor … K` collects the obligations for the call kinds admitted by `K`;
  `refinesFor_all_of` discharges them all (`Deployed.lean`), giving the `*_deployed`
  headlines. `Invariants/Events.lean`: `trace_logs`, the concatenated logs of a trace equal
  the model's event stream.

## 4. Any transaction: the nested simulation (`ERC4626/Nested/`)

Built on `EvmLogic.Program.Nested` ([proving.md](../proving.md#5-arbitrary-callers-the-nested-simulation-evmlogicprogramnested))
with protected accounts `Prot vault asset` and `Good = Follows crypto vault asset Act K w₀`:
deployed, and `abs w` agrees with the model run of some admitted calls.

- `FrameOk m`: on success the world is deployed and `abs` advanced by the frame's committed
  calls (one per state-changing function, none for a view); reverts and halts are free
  (`follows_of_frameOk`: the snapshot is restored). `processMessageCall_follows` reduces a
  top-level message to `FrameOk` of each vault/asset frame started by other code.
- Frame summaries: `frameOk_of_executes` (all twelve call kinds, from the refinement
  theorems), `frameOk_view` (every view of both contracts, including `name`/`symbol`,
  `nonces`, `DOMAIN_SEPARATOR()` under `DomainOk`), `frameOk_permit`, `frameOk_value` (value ⇒
  revert: `vault_value_reverts`, `asset_value_reverts`), `frameOk_unknown`,
  `frameOk_malformed`.
- **Coverage** (`Coverage.lean`): `covered_of_funded` does a case analysis over the 30 + 14
  selectors (checked against the ABI): every funded frame's calldata is short/unknown
  (`UnknownData`), malformed (`MalformedData`), or decodes (`wellFormed_of`) to a modelled
  call (`Executes`), a view (`ViewData`) or a permit (`PermitData`). `txOk_of` and
  `txOk_direct` (a direct transaction to the vault or asset) give `TxOk`.

## 5. Unknown selectors and malformed calldata

`UnknownSelectors.lean`: calldata shorter than four bytes or with a selector of none of the
contract's functions reverts in the dispatcher (`vault_unknown_reverts`,
`vault_short_reverts`, `asset_*`), by symbolic execution of the whole selector tree for a
symbolic selector, with at least 1000 gas. `Malformed.lean` (both contracts): a known
selector whose arguments are too short, or an `address` argument with dirty high bytes,
reverts (`vault_malformed_reverts`, `asset_malformed_reverts`, one lemma per function and
address argument), with at least 2000 gas.

## 6. Events

Model (`QEDefi/ERC4626/Events.lean`): `Solmate.events s op` lists exactly what Solmate emits:
`Transfer`/`Approval` of either token (no `Approval` when `transferFrom` spends an
allowance), `Transfer` from/to 0 for asset `mint`/`burn`; `deposit`/`mint` emit the asset's
`Transfer(caller, vault, assets)`, the share `Transfer(0, receiver, shares)` and
`Deposit`; `withdraw`/`redeem` emit the share burn, `Withdraw` and the asset's
`Transfer(vault, receiver, assets)`. Reverting calls emit nothing (`events_eq_nil`);
`Solmate.stream` concatenates (`stream_append`).

Encoding (`QEDefi/ERC4626/Logs.lean`): `transferLog`, `approvalLog`, `depositLog`,
`withdrawLog`; topic hashes are the bytecode's constants, `#guard`-checked against Keccak,
so no hash hypothesis. `EventsPost`: success after appending exactly the expected logs, or a
revert with none; `processMessageCall_logs_of_fail` makes reverts free. Theorems are
*companions* of the refinement theorems (same symbolic execution with a stronger post):
`assetTransfer_events`, … (`ERC20/Events.lean`), `deposit_events`, `mint_events`,
`withdraw_events`, `redeem_events` and their `*_events_call` forms (`ERC4626/EventsEntry.lean`),
share-token `transfer_events_call` etc. (`EventsShares.lean`).

## 7. `permit`, `nonces`, `DOMAIN_SEPARATOR()`

Model (`QEDefi/ERC20/Permit.lean`): `PermitToken` = ledger + nonces; `permit` approves and bumps
the nonce modulo `2²⁵⁶` iff a validity predicate holds.

Bytecode (`ERC20/Permit.lean`, `ERC4626/Permit.lean`, `ERC4626/PermitSpec.lean`):
`PermitValid … nonce := v < 256 ∧ timestamp ≤ deadline ∧ SigOk …`, where `SigOk` says the
owner is non-zero and `ecrecover` of the EIP-712 digest (computed with `crypto.keccak256`;
type hashes are the code's literals) returns the owner. `asset_permit_halts`,
`vault_permit_halts`: success with `permitWorld` and one `Approval` log **iff**
`PermitValid` at the stored nonce, else revert; `*_permit_refines`, `*_permit_call`,
`*_domainSeparator_call`, `*_nonces_call`. `domainSeparator` is the immutable on the
deployment chain, else recomputed from the stored name. Precompile call:
`WP.staticcall_ecrecover` (`EvmLogic/Program/PrecompileCall.lean`).

Assumptions: standard precompiles, `0x01` not delegated, depth below 1024, no value,
`100000 ≤ gas < 2⁶⁴`, `DomainCase` (deployment chain or a name under 32 bytes). Nothing
cryptographic is claimed: `SigUnforgeable crypto Signed` fixes the shape of ECDSA
unforgeability for users who want to add it (`signed_of_sigOk`); no theorem uses it.

In the any-transaction theorems a successful permit **commits the owner's approval**: the
nonce write is invisible to `abs` under `NonceSlotOk` (`agree_permitWorld_vault`,
`agree_permitWorld_asset`), so no nonce is added to the model. Top-level traces have no
`permit` `VCall`, since its success depends on nonce, timestamp and chain id, which the
abstraction does not hold.

## 8. `name()` and `symbol()`

`stringAt crypto w a p` (`EvmLogic/Solidity/Strings.lean`) decodes a Solidity string slot as
the getter reads it: short form in the slot, long form at `keccak256(p) + j`, `none` when
solc's length check panics. `vaultName_refines`, `vaultSymbol_refines`, `assetName_refines`,
`assetSymbol_refines` (any frame) and `*_call` (top level) return `Abi.encodeString s` for
**every** storable string; `*_canonical` specialise to the deployed names. Gas:
`Str.getterGas L = 8000 + 2400⌈L/32⌉ + memoryCost(256 + 64⌈L/32⌉)`. No Keccak hypothesis
(reads only). The long-string copy loop is proved with `WP.loop_nat` (`vaultCopyLoop_wp`);
`MCOPY` steps use the `pwp_msteps`/`psol_msteps` tactics.

## 9. Any gas and any depth (`ERC4626/LowGas/`)

The generic lockstep (`EvmLogic/GasMono/`) needs, per code, `GasFeedsCall`, `RegionOk` and
`FailureReverts` at each call return point. `LowGas/Code.lean` proves them for arbitrary
immutables (`vault_gasFeedsCall`, `vault_regionOk`, `vault_callReturnPoints`,
`vault_failureReverts`, `asset_*`):

| Code | Region end | Return points | Call there |
|---|---|---|---|
| vault | 5216 | 1233 | `asset.balanceOf(this)` (`totalAssets`, `STATICCALL`) |
| | | 3439 | `ecrecover` in `permit` (`STATICCALL` to `0x01`) |
| | | 3957 | `safeTransferFrom` in `deposit`/`mint` (`CALL`) |
| | | 4327 | `safeTransfer` in `withdraw`/`redeem` (`CALL`) |
| asset | 2838 | 1632 | `ecrecover` in `permit` |

At each return point a failed call (flag 0) leads to a revert: solc's bubble-revert for
high-level calls and `ecrecover`, and `require(success, "TRANSFER(_FROM)_FAILED")` in
`SafeTransferLib`, whose masked condition does not depend on the return data. Patching
immutables only changes `PUSH32` immediates, which the instruction scan skips, so the facts
are decided on the canonical code (`insns_vault`, `insns_asset`).

**Call targets** (`LowGas/Targets.lean`): the certified abstract interpreter explores the
vault (6618 abstract states over 3304 instructions) and asset (2964 over 1921) in the kernel
(`vault_certify`, `asset_certify`), proving every jump resolved, no reachable `CREATE`, and
every call to the `asset` immutable or `0x01` (vault) / `0x01` only (asset):
`vaultCallsAsset`, `assetCallsPrecompile`.

**Transfer** (`LowGas/Frames.lean`, `AnyGas.lean`): `frameOk_of_topBump` moves a frame
summary from more gas to less (premise `EcrecoverOk`: `0x01` not delegated);
`frameOk_of_depth` from one level up to depth 1024 (`depth_lockstep`). `CoveredAnyGas` =
covered with its own gas, with some more gas (`CoveredAtSomeGas`), or one level up
(`CoveredAtLimit`); `txOkAnyGas_of` derives `TxOkAnyGas` without gas or depth conditions,
and `txTraceAnyGas_of_txTrace` shows the `minGas` theorems are special cases.

## Extending

New model operations plug in as `VCall` constructors with a `frameOk_*` theorem and a
`CallData` case, or, like `permit`, as frames committing an existing `VCall` (a `Covered`
disjunct and a `FrameAdmitted` clause). `Follows`/`FrameOk` are parametric in the admitted-call
predicate `K`; the machine-level simulation is generic in the protected set and `Good`.
