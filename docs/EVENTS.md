# Events: the logs of the deployed vault and asset

The refinement theorems of this directory execute the `LOG` instructions but say nothing about
logs. The `Events*.lean` files prove that every state-changing call emits exactly the events of
the model, encoded as EVM logs, in order — including the asset's `Transfer` emitted inside the
vault's `deposit` / `mint` / `withdraw` / `redeem` (a child frame's logs, merged into the
vault's on return). Every theorem holds for every `Crypto` and any immutables, uses only the
standard axioms, and has the hypotheses of the corresponding refinement theorem (or fewer).

## Model (`defi/Defi/ERC4626/Events.lean`)

`Solmate.Event`: `transfer e src dst v` / `approval e owner spender v` (emitter `e` =
`.vault` for the share token, `.asset`), `deposit caller owner assets shares`,
`withdraw caller receiver owner assets shares`. `Solmate.events s op` is the list a call emits
from state `s`, matching Solmate exactly:

| call | events on success |
|---|---|
| `transfer` / asset `transfer` | `Transfer(caller, dst, v)` |
| `transferFrom` / asset `transferFrom` | `Transfer(src, dst, v)` — **no `Approval`** (Solmate does not emit one when spending) |
| `approve` / asset `approve` | `Approval(caller, spender, v)` |
| asset `mint` / `burn` | `Transfer(0, dst, v)` / `Transfer(src, 0, v)` |
| `deposit` / `mint` | asset `Transfer(caller, vault, assets)`, vault `Transfer(0, receiver, shares)`, `Deposit(caller, receiver, assets, shares)` |
| `withdraw` / `redeem` | vault `Transfer(owner, 0, shares)`, `Withdraw(caller, receiver, owner, assets, shares)`, asset `Transfer(vault, receiver, assets)` |

A reverting call emits nothing (`events_eq_nil`). `Solmate.stream s ops` is the event stream of a
sequence of calls (`stream_append`).

## Encoding (`defi/Defi/ERC4626/Logs.lean`, `defi/Examples/Solmate/ERC4626/Events.lean`)

`transferLog token src dst v`, `approvalLog`, `depositLog`, `withdrawLog` (`Defi.ERC4626.Logs`): emitter
address, topics `[signature hash, indexed args left-padded]` (`Word.ofAddress`), data the ABI
words of the unindexed args (`Abi.encodeArgs`). The signature hashes are the bytecode's
constants (`PUSH32` / code-copied), checked with `#guard` against the executable Keccak, so no
hash hypothesis is involved. `Event.toLog vault asset`, `encode vault asset evs` (`Events`).

`EventsPost m L mf o`: the frame ended with success after appending exactly `L`, or reverted
while `L = #[]` (never an exceptional halt). `events_call`: such a frame summary of a top-level
call gives `res.logs = L` for `processMessageCall`. `resumeAfter_eventsPost`: for a nested call,
the caller's logs after the callee are its own followed by `L` (a reverted callee's logs are
dropped).

## Generic facts (`EvmLogic/Solidity/Events.lean`)

`eventLog`, `logEntry_eq_eventLog` (the entry `LOGn` appends, as a memory read), logs through
child calls (`mergeSub_logs`, `resumeAfter_{success,revert,halt}_logs`), substate operations
keep logs (`warmKey_logs`, …), and **`processMessageCall_logs_of_fail`**: every top-level result
with `success = false` has no logs (by analysis of `step`/`run`/`initMachine`, independent of
the code). Reverts therefore need no new symbolic execution.

## Approach

The existing posts do not determine logs: callee summaries (`TransferOk`, …) do not mention
them, and every internal-function summary quantifies the returned substate existentially
(`∃ … sub, m' = m.resumeWith … sub`). Logs are not a function of anything those posts fix, so
the success paths are re-run: each `*_events` / `*_logs` theorem is a **companion** of an existing
theorem — the same symbolic execution script with the postcondition strengthened by the logs
(`event_log d` closes the `LOGn` entry against the expected log; `logs_simp` composes the logs of
summaries). No existing file was edited.

| companion file | companions of |
|---|---|
| `Examples.Solmate.ERC20.Events`, `Examples.Solmate.ERC20.Events`, `Examples.Solmate.ERC20.Events` | `transfer_halts_ok`, `approve_halts`, `transferFrom_halts_ok`, `mint_halts_ok`, `burn_halts_ok` |
| `EventsSharesCode` | `Shares.transfer_ok`, `approve_ok`, `transferFrom_ok` |
| `EventsConvert` | `totalAssets_wp_gas`, `convertToShares_wp_gas`, `previewMint_wp_gas`, `convertToAssets_wp_gas`, `previewWithdraw_wp_gas` (logs unchanged) |
| `Examples.Solmate.ERC4626.EventsInternal` | `assetTransferFrom_halts`, `safeTransferFrom_wp`, `mintShares_wp`, `afterDeposit_wp` |
| `Examples.Solmate.ERC4626.EventsInternal` | `bump_wp`, `burn_wp`, `withdrawSpend_wp`, `redeemSpend_wp`, `safeTransfer_wp` |
| `Examples.Solmate.ERC4626.EventsEntry`, `Examples.Solmate.ERC4626.EventsEntry` | `deposit_refines`, `mint_refines` (refinement post ∧ `EventsPost`) |
| `Examples.Solmate.ERC4626.EventsEntry`, `Examples.Solmate.ERC4626.EventsEntry` | `withdraw_halts`, `redeem_halts` (`OutPostLogs`) |

## Theorems

Frame form (any frame, top level or nested; `EventsPost` against `encode vault asset (…)`):
`assetTransfer_events`, `assetTransferFrom_events`, `assetApprove_events`, `assetMint_events`,
`assetBurn_events` (`Examples.Solmate.ERC20.Events`); `deposit_events`, `mint_events` (`EventsDeposit/Mint`),
`withdraw_events`, `redeem_events` (`EventsEntry`) — the last four also restate the refinement
post. The share functions have only top-level refinement theorems today, hence only top-level
event theorems.

Top-level form (`processMessageCall`, `res.logs = encode vault asset (events (abs ctx.crypto w
vault asset) op)`, both success and revert): `assetTransfer_events_call`, … (`Examples.Solmate.ERC20.Events`),
`Shares.transfer_events_call`, `approve_events_call`, `transferFrom_events_call` (and the
`vaultCall`/`Rep` forms `Shares.transfer_events`, …; `EventsShares`), `deposit_events_call`,
`mint_events_call`, `withdraw_events_call`, `redeem_events_call` (`EventsEntry`).

Trace form (`Examples.Solmate.ERC4626.Invariants.Events`): `OpEventsAt` (the per-call obligation in the shape of
`OpRefinesAt`), `opEvents_all` (every `VCall` kind), `events_agree` (events only read what
`AgreeOn` keeps), `LogTrace` (a `Trace` recording its calls' logs) and **`trace_logs`**: under
`SlotsOk`, the fixed-slot hypothesis and `250000 ≤ minGas`, the concatenated logs of a trace's
calls equal `encode vault asset (Solmate.stream (abs crypto w₀ vault asset) (cs.map VCall.op))`.
Environment steps contribute no logs to `LogTrace` (they may emit logs of other contracts, or
even of the vault/asset in nested calls that do not change their storage; those are outside the
model).
