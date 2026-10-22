# Aave V3: what the setup does not model yet

Shortcomings found while adding Aave V3 (Ethereum Core market, Pool revision 11 = v3.7, token
revision 5): the snapshot and anvil-fork differential (`contracts/README.md`, Snapshots), the
mainnet targets ([aave-v3.md](aave-v3.md)), the model ([aave-v3-model.md](aave-v3-model.md))
and the AToken bytecode proofs (`qedefi/Examples/AaveV3/AToken/`). Ordered by how much they
block an end-to-end statement ("every transaction preserves reserve backing, on the deployed
bytecode").

## What is established

| Layer | Result |
|---|---|
| Semantics vs. mainnet | 364/364 snapshot calls equal `eth_call`; a 25-step supply/borrow/accrue/repay/withdraw/liquidation sequence on an anvil fork equals the interpreter in status, output, 79 logs, 518 slots, balances, nonces and gas used |
| Model (`QEDefi.Aave`) | ray/wad/percentage math exact; indexes monotone; Σ scaled balances = scaled supply for every entry point; backing preserved exactly between accruals, ≤ ~½ wei slack per accrual under `RateSound`; health factor ≥ 1 after borrow/withdraw/transfer, < 1 before a liquidation |
| Bytecode (AToken) | the five Pool-only entry points revert with no effect for any non-Pool caller, also through the aToken proxy (`proxy_poolOnly_noEffect`, composing the proxy's EIP-1967 forwarding summary with the implementation's); views exact; `mint`/`burn` by the Pool change scaled balance and scaled supply by the same amount |
| Findings | exact backing cannot survive accrual (proved counterexample); live WETH and USDC reserves are under-backed by ~1.18 WETH / ~287 USDC against the model's invariant at block 26,243,228 (pre-existing, not reachable by the v3.7 operations modelled) |

## Proof machinery (EvmLogic)

| Gap | Where | Why it matters | Effort |
|---|---|---|---|
| No rule for calls into **unknown code** from a protected frame, and no **reentrancy** into it: every call rule needs a proved callee summary; the nested (any-transaction) machinery allows only the outermost protected frame | `Program/Call.lean` (`WP.call`, `WP.staticcall`), `Program/Nested/Run.lean` (`FrameInv.safe`, `DangerStart`) | flash-loan receivers, underlying tokens, oracles, the rewards controller are arbitrary code; Aave has no reentrancy guard. The AToken proofs take the rewards controller and the underlying's `transfer` as hypotheses (`HandleActionOk`, `TransferOk`) | L |
| **Scale**: largest contract proved before was 5.2 kB | — | Pool 21 kB + five libraries (7–12 kB each) + debt token + strategy; `GenericLogic`'s reserve loop calls the oracle per iteration (loop invariant with calls) | L |
| Storage-chosen, upgradeable call targets: the invariant may only depend on protected accounts, the abstract interpreter knows constants/immutables only | `Nested/Run.lean` (`GoodOk`), `AbsInt/Domain.lean` | aToken/debt token/strategy addresses come from storage; oracle and ACL from the addresses provider; admins can upgrade | M–L |
| `try/catch` violates gas monotonicity's `FailureReverts` | `GasMono/Interface.lean` | `supplyWithPermit`, `repayWithPermit` | M |
| Byte-granular `Field`s only | `Solidity/Layout.lean` | `ReserveConfiguration` bit fields, `UserConfiguration` 2 bits per reserve at a runtime index, `uint120`/`uint128` packing in `_userState` (hand lemmas in the AToken proofs) | S–M |
| ABI: static arguments and strings only | `Solidity/Abi.lean` | `flashLoan`, `multicall(bytes[])`, `getReservesList` | M |
| `pwp_step`'s table not extensible (`EXTCODESIZE`, `CALLDATACOPY`, `RETURNDATACOPY`, calls are stepped by hand); no join combinator for shared tails | `Tactic/WpStep.lean` (`stepLemmasFor`) | every external call site | S |
| Symbolic memory size and gas terms blow up (`wp_generalize_*`, `evm_gas` > 3 min, max recursion); the callee `Halts` gives no upper bound on returned gas | worked around by `wp_abstract`, `access_bounds` (AToken `Tactic.lean`), `maxRecDepth` raised | two sequential external calls force gas ≥ 5·10⁶ hypotheses; proofs of 20–30 s per function | M |

## Models (QEDefi)

| Gap | Why it matters | Effort |
|---|---|---|
| No refinement of the model to the bytecode (only AToken `mint`/`burn` effects match it) | the backing theorem is about the model, not the deployed Pool | L |
| `RateSound` assumed, not proved for `DefaultReserveInterestRateStrategyV2`; false once a backing gap exists (the live reserves) | per-accrual slack bound depends on it | M |
| Not modelled: flash loans, `setUserUseReserveAsCollateral`, `eliminateReserveDeficit` (Umbrella), aToken `transferFrom`/`permit`, eMode (users in category 0), configurator/admin operations, credit delegation checks, liquidation sweeping bad debt of other reserves, events, gas | each is an entry point or state change outside the invariant proofs | M each |
| Oracles are arbitrary per-transaction functions; Chainlink updates, price-cap adapters, L2 sequencer sentinel absent | health-factor statements are relative to the prices of the transaction | M |
| Underlying tokens trusted: only the virtual balance is tracked (no donations, fee-on-transfer, rebasing, upgradeable USDC/stETH) | backing vs. real balance differ (WETH: real balance does not cover the gap either) | M |
| Per-reserve, per-transaction invariants; no time-ordered trace (timestamps, `uint40` truncation, slack accumulation), no keepers or off-chain actors; no protocol-wide solvency across reserves | "for all reachable states" statements | S–M |
| The recorded `deficit` counts as backing (WETH deficit ≈ 52,965 WETH at block 26,243,228) | a stricter invariant without it fails on mainnet today | — |

## Targets and tooling

| Gap | Where | Effort |
|---|---|---|
| Mainnet modules have no `Immutables` structure / `runtimeCodeWith` / code table (immutables are concrete bytes; names hand-written in `immutables.json`) | `scripts/build-contracts.sh` | S |
| Library functions with storage-pointer arguments are absent from ABIs (selectors hand-copied in `librarySelectors.json`); BorrowLogic and FlashLoanLogic not on Sourcify (Blockscout fallback, link offsets hand-written) | `contracts/mainnet/AaveV3*/` | S |
| `genesis.json` mapping keys are addresses only; struct fields opaque in the generated `storageLayout` | `scripts/build-contracts.sh` | S |
| Snapshot discovery follows one call hop per round (no `debug_*` on the free tier): 197 rounds, ~4 min; no incremental re-fetch; positions found by hand from logs (`eth_getLogs` limited to 10 blocks) | `Snapshot/Fetch.lean` | M |
| Sequences need anvil for the block environment of each transaction; gas price 0 (no fees, base fee, typed transactions, EIP-7825 cap); no random generation or shrinking; oracle moved by replacing feed code | `Snapshot/Sequence.lean`, `Snapshot/Fork.lean` | M |
| `difftest` has no Aave family, no fork mode, Cancun only; `Snapshot/Fork.lean` duplicates part of its anvil client | `qedefi/Examples/Differential/` | M |
| No forks before Cancun (history before 2024-03 cannot be replayed); L2 EVM differences not modelled | `EvmLean/Fork.lean`, `Snapshot/Chain.lean` | M–L |
| Not exercised by any test here: `ecrecover` permits, transient storage (weETH's guard), `BLOCKHASH` of fork-mined blocks | — | S |
| Transactions that set EIP-7702 code are excluded from the any-transaction theorems | nested theorems' hypotheses | S |
