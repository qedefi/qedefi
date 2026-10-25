# Case study: verifying ERC-4626 vaults

Theorems about the **deployed bytecode** of a real ERC-4626 vault, stated against an abstract
Mathlib model of the vault, with the economic properties proved on the model and lifted to
the bytecode for arbitrary transactions. Every theorem holds for every `Crypto` and uses only
`propext`, `Classical.choice`, `Quot.sound`.

See also: [properties.md](properties.md) (the property catalogue),
[details.md](details.md) (technical notes per component),
[contracts/README.md](../../contracts/README.md) (pinned sources, artifacts, difftest).

## Targets

| Target | Asset | Vault | Verified at |
|---|---|---|---|
| Solmate @ `89365b88` | `MockERC20` | `MockERC4626` (`totalAssets = asset.balanceOf(this)`) | model **and** bytecode |
| OpenZeppelin v5.7.0 | `ERC20Mock` | `OzVault` (stock `ERC4626`, decimals offset δ = 0) | model (every δ), difftest, a16z suite |

Both compiled with solc 0.8.28 (optimizer 200 runs, Cancun, no via-IR); the artifacts are
committed, so proofs never depend on a local compiler. Bytecode theorems hold for **any
immutables** (`runtimeCodeWith i`: any asset address, chain id, domain separator, decimals).

## Pipeline

```
 EIP-4626, a16z erc4626-tests, crytic/properties
        │ formalised as
        ▼
 qedefi/QEDefi/ERC4626    models Solmate.State, Oz.State; properties, inflation theorems
        ▲ refinement: each external function of the bytecode implements its model
        │ operation, or reverts exactly when the model returns none
 qedefi/Verified/Solmate per-function WP/Halts summaries of the compiled vault and asset
        ▲
 EvmLogic               step lemmas, frame-local logic, calls, Solidity layer, GasMono, AbsInt
        ▲
 contracts/             pinned sources → solc → artifacts → generated Lean constants
```

1. **Model** (`QEDefi.ERC4626.Solmate`, `QEDefi.ERC4626.Oz`, over `QEDefi.ERC20.Token`): `Option`-valued
   operations (`none` = revert) mirroring the Solidity statement by statement, including
   Solmate's `mulDivDown`/`mulDivUp` overflow reverts, `ZERO_SHARES`/`ZERO_ASSETS`, checked
   and unchecked arithmetic, and the asset's own `mint`/`burn`/`transfer` (yield, losses,
   donations). Invariant `Solmate.Inv`: both ledgers well formed (Σ balances = supply < 2²⁵⁶).
2. **Abstraction** (`Verified/Solmate/ERC4626/Abstraction.lean`): `abs crypto w vault asset`
   reads both ledgers and the hook counters through the storage layout. Reading needs no hash
   hypothesis.
3. **Refinement**: one theorem per external function (`deposit_refines`, `mint_refines`,
   `withdraw_refines`, `redeem_refines`, the share-token and asset functions, all views,
   `permit`, `name`/`symbol`, events), for any frame (top level or called by other code).
4. **Invariants on traces** (`QEDefi.Trace.Lift`, EVM-independent): per-call refinement lifts to
   arbitrary sequences of calls; model invariants transfer to the bytecode.
5. **Any transaction, any gas** (`EvmLogic.Program.Nested`, `EvmLogic.GasMono`,
   `EvmLogic.AbsInt`): arbitrary code calling the vault at any depth and gas.

## Headline theorems

Namespaces `Verified.Solmate.ERC4626.Invariants` (top-level traces),
`.Nested` (any transaction), `.LowGas` (any gas). Quantities are read from storage:
`S` = share `totalSupply` (slot 2), `T` = the vault's balance slot in the asset.

| Statement | Top-level traces (`minGas ≥ 250000`) | Any transaction (`minGas ≥ 250000`) | Any transaction, any gas and depth |
|---|---|---|---|
| model simulation: `abs w ≈ Solmate.exec (abs w₀) cs` | `lift` | `lift_any_tx`, `lift_nested` | `lift_any_tx_anyGas`, `lift_nested_anyGas` |
| every model invariant holds | `invariant` | `invariant_any_tx`, `invariant_nested` | `invariant_any_tx_anyGas`, `invariant_nested_anyGas` |
| `totalSupply` = Σ `balanceOf`, shares and asset | `supply_eq_sum_deployed` | `supply_eq_sum_any_tx`, `supply_eq_sum_nested` | `supply_eq_sum_any_tx_anyGas`, `supply_eq_sum_nested_anyGas` |
| solvency `Σₐ ⌊shares[a]·T/S⌋ ≤ T` | `solvent_deployed` | `solvent_any_tx`, `solvent_nested` | `solvent_any_tx_anyGas`, `solvent_nested_anyGas` |
| no dilution: each user call from a world with shares has `T·S' ≤ T'·S` | `no_dilution_deployed` | | |
| price monotone: `T₀/S₀ ≤ T/S` over user calls not emptying the vault | `price_mono_deployed` | `price_mono_any_tx`, `price_mono_nested` | `price_mono_any_tx_anyGas`, `price_mono_nested_anyGas` |
| first-depositor attack as the model predicts | `donation_attack_deployed` | | |

`*_any_tx`: one transaction; `*_nested`: a sequence of transactions and environment steps.
`lift` and `invariant` are stated for any `RefinesFor` instance; `refinesFor_all_of`
provides it for every call kind, and the `*_deployed` theorems use it.
`donation_attack_deployed`: from an empty vault, attacker `deposit(1)`, donation `D`, victim
`deposit(a)`; for `a ≤ D` the attacker holds the only share and `T = D + 1`; for
`D < a ≤ 2D + 1` the victim either reverted or got exactly one share worth `⌊(a+D+1)/2⌋`.

`UserOp vault op` excludes only operations by or debiting the vault itself (a deposit/mint
or asset transfer *by* the vault, an asset `transferFrom`/`burn` *from* it); asset
`burn(vault, ·)` is the model's "loss" and lowers the price.

### Whole transactions and valid blocks

The columns above run over top-level `processMessageCall`s and assumed environment steps. The
same statements hold over the real transaction function `Tx.process` (any type, EIP-7702
included) and the real block function `Block.stateTransition`, with **no environment step**
(`Verified/Solmate/ERC4626/Process.lean`, `Blocks.lean`, namespace `.Nested`):

| Statement | Sequences of transactions (`ProcessTrace`) | Chains of valid blocks (`CoveredChain`) |
|---|---|---|
| `Follows` is kept | `follows_process_anyGas`, `follows_process`, `follows_processTrace` | `follows_stateTransition`, `follows_coveredChain` |
| model simulation | `lift_processTrace` | `lift_coveredChain` |
| every model invariant holds | `invariant_processTrace` | `invariant_coveredChain` |
| `totalSupply` = Σ `balanceOf` | `supply_eq_sum_process`, `supply_eq_sum_processTrace` | `supply_eq_sum_coveredChain` |
| solvency | `solvent_process`, `solvent_processTrace` | `solvent_coveredChain` |
| price monotone | `price_mono_processTrace` | `price_mono_coveredChain` |

- The prefix (nonce, fee purchase) and suffix (refund, coinbase reward, `SELFDESTRUCT`
  deletions, EIP-161 clean-up) of a transaction are proved to keep the vault's and the asset's
  storage and code (`process_envSteps`: the old `EnvStep`s, derived); `TopOk` and the message's
  context are derived from `check` (EIP-3607).
- Coverage is the any-gas one, stated for the transaction's own message in its prefix world
  (`TxCoveredAnyGas`; `TxCovered` with `TxOk` and `minGas ≥ 250000` implies it).
- Gas: `GasCapped fork gasAvail` — from Osaka EIP-7825 caps `tx.gas` at `2²⁴`; before Osaka
  nothing in `validate`/`check` bounds `tx.gas` except the block gas still available, so the
  transaction theorems take `gasAvail < 2⁶⁴`, which every valid block gives (EIP-1985,
  `gasLimit_envOf_le`).
- `ProcessTrace` is a sub-relation of `EvmLogic.Tx.Steps` (`ProcessTrace.steps`);
  `CoveredChain` of `EvmLogic.Chain.Applies` (`CoveredChain.applies`). `BlockPreserves` cannot
  be used as is: it asks the obligation of *every* transaction, and a transaction committing a
  call by a non-actor is not admitted. So `BlockCovered` asks coverage of the transactions
  (`TxsCovered`) and system calls (`SysCovered`, vacuous for system contracts that call no
  other contract) the block actually runs, at the world each runs in. Withdrawals need
  nothing. Extra hypothesis: `SYSTEM_ADDRESS` is neither the vault nor the asset
  (`not_prot_systemAddress` for the canonical deployment).

## Hypotheses and exclusions

Every hypothesis is an explicit argument; none is an axiom. The any-gas theorems take:

- **`hk : KeccakAvoids crypto (AddressKeyed [3]) [2, 6, 7]`**: no address's balance slot
  `keccak(a ‖ 3)` is slot 2 (`totalSupply`), 6 or 7 (hook counters). Three targets against
  `2¹⁶⁰` candidates; needed because a `Crypto` with such a collision really breaks the ledger
  view when `mint`/`burn` write slot 2.
- **`hs : SlotsOk crypto vault Act`** for a finite list `Act` of actors containing the vault:
  each actor's balance slot and each actor pair's allowance slot is fresh among the
  address-keyed preimages (`ERC20.BalanceSlotOk`, `ERC20.AllowanceSlotOk`), distinct actor
  pairs have distinct allowance slots, and none of these slots is 6 or 7. Finitely many hash
  values; never global injectivity (false for every `Crypto`). Because no plausible
  hypothesis rules out a written balance slot colliding with the allowance slot of *some* of
  the `2³²⁰` pairs, the world agrees with the model **up to allowances of non-actor pairs**
  (`AgreeOn (ActorPairs Act)`); every headline is insensitive to them.
- **`Deployed w₀ vault asset`** (the compiled vault, with `asset` as its immutable, and the
  compiled `MockERC20`, any other immutables, neither a precompile) and
  **`Solmate.Inv (abs crypto w₀ vault asset)`**.
- Per transaction: `ctx.crypto = crypto`; **no EIP-7702 authorizations** (or a fork before
  Prague); `TopOk`: depth 0, the sender is neither the vault nor the asset (senders have no
  code, EIP-3607), a call to them runs their code; message gas `< 2⁶⁴`; any result
  (`processMessageCall fuel … = .ok r`, any fuel).
- **`TxOkAnyGas`**, discharged by `txOkAnyGas_of` from: `0x01` (ecrecover) holds no EIP-7702
  designator before the transaction (always true before Prague), and every vault/asset frame
  started by other code either carries value (it reverts) or has calldata `< 2⁶⁴` bytes and
  `CoverOkAnyGas` — the stored `name`/`symbol` getter needs `< 2⁶⁴` gas, and
  `DOMAIN_SEPARATOR()`/`permit` run in a `DomainOk` case (on the token's deployment chain, or
  with a name shorter than 32 bytes; both canonical names are) — and the model calls it
  commits are admitted: their actors (callers, routers included, receivers, owners,
  spenders) are in `Act`, and for a `permit` the owner's nonce slot is fresh
  (`NonceSlotOk`). No gas and no depth condition.

The `*_any_tx`/`*_nested` theorems additionally take `250000 ≤ minGas` and `TxOk` (every such
frame has at least `minGas` gas and, for the vault, depth below 1024); the top-level-trace
theorems take `Trace` steps: zero-value top-level calls to a modelled function with any
arguments, any caller other than the vault and asset, `minGas ≤ gas < 2⁶⁴`, that terminate
(`Terminates`), plus environment steps that leave the vault's and asset's storage and code
unchanged.

**Not covered.**

- `DOMAIN_SEPARATOR()` and `permit` on a chain other than the token's deployment chain with a
  name of 32 bytes or more (solc's out-of-place string encoder is not verified).
- `0x01` delegated by EIP-7702 (nobody holds its key); calldata of `2⁶⁴` bytes or more
  (impossible within `2⁶⁴` gas); a stored `name`/`symbol` whose getter needs `2⁶⁴` gas
  (slots 0–1 are written only by the constructor).
- The transaction layer around `processMessageCall` (nonce, gas purchase and refund, fees) is
  an environment step: it changes no storage of the vault or asset, stated but not proved.
- Signature unforgeability: `permit` theorems say exactly when a permit succeeds in terms of
  `crypto.ecrecover`; that only the owner can sign is *not* claimed (`SigUnforgeable` is
  provided as an optional hypothesis, unused).
- The donation-attack theorem is stated for top-level traces; with nested calls the committed
  calls are only known to exist.
- OpenZeppelin's vault is verified at the model level only.

## Findings

**Solmate deviates from EIP-4626 and the a16z/crytic properties** (model theorems, see
[properties.md](properties.md)):

- `maxWithdraw` reverts when `balanceOf[owner]·totalAssets ≥ 2²⁵⁶`
  (`maxWithdraw_reverts_of_overflow`); the a16z suite also finds this on the compiled contract
  (`test_maxWithdraw`, 25 / 26 pass; OpenZeppelin passes 26 / 26).
- After a total loss (`S > 0 = T`): `convertToShares` reverts on every input, every
  `deposit` reverts while `maxDeposit = 2²⁵⁶−1`, and `previewMint` is 0 (shares are free).
- `maxRedeem` can be unredeemable (`ZERO_ASSETS`) when `balance·T < S`.
- With `S = 0 < T` the round trips `deposit→redeem` and `mint→redeem` fail: the first
  depositor captures earlier donations or yield. All eight a16z round trips hold when `S > 0`.

**Inflation (donation) attack, quantified.**

- Solmate: if the attacker holds all shares, profit equals the victim's loss, **`P = L`**
  (`solmate_donation_attack_all_shares`). After `deposit(1)` + donation `D`, every deposit
  `≤ D` reverts (`ZERO_SHARES`) and deposits in `(D, 2D+1]` mint one share, losing up to
  ~25 % (`solmate_attack_victim_one_share`).
- OpenZeppelin(δ), `k = 10^δ`: the attacker's profit is `P·(S+k) ≤ T + 1 − (k−1)·D`
  (`oz_profit_bound`), and inflicting a loss `L` costs more than `k·L − k·(T+1)/(S+k)`
  (`oz_cost_bound`). In crytic's setting the victim loses `< (3/4)·a/10^δ`
  (`crytic_inflation_bound`): below crytic's 0.1 % threshold for `δ ≥ 3`; at the pinned
  `δ = 0` griefing is possible but not profitable.
- Concretely (difftest, both implementations agree with anvil): alice deposits 1 wei,
  donates 10¹⁸, bob deposits 2·10¹⁸ − 1, alice redeems. On Solmate alice ends with 1.5·10¹⁸
  (profit ≈ 0.5·10¹⁸); on OpenZeppelin with 0.6·10¹⁸ (loss ≈ 0.4·10¹⁸).

## Files

| Path | Contents |
|---|---|
| `qedefi/QEDefi/Math/Arith.lean` | `mulDivDown`, `mulDivUp`, `ozMulDiv`; round-trip inequalities |
| `qedefi/QEDefi/ERC20/` | `Token` ledgers, `PermitToken`, word-level representation `Rep`/`RepOn` |
| `qedefi/QEDefi/ERC4626/` | `Solmate`, `Oz` models; `SolmateProps`, `OzProps`, `MoreProps`, `Inflation`, `Witnesses`; `Events`, `Logs`; `Agree`, `Price` |
| `qedefi/QEDefi/Trace/Lift.lean` | generic lifting of per-call refinement to traces |
| `qedefi/Verified/Solmate/Contracts/` | generated bytecode constants, immutables, deployment |
| `qedefi/Verified/Solmate/ERC20/` | asset: `balanceOf`, `transfer(From)`, `approve`, `mint`/`burn`, `permit`, strings, events, malformed calldata |
| `qedefi/Verified/Solmate/ERC4626/` | vault: `MulDiv`, `Convert`, `Views`, `Deposit`, `Withdraw`, shares, `permit`, strings, events, `UnknownSelectors`, `Malformed` |
| `…/ERC4626/Invariants/` | top-level traces: `System`, `Deployed`, `Events` (`trace_logs`) |
| `…/ERC4626/Nested/` | any transaction: `System`, `Calls`, `Views`, `Permit`, `Coverage`, `Invariants` |
| `…/ERC4626/LowGas/` | any gas: `Code`, `Targets`, `Frames`, `AnyGas` |
| `…/ERC4626/Process.lean`, `Blocks.lean` | whole transactions (`Tx.process`, EIP-7702 included) and chains of valid blocks (`Block.stateTransition`) |
