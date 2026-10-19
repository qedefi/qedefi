# Invariants of the deployed vault under arbitrary transaction sequences

The last layer of the ERC-4626 verification: the model's invariants (`../Vault/`) hold for the
**deployed bytecode** of Solmate `MockERC4626` + `MockERC20` across arbitrary sequences of
transactions by arbitrary callers. Files: `Lift.lean` (generic), `InvariantsAgree.lean`,
`InvariantsPrice.lean` (model side), `InvariantsSystem.lean` (the concrete system),
`InvariantsCalls.lean`, `AssetApproveCall.lean`, `AssetMintCall.lean`, `AssetBurnCall.lean`
(per-call obligations proved today), `Invariants.lean` (headlines), `InvariantsFinal.lean`
(every call kind); for arbitrary transactions with nested calls: `EvmLeanProofs/Program/
NestedExtra*.lean` (generic simulation), `NestedSystem.lean`, `NestedCalls.lean`,
`NestedViews.lean`, `NestedInvariants.lean`, `SharesFrame*.lean` (§6).
Every theorem uses only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

## 1. The concrete system (`InvariantsSystem.lean`)

**States.** Worlds `w` with `Deployed w vault asset`: the compiled vault (any immutables whose
`asset` is `asset`) at `vault`, the compiled `MockERC20` (any immutables) at `asset`, neither a
precompile. The abstraction is `abs crypto w vault asset` (balances, supplies, allowances,
hook counters read through the Solidity layout), for one fixed hash function `crypto`.

**Transitions** — a `Trace crypto vault asset minGas w₀ cs w` is a sequence of:

* **modelled calls** (`CallStep`, one per element of `cs : List VCall`): a top-level message
  call (`processMessageCall`) to the vault or the asset whose calldata ABI-encodes one of
  `deposit`, `mint`, `withdraw`, `redeem`, `transfer`, `transferFrom`, `approve` (vault) or
  `transfer`, `transferFrom`, `approve`, `mint`, `burn` (asset) with **arbitrary arguments**,
  from **any caller** except the vault and the asset themselves (they have code, so cannot be
  transaction senders, EIP-3607), with zero value, `minGas ≤ gas < 2⁶⁴`, any transient storage
  and warm sets, any context with hash `crypto` that is before Prague or carries no EIP-7702
  authorizations, and that **terminates** (`Terminates`: the same result for all large enough
  fuel). Both successful and reverting calls are steps; the next world is the result's world.
  `asset.transfer(vault, D)` is a donation.
* **environment steps** (`EnvStep`): anything leaving the storage *and* code of the vault and
  the asset unchanged — transactions to other contracts that do not reach them, ETH
  transfers (also to the vault/asset), the transaction-level bookkeeping around a message call
  (nonce, gas purchase/refund, fees), block rewards, and every **view call** (the
  `VaultViewsSpec.*_call` theorems show views return the model's values and keep the world;
  `envStep_of_world_eq`).

**Hash hypothesis, once per trace** (`SlotsOk crypto vault Act`), for a finite list `Act` of
actors containing the vault and every address in the trace's calls:

1. `vault ∈ Act`;
2. `BalanceSlotOk` for every actor: its balance slot `keccak(a ‖ 3)` is the hash of no other
   address-keyed preimage `pad(b) ‖ 3`, `pad(b) ‖ 4` (one target vs `2¹⁶¹` candidates), and is
   not slot 2;
3. `AllowanceSlotOk` for every pair of actors: likewise for `keccak(sp ‖ keccak(o ‖ 4))`, plus
   `keccak(o ‖ 4) ≠ 3`, slot ≠ 2;
4. distinct actor pairs have distinct allowance slots (finitely many hashes);
5. no actor's balance slot and no actor pair's allowance slot is 6 or 7 (the hook counters).

All are statements about finitely many hash values (plausible for Keccak), never global
injectivity. The asset's `mint`/`burn` (which write the `totalSupply` slot 2) additionally need
`hk : KeccakAvoids crypto (AddressKeyed [3]) [2]`: no address's balance slot `keccak(a ‖ 3)` is
slot 2 (one target against `2¹⁶⁰` candidates, plausible). It is necessary: for a `Crypto` with
such a collision, writing slot 2 changes that address's balance in the storage view. Because no plausible hypothesis excludes a collision between a *written* balance
slot and the allowance slot of *some* of the `2³²⁰` pairs, the concrete world is related to the
model **up to the allowances of non-actor pairs** (`AgreeOn (ActorPairs Act)`): balances,
supplies, hook counters and all actor allowances are exact.

**Initial state.** `Deployed w₀ vault asset` and `Solmate.Inv (abs crypto w₀ vault asset)`
(both ledgers well formed: balances sum to the supply, which fits 256 bits).

## 2. The generic lifting theorem (`Lift.lean`)

A `System W S O` packs the model `step`, the abstraction `abs`, concrete `call`/`env`
transitions, a concrete well-formedness `Pre`, the model invariant `Inv`, the agreement
`Agree` and per-operation side conditions `Ok`. `System.Refinement σ` is the list of proof
obligations: `Agree` is an equivalence preserving `Inv`; `step` preserves `Inv` and respects
`Agree` on `Ok` operations; every `Ok` call refines its operation in the shape of the
refinement files (`OpRefines`: `match step (abs w) op with | some s' => abs w' ≈ s' |
none => w' = w`) and keeps `Pre`; environment steps keep `Pre` and `abs`.

* `Refinement.lift`: `Reach σ w₀ ops w → (∀ op ∈ ops, Ok op) → Pre w₀ → Inv (abs w₀) →
  Pre w ∧ Inv (abs w) ∧ Agree (abs w) (exec step (abs w₀) ops)`.
* `Refinement.invariant`: any `I` with `I (abs w₀)`, `Inv s → I s → step s op = some s' → I s'`
  and `Agree`-stable holds on `abs w` (`invariant_eq`/`lift_eq`: the `Agree = Eq` forms).
* `Refinement.lift_step`: the call implementing `op` inside `ops₁ ++ op :: ops₂` goes from a
  world `≈ exec ops₁` to a world `≈ stepD (exec ops₁) op` (two-state properties).

Proved by induction on traces, independently of the EVM.

## 3. Instantiation and headline theorems (`Invariants.lean`)

`RefinesFor crypto vault asset minGas Act K` = every call kind admitted by `K` satisfies
`OpRefinesAt`; `refinement` turns it (with `SlotsOk`) into `System.Refinement`.

* **Today** — `refinesFor_now (hmin : 100000 ≤ minGas) hk`, `K = VCall.NotEntry`: every
  modelled call except the four ERC-4626 entry points —
  - vault `transfer`/`transferFrom`/`approve` (`Shares.*_refines`), `InvariantsCalls.lean`;
  - asset `transfer`/`transferFrom` (frame-level `assetTransfer_refines` /
    `assetTransferFrom_refines` lifted to top level by `call_of_halts`), `InvariantsCalls.lean`;
  - asset `approve` (`assetApprove_refines`, `AssetApprove.lean`; always succeeds, world
    `Erc20.approveWorld`), `AssetApproveCall.lean`;
  - asset `mint(dst, v)` / `burn(src, v)`, unrestricted in `MockERC20`, any caller
    (`assetMint_refines` / `assetBurn_refines`: success with worlds `mintWorld` / `burnWorld`
    representing `Token.mint` / `Token.burn`, or `Panic(0x11)` on supply overflow / insufficient
    balance, exactly when the model returns `none`), `AssetMintCall.lean`, `AssetBurnCall.lean`.
    These need `hk`.

  `refinesFor_proven hmin` (`K = VCall.Proven`: the share functions and asset transfers) needs
  no `hk`.
* **After the other work packages** — `refinesFor_all hmin hk (hp : Pending …)`, all kinds.

Headlines (each for any `K` with `RefinesFor`, under `SlotsOk`, from a deployed well-formed
`w₀`, for every trace whose calls are admitted and whose actors are in `Act`; `*_now` =
today's instance `refinesFor_now`: any trace of calls other than the four entry points, under
`SlotsOk` and `hk`):

| theorem | statement (all quantities read from the final world's storage) |
|---|---|
| `lift` | `Deployed w`, `Inv (abs w)`, `abs w ≈ Solmate.exec (abs w₀) (cs.map op)` |
| `invariant` | every model invariant insensitive to non-actor allowances holds on `abs w` |
| `supply_eq_sum`, `_now` | `sload(vault, 2) = Σₐ sload(vault, keccak(a‖3))`, same for the asset |
| `solvent`, `_now` | `Σₐ ⌊shares[a]·T/S⌋ ≤ T` (`T` = vault's asset balance slot, `S` = slot 2) |
| `no_dilution`, `_now` | every user call (`UserOp`) in the trace from a world with shares: `T·S' ≤ T'·S` |
| `price_mono`, `_now` | along a trace of user calls never emptying the vault: `T₀/S₀ ≤ T/S` (ℚ) |
| `donation_attack` | from an empty vault: attacker `deposit(1)`, donation `D`, victim `deposit(a)` ⇒ for `a ≤ D`: `S = 1`, `T = D+1`, attacker holds the share, receiver none; for `D < a ≤ 2D+1`: victim reverted (`S = 1`, `T = D+1`) or got exactly one share with `S = 2`, `T = a+D+1`, `convertToAssets(1) = ⌊(a+D+1)/2⌋` |
| `donation_attack_view` | a top-level `convertToAssets(1)` on that world returns `⌊(a+D+1)/2⌋` |

`UserOp vault op`: not a deposit/mint by the vault, not an asset transfer by the vault, not an
asset `transferFrom`/`burn` from the vault. With top-level calls only the asset `burn(vault, ·)`
(unrestricted in `MockERC20`: the model's "loss") and `transferFrom(vault, …)` are excluded.
`donation_attack` and `no_dilution`/`price_mono` over deposits need the `deposit` (resp.
entry-point) refinement as hypothesis; `no_dilution_now`/`price_mono_now` cover every other
user call, e.g. yield (`asset.mint(vault, ·)`) and burns of other accounts' assets.

## 4. Every call kind is wired

`InvariantsFinal.lean` discharges `RefinesFor … (fun _ => True)` (`refinesFor_all_of`, the
`Pending` obligations from `InvariantsDepositMint.lean` / `InvariantsWithdrawRedeem.lean`) and
states the headlines on the deployed bytecode (`*_deployed`, `minGas = 250000`, fixed-slot
hypothesis `[2, 6, 7]`). Those are about traces of **top-level** calls; §6 removes that
restriction.

## 5. Not covered by the top-level traces of §1–§4 (see §6 for what is now covered)

* **Calls from other contracts (nested frames), reentrancy, reverting routers**: covered by
  §6. Reentrancy into the vault from the asset cannot happen: `MockERC20` makes no calls.
* **Gas.** Calls with less than `minGas` are not steps, neither here nor in §6 (pending, §6.5).
  Fuel is handled exactly (`Terminates`).
* **ETH / value.** Top-level steps carry zero value; §6 proves that calls with value to the
  vault or the asset revert (`vault_value_reverts`, `asset_value_reverts`).
* **Transaction layer.** Steps are `processMessageCall`; the surrounding `processTransaction`
  bookkeeping changes no storage of the vault/asset (stated, not proved; an environment step).
  EIP-7702: contexts are before Prague or carry no authorizations.
* **Unmodelled functions**: `permit` (vault and asset), `name`/`symbol`, `nonces`,
  `DOMAIN_SEPARATOR`, the hook counters, the asset's views other than `balanceOf`, and calldata
  not encoding a function (§6.5).
* **Allowances of non-actor pairs** are only related to the model up to Keccak collisions
  (see §1); every headline is insensitive to them.

## 6. Arbitrary transactions: nested calls, any code, reverting callers

Real usage is contracts (routers, attackers, other protocols) calling the vault and the asset
with arbitrary gas, possibly many times per transaction, possibly reverting afterwards. The
theorems of this section cover a top-level message call **from any account without code to any
code**, and sequences of such transactions.

### 6.1 The machine-level simulation (root package, `EvmLeanProofs/Program/NestedExtra*.lean`)

Generic in a set `P` of *protected* accounts and a property `Good` of worlds that depends only
on their storage and code (`GoodOk`: protected accounts hold code that is not an EIP-7702
designator). Everything else runs arbitrary code.

* `NestedExtraWp`: a weakest-precondition calculus for the instruction monad (`Wp`, simp lemmas
  through `do` blocks).
* `NestedExtraFrame`, `exec_frame`: **the frame condition of every opcode** (one theorem, all
  ~150 opcodes): a successful instruction keeps the frame's identity and created accounts,
  never increases its gas, and keeps the storage and code of every account holding code that
  the frame may not write (`Writable`: the executing account of a non-static frame — `SSTORE`
  needs a non-static frame and writes the executing account; value transfers and `SELFDESTRUCT`
  change balances only; an account with code is never empty, so never deleted; `CREATE` only
  deploys at accounts without code). A requested child is described by `CallOk` (depth, gas
  taken from the caller, and for a non-static child: from a non-static frame, at the caller's
  own account — `CALLCODE`/`DELEGATECALL` — or a `CALL` from the caller's account running the
  callee's own code) / `CreateOk` (the new account holds no code).
* `NestedExtraStep`: `step_cases`, `frameResult_world` (a finished frame hands over its world,
  its world with deposited code, or its snapshot), and **gas conservation** (`step_gas`,
  `stepN_gas`: the total gas of the frame stack never increases; all standard precompiles
  return at most the gas they get, `precompile_gasLeft_le`).
* `NestedExtraRun`: a frame is **dangerous** (`Danger`) if it runs at a protected account and
  is not static. **The simulation invariant** `MInv P Good G m` of a machine whose executing
  frame is not dangerous: the current world is `Good`; every frame of the stack (executing and
  suspended) is not dangerous, has a `Good` rollback snapshot, and does not create a protected
  account; the stack's total gas is `≤ G`; standard precompiles. Rollbacks restore a snapshot,
  and every snapshot was the current world when its frame started, so a revert or out-of-gas
  of **any enclosing frame** — after it called the vault any number of times — restores a
  `Good` world; no log of committed operations is needed.
  - `minv_step`: a step from `MInv` reaches `MInv`, a finished message with a `Good` world, or
    a freshly pushed dangerous frame (`DangerStart`: a `CALL` from an unprotected account
    running the protected account's own code, `Good` snapshot, world equal up to the value
    transfer, gas `≤ G`, depth `≤ 1024`). `DELEGATECALL`/`CALLCODE` *to* vault code run it on the
    caller's storage (not dangerous); `STATICCALL` frames are not dangerous; `CREATE` cannot
    target an account with code.
  - `run_good`: if every dangerous frame reached `Halts` in a `Good` world (a **frame
    summary**), every finished run ends in a `Good` world (dangerous frames are jumped over with
    their summary, `Halts.resume`, gas bounded by `stepN_gas`).
  - `processMessageCall_good`: the same for a top-level message (`TopOk`: depth 0, caller not
    protected — a transaction's sender has no code, EIP-3607 —, a call to a protected account
    runs its code; any target, code, value, calldata, gas `≤ G`), before Prague or without
    authorizations.

### 6.2 The vault instance (`NestedSystem.lean`)

`Prot vault asset` = {vault, asset}; `Good = Follows crypto vault asset Act K w₀`: deployed, and
`abs w ≈ Solmate.exec (abs w₀) (cs.map op)` (`AgreeOn (ActorPairs Act)`) for some list `cs` of
**admitted** calls (`Admitted Act K c`: actors in `Act`, kind admitted by `K`). `goodOk` checks
`GoodOk`. The frame summary in model terms is `FrameOk m`: on success the world is deployed and
`abs mf.world ≈ exec (abs m.world)` of admitted calls (one call for a state-changing function,
none for a view); reverts/halts are free (the snapshot is restored, `follows_of_frameOk`).
`processMessageCall_follows`: any top-level message keeps `Follows` given `FrameOk` of every
dangerous frame it reaches.

### 6.3 Frame summaries (`SharesFrame*.lean`, `NestedCalls.lean`, `NestedViews.lean`)

* **Share-token functions in any frame** (`SharesFrame.lean`): `sharesTransfer_halts_ok/_revert`,
  `sharesTransferFrom_halts_ok/_revert`, `sharesApprove_halts` (fresh frame, any parents,
  calldata as the decoder reads it); model level in `SharesFrameSpec.lean`
  (`sharesTransfer_refines`, `sharesTransferFrom_refines`, `sharesApprove_refines`); views
  `sharesTotalSupply_halts`, `sharesBalanceOf_halts`, `sharesAllowance_halts`,
  `sharesDecimals_halts` (`SharesFrameViews.lean`).
* `frameOk_of_executes`: a frame executing a modelled call (`Executes`: caller, account and
  ABI calldata `CallData c` of a `VCall`) that is funded (`Funded`: no value, `≥ minGas` and
  `< 2⁶⁴` gas, for the vault depth `< 1024` — it calls the asset —, calldata `< 2⁶⁴` bytes), for all twelve call kinds, from the
  frame-level refinement theorems (`deposit_refines`, `mint_refines`, `withdraw_refines`,
  `redeem_refines`, `shares*_refines`, `asset*_refines`).
* `frameOk_view`: the vault's twelve ERC-4626 views, its four share-token views and the asset's
  `balanceOf` (world unchanged).
* `frameOk_value`: calls with value revert (`vault_value_reverts`, `asset_value_reverts`: the
  dispatcher's `CALLVALUE` check), with at least 100 gas.

### 6.4 Headlines (`NestedInvariants.lean`)

A transaction is **covered** (`TxOk vault asset minGas Act K ctx w tr msg`) when every
non-static frame of the vault's or the asset's code it starts (`Reaches`, `VaultStart`) is
`Covered` (value with `≥ 100` gas, or funded and executing a modelled call or a covered view)
and executes an admitted call. **Actors** are thus required per executed call — callers
(routers included), receivers, owners, spenders, sources — not fixed before the transaction.

| theorem | statement |
|---|---|
| `follows_tx`, `follows_trace` | one covered transaction / any `TxTrace` (covered transactions and `EnvStep`s) keeps `Follows w₀` |
| `follows_tx_pending` | the same with the uncovered frames' summaries as hypothesis (`PendingFrames`) |
| `lift_any_tx`, `lift_nested` | deployed, `Inv`, and `abs w ≈ Solmate.exec (abs w₀) (cs.map op)` for some admitted `cs` (the committed calls) |
| `invariant_nested` | every model invariant insensitive to non-actor allowances holds |
| `supply_eq_sum_any_tx`, `supply_eq_sum_nested` | `totalSupply` = Σ balances, shares and asset, read from storage |
| `solvent_any_tx`, `solvent_nested` | `Σₐ ⌊shares[a]·T/S⌋ ≤ T` |
| `price_mono_nested` | with `K = UserOp`: for the committed calls `cs`, unless a prefix empties the vault, `T₀/S₀ ≤ T/S` |

Hypotheses: `hmin : 250000 ≤ minGas`; `hk` (no balance slot is 2, 6, 7); `SlotsOk crypto vault
Act`; `Deployed w₀`, `Inv (abs w₀)`; per transaction `ctx.crypto = crypto`, before Prague or no
authorizations, `TopOk` (sender without code), gas `< 2⁶⁴`, `TxOk`. The donation attack stays a
statement about a top-level trace (`donation_attack_deployed`): with nested calls the committed
calls are only known to exist.

### 6.5 What remains (pending frame summaries, `PendingFrames`)

* **Low gas** (part 2): frames with less than `minGas` gas, the vault at depth 1024 (its call
  into the asset fails), value with `< 100` gas. A frame either succeeds or rolls back; what is
  missing is that a *successful* low-gas frame commits the high-gas outcome. The planned
  argument is a lockstep simulation of the low-gas frame against the same frame with more gas:
  every instruction except `GAS`/`CALL*`/`CREATE*` commutes with adding gas to a successful
  run; in this bytecode every reachable `GAS` is immediately followed by `CALL`/`STATICCALL`
  (offsets 1231, 3437, 3955, 4325 in the vault, 1630 in the asset; the metadata after offset
  5215 is unreachable: no jump destination there), so child frames get monotonically more gas;
  the only divergence is a child call that fails with less gas but succeeds with more, after
  which the frame must fail — a per-call-site fact (the post-call code computes
  `and(…, success)` and reverts) still to be proved for the five call sites.
* **Unmodelled selectors**: `permit` (permit work package; it needs a model operation),
  `name`/`symbol` (strings work package), `nonces`, `DOMAIN_SEPARATOR`, the hook counters, the
  asset's `totalSupply`/`allowance`/`decimals`, unknown selectors and malformed calldata
  (dirty address words, short calldata: solc's decoder reverts — not proved). Views only need
  "success ⇒ world unchanged".
* **Calldata of `2⁶⁴` bytes or more** (impossible within `2⁶⁴` gas: memory expansion).
* **Transaction layer**: `processTransaction` around `processMessageCall` as an `EnvStep`
  (stated, not proved).

Extension points: new model operations (e.g. `permit`) plug in as new `VCall` constructors with
a `frameOk_*` theorem and a `CallData` case; `Follows`/`FrameOk` are parametric in the
admitted-call predicate `K`, and the machine-level simulation is generic in `P` and `Good`.
