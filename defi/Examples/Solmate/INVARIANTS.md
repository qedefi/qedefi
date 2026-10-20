# Invariants of the deployed vault under arbitrary transaction sequences

The last layer of the ERC-4626 verification: the model's invariants (`../Vault/`) hold for the
**deployed bytecode** of Solmate `MockERC4626` + `MockERC20` across arbitrary sequences of
transactions by arbitrary callers. Files: `Lift.lean` (generic), `InvariantsAgree.lean`,
`InvariantsPrice.lean` (model side), `InvariantsSystem.lean` (the concrete system),
`InvariantsCalls.lean`, `AssetApproveCall.lean`, `AssetMintCall.lean`, `AssetBurnCall.lean`
(per-call obligations proved today), `Invariants.lean` (headlines), `InvariantsFinal.lean`
(every call kind); for arbitrary transactions with nested calls: `EvmLeanProofs/Program/
NestedExtra*.lean` (generic simulation), `NestedSystem.lean`, `NestedCalls.lean`,
`NestedViews.lean`, `NestedPermit.lean`, `NestedInvariants.lean`, `NestedCoverage.lean`,
`SharesFrame*.lean`, `ViewsRest.lean`, `UnknownSelectors.lean`, `Malformed*.lean` (§6); for any
gas and any depth: `LowGas*.lean` with `EvmLeanProofs/Program/GasMono/` and
`EvmLeanProofs/Program/AbsInt/` (§6.5).
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
* **Gas.** Calls with less than `minGas` are not steps here; §6.5 removes the gas requirement
  for arbitrary transactions (`*_anyGas`). Fuel is handled exactly (`Terminates`).
* **ETH / value.** Top-level steps carry zero value; §6 proves that calls with value to the
  vault or the asset revert (`vault_value_reverts`, `asset_value_reverts`).
* **Transaction layer.** Steps are `processMessageCall`; the surrounding `processTransaction`
  bookkeeping changes no storage of the vault/asset (stated, not proved; an environment step).
  EIP-7702: contexts are before Prague or carry no authorizations.
* **Unmodelled functions** in the top-level traces: `permit` (vault and asset), `name`/`symbol`,
  `nonces`, `DOMAIN_SEPARATOR`, the hook counters, the asset's views other than `balanceOf`,
  and calldata not encoding a function. All of these are covered by §6 (which includes direct
  top-level transactions, `txOk_direct`), except the cases listed in §6.6. `permit` is not
  added to the top-level `VCall`s: their per-call obligation `OpRefinesAt` relates a call to
  *one* model operation from the abstraction alone, and whether a permit succeeds depends on
  the nonce, the block timestamp and the chain id, which the abstraction does not hold (§6.3).
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
* `NestedExtraGas`: `exec_bump` (gas monotonicity of every gas-oblivious opcode, §6.5).
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
* `frameOk_view` (`NestedViews.lean`, world unchanged): **every view of both contracts** —
  the vault's twelve ERC-4626 views, its share-token views `totalSupply`, `balanceOf`,
  `allowance`, `decimals`, its hook counters `beforeWithdrawHookCalledCounter`,
  `afterDepositHookCalledCounter` (`ViewsRest.lean`) and `nonces` (`PermitVaultDS.lean`); the
  asset's `balanceOf`, `totalSupply`, `allowance`, `decimals` (`ViewsRest.lean`) and `nonces`;
  for both tokens `name()`/`symbol()` (`Strings*Spec.lean`, with the gas the stored string's
  length needs, `Str.getterGas`: long strings cost more than `minGas` may cover) and
  `DOMAIN_SEPARATOR()` (`Permit*DS.lean`) in the cases `DomainOk` admits — `block.chainid` is
  the token's deployment chain id (immutable), or its name is stored in short form (< 32
  bytes; both canonical names are). **Not covered**: `DOMAIN_SEPARATOR()` on another chain
  with a name of 32 bytes or more (the out-of-place string encoder is not verified).
* `frameOk_permit` (`NestedPermit.lean`): `permit(owner, spender, value, deadline, v, r, s)` of
  either token (`PermitData`, calldata as the decoder reads it), see below.
* `frameOk_value`: calls with value revert (`vault_value_reverts`, `asset_value_reverts`: the
  dispatcher's `CALLVALUE` check), with at least 100 gas.
* `frameOk_unknown` (`UnknownSelectors.lean`): calldata shorter than four bytes, or a selector
  that is none of the contract's functions (`vaultSelectors`, `assetSelectors`, checked
  against the ABI's `SolmateVault.selectors` / `SolmateAsset.selectors`), reverts in the
  dispatcher (`vault_unknown_reverts`, `vault_short_reverts`, `asset_*`: symbolic execution of
  the whole selector tree for a symbolic selector), with at least 1000 gas.
* `frameOk_malformed` (`Malformed*.lean`): the selector of a function with arguments but
  calldata malformed for its ABI decoder (`MalformedData`: fewer argument words than the
  function takes, or an `address` argument with dirty high bytes after clean ones) reverts
  (`vault_<f>_short`, `vault_<f>_dirty<j>`, `asset_*`, one theorem per function and address
  argument, dispatched by `vault_malformed_reverts` / `asset_malformed_reverts` over the
  function shapes `vaultArgShapes` / `assetArgShapes`), with at least 2000 gas.
* **Every calldata is accounted for** (`NestedCoverage.lean`, `covered_of_funded`): a funded
  frame of either contract is `Covered` whatever its calldata, under `CoverOk` — gas for the
  stored `name`/`symbol` string, `DomainOk` for `DOMAIN_SEPARATOR()`, `PermitFrame` for
  `permit`. The proof is a case analysis over the 30 + 14 selectors (`vaultSelectors`,
  `assetSelectors`, checked against the ABI): short or unknown → `UnknownData`; malformed →
  `MalformedData`; otherwise the arguments decode (`wellFormed_of`: all words present, every
  `address` clean) to a modelled call (`Executes`), a view (`ViewData`) or a permit
  (`PermitData`). `txOk_of` turns it into a simple sufficient condition for `TxOk`: every frame
  of the vault or the asset started by other code carries value with `≥ 100` gas or is funded
  with `CoverOk`, and its committed calls are admitted.

**`permit` as a modelled call.** The abstraction has no nonces and no invariant mentions them,
so they are not added to it. Instead (`NestedPermit.lean`):

* the nonce write is **invisible to `abs`**: under `NonceSlotOk crypto Act owner` — the owner's
  nonce slot `keccak(owner ‖ 5)` is fresh among the address-keyed preimages of slots 3, 4, 5
  (one target against `3 · 2¹⁶⁰` candidates; so it is no balance slot), is not slot 2, 6 or 7,
  and is no actor pair's allowance slot (finitely many hashes) — `abs (permitWorld w token
  owner spender value)` agrees (up to non-actor allowances) with the model's `approve(owner →
  spender, value)` on that token applied to `abs w` (`agree_permitWorld_vault`,
  `agree_permitWorld_asset`, from `Permit.rep_permitWorld`);
* a `permit` frame therefore **commits the owner's approval**: on success, the model call
  `.approve owner spender value` (vault) or `.assetApprove owner spender value` (asset), the
  `VCall` whose `caller` is the owner — its model operation is exactly the allowance write.
  The frame succeeds **iff** the bytecode's validity predicate `Permit.PermitValid` holds at the
  stored nonce (`v < 256`, deadline not passed, `ecrecover` of the EIP-712 digest is the owner,
  owner ≠ 0, for the context's `Crypto`; `vault_permit_halts` / `asset_permit_halts`), and
  otherwise reverts, committing nothing. Nothing about ECDSA unforgeability is assumed
  (`PERMIT.md`).
* frame conditions (`PermitFrame`): `DomainOk` (as for `DOMAIN_SEPARATOR()`), the
  `ECRECOVER` precompile's address `0x01` not EIP-7702-delegated (always true before Prague; on
  a real chain nobody holds the key of `0x01`), depth below 1024 (room for the precompile
  call), at least 100000 gas (below `minGas`).
* The events of a permit are the model's `approve` events (`Approval(owner, spender, value)` by
  the token, `PermitEvents.lean`); the event-stream theorem `trace_logs` is about top-level
  traces of `VCall`s and is unchanged.

### 6.4 Headlines (`NestedInvariants.lean`)

A transaction is **covered** (`TxOk vault asset minGas Act K ctx w tr msg`) when every
non-static frame of the vault's or the asset's code that **unprotected code** starts during it
(`Reaches`, `VaultStart`, no non-static vault/asset frame below it — the vault's own calls into
the asset are inside the vault's frame summary) is `Covered` and the model calls it commits are
admitted (`FrameAdmitted`: the executed modelled call, or for a `permit` the owner's approval
together with the owner's `NonceSlotOk`). `Covered` = value with `≥ 100` gas, or funded
(`FundedCall`: no value, `≥ minGas` gas, for the vault depth `< 1024`, calldata `< 2⁶⁴` bytes)
and one of: executing a modelled call (`Executes`), a covered view (`ViewData`), `permit` with
`PermitFrame`, calldata selecting no function (`UnknownData`) or malformed for the selected
function (`MalformedData`) — by `covered_of_funded`, every funded frame under `CoverOk`.
**Actors** are thus required per executed call — callers (routers included), receivers,
owners, spenders, sources — not fixed before the transaction. `txOk_direct`: a direct
transaction to the vault or the asset is covered as soon as its own frame is (proved with the
bottom-frame invariant `Reaches.bottom`: any later fresh frame has the transaction's frame,
which is dangerous, below it).

| theorem | statement |
|---|---|
| `follows_tx`, `follows_trace` | one covered transaction / any `TxTrace` (covered transactions and `EnvStep`s) keeps `Follows w₀` |
| `follows_tx_pending` | the same with the uncovered frames' summaries as hypothesis (`PendingFrames`) |
| `lift_any_tx`, `lift_nested` | deployed, `Inv`, and `abs w ≈ Solmate.exec (abs w₀) (cs.map op)` for some admitted `cs` (the committed calls; a permit commits the owner's approval) |
| `invariant_any_tx`, `invariant_nested` | every model invariant insensitive to non-actor allowances holds |
| `supply_eq_sum_any_tx`, `supply_eq_sum_nested` | `totalSupply` = Σ balances, shares and asset, read from storage |
| `solvent_any_tx`, `solvent_nested` | `Σₐ ⌊shares[a]·T/S⌋ ≤ T` |
| `price_mono_any_tx`, `price_mono_nested` | with `K = UserOp`: for the committed calls `cs`, unless a prefix empties the vault, `T₀/S₀ ≤ T/S` (permits included: approvals are user operations) |

Hypotheses: `hmin : 250000 ≤ minGas`; `hk` (no balance slot is 2, 6, 7); `SlotsOk crypto vault
Act`; `Deployed w₀`, `Inv (abs w₀)`; per transaction `ctx.crypto = crypto`, before Prague or no
authorizations, `TopOk` (sender without code), gas `< 2⁶⁴`, `TxOk`. These statements are
unchanged by the `permit`/views/unknown-selector integration; what changed is the definition of
`TxOk` (more frames covered; admission is `FrameAdmitted`, which adds the `permit` clause) and
the type of `txOk_direct`'s / `follows_tx_pending`'s admission hypotheses. The donation attack stays a
statement about a top-level trace (`donation_attack_deployed`): with nested calls the committed
calls are only known to exist.

### 6.5 Any gas, any depth (`LowGas*.lean`)

The theorems of §6.4 ask every vault/asset frame to be covered **with at least `minGas ≥
250000` gas** (and, for the vault and the asset's `permit`, below the call-depth limit). These
requirements are gone:

* **Gas monotonicity** (`EvmLeanProofs/Program/GasMono/`, `LowGasMono.lean`,
  `LowGasFrames.lean`). Every instruction except `GAS`, `CALL*`, `CREATE*` commutes with adding
  gas (`exec_bump`); the frame-level lockstep `monoFrom_of_code` (code conditions `CodeOk`:
  `GAS` only feeds `CALL`/`STATICCALL`, execution stays in the code region, every call is fed
  by `GAS`, and after each call a failed call makes the frame fail, `FailureReverts`, proved by
  symbolic execution at the four vault and the one asset return points, `LowGas.lean`): with
  less gas a frame fails or ends exactly as with more gas. `frameOk_of_topBump`: a frame
  summary of the same frame with more gas `G` (at the top level, `topBump G m`) transfers.
  Premises: `0x01` not EIP-7702-delegated in the frame's world (`EcrecoverOk`), and the
  call targets below.
* **Call targets by certified abstract interpretation** (`EvmLeanProofs/Program/AbsInt/`,
  `LowGasTargets.lean`). The lockstep needs every child of a frame to be a precompile call or a
  gas-monotone frame (`CallsTo`). An explicit-state abstract interpreter (exact stack depth;
  values unknown, constant, or the symbolic address immutable `sym k`, so that one certificate
  holds for all immutables; constants folded through `SHL`/`SUB`/`AND` and solc's address
  mask) explores each code from pc 0 in the kernel (`decide +kernel` on a worklist over a
  balanced tree of the instruction scan): the vault in 6618 abstract states (3304 instructions),
  the asset in 2964 (1921 instructions), every jump resolved, no reachable `CREATE`, every
  reachable call to the `asset` immutable or the constant `1` (vault) / to `1` only (asset).
  `absint_frame` (soundness): every machine of a frame up to its real end (`Exit`) is described
  by a recorded abstract state, children skipped by `exit_frame_ind`; the stack effect of every
  opcode is one theorem (`exec_eff`). With the code of every account constant along those frames
  (`exec_code`; the asset's frames call only the precompile, and a failed child restores a
  snapshot taken inside the frame), the asset immutable's code is the asset's:
  `assetCallsPrecompile`, `vaultCallsAsset` (no hypotheses).
* **The depth limit** (`GasMono/Depth.lean`, `depth_lockstep`). Only the `CALL`/`CREATE`
  families read a frame's depth; a frame at depth 1024 runs in lockstep with the same frame one
  level up until its first call, which fails at once and makes it fail (`FailureReverts`).
  `frameOk_of_depth`: the summary of the frame one level up (with more gas) transfers.

**Headlines at any gas** (`LowGasHeadline.lean`). `CoveredAnyGas vault asset m`: `Covered` with
its own gas, or (`EcrecoverOk m`) covered with some more gas below `2⁶⁴` (`CoveredAtSomeGas`), or
at depth 1024 and covered one level up with more gas (`CoveredAtLimit`). `TxOkAnyGas` is `TxOk`
with `CoveredAnyGas` and no `minGas`; `txOkAnyGas_of_txOk`: every transaction covered in the
sense of §6.4 (with `minGas ≥ 250000`) is. **Simple sufficient condition** `txOkAnyGas_of`:
before Prague or without authorizations, `0x01` holding no designator before the transaction
(always true before Prague; no step can create one, `reaches_allWorlds`), message gas below
`2⁶⁴`, and every vault/asset frame started by other code carries value, or carries none, has
calldata below `2⁶⁴` bytes and `CoverOkAnyGas` (the `name`/`symbol` getter's gas below `2⁶⁴`,
`DomainOk` for `DOMAIN_SEPARATOR()` and `permit`), with its committed calls admitted — **no gas
and no depth condition**.

| theorem | as in §6.4, without `hmin`, over `TxOkAnyGas` / `TxTraceAnyGas` |
|---|---|
| `follows_tx_anyGas`, `follows_trace_anyGas` | `follows_tx`, `follows_trace` |
| `lift_any_tx_anyGas`, `lift_nested_anyGas` | `lift_any_tx`, `lift_nested` |
| `invariant_any_tx_anyGas`, `invariant_nested_anyGas` | `invariant_any_tx`, `invariant_nested` |
| `supply_eq_sum_any_tx_anyGas`, `supply_eq_sum_nested_anyGas` | `supply_eq_sum_any_tx`, `supply_eq_sum_nested` |
| `solvent_any_tx_anyGas`, `solvent_nested_anyGas` | `solvent_any_tx`, `solvent_nested` |
| `price_mono_any_tx_anyGas`, `price_mono_nested_anyGas` | `price_mono_any_tx`, `price_mono_nested` |

Hypotheses: `hk`, `SlotsOk crypto vault Act`, `Deployed w₀`, `Inv (abs w₀)`; per transaction
`ctx.crypto = crypto`, before Prague or no authorizations, `TopOk`, gas `< 2⁶⁴`, `TxOkAnyGas`.
The §6.4 statements keep their names and proofs; they are the special case `minGas ≥ 250000`
(`txTraceAnyGas_of_txTrace`).

### 6.6 What remains

* **`DOMAIN_SEPARATOR()` and `permit` outside `DomainOk`**: on a chain other than the token's
  deployment chain, with a name of 32 bytes or more (the out-of-place encoding loop of
  `abi_encode_t_string_storage` is not verified).
* **`0x01` EIP-7702-delegated** (from Prague): `EcrecoverOk`, derived from the world before the
  transaction by `txOkAnyGas_of` (only authorizations can delegate an account; nobody holds the
  key of `0x01`).
* **Calldata of `2⁶⁴` bytes or more** (impossible within `2⁶⁴` gas: memory expansion), and a
  stored `name`/`symbol` whose getter needs `2⁶⁴` gas or more (slots 0 and 1 are only written
  by the constructor).
* **Transaction layer**: `processTransaction` around `processMessageCall` as an `EnvStep`
  (stated, not proved).

Extension points: new model operations plug in as new `VCall` constructors with a `frameOk_*`
theorem and a `CallData` case (or, like `permit`, as a frame committing an existing `VCall`,
with a `Covered` disjunct and a `FrameAdmitted` clause); `Follows`/`FrameOk` are parametric in the
admitted-call predicate `K`, and the machine-level simulation is generic in `P` and `Good`.
