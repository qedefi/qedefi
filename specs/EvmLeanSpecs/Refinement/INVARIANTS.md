# Invariants of the deployed vault under arbitrary transaction sequences

The last layer of the ERC-4626 verification: the model's invariants (`../Vault/`) hold for the
**deployed bytecode** of Solmate `MockERC4626` + `MockERC20` across arbitrary sequences of
transactions by arbitrary callers. Files: `Lift.lean` (generic), `InvariantsAgree.lean`,
`InvariantsPrice.lean` (model side), `InvariantsSystem.lean` (the concrete system),
`InvariantsCalls.lean` (per-call obligations proved today), `Invariants.lean` (headlines).
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
injectivity. Because no plausible hypothesis excludes a collision between a *written* balance
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

* **Today** — `refinesFor_proven (hmin : 100000 ≤ minGas)`, `K = VCall.Proven`: vault
  `transfer`/`transferFrom`/`approve` (`Shares.*_refines`), asset `transfer`/`transferFrom`
  (frame-level `assetTransfer_refines`/`assetTransferFrom_refines` lifted to top level by
  `call_of_halts`), all in `InvariantsCalls.lean`.
* **After the other work packages** — `refinesFor_all hmin (hp : Pending …)`, all kinds.

Headlines (each for any `K` with `RefinesFor`, under `SlotsOk`, from a deployed well-formed
`w₀`, for every trace whose calls are admitted and whose actors are in `Act`; `*_now` =
today's instance):

| theorem | statement (all quantities read from the final world's storage) |
|---|---|
| `lift` | `Deployed w`, `Inv (abs w)`, `abs w ≈ Solmate.exec (abs w₀) (cs.map op)` |
| `invariant` | every model invariant insensitive to non-actor allowances holds on `abs w` |
| `supply_eq_sum`, `_now` | `sload(vault, 2) = Σₐ sload(vault, keccak(a‖3))`, same for the asset |
| `solvent`, `_now` | `Σₐ ⌊shares[a]·T/S⌋ ≤ T` (`T` = vault's asset balance slot, `S` = slot 2) |
| `no_dilution` | every user call (`UserOp`) in the trace from a world with shares: `T·S' ≤ T'·S` |
| `price_mono` | along a trace of user calls never emptying the vault: `T₀/S₀ ≤ T/S` (ℚ) |
| `donation_attack` | from an empty vault: attacker `deposit(1)`, donation `D`, victim `deposit(a)` ⇒ for `a ≤ D`: `S = 1`, `T = D+1`, attacker holds the share, receiver none; for `D < a ≤ 2D+1`: victim reverted (`S = 1`, `T = D+1`) or got exactly one share with `S = 2`, `T = a+D+1`, `convertToAssets(1) = ⌊(a+D+1)/2⌋` |
| `donation_attack_view` | a top-level `convertToAssets(1)` on that world returns `⌊(a+D+1)/2⌋` |

`UserOp vault op`: not a deposit/mint by the vault, not an asset transfer by the vault, not an
asset `transferFrom`/`burn` from the vault. With top-level calls only the asset `burn(vault, ·)`
(unrestricted in `MockERC20`: the model's "loss") and `transferFrom(vault, …)` are excluded.
`donation_attack` and `no_dilution`/`price_mono` over deposits need the `deposit` (resp.
entry-point) refinement as hypothesis.

## 4. What remains to wire

`Pending` lists the open obligations: `deposit`, `mint`, `withdraw`, `redeem` (in progress in
the other work packages) and the asset's `approve`, `mint`, `burn` (no bytecode proof yet).
For each, `OpRefinesAt` follows from a top-level `X_refines` theorem exactly as in
`InvariantsCalls.lean`: destructure `CallStep`, pick the fuel `max n n₀` (`terminates_unique`),
case on the model result, and close with `callRefines_some` + `agree_of_reps` (both ledgers
`RepOn` with actor pairs ⊆ the allowance predicate, counters from slots 6/7) or
`callRefines_none`, plus `Deployed.of_code` (codes unchanged). Then `refinesFor_all` yields
every headline for all twelve call kinds.

## 5. Not covered

* **Calls from other contracts (nested frames), reentrancy.** Concrete steps are top-level
  calls; a transaction to another contract that calls the vault/asset is covered only if it
  leaves their storage unchanged (an environment step, e.g. it reverts or only reads). The
  vault's share functions have only top-level refinement theorems, so the frame-level
  instantiation (`call` = "a frame running the vault/asset code with these calldata"; the
  generic `Lift` theorems apply verbatim) needs frame-form versions of `Shares.*_refines`.
  Reentrancy into the vault from the asset cannot happen: `MockERC20` makes no calls.
* **Gas.** Calls with less than `minGas` (100000 for today's functions) are not steps. Such a
  call either behaves like a sufficiently funded one or runs out of gas and reverts (world
  unchanged), but gas monotonicity is not proved, so they are excluded rather than covered.
  Fuel is handled exactly (`Terminates`).
* **ETH / value.** Calls carry zero value; calls with value to these non-payable functions
  revert in the bytecode, but this is not proved, so they are not steps. ETH balances are not
  part of the model; plain ETH transfers are environment steps.
* **Transaction layer.** Steps are `processMessageCall`; the surrounding `processTransaction`
  bookkeeping changes no storage of the vault/asset (stated, not proved). EIP-7702: contexts
  are before Prague or carry no authorizations.
* **Unmodelled functions**: `permit` (vault and asset), `name`/`symbol`, and calldata not
  encoding a modelled function are not steps (not proved to revert or be harmless).
* **Allowances of non-actor pairs** are only related to the model up to Keccak collisions
  (see §1); every headline is insensitive to them.
