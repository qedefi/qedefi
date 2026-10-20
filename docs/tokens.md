# Token verification targets

Preparation for verifying further tokens, one at a time, each as `defi/Examples/<Project>/`
with pinned sources, artifacts, differential tests, a refinement against the `Defi.ERC20`
model and invariants, the way Solmate's ERC-4626 vault is verified
([erc4626](erc4626/README.md)). Nothing here is proved yet; this file records what each target
is, exactly, and what should be proved about it.

| Target | Kind | Artifact | Lean module | `difftest` family |
|---|---|---|---|---|
| OpenZeppelin `ERC20` v5.7.0 (`ERC20Mock`) | compiled | `contracts/artifacts/OzAsset/` | `Examples.OpenZeppelin.Contracts.OzAsset` | `oz20` (alone), `oz`/`oz3` (as vault asset) |
| OpenZeppelin `ERC4626`, δ = 0 | compiled | `contracts/artifacts/OzVault/` | `…OpenZeppelin.Contracts.OzVault` | `oz` |
| OpenZeppelin `ERC4626`, **δ = 3** | compiled | `contracts/artifacts/OzVaultOffset/` | `…OpenZeppelin.Contracts.OzVaultOffset` | `oz3` |
| WETH9 | **mainnet** `0xC02a…6Cc2` | `contracts/mainnet/WETH9/` | `Examples.WETH9.Contracts.WETH9` | `weth9` |
| Solady `ERC20` v0.1.26 (`SoladyToken`) | compiled | `contracts/artifacts/SoladyToken/` | `Examples.Solady.Contracts.SoladyToken` | `solady` |
| weird ERC-20s (USDT, BNB, …) | **mainnet** | `contracts/mainnet/<Token>/` | `Examples.WeirdERC20.<Token>.Contracts.<Token>` | see [below](#weird-erc-20s) |

*Compiled* targets are built from vendored sources by `scripts/build-contracts.sh` (solc
0.8.28, optimizer 200, Cancun, no metadata) and deployed through their creation code.
*Mainnet* targets are the deployed bytecode itself, read once by `scripts/fetch-mainnet.sh`
(verified source and compiler settings from Sourcify, code at a recorded block, code hash);
the build script is offline, checks `keccak(runtime.hex)` against the recorded hash and that
every ABI selector is pushed by the dispatcher, and generates a Lean module with
`runtimeCode`, `address` (the mainnet address), `codeHash`, `genesisStorage` (what the
constructor leaves, with test parameters, from the hand-written `genesis.json`), `selectors`,
`events`, `errors` and `storageLayout` (hand-derived: solc < 0.5.13 has no layout output).
Tests and proofs install `runtimeCode` at `address` with `genesisStorage`
(`anvil_setCode`/`anvil_setStorageAt` on the reference side).

## The generic ERC-20 property catalogue

For a token at `T` with view `σ(w) = (supply, balanceOf, allowance)` read from the world
through the token's layout (`EvmLogic.Solidity.ERC20.view`, generalized below), and every
transaction (any sender, any calldata, any value, any gas, top-level or nested):

1. **Supply invariant**: `Σₐ balanceOf a = supply ≤ 2²⁵⁶ − 1` holds after every call if it held
   before (`Token.WF`); the model operations are `ℕ`-exact under it.
2. **Exact effects** (refinement): each successful entry point changes `σ` exactly as the
   model operation (`Token.transfer`/`ozTransfer`/…), emits exactly the model's logs, returns
   exactly the ABI-encoded result; it reverts exactly when the model returns `none`, with the
   token's revert data.
3. **Frame**: a call changes no storage of `T` outside the rows the model touches, no
   storage of other accounts, no ether (non-payable entry points revert on value).
4. **No unauthorized mint/burn/move**: a transaction whose sender is not `o` and which is not
   an allowance-backed `transferFrom` by an approved spender never lowers `balanceOf o` nor
   `allowance o _`; supply only changes through the mint/burn entry points (or never, for
   tokens without them).
5. **Views**: `balanceOf`, `allowance`, `totalSupply`, `name`, `symbol`, `decimals` return the
   layout's values, change nothing, and never revert on well-formed calldata with enough gas.
6. **Malformed calldata and unknown selectors**: revert (or the fallback, where there is one)
   with no effect.
7. **Arbitrary callers** (nested simulation, `EvmLogic/Program/Nested/`): 1–4 hold for any
   transaction in which `T` is called by arbitrary contracts at any depth.

The Solmate ERC-20 already has 2, 3, 5, 6 at the bytecode level
(`defi/Examples/Solmate/ERC20/`) and 1, 4, 7 through the vault proofs.

## OpenZeppelin `ERC20` (v5.7.0, `ERC20Mock`)

Artifact `OzAsset`: 1,900 B runtime, no immutables, no constructor arguments (`name =
"ERC20Mock"`, `symbol = "E20M"`, `decimals = 18`), canonical address `0x1313…020e`.

**Storage**: `_balances` slot 0, `_allowances` slot 1, `_totalSupply` slot 2, `_name` 3,
`_symbol` 4 (short strings: `bytes ‖ 2·len`). `_balances[a]` at `keccak(pad(a) ‖ pad(0))`,
`_allowances[o][s]` at `keccak(pad(s) ‖ keccak(pad(o) ‖ pad(1)))`. Confirmed by the
`oz20` layout check (views vs. slot reads, below).

**Functions** (`ERC20Mock` adds unrestricted `mint`/`burn`):

| Function | Reverts (revert data) | Effect | Events |
|---|---|---|---|
| `transfer(to, v)` | in order: caller `= 0`: `ERC20InvalidSender(0)`; `to = 0`: `ERC20InvalidReceiver(0)`; `bal[caller] < v`: `ERC20InsufficientBalance(caller, bal, v)` | `_update(caller, to, v)` | `Transfer` |
| `transferFrom(f, to, v)` | allowance first: `alw < v` (and `alw ≠ max`): `ERC20InsufficientAllowance(caller, alw, v)`; then `f = 0` gives **`ERC20InvalidApprover(0)`** (the allowance write, before the sender check) when `v = 0`, then `to = 0`, then balance as `transfer` | `alw ≠ max ⇒ alw −= v` (no event), `_update(f, to, v)` | `Transfer` only (v5 no longer emits `Approval` on spend) |
| `approve(s, v)` | caller `= 0`: `ERC20InvalidApprover(0)`; `s = 0`: `ERC20InvalidSpender(0)` | `alw[caller][s] = v` | `Approval` |
| `mint(a, v)` | `a = 0`: `ERC20InvalidReceiver(0)`; supply overflow: `Panic(0x11)` | supply += v (checked), `bal[a] += v` (unchecked) | `Transfer(0, a, v)` |
| `burn(a, v)` | `a = 0`: `ERC20InvalidSender(0)`; `bal[a] < v`: `ERC20InsufficientBalance` | `bal[a] −= v`, supply −= v (unchecked) | `Transfer(a, 0, v)` |
| views | value sent: empty revert | — | — |

**Differences from Solmate's `ERC20`** (both already modelled in `Defi.ERC20.Token`:
`transfer` vs. `ozTransfer` etc.):

- zero-address checks on sender, receiver, approver, spender (Solmate has none: transfers to
  `0` keep the supply and count in `Σ balances`);
- custom errors with arguments vs. Solmate's `Panic(0x11)` from checked arithmetic and string
  reverts in `permit`;
- one internal `_update(from, to, v)` for transfer/mint/burn with `from = 0` / `to = 0`
  meaning mint/burn; `unchecked` blocks for `bal[from] −= v` (after the explicit check),
  `bal[to] += v` and `supply −= v`, justified by `Σ balances = supply`;
- the order of checks in `transferFrom` (allowance before addresses) shows up in revert data;
- no `permit`/`nonces`/`DOMAIN_SEPARATOR` in `ERC20Mock`.

## OpenZeppelin `ERC4626` with decimals offset δ = 3 (`OzVaultOffset`)

`contracts/src/OzVaultOffset.sol`: the stock `ERC4626` with only `_decimalsOffset()`
overridden to `3` (name `"OZ Vault d3"`, symbol `"ozVLT3"`, `decimals = 18 + 3 = 21`). Same
immutables as `OzVault` (`_asset` at 556, 896, 2775, 2927; `_underlyingDecimals` at 1277),
`runtimeCodeFor` in `OpenZeppelin/Contracts/Deploy.lean`, deployed at the vault's canonical
address over a fresh `ERC20Mock`. Its bytecode differs from `OzVault`'s in exactly three
instructions (the offset is pushed as `PUSH1 3` where δ = 0 had `PUSH0`/`DUP`) plus shifted
jump targets: `10^δ` is computed at run time by the checked-exponentiation helper (one
`EXP`), so a bytecode proof for `OzVault` should be written once with δ symbolic in that
helper and instantiated twice.

`convertToShares(a) = a · (S + 10^δ) / (T + 1)`, `convertToAssets(s) = s · (T + 1) /
(S + 10^δ)` (rounding per EIP-4626), `T = asset.balanceOf(vault)`.

**Properties to prove on the bytecode**: the refinement `OzVaultOffset ⊑ Defi.ERC4626.Oz`
with `δ = 3` (the model is already parametric in δ: `Oz.lean`, `OzProps.lean`), and through it
the inflation bounds already proved on the model: attacker profit
`P·(S + 1000) ≤ T + 1 − 999·D` (`Inflation.oz_profit_bound`), cost of inflicting loss `L`
more than `1000·L − …` (`oz_cost_bound`), victim loss `< (3/4)·a/1000` in crytic's setting
(`Oz.crytic_inflation_bound`, the case where the bound is meaningful). The difftest's fixed
first-depositor scenario shows it concretely: on `oz3` alice pays `10¹⁸ + 1`, ends with
`5.0008·10¹⁴` (she loses 99.95 % of the donation), bob deposits `2·10¹⁸ − 1` and gets
3,999 shares (on `oz`, δ = 0: alice ends with `0.6·10¹⁸`).

## WETH9

**Target**: the deployed bytecode at `0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2`
(3,124 B, code hash `0xd0a06b12…5e23`), source `contracts/mainnet/WETH9/source/WETH9.sol`
(GPL-3.0, Dapphub), deployed at block 4,719,568 by `0x4F26…0876`, compiled with **solc
0.4.19+commit.c4cbbb05, optimizer off**. Sourcify reports a *partial* match for creation and
runtime code: the recompiled code equals the deployed code except the 43-byte metadata trailer
(`a165627a7a72305820<swarm hash>0029`, offset 3,081), whose swarm hash differs, so
**byte-exact reproduction from source is impossible with any compiler**; reproduction modulo
the trailer needs solc 0.4.19, which is not installed here (the installed 0.4.26 produces
different code, 3,161 B). The pin is therefore the code hash, checked by the build script
and by `scripts/fetch-mainnet.sh` against Sourcify's on-chain bytecode.

**Storage** (verified against mainnet slots 0–2): `name` slot 0 (`"Wrapped Ether"`,
`0x5772…00 1a`), `symbol` 1 (`"WETH"`, `…08`), `decimals` 2 (`18`), `balanceOf` 3
(`keccak(pad(a) ‖ pad(3))`), `allowance` 4 (`keccak(pad(s) ‖ keccak(pad(o) ‖ pad(4)))`). No
total-supply slot: `totalSupply()` returns `address(this).balance` (`ADDRESS BALANCE`, warm,
100 gas).

**Functions** (0.4.19: no ABI length checks — short calldata reads zeros; `require` → `REVERT`
with empty data; non-payable functions revert on value):

| Function | Payable | Reverts | Effect | Events |
|---|---|---|---|---|
| fallback (no selector match, incl. < 4 bytes) | yes | never (gas) | `deposit()` | `Deposit(caller, value)` |
| `deposit()` | yes | never | `bal[caller] += value` (**unchecked**) | `Deposit` |
| `withdraw(wad)` | no | `bal[caller] < wad`; the ether transfer fails | `bal[caller] −= wad`, then `CALL caller` with `wad` wei and gas `2300·[wad = 0]` (stipend 2300 if `wad > 0`), `REVERT` if it fails | `Withdrawal(caller, wad)` after the call |
| `totalSupply()` | no | — | returns `this.balance` | — |
| `approve(guy, wad)` | no | — | `alw[caller][guy] = wad`, returns `true` | `Approval` |
| `transfer(dst, wad)` | no | as `transferFrom(caller, dst, wad)` | | |
| `transferFrom(src, dst, wad)` | no | `bal[src] < wad`; `src ≠ caller ∧ alw ≠ 2²⁵⁶−1 ∧ alw < wad` | if `src ≠ caller` and allowance not infinite: `alw −= wad`; `bal[src] −= wad`, `bal[dst] += wad` (unchecked); returns `true` | `Transfer` |
| `name`, `symbol`, `decimals`, `balanceOf`, `allowance` | no | — | views | — |

No zero-address checks, no mint/burn other than deposit/withdraw, `transfer` to self is a
no-op with an event.

**Property catalogue (WETH-specific)**:

- **Ether backing** (the distinctive invariant): `Σₐ balanceOf a ≤ address(T).balance`,
  preserved by every transaction (any caller, nested). Equality does *not* hold in general:
  ether can arrive without `deposit` (`SELFDESTRUCT` beneficiary, coinbase, value sent before
  deployment), so `totalSupply() ≥ Σ balanceOf`, and the ERC-20 supply invariant of the
  catalogue becomes this inequality. It also rules out overflow of the unchecked additions
  (all ether < 2²⁵⁶).
- **Exact effects** of deposit/fallback/withdraw on token balances *and* ether: deposit moves
  `value` wei from caller to `T` and credits it; a successful withdraw debits `wad` and moves
  `wad` wei from `T` to the caller.
- **Withdrawal liveness**: a holder with `bal ≥ wad` can always withdraw, unless the
  recipient's code reverts or the transaction lacks gas.
- **Reentrancy (external call in `withdraw`)**: the balance is debited *before* the call
  (checks-effects-interactions) and the callee runs with at most 2300 gas. With ≤ 2300 gas a
  frame (and every frame it calls, which gets less) cannot `SSTORE` (EIP-2200 sentry), cannot
  send value (`CALL` with value costs 9000), cannot `CREATE` or `SELFDESTRUCT`: **any callee
  summary is "no persistent state change; only logs and transient storage (`TSTORE` has no
  sentry); then success or failure"** — a generic EvmLogic lemma (stipend frames do not
  write persistent state) that turns the reentrancy surface into a two-case split. WETH9
  never reads transient storage, so the `TSTORE` effects are irrelevant to it. This is the
  first target whose correctness depends on an arbitrary external callee.
- ERC-20 exact effects / frame / views for `transfer`, `transferFrom`, `approve` (the
  Solmate-style `Token.transfer`/`spend` model applies with WETH's ordering: balance check
  before the allowance check, self-spend skips the allowance).

**Difficulties**: unoptimized 0.4 code (long stack shuffles, no `PUSH0`, `EXP`-based shifts
`0x0100…00 / x`, `DIV` by `2²²⁴` in the dispatcher instead of `SHR`); the external call;
ether accounting in the invariant (balances of `T` change through `CALL` value transfers,
`SELFDESTRUCT` of other contracts); `this.balance` as the supply.

## Solady `ERC20` (v0.1.26, `SoladyToken`)

`contracts/lib/solady/src/tokens/ERC20.sol` (MIT, `Vectorized/solady` tag `v0.1.26`, commit
`acd959aa`), vendored unmodified; `contracts/src/SoladyToken.sol` makes it concrete: constant
`name = "Solady Token"`, `symbol = "SLDY"`, `decimals = 18`, unrestricted `mint`/`burn`,
nothing else overridden (Permit2 infinite allowance enabled, name hash computed from
`name()`). No immutables, no Solidity state variables (`forge inspect … storageLayout` is
empty): 2,278 B runtime, canonical address `0x1313…020e`.

**Storage** (inline assembly, exact derivations from source, confirmed on the compiled
artifact: the seeds appear as `PUSH4 0x87a211a2` (5×), `PUSH4 0x7f5e9f20` (3×),
`PUSH9 0x05345cdf77eb68f44c` (4×), and the `solady` difftest layout check compares
`balanceOf`/`allowance`/`totalSupply` with reads of these slots):

| Variable | Slot |
|---|---|
| `totalSupply` | constant `0x05345cdf77eb68f44c` |
| `balanceOf(o)` | `keccak256(o₂₀ ‖ 0⁸ ‖ 0x87a211a2)`: 32 bytes (`mstore(0x0c, seed)`, `mstore(0x00, o)`, `keccak256(0x0c, 0x20)`) |
| `allowance(o, s)` | `keccak256(o₂₀ ‖ 0⁸ ‖ 0x7f5e9f20 ‖ s₂₀)`: **52 bytes** (`keccak256(0x0c, 0x34)`) |
| `nonces(o)` | `keccak256(o₂₀ ‖ 0⁸ ‖ 0x38377508)`: 32 bytes |

(`o₂₀` the 20 address bytes, `0⁸` eight zero bytes.) The `transferFrom`/`_transfer` paths
build the same preimages as `or(shl(96, from), seed)` at `0x0c`; `permit` builds the allowance
preimage at `0x2c` from the recovered owner and `or(shl(160, seed), spender)`.

**Functions**:

| Function | Reverts (4-byte custom errors, no arguments) | Effect | Events |
|---|---|---|---|
| `transfer(to, v)` | `bal < v`: `InsufficientBalance()` | `bal[caller] −= v`, `bal[to] += v` (unchecked) | `Transfer` |
| `transferFrom(f, to, v)` | caller `≠ PERMIT2` ∧ `alw ≠ max` ∧ `v > alw`: `InsufficientAllowance()`; then `InsufficientBalance()` | allowance decreased unless infinite or caller is Permit2 | `Transfer` |
| `approve(s, v)` | `s = PERMIT2 ∧ v ≠ max`: `Permit2AllowanceIsFixedAtInfinity()` | `alw[caller][s] = v` | `Approval` |
| `allowance(o, s)` | — | `s = PERMIT2 ⇒ 2²⁵⁶ − 1`, else the slot | — |
| `permit(o, s, v, d, v8, r, s32)` | Permit2 rule as `approve`; `timestamp > d`: `PermitExpired()`; recovered `≠ o` (incl. failed recovery): `InvalidPermit()` | `nonce[o] += 1`, `alw[o][s] = v` | `Approval` |
| `mint(a, v)` | supply overflow: `TotalSupplyOverflow()` | supply += v, `bal[a] += v` | `Transfer(0, a, v)` |
| `burn(a, v)` | `bal < v`: `InsufficientBalance()` | `bal −= v`, supply −= v | `Transfer(a, 0, v)` |
| `nonces`, `DOMAIN_SEPARATOR`, `name`, `symbol`, `decimals`, `balanceOf`, `totalSupply` | — | views (`DOMAIN_SEPARATOR` hashes `name()` each time) | — |

Like Solmate: no zero-address checks (mint/transfer to `0` allowed, counted in `Σ balances`),
self-approvals and zero transfers allowed. Address arguments are validated by solc's ABI
decoder (dirty upper bits: empty revert).

**Properties**: the generic catalogue under this layout, plus

- `allowance` is a *view function*, not a slot: the model allowance is
  `if s = PERMIT2 then max else slot`; storage rows `(o, PERMIT2)` can still be written
  (`approve(PERMIT2, max)` stores `max`), and `transferFrom` by Permit2 bypasses them;
- `permit` refinement as for Solmate (`Defi.ERC20.Permit`), with Solady's revert order;
- `totalSupply`'s fixed slot must avoid every hashed slot the proof touches (a
  `KeccakAvoids`-style hypothesis over the three preimage families), and the three families
  must be mutually fresh (`KeccakFresh` per touched preimage) — the 52-byte allowance
  preimages cannot coincide with the 32-byte ones as *inputs*, but their hashes need the same
  freshness hypotheses as Solmate's nested mappings.

**Difficulties**: everything is inline assembly with hand-placed scratch memory: proofs read
`keccak256` over memory windows that straddle two `mstore`s (`0x0c..0x2c`, `0x0c..0x40`),
so they need the memory-window lemmas (`Bytes`/`State` in EvmLogic) at unaligned offsets;
`permit` writes the zero slot `0x60` and restores it; `log3` reads its topic from `mload(0x0c)`
after the `mstore`s; one copy of the transfer logic per entry point (inlined, not
`_transfer`), so no shared internal-function summary.

## Generalizing `Defi/ERC20` into a reusable kit

Today: `Defi.ERC20.Token` (balances `A →₀ ℕ`, supply, allowances) with Solmate operations
and OZ variants (`ozTransfer`, `ozSpend`, …), `Rep` relating it to
`EvmLogic.Solidity.ERC20.State` read through `Layout` (`⟨supply, balances, allowances⟩`
slot numbers, Solidity mapping derivation only). Proposed shape:

1. **Layout as a parameter**: `structure Layout where supplySlot : Option Word;
   balanceSlot : Crypto → Address → Word; allowanceSlot : Crypto → Address → Address → Word;
   fresh : Crypto → … → Prop` with instances `solidity (supply balances allowances : Nat)`
   (Solmate 2/3/4, OZ 2/0/1, WETH none/3/4, USDT …) and `solady`. `view`, `view_sstore_*`
   and the `*SlotOk` hypotheses become layout-generic (the freshness predicate is part of the
   layout). The current `EvmLogic.Solidity.ERC20.Layout` is in the root package; changing it
   is an interface change for its owner.
2. **Supply as a parameter**: stored (`supplySlot = some k`) or derived (WETH: ether balance;
   rebasing tokens: scaled). The `WF` invariant takes the relation (`=` or `≤`).
3. **Operation semantics as a record of policies** instead of one function per vendor:
   `zeroAddress : Bool` (OZ checks), `infiniteAllowance : Option ℕ` (max not decremented),
   `selfSpendSkipsAllowance : Bool` (WETH), `checkOrder` (allowance-then-balance vs.
   balance-then-allowance), `allowanceOverride : A → A → Option ℕ` (Solady Permit2),
   `approveGuard : ℕ → ℕ → Prop` (USDT: `v = 0 ∨ current = 0`), `fee : ℕ → ℕ` (USDT/STA),
   `blocked : A → Prop` and `paused : Prop` (USDT/BNB), giving one `transfer`/`transferFrom`/
   `approve` with the current Solmate and OZ functions as instances (and their existing
   theorems as corollaries).
4. **Observable conventions as parameters**: revert data per failure reason (`Panic(0x11)`,
   OZ custom errors with arguments, Solady 4-byte errors, empty reverts, `INVALID` for 0.4
   `throw`), return convention (`bool` vs. nothing), and the event list per operation (OZ v5
   and Solady emit no `Approval` on spend; USDT emits `Transfer` to the owner for fees). The
   `Events`/`Logs` modules of `Defi.ERC4626` show the pattern.
5. **One refinement theorem shape** per token: for each selector, the bytecode's
   `processMessageCall` result equals the model step lifted through `Rep` (as
   `Examples.Solmate.ERC20.Spec`), so the vault theorems (`Defi.Trace.Lift`) can be
   instantiated with any asset satisfying it — in particular the integration theorems below.

## Expected proof difficulties (summary)

| Target | Main obstacles |
|---|---|
| OZ ERC20 | revert data with arguments (ABI-encoded custom errors), check order in `transferFrom`; otherwise close to Solmate |
| OZ vault δ = 3 | the full ERC-4626 bytecode (as for OZ δ = 0, not yet done); `mulDiv` (512-bit `mulmod` trick) and the `EXP` helper; SafeERC20 call/return handling |
| WETH9 | external call with stipend in `withdraw`; ether accounting; 0.4.19 unoptimized code |
| Solady | inline assembly with unaligned scratch memory; custom hashed layout and fixed supply slot; Permit2 special cases |
| weird tokens | 0.4.x code (`throw` = `INVALID`, `EXP`-shifts), missing return values, owner state (fees, blacklist, pause), forwarding calls (USDT `deprecated`) |

## Later, separately: proxies and upgradeable tokens (USDC, …)

Not prepared here. Needed: `DELEGATECALL` semantics in the frame logic (code of the
implementation, storage and `ADDRESS`/`CALLER`/`CALLVALUE` of the proxy: `step_delegatecall`
exists, a `WP.delegatecall` callee-summary rule does not); the EIP-1967 slots (implementation
`keccak("eip1967.proxy.implementation") − 1`, admin `keccak("eip1967.proxy.admin") − 1`,
beacon) or the token's own scheme (USDC's `FiatTokenProxy` uses the older
`org.zeppelinos.proxy.implementation` slot); the admin's privileges as part of the threat
model (an upgrade replaces all code: properties hold *until* an admin transaction, or only
for a fixed implementation); and storage-layout compatibility between proxy and
implementation (the implementation's layout must avoid the proxy's slots). A verified
token behind a proxy is then: proxy dispatch theorem (every non-admin call delegates) +
implementation refinement over the proxy's storage.

## Differential testing

`lake exe difftest --family oz3,oz20,solady,weth9` (or `tokens`, `vaults`, `all`; run from
`defi/`). Token families (`defi/Examples/Differential/Token.lean`): compiled tokens are
deployed through their creation code, mainnet tokens installed with their genesis storage
(both sides); actors are funded with 1000 ether where ether matters. The generator draws from
the token's ABI by weight with state-aware amounts, sends ether to payable functions, to the
fallback and occasionally to non-payable functions, uses Permit2 as address and sender for
Solady, and adds malformed calldata. After every call: status, output, logs, `gasUsed`,
storage of the token and every account anvil wrote, and ether balances of the token and the
actors (WETH). A fixed scenario per token (mint/approve/transfer/spend; WETH deposit,
fallback, transfer, spend, withdraw) is followed by a **storage-layout check**: in evm-lean,
`balanceOf`, `allowance` and `totalSupply` are called for every actor (pair) and compared with
reads of the slots derived above.
