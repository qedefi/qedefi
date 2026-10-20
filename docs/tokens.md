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
| USDT (`TetherToken`) | **mainnet** `0xdAC1…1ec7` | `contracts/mainnet/USDT/` | `Examples.WeirdERC20.USDT.Contracts.USDT` | `usdt`, `usdtfee` |
| BNB | **mainnet** `0xB8c7…DD52` | `contracts/mainnet/BNB/` | `Examples.WeirdERC20.BNB.Contracts.BNB` | `bnb` |
| STA (fee on transfer) | **mainnet** `0xa7DE…eED1` | `contracts/mainnet/STA/` | `Examples.WeirdERC20.STA.Contracts.STA` | `sta` |
| AMPL (rebasing; zos proxy + `UFragments`) | **mainnet** `0xD46b…A161` / `0xD0e3…35b1` | `contracts/mainnet/{AMPLProxy,AMPL}/` | `Examples.WeirdERC20.AMPL.Contracts.{AMPLProxy,AMPL}` | `ampl` |

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

## Weird ERC-20s

Real mainnet bytecode (table in `contracts/README.md`), chosen from the Trail of Bits
token-integration checklist and `d-xo/weird-erc20`. Each is installed in tests at its mainnet
address with `genesis.json` storage: owner/admin roles given to alice (`0xA11CE`), balances
to the four actors, supply = their sum, one finite and one infinite allowance. Notation:
`bal`, `alw`, `S` (supply); `pad(x)` 32-byte word; mapping slots as Solidity's
(`m[k]` at `keccak(pad(k) ‖ pad(slot))`, nested `keccak(pad(s) ‖ keccak(pad(o) ‖ pad(slot)))`).

### USDT (`TetherToken`, solc 0.4.18, unoptimized, 11,075 B)

**Layout** (C3 linearization `TetherToken, BlackList, StandardToken, ERC20, BasicToken,
ERC20Basic, Pausable, Ownable`; storage from the most base): slot 0 `owner` (bytes 0–19) and
`paused` (byte 20, read as `sload(0) / 2¹⁶⁰ & 0xff`); 1 `_totalSupply`; 2 `balances`; 3
`basisPointsRate`; 4 `maximumFee`; 5 `allowed`; 6 `isBlackListed`; 7 `name`; 8 `symbol`;
9 `decimals` (`uint256`); 10 `upgradedAddress` (bytes 0–19) and `deprecated` (byte 20).
`MAX_UINT` is a constant.

**Deviations** (all checked in the `usdt` scenario):

1. `transfer`, `transferFrom`, `approve` **return nothing** (empty return data).
2. **Approve race guard**: `approve(s, v)` reverts if `v ≠ 0 ∧ alw[caller][s] ≠ 0`; it
   ignores `paused` and the blacklist; requires calldata ≥ 68 bytes.
3. **Fee switch**: `fee = min(v · basisPointsRate / 10000, maximumFee)` credited to the
   *current owner* (`Transfer(from, owner, fee)` first, then `Transfer(from, to, v − fee)`);
   the sender is debited `v`, `transferFrom` spends `v` of allowance. `setParams(bps, max)`
   (owner) requires `bps < 20`, `max < 50` and stores `max · 10^decimals`. Mainnet: 0 / 0.
4. **Blacklist**: `transfer` requires `!isBlackListed[caller]`, `transferFrom` requires
   `!isBlackListed[from]` (spender and recipient unchecked); `destroyBlackFunds(u)` (owner,
   `u` blacklisted) zeroes `bal[u]` and lowers `_totalSupply` unchecked, emitting
   `DestroyedBlackFunds` but no `Transfer`.
5. **Pause**: `whenNotPaused` only on `transfer`/`transferFrom`.
6. **Short-payload check** `onlyPayloadSize`: `transfer` needs ≥ 68 bytes, `transferFrom` ≥ 100
   (only on the non-deprecated path, after pause and blacklist).
7. **Insufficient balance or allowance fails with `INVALID`** (SafeMath `assert`): all gas
   consumed, not `REVERT`.
8. `issue(v)` / `redeem(v)` (owner) change `bal[owner]` and `S` with `Issue`/`Redeem` events,
   no `Transfer`; `issue(0)` reverts (strict `>` checks). Infinite allowances are not spent.
9. **Deprecation forwarding** (`deprecate(a)`, owner, irreversible): with `deprecated` set,
   `transfer(to, v)` → `CALL a.transferByLegacy(caller, to, v)`, `transferFrom(f, t, v)` →
   `transferFromByLegacy(caller, f, t, v)`, `approve(s, v)` → `approveByLegacy(caller, s, v)`,
   `balanceOf`, `allowance`, `totalSupply` → the same functions on `a` — after the local
   pause/blacklist/payload checks, value 0, gas `gas − 710`, preceded by
   `require(extcodesize(a) > 0)` and followed by `require(success)` (no revert-data bubbling,
   no `RETURNDATASIZE`: a short view return leaves the *calldata word* in the output buffer).
   `destroyBlackFunds` reads the forwarded `balanceOf`. Getters `balances`, `allowed`,
   `_totalSupply` stay local. With `a` without code, all six revert (token bricked); with
   `a = USDT` itself, views recurse until gas runs out. The random generator exercises
   `deprecate` (weight 1).

**Model variant**: return convention `none`; `approveGuard`; `fee` with recipient `owner`;
`blocked` per entry point (sender for `transfer`, `from` for `transferFrom`); `paused` on
transfers only; owner-only `issue`/`redeem`/`setParams`/`pause`/`addBlackList`/`destroyBlackFunds`;
the `deprecated` state as a *switch to an external token* (refinement only up to deprecation,
or parametric in the upgraded token's summary). The supply invariant
`Σ bal = _totalSupply` holds (fees move tokens, `destroyBlackFunds` burns, issue/redeem mint
and burn to the owner) as long as `issue` cannot overflow (its strict checks ensure this).

### BNB (solc 0.4.12, unoptimized, 5,355 B)

**Layout** (`BNB is SafeMath`, no inherited state): 0 `name`, 1 `symbol`, 2 `decimals`
(`uint8`), 3 `totalSupply`, 4 `owner` (no setter: fixed forever), 5 `balanceOf`, 6
`freezeOf`, 7 `allowance`.

**Deviations** (in the `bnb` scenario): `transfer` returns nothing (`transferFrom`, `approve`,
`burn`, `freeze`, `unfreeze` return `true`); **zero values revert** in `transfer`,
`transferFrom`, `approve` (so an allowance cannot be reset to 0), `burn`, `freeze`,
`unfreeze`; transfers to `0` revert; **no `Approval` event** (not even declared); the infinite
allowance is decremented; `freeze` moves balance to `freezeOf` (supply unchanged:
`S = Σ bal + Σ freezeOf`); the **payable fallback accepts any unknown selector** with
success and empty return data ("phantom functions": `permit(…)` succeeds) and ether, which only
`withdrawEther(amount)` (owner, `transfer` with stipend) moves out. All failures are `REVERT`
(0.4.12 `throw`; before Byzantium the same opcode consumed all gas).

**Model variant**: `zeroValueReverts`, return convention per function, no approval event,
`frozen` balances as a second ledger in the supply invariant, a fallback that succeeds on
every unknown selector (the "malformed calldata" property 6 becomes "unknown selectors are
no-ops that accept ether").

### STA (Statera, solc 0.5.0, optimizer 200, 3,216 B): fee on transfer

**Layout**: 0 `_name`, 1 `_symbol`, 2 `_decimals`, 3 `_balances`, 4 `_allowed`, 5
`_totalSupply`, 6 `basePercent` (= 100, no setter). The Transfer topic is a data constant
after the code (read by `CODECOPY`): a linear disassembly shows bogus instructions there.

**Deviations** (in the `sta` scenario): `transfer(to, v)` burns `cut(v) = ⌈v/100⌉`
(`basePercent = 100`; `cut(1) = 1`, so `transfer(x, 1)` delivers 0), credits `v − cut(v)`,
lowers `S` by `cut(v)`, emits `Transfer(from, to, v − cut)` and `Transfer(from, 0, cut)`;
`transferFrom` the same and spends `v` (infinite allowances too, no `Approval`); zero
transfers succeed with two zero events; `approve` to `0` reverts; `destroy`/`destroyFrom`
burn; `downAllowance` below zero is `INVALID`. Invariant `S = Σ bal` holds (fees are burned).

**Model variant**: `fee v = ⌈v/100⌉` *burned* (recipient receives `v − fee`); the generic
"exact effects" property becomes "recipient's balance increases by `v − fee v`".

### AMPL (Ampleforth): rebasing, behind a proxy

**Proxy**: the token address `0xD46b…A161` holds a zos-lib `AdminUpgradeabilityProxy`
(solc 0.5.3) with **pre-EIP-1967 slots**: implementation at
`keccak("org.zeppelinos.proxy.implementation") = 0x7050c9e0…f8c3`, admin at
`keccak("org.zeppelinos.proxy.admin") = 0x10d6a54a…390b`. Calls from the admin to
`admin()`, `implementation()`, `changeAdmin`, `upgradeTo(AndCall)` run in the proxy; every other
call `DELEGATECALL`s the implementation `0xD0e3…35b1` (`UFragments`, solc 0.7.6) with the
whole calldata, bubbling return or revert data; **the admin cannot use the token** (its
fallback calls revert with a reason string). This is the one target that exercises proxy
semantics already (`ampl` difftest family: both codes installed, state in the proxy).

**Layout** (in the proxy's storage; Sourcify's/solc's layout equals the hand derivation):
0 `initialized` (byte 0), `initializing` (byte 1); 1–50 gap; 51 `_name`, 52 `_symbol`, 53
`_decimals` (9); 54–103 gap; 104 `_owner`; 105–154 gap; 155 `monetaryPolicy` (bytes 0–19)
with two deprecated `bool`s (bytes 20, 21); 156 `_totalSupply`; 157 `_gonsPerFragment`; 158
`_gonBalances`; 159 `_allowedFragments`; 160 `_nonces`. `TOTAL_GONS = M − (M mod 5·10¹⁶)`,
`M = 2²⁵⁶ − 1`.

**Deviations** (in the `ampl` scenario): `balanceOf(a) = gons[a] / gonsPerFragment` (rounded
down; `Σ balanceOf ≤ S`, not equal); `rebase(epoch, δ)` (monetary policy) changes `S` and
`gonsPerFragment = TOTAL_GONS / S`, i.e. **every balance changes without any `Transfer`
event**; `transfer(v)` moves `v · gpf` gons; `transferAll`/`transferAllFrom` move all gons
(including dust); transfers to `0` or to the token revert; infinite allowances are
decremented; `decreaseAllowance` saturates at 0; `permit` (EIP-2612) accepts `owner = 0`
with an invalid signature (`ecrecover` returns 0).

**Model variant**: balances stored in *shares* (gons) with a global scale; the ERC-20 view is
`gons / gpf`; `rebase` is a privileged operation changing the view of every account; the
supply invariant becomes `Σ gons ≤ TOTAL_GONS` (exact for gons) with the fragment view
bounded by `S`. Structurally this is an ERC-4626-like share ledger, so `Defi.ERC4626` rounding
lemmas apply.

### Recorded examples (not targets)

LEND (zero-value transfers revert: strict `balances[to] + v > balances[to]`, approve race
guard), GUSD (2 decimals; a front contract forwarding by `CALL` to a replaceable
`erc20Impl` with balances in a separate store), YAM-V2 (24 decimals), USDC and PAXG (zos-slot
proxies; PAXG's current implementation has no transfer fee anymore, contrary to the
`weird-erc20` list). Addresses and code hashes in `contracts/README.md`.

### The `Defi/ERC20` variant these need

One `Token.Variant` record (see the next section) with: return convention
(`bool | none | perFunction`), `zeroValueReverts`, `zeroAddressReverts`, `approveGuard`,
`infiniteAllowance : Bool` (spent or not), `fee : ℕ → ℕ` with a sink (`owner` or burn),
`blocked`, `paused`, `allowanceOverride` (Permit2), owner-only `mint`/`burn` entry points, a
`frozen` ledger, and a *scaled* ledger (`gons`, `gpf`) for rebasing; events per operation as
data. Each target instantiates it; the generic catalogue theorems are proved once for the
variant, with hypotheses where a variant breaks them (fee: recipient receives less;
rebasing: balances change without transfers; deprecation: behaviour delegated).

### Integration theorems worth proving

- **SafeTransferLib handles missing return values.** Solmate's `safeTransfer`/
  `safeTransferFrom` accept empty return data or a `true` word (`SafeTransfer.lean` already
  has its call shape). With USDT or BNB bytecode as the vault's asset (fee off, not paused,
  not blacklisted, not deprecated), the Solmate vault refinement and its invariants still
  hold: the asset's `transferFrom`/`transfer` summaries (`Halts` frames, empty output) plug
  into `WP.call` exactly where `MockERC20`'s did. Conversely, an integration that
  ABI-decodes a `bool` (solc ≥ 0.4.22 `returns (bool)` interface) **reverts** on every USDT
  transfer: a concrete witness by kernel evaluation.
- **USDT approve race guard breaks re-approval.** Any integration that calls
  `approve(spender, x)` with a nonzero existing allowance reverts; e.g. a vault that
  re-approves a router each deposit. The witness is the `usdt` scenario's second call;
  a theorem: `approve` succeeds iff `v = 0 ∨ alw = 0` (and payload ≥ 68).
- **Fee-on-transfer breaks vault accounting.** With STA (or USDT with the fee on) as the
  asset, Solmate's `deposit(a)` mints shares for `a` while the vault receives `a − fee(a)`:
  `totalAssets` grows by less than credited, so the share price falls and the first-depositor
  and solvency properties fail; a concrete bytecode witness (two deposits, one redeem that
  reverts or underpays) by kernel evaluation over the STA runtime code.
- **Rebasing breaks vault solvency.** With AMPL as the asset, a negative `rebase` lowers
  `asset.balanceOf(vault)` with no vault interaction: `convertToAssets` drops for all holders
  and a vault caching balances becomes insolvent; a positive rebase gives an unaccounted
  surplus. Witness: deposit, `rebase(−δ)`, withdraw of the previewed amount reverts.
- **BNB's zero-value revert** breaks integrations that transfer computed amounts that can
  be 0 (fee splits, dust sweeps); witness by `transfer(x, 0)`.
- **Phantom functions**: calling `permit` on BNB "succeeds" without effect; an integration
  relying on `permit` for authorization then uses a stale allowance (witness: the scenario's
  phantom call).

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

**Results** (`nice -n 19 lake exe difftest --seed 2026 --family all --sequences 30 --length
40`): **13,358 transactions** (7,924 successful on both sides) over the 3 vault and 8 token
families, **0 mismatches**, 510 s; every fixed scenario and layout check agrees. The random
sequences reached the quirks: USDT `deprecate` succeeded 14 times (followed by forwarded
calls to code-less or self addresses), `pause` 13, `setParams` 4 (plus the `usdtfee`
genesis), `destroyBlackFunds` 2; AMPL `rebase` 16, a successful `upgradeTo` by the admin;
WETH9 189 deposits, 77 fallback deposits, 115 withdrawals; BNB 63 phantom/fallback calls. An
earlier run (`--seed 2026 --family oz3,tokens --sequences 40 --length 40`, before the
mainnet weird tokens): 6,445 transactions, 0 mismatches. No evm-lean discrepancy was found.


## Model-level results

Proved in Mathlib (standard axioms only, `#print axioms` checked), no bytecode yet.

**The variant model** (`defi/Defi/ERC20/Variant.lean`). `Defi.ERC20.Variant A` is a record of
policies: return data per entry point (`bool`/`empty`), how guards and insufficient
balance/allowance fail (`revert`/`invalid`/`returnFalse`), zero-address checks (also inside
OZ's `_spendAllowance`), `rejectsSelf`, `zeroValueReverts`, `approveGuard`, infinite
allowances (`none`/`= MAX`/`≥ MAX`), WETH's self-spend, Solady's Permit2, `fee`
(`bpsCapped`: USDT `min(v·bps/10⁴, maxFee)`; `ceilPercent 100`: STA `⌈v/100⌉`) with a sink
(`owner`/`burn`), `pausable`, `blacklist` (+ `destroyBlackFunds`), `rebasing` (gons with
`scale = TOTAL_GONS / supply`), mint/burn authority, the fallback (`revert`/`accept`/`deposit`),
and `totalSupply` stored or the ether balance. `VState A` holds every field; `Variant.call`
adds the observable outcome and `Result.safe`/`decoded`/`unchecked` are the three ways a
caller consumes it. Instances: `standard` (Solmate), `oz`, `solady p`, `weth9`, `usdt`, `bnb`,
`sta`, `ampl`.

| Theorem | Statement |
|---|---|
| `Variant.standard_transfer`, `_transferFrom`, `_approve`, `_mint`, `_burn` | `standard`'s operations are `Token.transfer` … (through `VState.toToken`/`withToken`) |
| `Variant.oz_transfer`, `_transferFrom`, `_approve`, `_mint`, `_burn` | `oz`'s operations are `Token.ozTransfer` … |
| `Variant.safe_call` | through `SafeTransferLib`/`SafeERC20` a call is exactly its state change, for every return and failure convention |
| `Variant.usdt_decoded_eq_none`, `bnb_decoded_transfer` | a `returns (bool)` decoder rejects every USDT `transfer`/`transferFrom`/`approve` and every BNB `transfer` |
| `Variant.usdt_call_invalid`, `unchecked_call_returnFalse`, `bnb_phantom` | USDT fails with `INVALID` on insufficient balance; ignoring return data continues after `false`; BNB's fallback accepts any unknown selector (e.g. `permit`) with no effect |
| `Variant.WF_exec` (+ `*_sane`) | the supply invariant holds after any operation sequence for every `Sane` variant: `Σ bal = supply ≤ MAX` (owner fees stay in `Σ`, burned fees and `destroyBlackFunds` leave both sides), `Σ bal ≤ ether` (WETH9), `Σ gons = TOTAL_GONS ∧ scale = TOTAL_GONS/supply` (rebasing) |
| `Variant.sum_balanceOf_le_supply` | rebasing: `Σ ⌊gons/scale⌋ ≤ supply` (from `cap² ≤ TOTAL_GONS`; for AMPL `(2¹²⁸−1)² ≤ TOTAL_GONS`) |
| `Variant.weth9_backed_exec`, `weth9_deposit`, `weth9_withdraw` | ether backing `Σ balanceOf ≤ address(this).balance` under deposits, withdrawals, transfers, forced ether; exact deposit/withdraw effects, withdrawal liveness |
| `Variant.move_balanceOf` | without fee every variant (rebasing included) moves exactly `v` in the `balanceOf` view |
| `Variant.move_fee_dst`, `move_fee_src`, `move_fee_supply` | with a fee the recipient gets `v − fee`, the payer loses `v`, a burned fee leaves the supply |
| `Variant.usdt_approve_isSome_iff`, `approve_approve_eq_none`, `usdt_approve_reset`, `bnb_approve_zero` | USDT `approve` succeeds iff `v = 0 ∨ allowance = 0`; approve-then-approve fails; resetting to 0 works on USDT and is impossible on BNB |

**The vaults over an asset variant** (`defi/Defi/ERC4626/AssetVariants.lean`). `Asset σ A`
abstracts what a vault uses (balance view, `transfer`, `transferFrom`); `GSolmate` and `GOz`
are the two vault models over any `Asset`, and `GSolmate.deposit_solmate` …,
`GOz.deposit_oz` … prove they are the existing models over `Asset.solmate`/`Asset.oz`.
`Asset.variant V` is a variant behind `SafeTransferLib`. For any asset: share ledger
invariant (`Inv_*`) and solvency (`GSolmate.solvent`, `GOz.solvent`); for an
`Asset.ExactOn` asset: no dilution (`GSolmate.*_price_mono` while `S > 0`, `GOz.*_price_mono`
always). `Asset.variant_exactOn`: every variant is exact in a fee-free state (`NoFee`).

**Integration** (`defi/Defi/ERC4626/Integration.lean`, namespace `Defi.ERC4626.Integration`):

| Theorem | Statement |
|---|---|
| `solmate_vinv_deposit`, `_mint`, `_withdraw`, `_redeem` | asset `WF` and share ledger preserved for every `Sane` variant, fees and rebasing included: the breakage below is economic, not a ledger bug |
| `noFee_solmate_*_price_mono`, `noFee_oz_*_price_mono`; `usdt_solmate_deposit_price_mono`, `bnb_solmate_deposit_price_mono` | (a) no dilution with any fee-free variant whatever its conventions: USDT with `basisPointsRate = 0` (`usdt_noFee`), BNB (`bnb_noFee`), AMPL between rebases (`ampl_noFee`) |
| `naive_usdt_deposit_eq_none`, `naive_usdt_withdraw_eq_none` | a vault that decodes a `bool` reverts on every USDT deposit and withdrawal |
| `unchecked_returnFalse_deposit` | a vault ignoring return data mints shares without receiving tokens from a `returnFalse` token |
| `fee_deposit_totalAssets` | (b) deposit of `a` with fee `f`: `T' + f = T + a` while shares are minted for `a` |
| `fee_deposit_dilution` | exactly `T·S' + ρ = T'·S + f·S` with rounding remainder `ρ = a·S − n·T < T`: existing holders lose `(f·S − ρ)/S'` |
| `fee_deposit_price_drop`, `oz_fee_deposit_price_drop` | if the fee is worth a share (`T ≤ f·S`; OZ `T̂ ≤ f·Ŝ`) the price strictly drops (`T'·S < T·S'`), refuting no-dilution |
| `fee_withdraw_receiver` | `withdraw(a)` delivers `a − fee(a)` (EIP-4626: exactly `a`) |
| `sta_solmate_witness` | STA: alice deposits 100 (100 shares, vault gets 99), bob deposits 100 (101 shares, vault 198); alice's shares go from 99 to 98 (`99·201 > 198·100`), she redeems 98 and receives 97: bob's inbound fee is socialised onto her |
| `rebase_totalAssets`, `negative_rebase_totalAssets_le`, `positive_rebase_accrues` | a rebase sets `T = gons/(TOTAL_GONS/S)` with no vault call; negative lowers `T`, positive raises it and every holder's `convertToAssets` |
| `ampl_rebase_witness` | AMPL: deposit 100 (100 shares); after halving the supply the shares are worth 50 and the previewed `withdraw(100)` reverts; after doubling, worth 200 |
| `usdt_reapprove_reverts` | (c) `approve(x)` then `approve(y)`, `x, y ≠ 0`: the second call halts with `REVERT` |
| `usdt_reapprove_after_pull` | after `approve(x)` (`x < MAX`) and a spender's `transferFrom` of `x'`, a nonzero `approve(y)` succeeds iff `x' = x` |

**Left for the bytecode phase**: refinement of each mainnet/compiled token against its
instance (`processMessageCall` = `Variant.call` lifted through a per-token storage layout,
including the `INVALID`/`REVERT` distinction and empty return data), and of the vaults'
`SafeTransferLib`/`SafeERC20` call sites against `Result.safe` so that the integration
theorems above transfer to the deployed code; events per operation; the parts the model does
not cover (USDT deprecation forwarding, BNB `freeze`/`unfreeze`/`withdrawEther`, STA allowance
helpers, `permit`, fee-arithmetic overflow, AMPL `transferAll` and dust), and WETH's
2300-gas stipend callee summary.
