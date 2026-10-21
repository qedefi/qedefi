# Token verification targets

Preparation for verifying further tokens, one at a time, each as `qedefi/Examples/<Project>/`
with pinned sources, artifacts, differential tests, a refinement against the `QEDefi.ERC20`
model and invariants, the way Solmate's ERC-4626 vault is verified
([erc4626](erc4626/README.md)). Besides Solmate, only OpenZeppelin's `ERC20` is proved on the
bytecode so far (below); this file records what each target is, exactly, and what should be
proved about it. The model-level results (the
`QEDefi.ERC20.Variant` model and its integration with the vault models) are in the last section.

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
| GUSD (2 decimals; `CALL` proxy + implementation + store) | **mainnet** `0x056F…d5Cd` / `0x483A…40A2` / `0xc42B…68a0` | `contracts/mainnet/{GUSD,GUSDImpl,GUSDStore}/` | `Examples.WeirdERC20.GUSD.Contracts.{GUSD,GUSDImpl,GUSDStore}` | `gusd` |
| YAMv2 (24 decimals) | **mainnet** `0xAba8…aD8A` | `contracts/mainnet/YAMV2/` | `Examples.WeirdERC20.YAMV2.Contracts.YAMV2` | `yamv2` |
| LEND (zero-value transfers revert; approve guard; ICO) | **mainnet** `0x80fB…ab03` | `contracts/mainnet/LEND/` | `Examples.WeirdERC20.LEND.Contracts.LEND` | `lend`, `lendico` |
| ZRX (returns `false` instead of reverting) | **mainnet** `0xE41d…F498` | `contracts/mainnet/ZRX/` | `Examples.WeirdERC20.ZRX.Contracts.ZRX` | `zrx` |

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
(`qedefi/Examples/Solmate/ERC20/`) and 1, 4, 7 through the vault proofs.

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

**Differences from Solmate's `ERC20`** (both already modelled in `QEDefi.ERC20.Token`:
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

**Proved on the bytecode** (`qedefi/Examples/OpenZeppelin/ERC20/`, top-level calls with zero
value): property 2 without logs and revert data, the storage part of 3, and the
`totalSupply`/`balanceOf`/`allowance`/`decimals` part of 5 (1 is `Token.WF_oz*`):

- `EvmLogic.Solidity.ERC20Oz`: `Layout.oz = ⟨2, 0, 1⟩`, the word-level model `Model.ozTransfer`,
  `ozApprove`, `ozSpend`, `ozTransferFrom`, `ozMint`, `ozBurn` (Solmate's `Model` operations
  behind the zero-address checks, plus `_update`'s mint/burn), the code's `SSTORE` sequences
  (`moveWorld`, `allowanceWorld`, `ozSpendWorld`, `ozTransferFromWorld`, `mintWorld`,
  `burnWorld`, for any layout) and their `view_*World` theorems. Writing the supply slot needs
  `SupplySlotOk` (no balance row hashes to slot 2).
- `Transfer`, `Approve`, `TransferFrom`, `MintBurn`: success and each revert path (every
  zero-address check, insufficient balance/allowance, supply overflow; infinite vs. finite
  allowance), and `*_spec`: `processMessageCall` refines `Model.oz*` through `ERC20.view`
  (revert ⇒ world unchanged; success ⇒ supply, balances, allowances in unwritten slots, other
  accounts unchanged). `Views`: the four views return the view's words, world unchanged.
- `QEDefi.ERC20.RepOz` (`Model.oz*` and `Token.oz*` succeed together, related results on
  `Token.WF` ledgers) and `Spec` (`*_refines`): the bytecode against `Token.ozTransfer` etc.
  directly, hence `Variant.oz` by `Variant.oz_transfer`/….

Not yet: events (`Transfer`, `Approval` logs), revert data, calls with value, `name`/`symbol`,
callee summaries in arbitrary frames (needed for the OZ vaults), malformed calldata, nested
callers (7).

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

**Properties to prove on the bytecode**: the refinement `OzVaultOffset ⊑ QEDefi.ERC4626.Oz`
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
- `permit` refinement as for Solmate (`QEDefi.ERC20.Permit`), with Solady's revert order;
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
bounded by `S`. Structurally this is an ERC-4626-like share ledger, so `QEDefi.ERC4626` rounding
lemmas apply.

### GUSD (Gemini dollar): 2 decimals, three contracts linked by `CALL`

**Contracts** (all at their mainnet addresses; custodian alice in each genesis):
`ERC20Proxy` at the token address (0.4.21, optimizer 200, 3,490 B), `ERC20Impl`
`0x483A…40A2` (0.8.30, optimizer 100,000, 12,180 B; deployed 2026-10-09, immutables
`erc20Proxy`, `erc20Store`), `ERC20Store` `0xc42B…68a0` (0.4.21, 2,026 B). Every proxy
entry point calls `erc20Impl.xWithSender(msg.sender, …)`; the implementation reads and writes
the store through its setters and calls back `proxy.emitTransfer`/`emitApproval`, so the
logs of a transfer come from the token address while the state changes in the store: one
`transfer` is a depth-3 call tree (proxy → impl → store ×2, impl → proxy).

**Layout**: proxy 0 `lockRequestCount`, 1 `custodian`, 2 `custodianChangeReqs`, 3
`erc20Impl`, 4 `implChangeReqs`, 5 `name`, 6 `symbol`, 7 `decimals` (2); store 0–4 the same
prefix (`erc20Impl` in slot 3), 5 `totalSupply`, 6 `balances`, 7 `allowed`; implementation 0
`lockRequestCount`, 1 `custodian`, 2 `custodianChangeReqs`, 3 `pendingPrintMap` (struct
`receiver`, `value` in two slots).

**Deviations** (in the `gusd` scenario): 2 decimals; transfers and approvals to `0` revert;
`increaseApproval`/`decreaseApproval` with explicit overflow checks; infinite allowances
decremented; no approve guard. **The proxy does not bubble revert data**: the implementation
reverts with `"zero address"`, `"insufficient balance"` …, the token address returns empty
revert data (0.4.21 `require(call)`); calls to the implementation directly return the strings.
`batchTransfer(tos, values)` (implementation, any holder) checks the lengths, skips the
ledger update for self-entries but still emits their `Transfer`; `burn(v)` (holder) and
custodian-only `executePrint`, `burn(owner, v)`; `requestPrint` returns a lock id hashing
`BLOCKHASH(number − 1)`, the implementation's address and a counter, `confirmPrint(lockId)`
(custodian) mints it. Access control: store setters only from `erc20Impl`, `emitTransfer`
/`emitApproval` only from the implementation, `*WithSender` only from the proxy. The custodian
can replace the implementation of the proxy or the store (`requestImplChange` then
`confirmImplChange(lockId)`): with an EOA as implementation every proxy call reverts
(extcodesize check), with the store re-pointed the implementation's writes revert.

**Model variant**: `Variant` with return `bool`, `zeroAddressReverts` (recipient and
spender), checked allowance helpers; the three-contract structure is a *frame* question
(the ledger lives in another account, written only by the current implementation): a
refinement relates the store's storage, not the token's, to `VState`; revert data is lost at
the proxy.

### YAMv2: 24 decimals

`YAMv2` (0.6.12, optimizer 50,000, 3,683 B), an OpenZeppelin-3 style token with
`_setupDecimals(24)` and a `minter` (no burn). **Layout**: 0 `minter`, 1 `_balances`, 2
`_allowances`, 3 `_totalSupply`, 4 `_name`, 5 `_symbol`, 6 `_decimals`. Balances in the tests
are `~10³⁰` (a million tokens), so amounts sit 6 orders of magnitude above 18-decimals
tokens; nothing overflows before `2²⁵⁶` (SafeMath with string reasons). **Deviations** (in the
`yamv2` scenario): string revert reasons (`"!minter"`, `"ERC20: transfer amount exceeds
balance"`, …); `transferFrom` moves the tokens *before* spending the allowance, so a
transfer that fails both checks reports the balance; the spend emits `Approval`; infinite
allowances decremented; zero-address checks on sender, recipient, owner, spender and mint
recipient. The variant is OZ's with `decimals = 24`; the generic catalogue holds unchanged.

### LEND (EthLend): zero-value transfers revert

`EthLendToken` (0.4.16, unoptimized, 6,872 B). **Layout**: 0 `balances`, 1 `allowed`, 2
`supply`, 3 `currentState` (enum, byte 0), `enableTransfers` (byte 1), `teamTokenBonus`
(bytes 2–21), 4 `escrow`, 5 `tokenManager`, 6 `presaleSoldTokens`, 7 `icoSoldTokens`, 8
`totalSoldTokens`. **Deviations** (in the `lend` scenario, mainnet state ICOFinished):
`transfer`/`transferFrom` require `balances[to] + v > balances[to]` — **zero-value transfers
revert** (also self-transfers of 0 and `transferFrom` of 0); the approve race guard (as USDT,
but returning `true`); infinite allowances decremented; no zero-address checks; transfers and
approvals gated by `enableTransfers` (set exactly when the state becomes ICOFinished, which
is final). The `lendico` family reopens the ICO (state ICORunning, transfers disabled):
`buyTokens`/the payable fallback mint `msg.value · price` (price tiers 27,500 / 26,250 /
25,000 per ether by `icoSoldTokens`; the genesis puts the first tier boundary 1,000 tokens
away), `withdrawEther` sends the whole ether balance to the escrow with `send` (2,300
stipend), `setState` by the token manager (out-of-range enum values halt
exceptionally: all gas consumed), and transfers
unlock at ICOFinished. **Model variant**: `zeroValueReverts` (strict-increase check, so also
for self-transfers), `approveGuard`, a global `paused` (= `¬enableTransfers`) that also
covers `approve`, and a sale entry point minting against ether.

### ZRX (0x Protocol Token): failures return `false`

`ZRXToken` (0.4.11, unoptimized, 2,946 B). **Layout**: 0 `balances`, 1 `allowed`, 2
`StandardToken.totalSupply` (**shadowed**: `ZRXToken` redeclares `totalSupply`, the
constructor and the public getter use slot 3; slot 2 is 0 on mainnet), 3 `totalSupply`.
`name`, `symbol`, `decimals` are constants. **Deviations** (in the `zrx` scenario):
insufficient balance or allowance makes `transfer`/`transferFrom` **return `false`** with
status success, no event and no state change (an integration that ignores the return value
proceeds as if paid); an allowance of exactly `2²⁵⁶ − 1` is not spent; no zero-address checks
(transfers to `0` keep the supply); zero transfers and self-transfers succeed. Unknown
selectors fail by `throw` and consume all gas (204 of 276 malformed calls in campaign pass
A; arguments cut short are read as zeros, so the others succeed). **Model variant**: failure convention `returnFalse` (already in `QEDefi.ERC20.Variant`, so
`unchecked_call_returnFalse` and `unchecked_returnFalse_deposit` apply to ZRX as is),
`infiniteAllowance = MAX`.

### Recorded examples (not targets)

USDC and PAXG (zos-slot proxies; PAXG's current implementation has no transfer fee anymore,
contrary to the `weird-erc20` list). Addresses and code hashes in `contracts/README.md`.

### The `QEDefi/ERC20` variant these need

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

## Generalizing `QEDefi/ERC20` into a reusable kit

Today: `QEDefi.ERC20.Token` (balances `A →₀ ℕ`, supply, allowances) with Solmate operations
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
   `Events`/`Logs` modules of `QEDefi.ERC4626` show the pattern.
5. **One refinement theorem shape** per token: for each selector, the bytecode's
   `processMessageCall` result equals the model step lifted through `Rep` (as
   `Examples.Solmate.ERC20.Spec`), so the vault theorems (`QEDefi.Trace.Lift`) can be
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
`qedefi/`; `--edge` and `--low-gas PCT` as in `contracts/README.md`). The GUSD family installs
all three contracts with their own storage, compares the storage of all three and sends 30 %
of its ABI calls to the implementation and the store directly (`batchTransfer`, prints, the
custodian's and the access-controlled setters); lock ids returned by earlier calls are reused
as `bytes32` arguments, so `confirmPrint`/`confirmImplChange`/`confirmCustodianChange` hit
real requests. Token families (`qedefi/Examples/Differential/Token.lean`): compiled tokens are
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

## Differential campaign

Run on 2026-10-21 (commits `da1fd70`…`e29730d`), every family in its own `difftest` process,
one at a time, at `nice -n 19` on a shared 12-core machine: pass A with the standard
generators, pass B edge-case-heavy. Seeds are per family (`--seed` below, one process per
family, so the family index is 0 and the generator state of sequence `k` is
`seed · 1,000,003 + k`); every run is reproducible from `lake exe difftest --seed S --family F`
with the options shown. "Fail" counts calls that failed on both sides (reverts, `INVALID`,
out of gas: any status mismatch would be a mismatch); "exceptional halts" are failures that
consumed the whole gas limit (out of gas, `INVALID`, invalid jumps); "low-gas calls" are
those whose limit `--low-gas` lowered, with how many of them halted. The special paths count
successful calls of each quirk (ZRX: calls that returned `false`).

**Totals: 240,460 transactions, 144,245 successful on both sides, 7,486 exceptional halts,
19,842 low-gas calls (3,065 out of gas or halted), 0 mismatches** (9,075 s of niced runtime).
Every fixed scenario, getter check and storage-layout check agreed.

**Pass A** (`--sequences 200 --length 50 --low-gas 5`):

| Family | Seed | Transactions | Both succeed | Fail | Exceptional halts | Low-gas calls (halted) | Mismatches | Time | Special paths (successes unless noted) |
|---|---|---|---|---|---|---|---|---|---|
| `solmate` | 2026102100 | 10,015 | 5,347 | 4,668 | 89 | 466 (89) | 0 | 361 s | 111 deposits, 45 redeems, 400 withdrawals, 157 invalid permits |
| `oz` | 2026102101 | 10,015 | 5,693 | 4,322 | 90 | 490 (90) | 0 | 363 s | 367 deposits, 369 redeems, 412 withdrawals |
| `oz3` | 2026102102 | 10,015 | 5,741 | 4,274 | 57 | 492 (57) | 0 | 360 s | 384 deposits, 384 redeems, 400 withdrawals |
| `oz20` | 2026102103 | 10,010 | 6,531 | 3,479 | 76 | 509 (76) | 0 | 359 s | 1,043 mints, 469 burns, 581 transferFroms |
| `solady` | 2026102104 | 10,010 | 6,358 | 3,652 | 66 | 478 (66) | 0 | 344 s | 584 permits, 639 transferFroms, 245 failed approves (Permit2 rule) |
| `weth9` | 2026102105 | 10,010 | 7,597 | 2,413 | 70 | 514 (70) | 0 | 446 s | 1,638 deposits, 669 fallback deposits, 1,004 withdrawals |
| `usdt` | 2026102106 | 10,023 | 5,420 | 4,603 | 1,341 | 485 (125) | 0 | 363 s | 33 deprecations, 47 pauses, 7 fee changes, 1 destroyBlackFunds, 1,341 INVALID/OOG halts |
| `usdtfee` | 2026102107 | 10,023 | 5,407 | 4,616 | 1,357 | 497 (127) | 0 | 365 s | 757 fee transfers, 36 deprecations, 1,357 INVALID/OOG halts |
| `bnb` | 2026102108 | 10,013 | 5,682 | 4,331 | 66 | 485 (66) | 0 | 524 s | 696 phantom/fallback calls, 394 freezes, 35 unfreezes, 40 withdrawEther |
| `sta` | 2026102109 | 10,011 | 6,077 | 3,934 | 505 | 505 (105) | 0 | 360 s | 1,283 fee transfers, 52 destroyFrom, 505 INVALID/OOG halts |
| `ampl` | 2026102110 | 10,013 | 5,321 | 4,692 | 50 | 502 (50) | 0 | 394 s | 139 rebases, 263 transferAll, 2 upgrades |
| `gusd` | 2026102111 | 10,019 | 5,735 | 4,284 | 52 | 530 (52) | 0 | 432 s | 99 batchTransfers, 144 print requests, 0 confirmed prints, 4 proxy impl changes, 1 store impl changes, 4 custodian changes |
| `yamv2` | 2026102112 | 10,013 | 5,762 | 4,251 | 69 | 528 (69) | 0 | 397 s | 225 mints, 433 transferFroms |
| `lend` | 2026102113 | 10,015 | 5,846 | 4,169 | 53 | 499 (53) | 0 | 441 s | 581 failed transfers, 223 failed approves |
| `lendico` | 2026102114 | 10,014 | 4,990 | 5,024 | 65 | 461 (44) | 0 | 447 s | 207 purchases, 435 fallback purchases, 69 state changes, 42 withdrawEther |
| `zrx` | 2026102115 | 10,011 | 9,734 | 277 | 277 | 475 (73) | 0 | 323 s | 934 transfer → false/0, 2,148 transferFrom → false/0, 277 halts |

**Pass B** (`--sequences 100 --length 50 --edge --low-gas 15`):

| Family | Seed | Transactions | Both succeed | Fail | Exceptional halts | Low-gas calls (halted) | Mismatches | Time | Special paths (successes unless noted) |
|---|---|---|---|---|---|---|---|---|---|
| `solmate` | 2026102200 | 5,015 | 2,600 | 2,415 | 126 | 737 (126) | 0 | 159 s | 45 deposits, 26 redeems, 186 withdrawals, 78 invalid permits |
| `oz` | 2026102201 | 5,015 | 2,835 | 2,180 | 152 | 749 (152) | 0 | 168 s | 220 deposits, 184 redeems, 198 withdrawals |
| `oz3` | 2026102202 | 5,015 | 2,900 | 2,115 | 137 | 793 (137) | 0 | 167 s | 201 deposits, 192 redeems, 187 withdrawals |
| `oz20` | 2026102203 | 5,010 | 3,047 | 1,963 | 107 | 751 (107) | 0 | 151 s | 485 mints, 196 burns, 273 transferFroms |
| `solady` | 2026102204 | 5,010 | 2,982 | 2,028 | 90 | 720 (90) | 0 | 143 s | 310 permits, 317 transferFroms, 137 failed approves (Permit2 rule) |
| `weth9` | 2026102205 | 5,010 | 3,692 | 1,318 | 119 | 774 (119) | 0 | 190 s | 804 deposits, 329 fallback deposits, 446 withdrawals |
| `usdt` | 2026102206 | 5,023 | 2,564 | 2,459 | 719 | 741 (174) | 0 | 160 s | 35 deprecations, 16 pauses, 3 fee changes, 1 destroyBlackFunds, 719 INVALID/OOG halts |
| `usdtfee` | 2026102207 | 5,023 | 2,620 | 2,403 | 660 | 698 (157) | 0 | 165 s | 363 fee transfers, 24 deprecations, 660 INVALID/OOG halts |
| `bnb` | 2026102208 | 5,013 | 2,692 | 2,321 | 101 | 784 (101) | 0 | 194 s | 335 phantom/fallback calls, 174 freezes, 16 unfreezes, 14 withdrawEther |
| `sta` | 2026102209 | 5,011 | 2,858 | 2,153 | 318 | 743 (141) | 0 | 162 s | 623 fee transfers, 15 destroyFrom, 318 INVALID/OOG halts |
| `ampl` | 2026102210 | 5,013 | 2,487 | 2,526 | 82 | 729 (82) | 0 | 163 s | 82 rebases, 121 transferAll, 0 upgrades |
| `gusd` | 2026102211 | 5,019 | 2,807 | 2,212 | 79 | 758 (79) | 0 | 172 s | 43 batchTransfers, 59 print requests, 2 confirmed prints, 2 proxy impl changes, 0 store impl changes, 3 custodian changes |
| `yamv2` | 2026102212 | 5,013 | 2,847 | 2,166 | 119 | 755 (119) | 0 | 180 s | 106 mints, 205 transferFroms |
| `lend` | 2026102213 | 5,015 | 2,820 | 2,195 | 78 | 710 (78) | 0 | 221 s | 323 failed transfers, 114 failed approves |
| `lendico` | 2026102214 | 5,014 | 2,481 | 2,533 | 77 | 718 (67) | 0 | 221 s | 123 purchases, 208 fallback purchases, 29 state changes, 24 withdrawEther |
| `zrx` | 2026102215 | 5,011 | 4,772 | 239 | 239 | 766 (124) | 0 | 180 s | 501 transfer → false/0, 1,036 transferFrom → false/0, 239 halts |


Notes. The first pass-A `weth9` run stopped after its scenario: `--low-gas` repeated a call
with ether its sender no longer had, which anvil rejects (fixed in `40fad80`; the table shows
the rerun). Pass-A `gusd` was rerun with lock-id reuse (`e29730d`); the first run (10,019
transactions, 0 mismatches, 0 confirmed prints) is superseded. Coverage gaps: GUSD prints are
rarely confirmed (2 in pass B: a lock id must reach `confirmPrint` from the custodian), AMPL
upgrades and USDT `destroyBlackFunds` are rare, and BLOCKHASH beyond `number − 1` is not
provided to evm-lean (no target reads it). Lowered gas limits were applied to calls that
go through external calls too (GUSD's proxy → implementation → store, AMPL's `DELEGATECALL`,
WETH9/BNB/LEND ether sends, USDT's deprecated forwarding), where the 63/64 rule and the
stipend decide whether the inner or the outer frame runs out; the tester does not record at
which depth a call ran out of gas.

**Result: no discrepancy between evm-lean and anvil (revm) was found.** Status, return and
revert data, logs, receipt `gasUsed` (refunds included), every touched storage slot of every
contract and, for ether-holding tokens, the ether balances agreed on all 240,460
transactions.

## Model-level results

Proved in Mathlib (standard axioms only, `#print axioms` checked), no bytecode yet.

**The variant model** (`qedefi/QEDefi/ERC20/Variant.lean`). `QEDefi.ERC20.Variant A` is a record of
policies: return data per entry point (`bool`/`empty`), how guards and insufficient
balance/allowance fail (`revert`/`invalid`/`returnFalse`), zero-address checks (also inside
OZ's `_spendAllowance`), `rejectsSelf`, `zeroValueReverts`, `approveGuard`, infinite
allowances (`none`/`= MAX`/`≥ MAX`), WETH's self-spend, Solady's Permit2, `fee`
(`bpsCapped`: USDT `min(v·bps/10⁴, maxFee)`; `ceilPercent 100`: STA `⌈v/100⌉`) with a sink
(`owner`/`burn`), `pausable`, `blacklist` (+ `destroyBlackFunds`), `rebasing` (gons with
`scale = TOTAL_GONS / supply`), mint/burn authority, the fallback (`revert`/`accept`/`deposit`),
`totalSupply` stored or the ether balance, and the extra entry points: BNB's
`freeze`/`unfreeze` ledger and `withdrawEther`, allowance helpers (`checked`: STA;
`saturating`: AMPL), STA's `destroyFrom`, AMPL's `transferAll`/`transferAllFrom`, and EIP-2612
`permit` (`eip2612 rejectZero wraps`: Solmate/Solady `true true`, AMPL `false false`; without
it a `permit` call reaches the fallback). The fee computation's SafeMath overflow
(`feeOverflow`) fails a transfer with `INVALID` (`failKind`). `VState A` holds every field
(including `frozen` and `nonces`); `Variant.call` adds the observable outcome and
`Result.safe`/`decoded`/`unchecked` are the three ways a caller consumes it. Instances:
`standard` (Solmate), `oz`, `solady p`, `weth9`, `usdt`, `bnb`, `sta`, `ampl`.

| Theorem | Statement |
|---|---|
| `Variant.standard_transfer`, `_transferFrom`, `_approve`, `_mint`, `_burn` | `standard`'s operations are `Token.transfer` … (through `VState.toToken`/`withToken`) |
| `Variant.oz_transfer`, `_transferFrom`, `_approve`, `_mint`, `_burn` | `oz`'s operations are `Token.ozTransfer` … |
| `Variant.safe_call` | through `SafeTransferLib`/`SafeERC20` a call is exactly its state change, for every return and failure convention |
| `Variant.usdt_decoded_eq_none`, `bnb_decoded_transfer` | a `returns (bool)` decoder rejects every USDT `transfer`/`transferFrom`/`approve` and every BNB `transfer` |
| `Variant.usdt_call_invalid`, `unchecked_call_returnFalse`, `bnb_phantom` | USDT fails with `INVALID` on insufficient balance; ignoring return data continues after `false`; BNB's fallback accepts any unknown selector (e.g. `permit`) with no effect |
| `Variant.WF_exec` (+ `*_sane`) | the supply invariant holds after any operation sequence for every `Sane` variant: `Σ bal + Σ frozen = supply ≤ MAX` (owner fees stay in `Σ`, burned fees, `destroyBlackFunds` and `destroyFrom` leave both sides, freezing moves between the ledgers), `Σ bal ≤ ether` (WETH9), `Σ gons = TOTAL_GONS ∧ scale = TOTAL_GONS/supply` (rebasing; `transferAll` moves whole gon balances) |
| `Variant.sum_balanceOf_le_supply` | rebasing: `Σ ⌊gons/scale⌋ ≤ supply` (from `cap² ≤ TOTAL_GONS`; for AMPL `(2¹²⁸−1)² ≤ TOTAL_GONS`) |
| `Variant.weth9_backed_exec`, `weth9_deposit`, `weth9_withdraw` | ether backing `Σ balanceOf ≤ address(this).balance` under deposits, withdrawals, transfers, forced ether; exact deposit/withdraw effects, withdrawal liveness |
| `Variant.move_balanceOf` | without fee every variant (rebasing included) moves exactly `v` in the `balanceOf` view |
| `Variant.move_fee_dst`, `move_fee_src`, `move_fee_supply` | with a fee the recipient gets `v − fee`, the payer loses `v`, a burned fee leaves the supply |
| `Variant.usdt_approve_isSome_iff`, `approve_approve_eq_none`, `usdt_approve_reset`, `bnb_approve_zero` | USDT `approve` succeeds iff `v = 0 ∨ allowance = 0`; approve-then-approve fails; resetting to 0 works on USDT and is impossible on BNB |

**The extra entry points** (`qedefi/QEDefi/ERC20/VariantExtras.lean`, namespace
`QEDefi.ERC20.Variant`):

| Theorem | Statement |
|---|---|
| `usdt_call_transfer`, `usdt_call_transferFrom` | complete outcome of a USDT transfer (`bps ≤ 10⁴`): `REVERT` iff paused or the sender (`transferFrom`: `from`; spender and recipient unchecked) is blacklisted; else `INVALID` iff the allowance (unless `≥ MAX`) or balance is short or `MAX < v·bps` (SafeMath `mul` `assert`, computed first); else success, no return data |
| `usdt_feeOverflow_false`, `usdt_overflow_unreachable` | with `bps < 20` the overflow needs `v > MAX/19 ≈ 6.1·10⁷⁵`; unreachable in a well-formed state with `19·totalSupply ≤ MAX` |
| `sta_feeOverflow_iff`, `sta_call_transfer_overflow`, `sta_call_transfer_short` | STA's `cut` overflows iff `MAX < ⌈v/100⌉·100·100` (the `.mul(basePercent)` step, from `v ≈ MAX/100`, not `ceil`'s `v + 100`); that is `INVALID`, while a short balance is `REVERT` |
| `bnb_freeze`, `bnb_unfreeze`, `bnb_freeze_unfreeze` | `freeze`/`unfreeze` are holder-level (not owner-only): fail iff short, `v = 0` or overflow; freezing is undone exactly by unfreezing |
| `bnb_supply_exec`, `bnb_sum_lt_supply` | `Σ balanceOf + Σ freezeOf = totalSupply ≤ MAX` after any sequence; `Σ balanceOf < totalSupply` while anything is frozen |
| `bnb_withdrawEther_not_owner`, `bnb_withdrawEther`, `ether_le_stepOp`, `bnb_ether_le_stepOp` | `withdrawEther` is owner-only; only `withdraw` (WETH9) and `withdrawEther` lower a token's ether, so BNB's ether (phantom calls' value) leaves only to the owner |
| `sta_upAllowance`, `sta_downAllowance`, `sta_adjustFail` | STA has `upAllowance`/`downAllowance` (no `increaseAllowance`): spender `0` → `REVERT`, overflow/underflow → `INVALID` |
| `ampl_increaseAllowance`, `ampl_decreaseAllowance` | AMPL: increase reverts only on overflow (any spender), decrease saturates at `0`, never fails |
| `sta_burnFrom` | `destroyFrom` fails iff allowance short, `v = 0` or balance short; spends even an infinite allowance |
| `ampl_transferAll_balanceOf`, `ampl_transfer_dust` | `transferAll` moves all gons: sender `0`, recipient gains the reported value or one more; `transfer(balanceOf)` leaves `gons mod gonsPerFragment` behind |
| `standard_permit` | Solmate `permit` is `PermitToken.permit` with validity "not expired ∧ `ecrecover = owner ≠ 0`" |
| `standard_permit_zero_owner`, `ampl_permit_zero_owner`, `ampl_permit_nonce_max`, `standard_permit_wraps` | a failed recovery (`0`) passes for `owner = 0` on AMPL, not on Solmate; AMPL's nonce is checked, Solmate's wraps |
| `weth9_permit_phantom`, `bnb_permit_phantom`, `permit_none_revert` | without `permit`: WETH9 and BNB report success and change nothing; USDT, STA, OZ revert |
| `weth9_permit_then_transferFrom` | `permit` then `transferFrom` on WETH9 = the `transferFrom` alone, whatever the signature: a standing allowance is spent unsigned |
| `withdraw_eq_withdrawWith`, `weth9_withdraw_reject` | `withdraw` is `withdrawWith` with a stipend callee (accept/reject, no storage change: no `SSTORE` under the EIP-2200 sentry, no value transfer; `TSTORE`/logs only, never read by WETH9); a rejection reverts the withdrawal |
| `weth9_backed_withdrawWith`, `weth9_reentrant_withdraw` | even an unbounded reentrant callee keeps the ether backing and cannot withdraw the same funds twice (debit before the call) |

**USDT deprecation** (`qedefi/QEDefi/ERC20/VariantDeprecation.lean`): `DState` is legacy USDT, the
switch, and the upgraded token's state (`none`: no code), the upgraded token any variant `W`
with legacy entry points `byLegacy trusted` (accepted only from `msg.sender = trusted`, then
executed as called by the original user passed as an argument: `msg.sender` is rewritten to
USDT by the forward).

| Theorem | Statement |
|---|---|
| `DState.call_of_not_deprecated` | before deprecation: `usdt.call` |
| `DState.safe_call_deprecated` | through `SafeTransferLib`: USDT's guards (pause, blacklist of caller/`from`; none for `approve`) then `W`'s ordinary entry point called by the original user |
| `DState.call_noCode`, `call_untrusted`, `balanceOf_noCode` | no code at `upgradedAddress`, or an upgraded token not trusting USDT: every transfer/`transferFrom`/`approve` and the views revert |
| `DState.call_halt_revert`, `call_masks_returnFalse` | every failure of `W` (incl. `INVALID`) surfaces as `REVERT`; a `false` from `W` is dropped: success with nothing moved, accepted by `SafeTransferLib` |
| `DState.approve_ignores_guards`, `transfer_guarded`, `call_legacy_eq` | `approve` is forwarded while paused/blacklisted; transfers are not; the legacy ledger is frozen |
| `DState.destroyBlackFunds_deprecated`, `destroyBlackFunds_of_not_deprecated` | after deprecation it zeroes the stale legacy balance and lowers the stale `_totalSupply` by the forwarded balance (unchecked); the live ledger and all views are unchanged; before, it is `usdt`'s |
| `Variant.byLegacy_spoof`, `byLegacyUnchecked_impersonation` | with the `msg.sender` check direct calls revert; without it anyone moves anyone's tokens |
| `DState.deprecated_call`, `deprecated_setDeprecated` | `deprecated` is never cleared |

**The vaults over an asset variant** (`qedefi/QEDefi/ERC4626/AssetVariants.lean`). `Asset σ A`
abstracts what a vault uses (balance view, `transfer`, `transferFrom`); `GSolmate` and `GOz`
are the two vault models over any `Asset`, and `GSolmate.deposit_solmate` …,
`GOz.deposit_oz` … prove they are the existing models over `Asset.solmate`/`Asset.oz`.
`Asset.variant V` is a variant behind `SafeTransferLib`. For any asset: share ledger
invariant (`Inv_*`) and solvency (`GSolmate.solvent`, `GOz.solvent`); for an
`Asset.ExactOn` asset: no dilution (`GSolmate.*_price_mono` while `S > 0`, `GOz.*_price_mono`
always). `Asset.variant_exactOn`: every variant is exact in a fee-free state (`NoFee`).

**Integration** (`qedefi/QEDefi/ERC4626/Integration.lean`, namespace `QEDefi.ERC4626.Integration`):

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

**Vaults over USDT** (`qedefi/QEDefi/ERC4626/IntegrationUsdt.lean`, same namespace):

| Theorem | Statement |
|---|---|
| `usdt_fee_deposit_price_drop`, `usdt_oz_fee_deposit_price_drop` | (a) fee on: if `min(a·bps/10⁴, maximumFee)` is worth a share (`T ≤ fee·S`; OZ `T̂ ≤ fee·Ŝ`), a deposit strictly lowers the price |
| `usdtFee_reachable`, `usdt_fee_witness` | `bps = 19`, `maximumFee = 10⁶` (`setParams(19, 1)`), cap binding: alice deposits 10⁹ (10⁹ shares, vault gets 999·10⁶), bob 10⁹ (1,001,001,001 shares); alice's shares drop from 999,000,000 to 998,500,250, she receives 997,500,250 |
| `blacklisted_vault_withdraw`, `_redeem`, `_oz_withdraw`, `_oz_redeem` | (b) a blacklisted vault: every `withdraw`/`redeem` reverts (USDT checks the sender of `transfer`) |
| `deposit_setBl` | a deposit's outcome depends on the blacklist only at the caller: deposits into a blacklisted vault proceed unchanged |
| `blacklisted_caller_deposit`, `_mint`, `_oz_deposit`, `_oz_mint` | a blacklisted caller cannot deposit or mint (`from` is checked) |
| `destroyBlackFunds_vault`, `blacklisted_vault_witness` | `destroyBlackFunds(vault)` sets `totalAssets = 0` with the shares outstanding; witness: blacklisted vault takes alice's 100, her redeem reverts, then her shares are worth 0 |
| `blacklist_bypass_witness` | a user blacklisted after depositing cannot `transfer` but redeems her shares to another receiver, who gets the USDT |
| `paused_solmate`, `paused_oz` | (c) pausable variant, paused: every `deposit`/`mint`/`withdraw`/`redeem` reverts on both vaults |
| `paused_views`, `oz_paused_views` | `totalAssets` and all conversions/previews ignore `paused` and the blacklist |

**Left for the bytecode phase**: refinement of each mainnet/compiled token against its
instance (`processMessageCall` = `Variant.call` lifted through a per-token storage layout,
including the `INVALID`/`REVERT` distinction and empty return data), and of the vaults'
`SafeTransferLib`/`SafeERC20` call sites against `Result.safe` so that the integration
theorems above transfer to the deployed code; events per operation; the generic EvmLogic
lemma that a stipend frame writes no persistent state (which justifies `stipend` as the only
callees of WETH9's and BNB's ether sends); the parts the model still does not cover (USDT's
deprecation with `upgradedAddress = USDT`, the forwarded gas and short-return quirk; signature
recovery itself, which `permit` takes as a parameter; short-payload checks).
