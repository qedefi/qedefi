# ERC-20 targets

The ERC-20 tokens pinned in this repository, what each one does differently, and what is proved
about them: on the bytecode for Solmate's and OpenZeppelin's `ERC20`, on the model
(`QEDefi.ERC20.Variant`) for the others, together with what their quirks do to the vaults that
hold them. Pinning, layouts and the build are in [contracts/README.md](../contracts/README.md).

| Target | Code | Lean module | `difftest` family | Proved |
|---|---|---|---|---|
| Solmate `ERC20` (`MockERC20`) | compiled | `Verified.Solmate.Contracts.SolmateAsset` | `solmate` (as vault asset) | bytecode ([erc4626](erc4626/README.md)) |
| OpenZeppelin `ERC20` v5.7.0 (`ERC20Mock`) | compiled | `Verified.OpenZeppelin.Contracts.OzAsset` | `oz20`, `oz`, `oz3` | bytecode (below) |
| Solady `ERC20` v0.1.26 (`SoladyToken`) | compiled | `Verified.Solady.Contracts.SoladyToken` | `solady` | model |
| WETH9 | mainnet `0xC02a…6Cc2` | `Verified.WETH9.Contracts.WETH9` | `weth9` | bytecode: ether backing, `withdraw` ([proving.md](proving.md#7-untrusted-callees-and-reentrancy-evmlogicprogramreentrancy)); model |
| USDT (`TetherToken`) | mainnet `0xdAC1…1ec7` | `Verified.WeirdERC20.USDT.Contracts.USDT` | `usdt`, `usdtfee` | model |
| BNB | mainnet `0xB8c7…DD52` | `Verified.WeirdERC20.BNB.Contracts.BNB` | `bnb` | model |
| STA (Statera) | mainnet `0xa7DE…eED1` | `Verified.WeirdERC20.STA.Contracts.STA` | `sta` | model |
| AMPL (zos proxy + `UFragments`) | mainnet `0xD46b…A161` / `0xD0e3…35b1` | `Verified.WeirdERC20.AMPL.Contracts.{AMPLProxy,AMPL}` | `ampl` | model |
| GUSD (`ERC20Proxy` + `ERC20Impl` + `ERC20Store`) | mainnet `0x056F…d5Cd` / `0x483A…40A2` / `0xc42B…68a0` | `Verified.WeirdERC20.GUSD.Contracts.{GUSD,GUSDImpl,GUSDStore}` | `gusd` | — |
| YAMv2 | mainnet `0xAba8…aD8A` | `Verified.WeirdERC20.YAMV2.Contracts.YAMV2` | `yamv2` | — |
| LEND (`EthLendToken`) | mainnet `0x80fB…ab03` | `Verified.WeirdERC20.LEND.Contracts.LEND` | `lend`, `lendico` | — |
| ZRX (`ZRXToken`) | mainnet `0xE41d…F498` | `Verified.WeirdERC20.ZRX.Contracts.ZRX` | `zrx` | — |
| Aave V3 aEthWETH (`AToken` rev. 5 behind its proxy) | mainnet `0x4d5F…14E8` / `0xadC4…7AdA` | `Verified.AaveV3.Contracts.{ATokenProxy,AToken}` | — | bytecode, partly ([aave-v3.md](aave-v3.md)) |

The weird tokens come from the Trail of Bits token-integration checklist and
`d-xo/weird-erc20`. Tests and proofs install mainnet code at its mainnet address with the
hand-written `genesis.json` storage: owner and admin roles given to alice (`0xA11CE`), balances
to the four test actors, one finite and one infinite allowance.

## The property catalogue

For a token at `T` with view `σ(w) = (supply, balanceOf, allowance)` read through the token's
storage layout (`EvmLogic.Solidity.ERC20.view`), and every transaction (any sender, calldata,
value and gas, top level or nested):

1. **Supply invariant**: `Σₐ balanceOf a = supply ≤ 2²⁵⁶ − 1` after every call if it held before
   (`Token.WF`); the model operations are exact on `ℕ` under it.
2. **Exact effects** (refinement): each successful entry point changes `σ` exactly as the model
   operation, emits exactly the model's logs and returns the ABI-encoded result; it reverts
   exactly when the model returns `none`, with the token's revert data.
3. **Frame**: a call changes no storage of `T` outside the rows the model touches, no storage of
   other accounts, and no ether (non-payable entry points revert on value).
4. **No unauthorised movement**: a transaction not sent by `o`, other than an allowance-backed
   `transferFrom` by an approved spender, never lowers `balanceOf o` or `allowance o _`; the
   supply changes only through the mint and burn entry points.
5. **Views**: `balanceOf`, `allowance`, `totalSupply`, `name`, `symbol`, `decimals` return the
   layout's values, change nothing, and do not revert on well-formed calldata with enough gas.
6. **Malformed calldata and unknown selectors** revert (or reach the fallback, where there is
   one) with no effect.
7. **Arbitrary callers**: 1–4 hold when `T` is called by arbitrary contracts at any depth
   (`EvmLogic/Program/Nested/`).

Solmate's `ERC20` has 2, 3, 5 and 6 on the bytecode (`qedefi/Verified/Solmate/ERC20/`), and 1, 4
and 7 through the vault proofs. Each other target's deviations below say which items change.

## OpenZeppelin `ERC20` on bytecode

`qedefi/Verified/OpenZeppelin/ERC20/`, for calls with zero value: item 2 with logs (without
revert data), the storage part of 3, and the `totalSupply`/`balanceOf`/`allowance`/`decimals`
part of 5; item 1 is `Token.WF_oz*`.

- `EvmLogic.Solidity.ERC20Oz`: the layout `Layout.oz = ⟨2, 0, 1⟩`, the word-level operations
  `Model.ozTransfer`, `ozApprove`, `ozSpend`, `ozTransferFrom`, `ozMint`, `ozBurn` (Solmate's
  behind the zero-address checks, plus `_update`'s mint and burn), the code's `SSTORE` sequences
  for any layout and their `view_*World` theorems. Writing the supply slot needs `SupplySlotOk`
  (no balance row hashes to slot 2).
- `Transfer`, `Approve`, `TransferFrom`, `MintBurn`: success and every revert path (each
  zero-address check, insufficient balance or allowance, supply overflow; infinite and finite
  allowances), and `*_spec`: `processMessageCall` refines `Model.oz*` through `ERC20.view`.
  `Views`: the four views return the view's words and change nothing.
- `QEDefi.ERC20.RepOz` and `Spec` (`*_refines`): the bytecode against `Token.ozTransfer` and the
  rest directly, hence against `Variant.oz` by `Variant.oz_transfer` and its siblings.
- Callee summaries in any fresh frame, for `WP.call` from contracts that hold the token:
  `Callee` (posts `TransferOk`, `ApproveOk`, `TransferFromOk`, `MintOk`, `BurnOk`: output,
  world, transient storage, created accounts, the appended log, a gas bound), `CalleeTransfer`,
  `CalleeApprove`, `CalleeTransferFrom` (`TransferFromCond`: the exact success condition on the
  storage, no hash hypothesis), `CalleeMintBurn`; `CalleeSpec` against `Token.oz*`.
- `Events` (`*_logs`): the logs of a top-level call are the model's event when `Model.oz*`
  succeeds and empty otherwise. OpenZeppelin v5 emits no `Approval` when `transferFrom` spends.

Differences from Solmate, all visible in the model (`Token.transfer` against `Token.ozTransfer`
and so on): zero-address checks on sender, receiver, approver and spender; custom errors with
arguments instead of `Panic(0x11)`; one internal `_update` for transfer, mint and burn; in
`transferFrom` the allowance is checked before the addresses, which shows in the revert data;
no `permit` in `ERC20Mock`.

## How each target deviates

**Solady `ERC20`** (`contracts/src/SoladyToken.sol` over the vendored v0.1.26). All storage is
inline assembly at hashed slots: `totalSupply` at the constant `0x05345cdf77eb68f44c`,
`balanceOf(o)` at `keccak256(o₂₀ ‖ 0⁸ ‖ 0x87a211a2)`, `allowance(o, s)` at
`keccak256(o₂₀ ‖ 0⁸ ‖ 0x7f5e9f20 ‖ s₂₀)` (52 bytes), `nonces(o)` at
`keccak256(o₂₀ ‖ 0⁸ ‖ 0x38377508)`. `allowance` is a view, not a slot: Permit2 always has an
infinite allowance, `transferFrom` by Permit2 skips the stored row, and `approve(PERMIT2, v)`
with `v ≠ max` reverts. Errors are 4-byte custom errors without arguments; no zero-address
checks. Proofs read `keccak256` over memory windows that straddle two `mstore`s, and each entry
point inlines its own transfer logic.

**WETH9** (solc 0.4.19, unoptimised). No supply slot: `totalSupply()` is
`address(this).balance`, so the supply invariant becomes ether backing,
`Σₐ balanceOf a ≤ address(T).balance` (ether can arrive without `deposit`). The payable
fallback deposits; `withdraw` debits before sending `wad` wei with a 2,300-gas stipend and
reverts if the send fails. `transferFrom` by the owner skips the allowance; an allowance of
`2²⁵⁶ − 1` is not spent. No ABI length checks (short calldata reads zeros), no zero-address
checks. Its correctness depends on an arbitrary callee: the stipend frame.

**USDT** (solc 0.4.18, unoptimised). `transfer`, `transferFrom` and `approve` return nothing.
`approve(s, v)` reverts if `v ≠ 0` and the current allowance is not `0` (the race guard). A fee
`min(v · basisPointsRate / 10⁴, maximumFee)` goes to the current owner (0 on mainnet;
`setParams` keeps it below 20 bps and 50 tokens). A blacklist checks the sender of `transfer` and
the `from` of `transferFrom`; `destroyBlackFunds` burns a blacklisted balance without a
`Transfer` event. `pause` stops transfers only. Insufficient balance or allowance ends in
`INVALID` (all gas consumed), not `REVERT`. `issue`/`redeem` mint and burn to the owner without
`Transfer` events. `deprecate(a)` (irreversible) forwards every call to the token at `a`.

**BNB** (solc 0.4.12, unoptimised). `transfer` returns nothing, the others `true`. Zero values
revert in `transfer`, `transferFrom`, `approve` (an allowance cannot be reset to 0), `burn`,
`freeze`, `unfreeze`; transfers to `0` revert. No `Approval` event. `freeze` moves balance to a
second ledger, so `supply = Σ balanceOf + Σ freezeOf`. The payable fallback accepts every unknown
selector with success and empty return data (a `permit` call "succeeds"), and only the owner's
`withdrawEther` moves the ether out.

**STA** (solc 0.5.0). Every transfer burns `⌈v/100⌉` and delivers the rest, with two `Transfer`
events; the supply invariant holds because the fee is burned. `transferFrom` spends `v`, even
from an infinite allowance; `approve` to `0` reverts.

**AMPL** (zos `AdminUpgradeabilityProxy` over `UFragments`). Pre-EIP-1967 proxy slots; the admin
cannot use the token. Balances are stored as gons: `balanceOf(a) = gons[a] / gonsPerFragment`,
so `Σ balanceOf ≤ supply`, and `rebase` changes every balance without a `Transfer` event.
`transferAll` moves dust that `transfer(balanceOf)` leaves behind; infinite allowances are
spent; `permit` accepts `owner = 0` with an invalid signature.

**GUSD**. Three contracts linked by `CALL`, no `DELEGATECALL`: the token address forwards each
call to the implementation with `msg.sender` as an argument, the implementation keeps the ledger
in the store and asks the token address to emit the events, so one `transfer` is a call tree of
depth 3. The token address does not bubble revert data. 2 decimals; the custodian can replace
the implementation or the store.

**YAMv2**. OpenZeppelin-3 style with 24 decimals and a minter: string revert reasons, `transferFrom`
moves the tokens before spending the allowance, the spend emits `Approval`. The generic
catalogue holds unchanged.

**LEND** (solc 0.4.16). `transfer` requires `balances[to] + v > balances[to]`, so zero-value
transfers revert, self-transfers included; the USDT approve guard (returning `true`); transfers
and approvals are gated on the ICO having finished (`lendico` reopens it: purchases with ether).

**ZRX** (solc 0.4.11). Insufficient balance or allowance makes `transfer`/`transferFrom` return
`false` with success status, no event and no state change. An allowance of `2²⁵⁶ − 1` is not
spent. `ZRXToken` redeclares `totalSupply`, which shadows the base contract's slot 2 with slot 3.

**Recorded, not targets**: USDC and PAXG (zos-slot proxies; PAXG's current implementation no
longer charges a transfer fee).

## Differential testing

Each family deploys the compiled token, or installs the mainnet code with its genesis storage on
both sides, checks the getters against the installed state, runs a fixed scenario of the token's
quirks, compares `balanceOf`, `allowance` and `totalSupply` with reads of the documented slots,
and then random sequences over the whole ABI, with ether sent to payable functions and the
fallback. `--edge` favours extreme amounts, self-transfers and dirty address arguments;
`--low-gas PCT` lowers the gas limit of some calls so that out-of-gas hits every depth. Over all
16 families (200 sequences of 50 calls with `--low-gas 5`, then 100 of 50 with
`--edge --low-gas 15`): 240,460
transactions, 144,245 successful on both sides, 7,486 exceptional halts, **0 mismatches** in
status, return and revert data, logs, `gasUsed`, every touched slot and ether balances.

## Model-level results

Proved in Mathlib, standard axioms only; on the bytecode only where the table above says so.

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

## Laws per token (spec layer)

`QEDefi/ERC20/Spec/VariantLaws.lean` decides every law of `Spec/Laws.lean` for each `Variant`
instance as a token model (`V.model ev`, any event rule): ✓ proved, ✗ refuted with an explicit
witness state, well formed (`Variant.WF`) except where noted. Namespace
`QEDefi.ERC20.Spec.VariantLaws`.

| Instance | `ReturnsTrue` | `NoFalseReturn` | `RevertsOnly` | `ExactMoves` | `SupplyFixed` | `DebitAuth` | `AllowanceAuth` | `WFInvariant` |
|---|---|---|---|---|---|---|---|---|
| `standard` (Solmate) | ✓ | ✓ | ✓ | ✓ all states | ✓ | ✓ | ✓ | ✓ |
| `oz` | ✓ | ✓ | ✓ | ✓ all states | ✓ | ✓ | ✓ | ✓ |
| `solady p` | ✓ | ✓ | ✓ | ✓ all states | ✓ | ✓ | ✓ | ✓ |
| `weth9` | ✓ | ✓ | ✓ | ✓ all states | ✓ | ✓ | ✓ | ✓ |
| `usdt` | ✗ `usdt_approve_empty` | ✓ | ✗ `usdt_invalid_witness` | ✓ on `NoFee` (`bps = 0`); ✗ on `WF`, `usdt_fee_witness` | ✓ | ✓ | ✓ | ✓ |
| `bnb` | ✗ `bnb_empty_witness` | ✓ | ✓ | ✓ all states | ✓ | ✓ | ✓ | ✓ |
| `sta` | ✓ | ✓ | ✗ `sta_invalid_witness` | ✗ on `WF`, `sta_fee_witness` (no state is `NoFee`: `sta_not_noFee`) | ✗ `sta_fee_witness` | ✓ | ✓ | ✓ |
| `ampl` | ✓ | ✓ | ✓ | ✓ on `0 < scale` ⊇ `WF`; ✗ at scale `0` (not `WF`), `ampl_scale_zero_witness` | ✓ | ✓ | ✓ | ✓ |

One theorem per row: `standard_laws`, `oz_laws`, `solady_laws`, `weth9_laws` (`Standard` in all
states), `usdt_laws`, `bnb_laws`, `sta_laws`, `ampl_laws` (a conjunction; refutations need two
accounts, `[Nontrivial A]`). The rows rest on generic lemmas over any variant: `law_exactMoves`
(`ExactMoves (NoFee V)` for every variant, rebasing included), `law_debitAuth` and
`law_allowanceAuth` (every variant, unconditionally), `law_supplyFixed` (fee absent or paid to
the owner), `law_revertsOnly`, `law_returnsTrue`, `law_noFalseReturn`, `law_wfInvariant`
(`Sane`). AMPL's rounding never shows in `transfer`/`transferFrom`: a transfer of `v` moves
`v · scale` gons, exactly `v` in the `balanceOf` view; only `transferAll` (an operation, not a
call) moves dust. AMPL's zero-owner `permit` (`ampl_permit_zero_owner`) satisfies
`AllowanceAuth` as stated, since the failed recovery returns `0`, which is the owner.

## Bytecode spec per token (spec layer)

`ERC20Spec code abs M g₀ sel ops opAddrs` (`QEDefi/ERC20/Spec/Bytecode.lean`): in every fresh
frame of the code, at any depth, for every finite set of actors whose storage rows are distinct
(`TokenAbs.Sound`, usually `ActorRows`), each call ends exactly as the model says (return data,
new state, events, nothing else changed), or, below `g₀` gas, static or with value, fails. The
per-token data a reviewer reads is the model, the abstraction (`Spec/Abs.lean` of each token),
`g₀` and the decoder of the other entry points.

| Token | Model | `ERC20Spec` | `g₀` | Not covered |
|---|---|---|---|---|
| OpenZeppelin `ERC20Mock` | `Variant.oz` (`Instances/Oz.lean`) | ✓ `oz_erc20Spec` | 100000 | `MalformedSpec` |
| Solmate `MockERC20`, any immutables | `Variant.standard` | ✓ `solmate_erc20Spec`; `permit` ✓ on the deployment chain and short names off it (`permit_spec_case`) | 100000 | `permit` off-chain with `name` ≥ 32 bytes; `MalformedSpec` |
| Solady `SoladyToken` | `Variant.solady PERMIT2` | ✓ `solady_spec` | 100000 | `PermitSpec`, `MalformedSpec` |
| WETH9 (mainnet) | `Variant.weth9`, `Deposit` event | ✓ `weth9_erc20Spec` | 100000 | `withdraw` (calls the caller; `withdraw_halts_refines`) |
| USDT (mainnet) | `Variant.usdt` | ✓ `usdt_erc20Spec` (live: not deprecated, 6 decimals, owner an actor) | 200000 | `pause`/`unpause` (the model's `setPaused` never fails; the code does) |
| BNB (mainnet) | `bnbModel`: `Variant.bnb` plus the credit-overflow guard it lacks | ✓ `bnb_spec` | 100000 | `withdrawEther` (depends on the owner's code) |
| STA (mainnet) | `Variant.sta` (`basePercent = 100`) | ✓ `sta_spec` | 200000 | |
| AMPL (`UFragments` in the proxy's storage) | `Variant.ampl` | ✓ `ampl_spec` | 100000 | `rebase`, owner functions; the proxy's dispatch |
| ZRX (mainnet) | own model (`Instances/ZRX.lean`) | stated (`zrxSpec`); views ✓ at `g₀` without value | 100000 | the rest |
| YAMv2, LEND (mainnet) | own models | stated (`yamv2Spec`, `lendSpec`) | 100000, 150000 | proofs; LEND only in its final sale state |
| GUSD (mainnet, three contracts) | own model over the three accounts | no single-code spec: the docstring of `GUSD/Spec/Abs.lean` says what a system spec needs | | |

**What every token gets from its spec, proved once** (`Spec/TopLevel.lean`, `Callee.lean`,
`Asset.lean`, `Invariant.lean`, `QEDefi/ERC4626/AssetModel.lean`): the result of a top-level
call and of a whole transaction (EIP-7702 included), a `CALL`/`STATICCALL` rule for contracts
calling the token, `DebitAuth` and `WFInvariant` on bytecode, the vault theorems over any token
model, and the model invariant after any sequence of transactions with the token called at any
depth. **Challenges:** `oz_supply_eq_sum` (OzAssetSupplySum) and `solady_supply_eq_sum`
(SoladySupplySum, transactions without `permit`): the actors' balances sum to `totalSupply`
after any sequence of transactions whose token frames touch only actors, when they did before
and all ether is below `2²⁵⁶`.

**Why actors.** Mapping rows are hashes with more keys than slots: every allowance slot is
shared by about `2⁶⁴` pairs, and the balance rows of all `2¹⁶⁰` addresses collide about `2⁶³`
times. "Rows never collide" over all addresses is consistent in Lean but false for Keccak; for a
finite set of actors it is plausible. The older `weth9_backed*` theorems still assume the
global form (`hK`, `hinj`), so they say nothing about mainnet WETH9 until they are restated per
set of rows; `weth9_erc20Spec` does not.

## Open work

- **Bytecode refinement of each target against its instance**: `processMessageCall` equals
  `Variant.call` lifted through the token's storage layout, including the `INVALID`/`REVERT`
  distinction and empty return data, then events per operation. Expected obstacles: 0.4.x code
  (`throw` as `INVALID`, `EXP`-based shifts, no ABI length checks), WETH9's external call,
  Solady's unaligned scratch memory, USDT's forwarding.
- **The vaults' `SafeTransferLib`/`SafeERC20` call sites against `Result.safe`**, so that the
  integration theorems hold for the deployed vaults over the deployed tokens.
- **BNB's ether sends** on bytecode, with the stipend lemma `halts_low`
  (`EvmLogic/Program/Reentrancy/Halts.lean`) as the callee summary, as for WETH9's `withdraw`.
- **What the model leaves out**: USDT's deprecation with `upgradedAddress = USDT`, its forwarded
  gas and short-return quirk; signature recovery itself (`permit` takes it as a parameter);
  short-payload checks; models for GUSD, YAMv2, LEND and ZRX.
- **Generic layouts**: `EvmLogic.Solidity.ERC20.Layout` covers Solidity mapping layouts; WETH9
  (no supply slot), Solady (hashed slots, constant supply slot) and rebasing tokens need the
  layout, the supply relation and the freshness predicate as parameters.
- **Upgradeable tokens** (USDC): the proxy's dispatch theorem (every non-admin call delegates)
  and theorems that hold until an admin transaction. `WP.delegatecall` and Aave's aToken proxy
  (`Verified/AaveV3/ATokenProxy/`, `forward_halts`) are the worked pattern.
