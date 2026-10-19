# ERC-4626 property catalogue

The properties the ERC-4626 verification effort targets, where each one comes from, and the
Lean theorem that proves (✓) or refutes (✗) it on the abstract vault models in `specs/`
(`EvmLeanSpecs.Vault`). The models mirror, statement by statement and revert by revert:

* **Solmate**: `ERC4626` + `MockERC4626` (`totalAssets = asset.balanceOf(this)`) over a
  Solmate `MockERC20` asset (`specs/EvmLeanSpecs/Vault/Solmate.lean`);
* **OZ(δ)**: OpenZeppelin v5.7 `ERC4626` with decimals offset `δ` (`k = 10^δ` virtual shares,
  1 virtual asset) over `ERC20Mock` (`specs/EvmLeanSpecs/Vault/Oz.lean`). The pinned
  `OzVault` has `δ = 0`; every theorem below is for arbitrary `δ`.

Notation: `T = totalAssets`, `S = totalSupply`, `T̂ = T + 1`, `Ŝ = S + k`. Theorem names
are relative to `EvmLeanSpecs.Vault` (`Solmate.`, `Oz.`, `Inflation.`, `Witnesses.`).
"Standard hypotheses" for value-flow theorems: the caller of a deposit/mint and the
receiver of a withdraw/redeem is not the vault itself (true for the bytecode: the vault
never calls itself), and the state satisfies `Inv` (well-formed ledgers), which every
call sequence preserves.

Categories: **S** single call, **RT** round trip (two calls), **I** invariant over
arbitrary call sequences, **E** adversarial / economic.

## Sources

* [EIP-4626] — <https://eips.ethereum.org/EIPS/eip-4626> (MUST/SHOULD clauses per function,
  and "Security Considerations" on rounding direction and the empty-vault case).
* [a16z] — a16z `erc4626-tests`, `ERC4626.prop.sol`
  (<https://github.com/a16z/erc4626-tests/blob/main/ERC4626.prop.sol>): `prop_*` per
  function, the eight `prop_RT_*` round trips (with `vm.assume(totalSupply() > 0)` unless
  `_vaultMayBeEmpty`), and `checkNoFreeProfit`.
* [crytic] — crytic/properties ERC4626-001…037
  (<https://github.com/crytic/properties/blob/main/PROPERTIES.md#erc4626>,
  `contracts/ERC4626/properties/*.sol`).
* [OZ-docs] — OpenZeppelin, "ERC-4626: the inflation attack" and "Defending with a virtual
  offset" (<https://docs.openzeppelin.com/contracts/5.x/erc4626>); OpenZeppelin blog
  "A Novel Defense Against ERC4626 Inflation Attacks"
  (<https://blog.openzeppelin.com/a-novel-defense-against-erc4626-inflation-attacks>).
* [audits] — the first-depositor / donation attack and the opposing-rounding rule are
  recurring findings in public audit contests (Code4rena, Sherlock, Immunefi reports on
  vaults whose `totalAssets` is `asset.balanceOf(this)`); we take the attack shape and
  the crytic ERC4626-033 test as the precise formulation.

## Ledger invariants (category I)

| id | statement | source | Solmate | OZ(δ) | Lean |
|---|---|---|---|---|---|
| INV-SUPPLY | `totalSupply = Σ balanceOf` for shares, and for the asset, after any sequence of calls by arbitrary callers (reverted calls change nothing) | ERC-20 / [crytic] ERC20 props | ✓ | ✓ | `Solmate.totalSupply_eq_sum_exec`, `Solmate.Inv_exec`, `Oz.totalSupply_eq_sum_exec`, `Oz.Inv_exec` |
| INV-FIT | `totalSupply ≤ 2²⁵⁶−1` for both tokens (so every unchecked `+=` in the bytecode is exact) | Solidity semantics | ✓ | ✓ | `Inv` (`Token.WF`), preserved by `Inv_exec` |
| I-SOLVENT | the vault can pay everyone's `convertToAssets` at once: `Σₓ ⌊balanceOf[x]·T/S⌋ ≤ T` (OZ: `Σₓ ⌊balanceOf[x]·T̂/Ŝ⌋ ≤ T`) | [EIP-4626] rounding rationale | ✓ | ✓ | `Solmate.solvent`, `Oz.solvent` |

## Single-call properties (category S)

| id | statement | source | Solmate | OZ(δ) | Lean |
|---|---|---|---|---|---|
| P-CALLER | `convertTo*`, `preview*`, `max*` do not depend on `msg.sender` | [EIP-4626] "MUST NOT show any variations depending on the caller"; [a16z] `prop_convertTo*`; [crytic] 023–028 | ✓ | ✓ | by construction: the view functions take no caller argument |
| P-PREVIEW-DEPOSIT | `deposit` mints exactly `previewDeposit(assets)` (EIP: "no more than") | [EIP-4626]; [a16z] `prop_previewDeposit` | ✓ (=) | ✓ (=) | `Solmate.deposit_eq_previewDeposit`, `Oz.previews_exact` |
| P-PREVIEW-MINT | `mint` pulls exactly `previewMint(shares)` (EIP: "no fewer than") | [EIP-4626]; [a16z] `prop_previewMint` | ✓ | ✓ | `Solmate.mint_eq_previewMint`, `Oz.previews_exact` |
| P-PREVIEW-WITHDRAW | `withdraw` burns exactly `previewWithdraw(assets)` | [EIP-4626]; [a16z] `prop_previewWithdraw` | ✓ | ✓ | `Solmate.withdraw_eq_previewWithdraw`, `Oz.previews_exact` |
| P-PREVIEW-REDEEM | `redeem` pays exactly `previewRedeem(shares)` | [EIP-4626]; [a16z] `prop_previewRedeem` | ✓ | ✓ | `Solmate.redeem_eq_previewRedeem`, `Oz.previews_exact` |
| P-EFFECTS | `deposit`/`mint` move `assets` from caller to vault and credit `shares` to receiver; `withdraw`/`redeem` burn `shares` from owner and pay `assets` to receiver; supplies change accordingly | [a16z] `prop_deposit/mint/withdraw/redeem`; [crytic] 029–032 | ✓ | ✓ | `Solmate.deposit_eq_some`, `mint_eq_some'`, `withdraw_eq_some`, `redeem_eq_some`, `deposit_TS`…`redeem_TS`; `Oz.deposit_eq_some`…`Oz.redeem_eq_some` |
| A-AUTH | a third party (`caller ≠ owner`) can `withdraw`/`redeem` only within its share allowance (or with an infinite one) | [EIP-4626] withdraw/redeem; [a16z] "access control"; [crytic] 009–012, 035–036 | ✓ | ✓ | `Solmate.withdraw_auth`, `Solmate.redeem_auth`, `Oz.withdraw_auth`, `Oz.redeem_auth` |
| R-DEPOSIT | `deposit` rounds shares down: `n = ⌊a·S/T⌋` (OZ `⌊a·Ŝ/T̂⌋`); over ℚ `n ≤ a·S/T` | [EIP-4626] Security Considerations; [crytic] 013, 019 | ✓ | ✓ | `Solmate.deposit_rounding`, `Solmate.deposit_shares_le_fair`, `Oz.deposit_rounding` |
| R-MINT | `mint` rounds assets up: `a = ⌈n·T/S⌉`; `n·price ≤ a` | same; [crytic] 014, 020 | ✓ | ✓ | `Solmate.mint_rounding`, `Solmate.mint_assets_ge_fair`, `Oz.mint_rounding` |
| R-WITHDRAW | `withdraw` rounds burned shares up: `n = ⌈a·S/T⌉` | same; [crytic] 017, 021 | ✓ | ✓ | `Solmate.withdraw_rounding`, `Solmate.withdraw_shares_ge_fair`, `Oz.withdraw_rounding` |
| R-REDEEM | `redeem` rounds paid assets down: `a = ⌊n·T/S⌋`; `a ≤ n·price` | same; [crytic] 016, 022 | ✓ | ✓ | `Solmate.redeem_rounding`, `Solmate.redeem_assets_le_fair`, `Oz.redeem_rounding` |
| R-FREE-WITHDRAW | `previewWithdraw(a) > 0` for `a > 0` (assets are never withdrawn for free) | [crytic] 017, 021 | ✓ | ✓ | `Solmate.previewWithdraw_pos`, `Oz.previewWithdraw_pos` |
| R-FREE-MINT | `previewMint(n) > 0` for `n > 0` (shares are never minted for free) | [crytic] 014, 020 | **✗** when `S > 0 = T` (after a total loss `mint` is free) | ✓ in every state | ✗ `Solmate.previewMint_zero_of_totalAssets_zero`; ✓ `Oz.previewMint_pos` |
| P-MAXWITHDRAW | withdrawing `maxWithdraw(owner)` never needs more shares than the owner has | [EIP-4626] maxWithdraw | ✓ | — | `Solmate.previewWithdraw_maxWithdraw_le` |
| EIP-CONVERT-NOREVERT | `convertToShares` MUST NOT revert except on overflow from an unreasonably large input | [EIP-4626]; [crytic] 004, 037 | **✗** reverts on every input (incl. 0) when `S > 0 = T` (division by zero) | expected ✓ (`T̂, Ŝ > 0`, so only overflow reverts; not stated as a theorem) | ✗ `Solmate.convertToShares_reverts_of_totalAssets_zero` |
| EIP-MAXDEPOSIT | `maxDeposit` MUST be the largest amount that does not revert (0 if deposits are disabled) | [EIP-4626] | **✗** same state: `maxDeposit = 2²⁵⁶−1` but every `deposit` reverts | (not proved) | ✗ `Solmate.deposit_reverts_of_totalAssets_zero` |
| EIP-MAXREDEEM | `maxRedeem(owner)` MUST be redeemable without revert | [EIP-4626]; [a16z] `prop_maxRedeem` | **✗** when `balance·T < S`: `maxRedeem = balance > 0` but `redeem` reverts (`ZERO_ASSETS`) | (no zero check; not proved) | ✗ `Solmate.maxRedeem_reverts` |
| EIP-DEPOSIT-ZERO | a deposit whose shares round to 0 | [OZ-docs] | reverts (`ZERO_SHARES`) | succeeds and mints 0 shares (allowed by EIP; the depositor loses `a`) | `Solmate.solmate_attack_victim_reverts`; `Oz.deposit_zero_shares`, `Witnesses.oz_zero_shares_witness` |

## Round trips (category RT)

Each holds for Solmate when `S > 0` before the call (and, for withdraw/redeem-first trips, when
shares remain in between) — exactly the a16z suite's `vm.assume(totalSupply() > 0)` with
`_vaultMayBeEmpty = false`. For OZ(δ) all eight hold in every state, including empty and
drained vaults.

| id | statement | source | Solmate | OZ(δ) | Lean |
|---|---|---|---|---|---|
| RT-DEPOSIT-REDEEM | `redeem(deposit(a)) ≤ a` | [a16z] `prop_RT_deposit_redeem`; [EIP-4626] | ✓ if `S > 0`; **✗** if `S = 0 < T`: returns `T + a` | ✓ | `Solmate.rt_deposit_redeem`; ✗ `Solmate.rt_deposit_redeem_empty_supply`, `Witnesses.solmate_rt_deposit_redeem_witness`; `Oz.rt_deposit_redeem` |
| RT-DEPOSIT-WITHDRAW | `deposit(a) ≤ withdraw(a)` (shares) | [a16z] `prop_RT_deposit_withdraw` | ✓ if `S > 0` | ✓ | `Solmate.rt_deposit_withdraw`, `Oz.rt_deposit_withdraw` |
| RT-MINT-REDEEM | `redeem(n) ≤ mint(n)` (assets) | [a16z] `prop_RT_mint_redeem` | ✓ if `S > 0`; **✗** if `S = 0 < T`: pays `T + n` for `n` | ✓ | `Solmate.rt_mint_redeem`; ✗ `Solmate.rt_mint_redeem_empty_supply`; `Oz.rt_mint_redeem` |
| RT-MINT-WITHDRAW | `withdraw(mint(n)) ≥ n` (shares) | [a16z] `prop_RT_mint_withdraw` | ✓ if `S > 0` | ✓ | `Solmate.rt_mint_withdraw`, `Oz.rt_mint_withdraw` |
| RT-REDEEM-DEPOSIT | `deposit(redeem(n)) ≤ n` | [a16z] `prop_RT_redeem_deposit` | ✓ if shares remain; **✗** if the redemption drains the vault and `T > S`: get back `T` shares (share count only, no value gained) | ✓ | `Solmate.rt_redeem_deposit`; ✗ `Solmate.rt_redeem_deposit_drained`; `Oz.rt_redeem_deposit` |
| RT-REDEEM-MINT | `mint(n) ≥ redeem(n)` (assets) | [a16z] `prop_RT_redeem_mint` | ✓ if shares remain | ✓ | `Solmate.rt_redeem_mint`, `Oz.rt_redeem_mint` |
| RT-WITHDRAW-MINT | `mint(withdraw(a)) ≥ a` | [a16z] `prop_RT_withdraw_mint` | ✓ if shares remain | ✓ | `Solmate.rt_withdraw_mint`, `Oz.rt_withdraw_mint` |
| RT-WITHDRAW-DEPOSIT | `deposit(a) ≤ withdraw(a)` (shares) | [a16z] `prop_RT_withdraw_deposit` | ✓ if shares remain | ✓ | `Solmate.rt_withdraw_deposit`, `Oz.rt_withdraw_deposit` |
| RT-CONVERT | `convertToAssets(convertToShares(a)) ≤ a` and `convertToShares(convertToAssets(n)) ≤ n` | [crytic] `verify_convertRoundTrip`, `…2` | ✓ (all states) | ✓ | `Solmate.convert_roundtrip`, `Solmate.convert_roundtrip2`, `Oz.convert_roundtrip`, `Oz.convert_roundtrip2` |

The arithmetic core of all eight is `rt_in_out_assets`, `rt_in_out_shares`,
`rt_out_in_shares`, `rt_out_in_assets` (`RoundTripAlgebra.lean`).

## Economic properties (category E)

| id | statement | source | Solmate | OZ(δ) | Lean |
|---|---|---|---|---|---|
| E-PRICE-DEPOSIT / -MINT | no dilution: a deposit or mint never lowers assets-per-share, `T·S' ≤ T'·S` (OZ: `T̂·Ŝ' ≤ T̂'·Ŝ`); over ℚ `price ≤ price'` | [EIP-4626] rounding rationale; [OZ-docs] | ✓ if `S > 0` | ✓ always | `Solmate.deposit_price_mono`, `Solmate.mint_price_mono`, `Solmate.deposit_price_le`; `Oz.deposit_price_mono`, `Oz.mint_price_mono`, `Oz.price_le_of_cross` |
| E-PRICE-WITHDRAW / -REDEEM | a withdrawal or redemption never lowers assets-per-share | same | ✓ if `S > 0` (any receiver) | ✓ always | `Solmate.withdraw_price_mono`, `Solmate.redeem_price_mono`, `Solmate.redeem_price_le`; `Oz.withdraw_price_mono`, `Oz.redeem_price_mono` |
| E-FREE-MINT | after a total loss (`S > 0 = T`) shares cost nothing | [crytic] 014/020 | ✗ (see R-FREE-MINT) | ✓ | `Solmate.previewMint_zero_of_totalAssets_zero` |
| INFL-SOLMATE-DOS | empty vault; attacker `deposit(1)` then donates `D`: state `S = 1`, `T = D+1`, attacker holds the share; every victim `deposit(a)` with `a ≤ D` has `previewDeposit = 0` and reverts | [OZ-docs]; [crytic] 033; [audits] | ✓ (attack works as DoS) | — | `Solmate.solmate_attack_setup`, `Solmate.solmate_attack_victim_reverts`, `Witnesses.solmate_attack_witness` |
| INFL-SOLMATE-THEFT | in the same state a victim `deposit(a)` with `D < a ≤ 2D+1` mints exactly 1 share worth `⌊(a+D+1)/2⌋`: the victim loses `⌊(a−D)/2⌋` (≈ 25 % at `a = 2D+1`), the attacker's share (cost `D+1`) is worth `D+1+⌊(a−D−1)/2⌋`. Fails crytic 033's 0.1 % threshold | [crytic] 033 | ✗ (vulnerable) | — | `Solmate.solmate_attack_victim_one_share`, `Witnesses.solmate_attack_witness` (D = 100, a = 201: loss 50) |
| INFL-PROFIT | general donation attack (attacker holds `b` shares, donates `D`, victim deposits `a`): profit `P` and victim loss `L` (at the vault's rate) satisfy `P·Ŝ = b·L − D·(Ŝ − b)`, `0 ≤ L <` one post-donation share | [OZ-docs] analysis | ✓ with `Ŝ = S`; if the attacker holds all shares, **`P = L`** (donating is free) | ✓ | `Solmate.solmate_donation_attack`, `Solmate.solmate_donation_attack_all_shares`; `Oz.oz_donation_attack` (1–2); `Inflation.profit_mul`, `Inflation.loss_mul`, `Inflation.loss_bounds` |
| INFL-OZ-BOUND | attacker profit `P·(S+k) ≤ T + 1 − (k−1)·D`: less than one pre-attack share, negative once `(k−1)·D > T+1` | [OZ-docs] "attacker's loss ≥ victim's loss" | — | ✓ | `Oz.oz_donation_attack` (3), `Inflation.oz_profit_bound` |
| INFL-OZ-COST | making the victim lose `L` costs the attacker more than `k·L − k·(T+1)/(S+k)` in donation captured by the virtual shares (`> k·L − 1` in a fresh vault) | [OZ-docs] "orders of magnitude bigger" | — | ✓ | `Oz.oz_donation_attack` (4), `Inflation.oz_cost_bound` |
| INFL-CRYTIC | crytic 033 setting (fresh vault, attacker deposits 1, donates `D ≥ 1`, victim deposits `a ≥ D+1`): victim loss `< (3/4)·a/10^δ` — below crytic's 0.1 % for `δ ≥ 3`. With `δ = 0` the bound is `3a/4`, so the victim-loss test can still fail, although the attacker cannot profit (INFL-OZ-BOUND) | [crytic] 033 | ✗ | ✓ for `δ ≥ 3`; griefing only for `δ = 0` | `Oz.crytic_inflation_bound` |

## Not covered (yet)

* `asset()`, `totalAssets()`, `max*` "MUST NOT revert" ([crytic] 001–008): views that make
  no state change; for Solmate the only reverting views are the `mulDiv` ones above.
  `decimals` ([crytic] 034) is not modelled.
* Events, gas, `permit` (EIP-2612; its storage effect is an owner `approve`), reentrancy
  (the pinned assets make no calls), fee-on-transfer or rebasing assets.
* a16z `checkNoFreeProfit` (caller's `convertToAssets(balance) + asset balance` does not
  grow over a round trip) is implied by the RT theorems for the asset side but not stated
  as such.
* OZ `maxDeposit`/`maxRedeem` exactness and an empty-vault setup theorem for OZ (the
  attack theorems take the post-setup state as a hypothesis).
