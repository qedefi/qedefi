# ERC-4626 property catalogue

Each property, its source, and the Lean theorem proving (✓) or refuting (✗) it on the models
in `qedefi/QEDefi/ERC4626/`. Names are relative to `QEDefi.ERC4626` (`Solmate.`, `Oz.`,
`Inflation.`, `Witnesses.`); the round-trip arithmetic is in `QEDefi.Math`.

- **Solmate**: `ERC4626` + `MockERC4626` (`totalAssets = asset.balanceOf(this)`) over
  `MockERC20` (`Solmate.lean`).
- **OZ(δ)**: OpenZeppelin v5.7 `ERC4626` with decimals offset `δ` (`k = 10^δ` virtual shares,
  one virtual asset) over `ERC20Mock` (`Oz.lean`). The pinned `OzVault` has `δ = 0`; every
  theorem is for arbitrary `δ`.

Notation: `T = totalAssets`, `S = totalSupply`, `T̂ = T + 1`, `Ŝ = S + k`. Value-flow theorems
assume the state satisfies `Inv` (preserved by every call sequence) and that the vault is not
the caller of a deposit/mint or the receiver of a withdraw/redeem (true of the bytecode: the
vault never calls itself).

Sources: [EIP-4626](https://eips.ethereum.org/EIPS/eip-4626) (MUST/SHOULD clauses, Security
Considerations); [a16z](https://github.com/a16z/erc4626-tests/blob/main/ERC4626.prop.sol)
`prop_*` and the eight `prop_RT_*` (with `vm.assume(totalSupply() > 0)` unless
`_vaultMayBeEmpty`); [crytic](https://github.com/crytic/properties/blob/main/PROPERTIES.md#erc4626)
ERC4626-001…037; [OZ-docs](https://docs.openzeppelin.com/contracts/5.x/erc4626) on the
inflation attack and virtual offsets; public audit findings on first-depositor attacks.

## Ledger invariants

| Property | Source | Solmate | OZ(δ) | Lean |
|---|---|---|---|---|
| `totalSupply = Σ balanceOf` for shares and asset after any call sequence | ERC-20, crytic | ✓ | ✓ | `Solmate.totalSupply_eq_sum_exec`, `Solmate.Inv_exec`, `Oz.totalSupply_eq_sum_exec`, `Oz.Inv_exec` |
| `totalSupply ≤ 2²⁵⁶−1` (every unchecked `+=` is exact) | Solidity | ✓ | ✓ | `Inv` (`Token.WF`), preserved by `Inv_exec` |
| solvency: `Σₓ ⌊balanceOf[x]·T/S⌋ ≤ T` (OZ: with `T̂/Ŝ`) | EIP rounding rationale | ✓ | ✓ | `Solmate.solvent`, `Oz.solvent` |

## Single calls

| Property | Source | Solmate | OZ(δ) | Lean |
|---|---|---|---|---|
| views do not depend on `msg.sender` | EIP; a16z; crytic 023–028 | ✓ | ✓ | by construction (no caller argument) |
| `deposit`/`mint`/`withdraw`/`redeem` match their previews exactly | EIP; a16z `prop_preview*` | ✓ | ✓ | `Solmate.deposit_eq_previewDeposit`, `mint_eq_previewMint`, `withdraw_eq_previewWithdraw`, `redeem_eq_previewRedeem`; `Oz.previews_exact` |
| effects: assets and shares move as specified, supplies change accordingly | a16z; crytic 029–032 | ✓ | ✓ | `Solmate.deposit_eq_some`, `mint_eq_some'`, `withdraw_eq_some`, `redeem_eq_some`; `Oz.deposit_eq_some` … |
| a third party withdraws/redeems only within its allowance | EIP; a16z; crytic 009–012, 035–036 | ✓ | ✓ | `Solmate.withdraw_auth`, `redeem_auth`, `Oz.withdraw_auth`, `Oz.redeem_auth` |
| rounding: deposit shares ↓, mint assets ↑, withdraw shares ↑, redeem assets ↓ (also over ℚ) | EIP Security Considerations; crytic 013–022 | ✓ | ✓ | `Solmate.{deposit,mint,withdraw,redeem}_rounding`, `deposit_shares_le_fair`, `mint_assets_ge_fair`, `withdraw_shares_ge_fair`, `redeem_assets_le_fair`; `Oz.*_rounding` |
| `previewWithdraw(a) > 0` for `a > 0` | crytic 017, 021 | ✓ | ✓ | `Solmate.previewWithdraw_pos`, `Oz.previewWithdraw_pos` |
| `previewMint(n) > 0` for `n > 0` | crytic 014, 020 | **✗** when `S > 0 = T` | ✓ | ✗ `Solmate.previewMint_zero_of_totalAssets_zero`; `Oz.previewMint_pos` |
| withdrawing `maxWithdraw(owner)` needs at most the owner's shares | EIP | ✓ | — | `Solmate.previewWithdraw_maxWithdraw_le` |
| `maxWithdraw` MUST NOT revert | EIP; a16z `prop_maxWithdraw` | **✗** when `balanceOf[owner]·T ≥ 2²⁵⁶` | — | ✗ `Solmate.maxWithdraw_reverts_of_overflow` |
| `convertToShares` reverts only on overflow | EIP; crytic 004, 037 | **✗** reverts on every input when `S > 0 = T` | not stated | ✗ `Solmate.convertToShares_reverts_of_totalAssets_zero` |
| `maxDeposit` is the largest non-reverting deposit | EIP | **✗** `2²⁵⁶−1` while every deposit reverts (`S > 0 = T`) | not stated | ✗ `Solmate.deposit_reverts_of_totalAssets_zero` |
| `maxRedeem(owner)` is redeemable | EIP; a16z `prop_maxRedeem` | **✗** when `balance·T < S` (`ZERO_ASSETS`) | not stated | ✗ `Solmate.maxRedeem_reverts` |
| a deposit whose shares round to 0 | OZ-docs | reverts (`ZERO_SHARES`) | mints 0 shares (allowed; the depositor loses `a`) | `Solmate.solmate_attack_victim_reverts`; `Oz.deposit_zero_shares`, `Witnesses.oz_zero_shares_witness` |

## Round trips

Solmate satisfies each when `S > 0` before the call (and, for trips starting with a
withdrawal or redemption, shares remain in between): exactly the a16z assumption with
`_vaultMayBeEmpty = false`. OZ(δ) satisfies all eight in every state. The arithmetic core is
`QEDefi.Math.rt_in_out_assets`, `rt_in_out_shares`, `rt_out_in_shares`, `rt_out_in_assets`.

| Property (a16z `prop_RT_*`) | Solmate | Lean |
|---|---|---|
| `redeem(deposit(a)) ≤ a` | ✓ if `S > 0`; **✗** if `S = 0 < T` (returns `T + a`) | `Solmate.rt_deposit_redeem`; ✗ `Solmate.rt_deposit_redeem_empty_supply`, `Witnesses.solmate_rt_deposit_redeem_witness` |
| `deposit(a) ≤ withdraw(a)` (shares) | ✓ if `S > 0` | `Solmate.rt_deposit_withdraw` |
| `redeem(n) ≤ mint(n)` (assets) | ✓ if `S > 0`; **✗** if `S = 0 < T` | `Solmate.rt_mint_redeem`; ✗ `Solmate.rt_mint_redeem_empty_supply` |
| `withdraw(mint(n)) ≥ n` (shares) | ✓ if `S > 0` | `Solmate.rt_mint_withdraw` |
| `deposit(redeem(n)) ≤ n` | ✓ if shares remain; **✗** if the redemption drains a vault with `T > S` (share count only) | `Solmate.rt_redeem_deposit`; ✗ `Solmate.rt_redeem_deposit_drained` |
| `mint(n) ≥ redeem(n)` (assets) | ✓ if shares remain | `Solmate.rt_redeem_mint` |
| `mint(withdraw(a)) ≥ a` | ✓ if shares remain | `Solmate.rt_withdraw_mint` |
| `deposit(a) ≤ withdraw(a)` after withdrawing | ✓ if shares remain | `Solmate.rt_withdraw_deposit` |
| `convertToAssets(convertToShares(a)) ≤ a` and conversely (crytic) | ✓ in every state | `Solmate.convert_roundtrip`, `convert_roundtrip2` |

The OZ theorems have the same names in `Oz.` (`Oz.rt_deposit_redeem`, …, `Oz.convert_roundtrip2`).

## Economic properties

| Property | Source | Solmate | OZ(δ) | Lean |
|---|---|---|---|---|
| no dilution: deposit/mint/withdraw/redeem never lower assets per share (`T·S' ≤ T'·S`; OZ with `T̂, Ŝ`) | EIP; OZ-docs | ✓ if `S > 0` | ✓ always | `Solmate.{deposit,mint,withdraw,redeem}_price_mono`, `deposit_price_le`, `redeem_price_le`; `Oz.*_price_mono`, `Oz.price_le_of_cross` |
| attack as denial of service: after `deposit(1)` + donation `D`, every `deposit(a ≤ D)` reverts | OZ-docs; crytic 033 | ✓ | — | `Solmate.solmate_attack_setup`, `solmate_attack_victim_reverts`, `Witnesses.solmate_attack_witness` |
| attack as theft: `D < a ≤ 2D+1` mints one share worth `⌊(a+D+1)/2⌋`, victim loses `⌊(a−D)/2⌋` (≈ 25 %) | crytic 033 | ✗ vulnerable | — | `Solmate.solmate_attack_victim_one_share`, `Witnesses.solmate_attack_witness` (`D = 100`, `a = 201`: loss 50) |
| general attack (attacker holds `b` shares): `P·Ŝ = b·L − D·(Ŝ − b)`, `0 ≤ L <` one post-donation share | OZ-docs | ✓ (`Ŝ = S`); all shares ⇒ **`P = L`** | ✓ | `Solmate.solmate_donation_attack`, `solmate_donation_attack_all_shares`; `Oz.oz_donation_attack`; `Inflation.profit_mul`, `loss_mul`, `loss_bounds`, `solmate_profit_eq_loss` |
| attacker profit `P·(S+k) ≤ T + 1 − (k−1)·D` | OZ-docs | — | ✓ | `Inflation.oz_profit_bound` |
| inflicting loss `L` costs more than `k·L − k·(T+1)/(S+k)` | OZ-docs | — | ✓ | `Inflation.oz_cost_bound` |
| crytic 033: victim loss `< (3/4)·a/10^δ` | crytic 033 | ✗ | ✓ for `δ ≥ 3`; griefing only at `δ = 0` | `Oz.crytic_inflation_bound` |

## Not covered at the model level

- `asset()`, `totalAssets()`, `max*` "MUST NOT revert" (crytic 001–008) beyond the `mulDiv`
  reverts above; `decimals` (crytic 034).
- Fee-on-transfer or rebasing assets; reentrancy (the pinned assets make no calls).
- a16z `checkNoFreeProfit` as a separate statement (implied by the round trips on the asset
  side).
- OZ `maxDeposit`/`maxRedeem` exactness, and an empty-vault setup theorem for OZ (its attack
  theorems take the post-setup state as hypothesis).

Events and `permit` are modelled separately (`QEDefi.ERC4626.Events`, `QEDefi.ERC20.Permit`) and
proved on the bytecode ([details.md](details.md)).
