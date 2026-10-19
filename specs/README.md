# EvmLeanSpecs — abstract ERC-4626 vault models

A separate Lake package (it uses Mathlib, which the evm-lean semantics must not depend on)
holding the abstract specification side of the ERC-4626 verification effort
(`docs/erc4626-plan.md`): Lean models of the Solmate and OpenZeppelin vaults, the property
catalogue of `docs/erc4626-invariants.md` proved (or refuted) on them, and the
donation/inflation-attack theorems.

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd specs
lake exe cache get        # Mathlib oleans (also run automatically by `lake update`)
lake build                # ~45 s from scratch once Mathlib's cache is present
```

* Toolchain `leanprover/lean4:v4.35.0` (same as the root package).
* Dependencies: Mathlib at tag `v4.35.0`, and evm-lean itself by path (`..`). Requiring the
  parent by path works without cycles; `EvmLeanSpecs/Bridge.lean` imports both and fixes
  the actor type for refinement proofs (`EvmLean.Address`).
* The vault files use the Lean module system (`module`, `public import`) because Mathlib
  does; `Bridge.lean` and the root are ordinary files since evm-lean is not a module
  library.
* Trust: no `sorry`, `axiom`, `native_decide`, `opaque`, `partial`. All theorems use only
  `propext`, `Classical.choice`, `Quot.sound` (checked with `Lean.collectAxioms` over every
  theorem in the `EvmLeanSpecs` namespace). The models are `noncomputable` (Finsupp), so
  concrete runs are proved with `simp` (`Witnesses.lean`), not `#eval`.

## The models

`Token A` (`Token.lean`) is ERC-20 storage over addresses `A`: `balanceOf : A →₀ ℕ`,
`totalSupply`, `allowance`. Solmate (`transfer`, `transferFrom`, `approve`, `mint`, `burn`)
and OpenZeppelin v5 (`ozUpdate`, `ozTransfer`, `ozMint`, `ozBurn`, `ozApprove`, `ozSpend`,
`ozTransferFrom`) operations return `Option` (`none` = revert) and mirror the Solidity
sources, including every checked operation and zero-address check. Unchecked additions are
`ℕ` additions, exact under `Token.WF` (`Σ balanceOf = totalSupply ≤ 2²⁵⁶−1`), which every
operation preserves.

`Solmate.State A` (`Solmate.lean`): vault address, asset ledger (`MockERC20`), share ledger,
and `MockERC4626`'s two hook counters. Views `convertToShares`, `convertToAssets`,
`preview*`, `max*`; entry points `deposit`, `mint`, `withdraw`, `redeem` return the new
state and the returned amount. Rounding is Solmate's exactly: `mulDivDown` / `mulDivUp`
with the `supply == 0` identity case, `mulDiv` reverting on `denominator = 0` or product
overflow (tested as `y ≠ 0 ∧ x > MAX / y`, as in the assembly), `ZERO_SHARES` /
`ZERO_ASSETS`, checked `totalSupply += shares`, checked counter increments. `Op` / `step` /
`exec` give the transaction-level state machine, including the asset's own entry points:
donations (`assetTransfer` to the vault), yield (`assetMint`) and losses (`assetBurn`).

`Oz.State A` (`Oz.lean`): the same for OpenZeppelin v5.7 `ERC4626` with decimals offset `δ`
(a parameter of every function): conversions `mulDiv(x, S + 10^δ, T + 1, rounding)` with
OZ's full-precision `mulDiv` (reverts only on zero divisor or result overflow, checked
rounding increment), the `ERC4626ExceededMax*` checks, and OZ `ERC20` semantics.

Both models omit events, gas, `permit`, and reentrancy (the pinned assets make no calls).
Theorems about value flows assume the vault never calls itself (`caller ≠ self` for
deposits, `receiver ≠ self` for exact `totalAssets` bookkeeping on withdrawals).

## Theorem index

| File | Contents |
|---|---|
| `Vault/Arith.lean` | `mulDivDown`, `mulDivUp`, `ozMulDiv`, `ceilDiv`; `mulDivDown_eq_some`, `overflow_test_iff`, `le_ceilDiv_mul`, `ceilDiv_le_iff`, `ozMulDiv_eq_some` |
| `Vault/Token.lean` | ledgers; `WF_*` preservation for every operation; effect lemmas `transfer_eq_some`, `mint_eq_some`, `burn_eq_some`, `ozTransfer_eq_some`, … |
| `Vault/SolmateEffects.lean` | `deposit_eq_some`, `mint_eq_some'`, `withdraw_eq_some`, `redeem_eq_some`; `Inv_step`, **`Inv_exec`**, **`totalSupply_eq_sum_exec`** |
| `Vault/SolmateProps.lean` | previews = results; `*_rounding` (ℕ) and `*_fair` (ℚ); `*_price_mono`, `deposit_price_le`; **`solvent`**; the eight `rt_*`; refutations `rt_deposit_redeem_empty_supply`, `rt_mint_redeem_empty_supply`, `rt_redeem_deposit_drained`, `convertToShares_reverts_of_totalAssets_zero`, `deposit_reverts_of_totalAssets_zero`, `previewMint_zero_of_totalAssets_zero`, `maxRedeem_reverts` |
| `Vault/RoundTripAlgebra.lean` | the four inequalities behind all round trips |
| `Vault/OzProps.lean` | `Inv_exec`, `totalSupply_eq_sum_exec`, `previews_exact`, `*_rounding`, `*_price_mono` (unconditional), `solvent`, all eight `rt_*` (unconditional), `deposit_zero_shares` |
| `Vault/InflationAlgebra.lean` | `profit_mul`, `loss_mul`, `loss_bounds`, `oz_profit_bound`, `oz_cost_bound`, `solmate_profit_eq_loss` |
| `Vault/Inflation.lean` | Solmate: `solmate_attack_setup`, `solmate_attack_victim_reverts`, `solmate_attack_victim_one_share`, `solmate_donation_attack`, `solmate_donation_attack_all_shares`; OZ: `oz_donation_attack` |
| `Vault/MoreProps.lean` | `withdraw_auth`/`redeem_auth` (both), `convert_roundtrip`/`convert_roundtrip2` (both), `previewWithdraw_pos` (both), `Oz.previewMint_pos`, `Oz.crytic_inflation_bound` |
| `Vault/Witnesses.lean` | concrete runs: Solmate deposit 1 → redeem 2; Solmate attack with `D = 100` (victim deposits 201, gets 1 share worth 151; deposit of 100 reverts); OZ `δ = 0` deposit minting 0 shares |

Headline results:

* **Solmate** satisfies supply consistency, solvency, exact previews, correct rounding
  directions and no dilution, and all eight round trips *when the vault has shares*; it
  violates them on `S = 0 < T` (first depositor captures earlier donations/yield), and
  violates the EIP's no-revert/max clauses after a total loss. The first-depositor attack
  gives the attacker exactly the victim's loss (`P = L`); `ZERO_SHARES` turns deposits
  `≤ D` into reverts but deposits in `(D, 2D+1]` lose up to ~25 %.
* **OpenZeppelin(δ)** satisfies every round trip and price monotonicity unconditionally;
  the attacker's profit is at most `(T + 1 − (10^δ − 1)·D)/(S + 10^δ)`, and inflicting a
  loss `L` costs more than `10^δ·L − 10^δ·(T+1)/(S+10^δ)`.

See `docs/erc4626-invariants.md` for the full catalogue with sources.
