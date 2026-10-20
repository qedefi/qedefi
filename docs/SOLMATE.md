# Refinement: the compiled Solmate vault implements the model

Theorems relating the **deployed bytecode** of Solmate `MockERC4626` (vault) and `MockERC20`
(asset) — `Contracts.SolmateVault` / `Contracts.SolmateAsset`, solc 0.8.28, deployed with
**arbitrary immutables** (`runtimeCodeWith i`: any asset address, chain id, domain separator,
decimals) — to the Mathlib model `Vault.Solmate.State` (`defi/Defi/ERC4626/Solmate.lean`). Every theorem
holds for every `Crypto`; only the standard axioms are used.

Two families of files: the share-token functions (`Shares*.lean`, see `defi/Examples/Solmate/ERC4626/Shares.lean`) and the
core described here.

| file | contents |
|---|---|
| `defi/Examples/Solmate/ERC4626/MulDiv.lean` | `mulDivDown_wp`, `mulDivUp_wp`: Solmate's assembly `mulDiv` (internal, entries `0x0e62`, `0x0e7d`) |
| `defi/Examples/Solmate/ERC20/BalanceOf.lean` | `balanceOf_halts`: asset `balanceOf` as a callee summary; `fresh_intro` |
| `defi/Examples/Solmate/ERC20/Transfer.lean`, `defi/Examples/Solmate/ERC20/TransferFrom.lean` | `transfer_halts_ok/_revert`, `transferFrom_halts_ok/_revert` (callee summaries, exact worlds) |
| `defi/Examples/Solmate/ERC4626/Convert.lean` | `VaultFrame`, `totalAssets_wp`: the internal `totalAssets()` with its `STATICCALL` to the asset (via `WP.staticcall` + `balanceOf_halts`) |
| `defi/Examples/Solmate/ERC4626/Convert.lean` | `convertToShares_wp`, `convertToAssets_wp`, `previewMint_wp`, `previewWithdraw_wp`: the four internal conversions |
| `defi/Examples/Solmate/ERC4626/Views.lean`, `defi/Examples/Solmate/ERC4626/Views.lean` | `*_halts`: the 13 views at the bytecode level (`Nat` specs) |
| `defi/Examples/Solmate/ERC4626/Abstraction.lean` | `Deployed`, `toToken`, `tokenView`, `abs`, `Refines`, `refines_iff` |
| `defi/Examples/Solmate/ERC4626/ViewsSpec.lean` | `*_refines` (any frame) and `*_call` (top-level) for the views, against the model |
| `defi/Examples/Solmate/ERC20/Spec.lean` | `assetBalanceOf_refines`, `assetTransfer_refines`, `assetTransferFrom_refines` against `Token` |

Generic tools (root package): `EvmLogic/Program/Summary.lean` (`WP.bind_mono`,
`Machine.resumeAt/resumeWith`), `EvmLogic/Tactic/WpStep.lean` (`evm_gas` over symbolic memory,
`wp_generalize_gas`), `EvmLogic/Tactic/Patched.lean` (`pwp_step(s)`, `pwp_run_to`,
`pcode_fact`, `pjumpdest_disch`: `wp_step` on code with symbolic immutables),
`EvmLogic/Tactic/Patched.lean` (`pwp_codecopy`), `EvmLogic/Solidity/Word.lean` (the `mulDiv` guard,
ABI length check), `EvmLogic/Solidity/Memory.lean` (calldata assembled in memory).

## The bridge

* `Deployed w vault asset`: `w.code vault = SolmateVault.runtimeCodeWith i` for some `i` with
  `i.asset = asset`, `w.code asset = SolmateAsset.runtimeCodeWith ia` for some `ia`, neither a
  precompile. (`runtimeCodeFor keccak chainId asset vault` and the canonical deployment,
  `deployed_canonical`, are instances; codes are never EIP-7702 designators.)
* `abs crypto w vault asset : Solmate.State Address`: `self := vault`; `shares` / `asset` are
  `tokenView` = `toToken (Erc20.view …)`: `toNat` of `totalSupply` (slot 2), `balanceOf[a]`
  (`keccak(a ‖ 3)`, as a `Finsupp` — `Address` is finite, so no assumption is needed),
  `allowance[o][s]` (`keccak(s ‖ keccak(o ‖ 4))`); the hook counters are slots 7 and 6.
* `Refines crypto w vault asset s` is the `Shares.Rep` form (both ledgers represented, counters
  equal); `refines_iff : Refines … s ↔ s = abs …`. After writes use `Shares.RepOn P`: the
  allowances are known only for entries whose slot was not written.

Reading needs **no** hash hypothesis: `abs` is by definition what the code reads. Hypotheses
on Keccak appear only for writes and are pointwise (`EvmLogic/Solidity/Keccak.lean`):
`Erc20.BalanceSlotOk` for each balance written, `Erc20.AllowanceSlotOk` for each allowance
written; never global injectivity (false for every `Crypto`).

## The summaries

Every bytecode theorem is a `WP`/`Halts` statement about **any** machine whose frame is in the
stated shape — any parents, depth, `Crypto`, world — so it serves both as a top-level
theorem (`processMessageCall_of_halts`, see `view_call`) and as a callee summary
(`WP.call` / `WP.staticcall`).

* **Asset, callee role.** `balanceOf_halts` (`BalanceOfPost`: returns the balance word, world,
  transient storage, created accounts and logs unchanged, ≤ 3000 gas), `transfer_halts_ok`
  (`TransferOk`: returns `true`, world `transferWorld`, ≤ 55000 gas), `transfer_halts_revert`,
  `transferFrom_halts_ok` (`TransferFromOk`: world `Erc20.transferFromWorld`, ≤ 80000 gas),
  `transferFrom_halts_revert` (`Reverts g`). Model level: `assetTransfer_refines` and
  `assetTransferFrom_refines` `match` on `Token.transfer` / `Token.transferFrom` of a ledger
  `t` represented by the asset's storage (`Shares.Rep`, `t.WF`): `some t'` ⇒ the summary above
  and `RepOn … (view mf.world) t'`; `none` ⇒ a revert.
* **`mulDiv`.** `mulDivDown_wp` / `mulDivUp_wp`: from pc `0x0e62` / `0x0e7d` with stack
  `d :: y :: x :: r :: rest`, either `mulDivDownN x y d = some v` and the machine is
  `m.resumeAt r (v :: rest) (gas − 81)` (`− 107` for up), or the spec is `none` and the frame
  ends with `revert(0, 0)` (`MulDivRevert`). `mulDivDownN = Vault.mulDivDown` by `rfl`.
* **`totalAssets` (internal, `0x047b`).** `totalAssets_wp`: returns `assetsOf i.asset m` (the
  vault's balance slot in the asset) with memory `FmpAfterCall`, world unchanged, ≤ 8000 gas.
* **Conversions** (`0x0bda`, `0x0593`, `0x096b`, `0x062b`): result `some v` / revert per
  `convertToSharesN` … (at `supplyOf m`, `assetsOf i.asset m`), memory `FmpOk`, ≤ 12000 gas.
* **Views.** `convertToShares`, `convertToAssets`, `previewDeposit`, `previewMint`,
  `previewWithdraw`, `previewRedeem`, `maxDeposit`, `maxMint`, `maxWithdraw`, `maxRedeem`,
  `totalAssets`, `asset`: `X_refines (m) (h : ViewPre i m) (hd : WordCall/AddrCall/NoArgCall …)
  : Halts m (ViewPost m (<model value at absOf i.asset m>))`, and
  `X_call (hdep : Deployed w vault asset) … : ∃ n, ∀ fuel ≥ n, ∃ res, processMessageCall …
  (callMsg (w.code vault) vault caller (Abi.encodeCall sel args) gas …) = .ok res ∧
  res.world = w ∧ ViewResult res (<model value at abs ctx.crypto w vault asset>)`.

Assumptions of the views: `60000 ≤ gas < 2⁶⁴`, no value, the asset deployed and not a
precompile, call depth below 1024, and (top level) no EIP-7702 authorizations or a fork before
Prague.

## For the deposit / mint / withdraw / redeem agents

1. **Shape.** Prove a `Halts` summary of the external function from a fresh frame
   (`fresh_intro` / `view_intro`-style preamble, then `pwp_run_to <internal entry>`), composing
   internal summaries with `WP.bind_mono`, and lift it with `view_call`-style glue (or
   `processMessageCall_of_halts`) to `processMessageCall`. Use `pwp_steps` (not `wp_steps`):
   the vault code is `runtimeCodeWith i`; keep `have hagree := Shares.jumpDestsAgree i` in
   context, and pass `readBytes_code_asset1170`-style lemmas for `PUSH32`s of the `asset`
   immutable (offsets 688, 1170, 2014, 2169, 2668, 2995; see `readBytes_code_asset688`).
2. **Previews are done.** `deposit` starts with `previewDeposit(assets)` → `convertToShares_wp`
   (entry `0x0bda`); `mint` with `previewMint_wp`; `withdraw` with `previewWithdraw_wp`;
   `redeem` with `convertToAssets_wp` (after the allowance check). All take `VaultFrame i m`
   and `FmpInit` memory (solc's initial memory satisfies it: `initMemory_fmpInit`; scratch
   writes at `0x00–0x3f` keep it, see `maxWithdraw_halts`).
3. **Calls into the asset.** `safeTransferFrom` / `safeTransfer` are `CALL`s with value 0:
   use `WP.call` with `step_call` (there is no `WP.call` wrapper for `CALL` yet; follow
   `WP.staticcall` in `EvmLogic/Program/Call.lean`) and `transferFrom_halts_ok` / `transfer_halts_ok`
   on the child frame (the child message has `isStatic = false` from a non-static vault
   frame; calldata facts as `ThreeWordCall` / `TwoWordCall`, proved from memory as in
   `totalAssets_wp` with `Memory.readBytes_read`). After `resumeAfter_success`, rewrite
   `mf.world`, `mf.transient`, `mf.createdAccounts` with the summary, and use
   `wp_generalize_gas` + one `evm_gas` to replace the post-call gas by a variable with a
   lower bound (it keeps the following steps fast). Clear hypotheses that mention large code
   (`hcode`, `hdel`) before `pwp_steps` reaches a `JUMP` to a symbolic return address
   (`assumption` would otherwise unfold them).
4. **Model side.** Relate the final world with `Refines` / `RepOn`: shares via the share-token
   lemmas (`Erc20.view_sstore_balanceSlot`, `Shares.rep_*`), the asset via
   `assetTransferFrom_refines` / `assetTransfer_refines` (or directly
   `Erc20.view_transferFromWorld` + `Shares.rep_transferFrom`), hook counters by
   `World.sload_sstore`. `Vault.Solmate.deposit` etc. are `Option` chains whose steps map 1:1
   to these summaries; `none` steps are reverts of the whole call.
5. **Hypotheses to carry:** `BalanceSlotOk` (caller, receiver, owner, the vault itself in the
   asset), `AllowanceSlotOk` (the spent entries), `Inv` (`Token.WF` of both ledgers) for the
   unchecked additions, `caller ≠ vault` where the model needs it.

## Build

`cd defi && lake build`. Times of the core files (M-series laptop, sequential within a
file): `Examples.Solmate.ERC20.TransferFrom` 128 s, `Examples.Solmate.ERC4626.Views` 74 s, `Examples.Solmate.ERC20.Transfer` 56 s, `Examples.Solmate.ERC4626.Views`
51 s, `Examples.Solmate.ERC4626.Convert` 22 s, `Abstraction` 22 s (Mathlib import), `Examples.Solmate.ERC4626.Convert` 18 s,
`Examples.Solmate.ERC20.BalanceOf` 16 s, `MulDiv` 12 s, `Examples.Solmate.ERC4626.ViewsSpec`, `Examples.Solmate.ERC20.Spec` 5 s; about 4 min wall
clock in parallel.
