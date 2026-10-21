# Renames

The restructuring (files into `EvmLogic/`, `EvmTest/`, `defi/Defi/`, `defi/Examples/`; namespaces
mirroring directories) renamed modules and namespaces but kept every declaration's base name.
This table lists the old and new full names of the headline theorems; every other
declaration moved the same way (old namespace prefix → new prefix, see the module table at the end).

## Package rename: defi → qedefi, Defi → QEDefi

The DeFi package was later renamed to QEDefi ("QEDefi: DeFi, quod erat demonstrandum."). Every
declaration kept its base name and statement; only the `Defi` prefix changed. The sections
below record the restructuring as it happened, so their "new" names still read `Defi.*`
(and `defi/Defi/`): apply this mapping to get the current names.

| Old | New |
|---|---|
| directory `defi/` | `qedefi/` |
| Lake package `defi` | `qedefi` |
| library and root module `Defi` (`defi/Defi.lean`) | `QEDefi` (`qedefi/QEDefi.lean`) |
| modules `Defi.*` (`defi/Defi/…`) | `QEDefi.*` (`qedefi/QEDefi/…`) |
| namespace `Defi.Math.*` | `QEDefi.Math.*` |
| namespace `Defi.ERC20.*` | `QEDefi.ERC20.*` |
| namespace `Defi.ERC4626.*` | `QEDefi.ERC4626.*` |
| namespace `Defi.Trace.*` | `QEDefi.Trace.*` |
| `Examples.*` (library, modules, namespaces), in `defi/Examples/` | unchanged names, in `qedefi/Examples/` |

The core package `evm-lean` (`EvmLean`, `EvmLogic`, `EvmTest`, `Conformance`) is unchanged.

## `Defi.ERC4626.Inflation` (was `EvmLeanSpecs.Vault.InflationAlgebra`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Vault.Inflation.loss_bounds` | `Defi.ERC4626.Inflation.loss_bounds` |
| `EvmLeanSpecs.Vault.Inflation.loss_mul` | `Defi.ERC4626.Inflation.loss_mul` |
| `EvmLeanSpecs.Vault.Inflation.oz_cost_bound` | `Defi.ERC4626.Inflation.oz_cost_bound` |
| `EvmLeanSpecs.Vault.Inflation.oz_profit_bound` | `Defi.ERC4626.Inflation.oz_profit_bound` |
| `EvmLeanSpecs.Vault.Inflation.profit_mul` | `Defi.ERC4626.Inflation.profit_mul` |
| `EvmLeanSpecs.Vault.Inflation.solmate_profit_eq_loss` | `Defi.ERC4626.Inflation.solmate_profit_eq_loss` |

## `Defi.ERC4626.Inflation` (was `EvmLeanSpecs.Vault.Inflation`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Vault.Oz.donate_eq` | `Defi.ERC4626.Oz.donate_eq` |
| `EvmLeanSpecs.Vault.Oz.oz_donation_attack` | `Defi.ERC4626.Oz.oz_donation_attack` |
| `EvmLeanSpecs.Vault.Solmate.donate_eq` | `Defi.ERC4626.Solmate.donate_eq` |
| `EvmLeanSpecs.Vault.Solmate.solmate_attack_setup` | `Defi.ERC4626.Solmate.solmate_attack_setup` |
| `EvmLeanSpecs.Vault.Solmate.solmate_attack_victim_one_share` | `Defi.ERC4626.Solmate.solmate_attack_victim_one_share` |
| `EvmLeanSpecs.Vault.Solmate.solmate_attack_victim_reverts` | `Defi.ERC4626.Solmate.solmate_attack_victim_reverts` |
| `EvmLeanSpecs.Vault.Solmate.solmate_donation_attack` | `Defi.ERC4626.Solmate.solmate_donation_attack` |
| `EvmLeanSpecs.Vault.Solmate.solmate_donation_attack_all_shares` | `Defi.ERC4626.Solmate.solmate_donation_attack_all_shares` |

## `Defi.ERC4626.MoreProps` (was `EvmLeanSpecs.Vault.MoreProps`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Vault.Oz.crytic_inflation_bound` | `Defi.ERC4626.Oz.crytic_inflation_bound` |

## `EvmLogic.AbsInt.Check` (was `EvmLeanProofs.Program.AbsInt.Check`)

| Old name | New name |
|---|---|
| `EvmLean.Program.AbsInt.certify_sound` | `EvmLogic.AbsInt.certify_sound` |

## `EvmLogic.AbsInt.Frame` (was `EvmLeanProofs.Program.AbsInt.Frame`)

| Old name | New name |
|---|---|
| `EvmLean.Program.AbsInt.absint_call` | `EvmLogic.AbsInt.absint_call` |
| `EvmLean.Program.AbsInt.inCert_call` | `EvmLogic.AbsInt.inCert_call` |

## `EvmLogic.GasMono.Depth` (was `EvmLeanProofs.Program.GasMono.Depth`)

| Old name | New name |
|---|---|
| `EvmLean.Program.GasMono.effOf_ne_call` | `EvmLogic.GasMono.effOf_ne_call` |

## `EvmLogic.GasMono.Lockstep` (was `EvmLeanProofs.Program.GasMono.Lockstep`)

| Old name | New name |
|---|---|
| `EvmLean.Program.GasMono.decode_call` | `EvmLogic.GasMono.decode_call` |
| `EvmLean.Program.GasMono.monoFrom_of_code` | `EvmLogic.GasMono.monoFrom_of_code` |

## `EvmLogic.GasMono.Pc` (was `EvmLeanProofs.Program.GasMono.Pc`)

| Old name | New name |
|---|---|
| `EvmLean.Program.GasMono.callsFed_call` | `EvmLogic.GasMono.callsFed_call` |

## `EvmLogic.Program.Call` (was `EvmLeanProofs.Program.Call`)

| Old name | New name |
|---|---|
| `EvmLean.Program.step_call` | `EvmLogic.Program.step_call` |

## `EvmLogic.Program.Summary` (was `EvmLeanProofs.Program.Summary`)

| Old name | New name |
|---|---|
| `EvmLean.Program.frameResult_success_call` | `EvmLogic.Program.frameResult_success_call` |
| `EvmLean.Program.topLevelResult_success_call` | `EvmLogic.Program.topLevelResult_success_call` |

## `EvmLogic.Step.Basic` (was `EvmLeanProofs.Call`)

| Old name | New name |
|---|---|
| `EvmLean.Interpreter.initMachine_call` | `EvmLean.Interpreter.initMachine_call` |

## `Examples.Basic.AddStore` (was `EvmLeanProofs.Execution`)

| Old name | New name |
|---|---|
| `EvmLean.Examples.addStore_gas` | `Examples.Basic.addStore_gas` |
| `EvmLean.Examples.addStore_slot0` | `Examples.Basic.addStore_slot0` |
| `EvmLean.Examples.addStore_slot0'` | `Examples.Basic.addStore_slot0'` |

## `Examples.Basic.Token` (was `EvmLeanProofs.Examples.Token`)

| Old name | New name |
|---|---|
| `EvmLean.Examples.Token.transfer_spec` | `Examples.Basic.Token.transfer_spec` |

## `Examples.Solmate.ERC20.Approve` (was `EvmLeanSpecs.Refinement.AssetApprove`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.assetApprove_refines` | `Examples.Solmate.ERC20.assetApprove_refines` |

## `Examples.Solmate.ERC20.Events` (was `EvmLeanSpecs.Refinement.EventsAsset`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.assetApprove_events_call` | `Examples.Solmate.ERC20.assetApprove_events_call` |
| `EvmLeanSpecs.Refinement.assetBurn_events_call` | `Examples.Solmate.ERC20.assetBurn_events_call` |
| `EvmLeanSpecs.Refinement.assetMint_events_call` | `Examples.Solmate.ERC20.assetMint_events_call` |
| `EvmLeanSpecs.Refinement.assetTransferFrom_events_call` | `Examples.Solmate.ERC20.assetTransferFrom_events_call` |
| `EvmLeanSpecs.Refinement.assetTransfer_events_call` | `Examples.Solmate.ERC20.assetTransfer_events_call` |
| `EvmLeanSpecs.Refinement.asset_events_call` | `Examples.Solmate.ERC20.asset_events_call` |

## `Examples.Solmate.ERC20.MintBurn` (was `EvmLeanSpecs.Refinement.AssetBurn`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.assetBurn_refines` | `Examples.Solmate.ERC20.assetBurn_refines` |

## `Examples.Solmate.ERC20.MintBurn` (was `EvmLeanSpecs.Refinement.AssetMint`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.assetMint_refines` | `Examples.Solmate.ERC20.assetMint_refines` |

## `Examples.Solmate.ERC20.Spec` (was `EvmLeanSpecs.Refinement.AssetSpec`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.assetBalanceOf_refines` | `Examples.Solmate.ERC20.assetBalanceOf_refines` |
| `EvmLeanSpecs.Refinement.assetTransferFrom_refines` | `Examples.Solmate.ERC20.assetTransferFrom_refines` |
| `EvmLeanSpecs.Refinement.assetTransfer_refines` | `Examples.Solmate.ERC20.assetTransfer_refines` |

## `Examples.Solmate.ERC20.Strings` (was `EvmLeanSpecs.Refinement.StringsAssetSpec`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.assetName_call` | `Examples.Solmate.ERC20.assetName_call` |
| `EvmLeanSpecs.Refinement.assetName_refines` | `Examples.Solmate.ERC20.assetName_refines` |
| `EvmLeanSpecs.Refinement.assetSymbol_call` | `Examples.Solmate.ERC20.assetSymbol_call` |
| `EvmLeanSpecs.Refinement.assetSymbol_refines` | `Examples.Solmate.ERC20.assetSymbol_refines` |

## `Examples.Solmate.ERC20.Transfer` (was `EvmLeanProofs.Solidity.Examples.SolmateAssetTransferSpec`)

| Old name | New name |
|---|---|
| `EvmLean.Solidity.Examples.SolmateAssetTransfer.transfer_spec` | `Examples.Solmate.ERC20.transfer_spec` |

## `Examples.Solmate.ERC4626.Deposit` (was `EvmLeanSpecs.Refinement.DepositCall`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.deposit_call` | `Examples.Solmate.ERC4626.deposit_call` |
| `EvmLeanSpecs.Refinement.entry_call` | `Examples.Solmate.ERC4626.entry_call` |
| `EvmLeanSpecs.Refinement.mint_call` | `Examples.Solmate.ERC4626.mint_call` |

## `Examples.Solmate.ERC4626.Deposit` (was `EvmLeanSpecs.Refinement.Deposit`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.deposit_refines` | `Examples.Solmate.ERC4626.deposit_refines` |

## `Examples.Solmate.ERC4626.Deposit` (was `EvmLeanSpecs.Refinement.Mint`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.mint_refines` | `Examples.Solmate.ERC4626.mint_refines` |

## `Examples.Solmate.ERC4626.Events` (was `EvmLeanSpecs.Refinement.Events`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.events_call` | `Examples.Solmate.ERC4626.events_call` |

## `Examples.Solmate.ERC4626.EventsEntry` (was `EvmLeanSpecs.Refinement.EventsEntry`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.deposit_events_call` | `Examples.Solmate.ERC4626.deposit_events_call` |
| `EvmLeanSpecs.Refinement.mint_events_call` | `Examples.Solmate.ERC4626.mint_events_call` |
| `EvmLeanSpecs.Refinement.redeem_events_call` | `Examples.Solmate.ERC4626.redeem_events_call` |
| `EvmLeanSpecs.Refinement.withdraw_events_call` | `Examples.Solmate.ERC4626.withdraw_events_call` |

## `Examples.Solmate.ERC4626.EventsShares` (was `EvmLeanSpecs.Refinement.EventsShares`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.Shares.approve_events_call` | `Examples.Solmate.ERC4626.Shares.approve_events_call` |
| `EvmLeanSpecs.Refinement.Shares.transferFrom_events_call` | `Examples.Solmate.ERC4626.Shares.transferFrom_events_call` |
| `EvmLeanSpecs.Refinement.Shares.transfer_events_call` | `Examples.Solmate.ERC4626.Shares.transfer_events_call` |

## `Examples.Solmate.ERC4626.Invariants.Deployed` (was `EvmLeanSpecs.Refinement.InvariantsWithdrawRedeem`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.Invariants.agree_of_refinesOn` | `Examples.Solmate.ERC4626.Invariants.agree_of_refinesOn` |

## `Examples.Solmate.ERC4626.Invariants.Deployed` (was `EvmLeanSpecs.Refinement.Invariants`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.Invariants.donation_attack` | `Examples.Solmate.ERC4626.Invariants.donation_attack` |
| `EvmLeanSpecs.Refinement.Invariants.donation_attack_view` | `Examples.Solmate.ERC4626.Invariants.donation_attack_view` |

## `Examples.Solmate.ERC4626.Invariants.Deployed` (was `EvmLeanSpecs.Refinement.InvariantsFinal`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.Invariants.donation_attack_deployed` | `Examples.Solmate.ERC4626.Invariants.donation_attack_deployed` |
| `EvmLeanSpecs.Refinement.Invariants.no_dilution_deployed` | `Examples.Solmate.ERC4626.Invariants.no_dilution_deployed` |
| `EvmLeanSpecs.Refinement.Invariants.price_mono_deployed` | `Examples.Solmate.ERC4626.Invariants.price_mono_deployed` |
| `EvmLeanSpecs.Refinement.Invariants.solvent_deployed` | `Examples.Solmate.ERC4626.Invariants.solvent_deployed` |
| `EvmLeanSpecs.Refinement.Invariants.supply_eq_sum_deployed` | `Examples.Solmate.ERC4626.Invariants.supply_eq_sum_deployed` |

## `Examples.Solmate.ERC4626.LowGas.AnyGas` (was `EvmLeanSpecs.Refinement.LowGasHeadline`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.LowGas.follows_trace_anyGas` | `Examples.Solmate.ERC4626.LowGas.follows_trace_anyGas` |
| `EvmLeanSpecs.Refinement.LowGas.follows_tx_anyGas` | `Examples.Solmate.ERC4626.LowGas.follows_tx_anyGas` |
| `EvmLeanSpecs.Refinement.LowGas.invariant_any_tx_anyGas` | `Examples.Solmate.ERC4626.LowGas.invariant_any_tx_anyGas` |
| `EvmLeanSpecs.Refinement.LowGas.invariant_nested_anyGas` | `Examples.Solmate.ERC4626.LowGas.invariant_nested_anyGas` |
| `EvmLeanSpecs.Refinement.LowGas.lift_any_tx_anyGas` | `Examples.Solmate.ERC4626.LowGas.lift_any_tx_anyGas` |
| `EvmLeanSpecs.Refinement.LowGas.lift_nested_anyGas` | `Examples.Solmate.ERC4626.LowGas.lift_nested_anyGas` |
| `EvmLeanSpecs.Refinement.LowGas.price_mono_any_tx_anyGas` | `Examples.Solmate.ERC4626.LowGas.price_mono_any_tx_anyGas` |
| `EvmLeanSpecs.Refinement.LowGas.price_mono_nested_anyGas` | `Examples.Solmate.ERC4626.LowGas.price_mono_nested_anyGas` |
| `EvmLeanSpecs.Refinement.LowGas.solvent_any_tx_anyGas` | `Examples.Solmate.ERC4626.LowGas.solvent_any_tx_anyGas` |
| `EvmLeanSpecs.Refinement.LowGas.solvent_nested_anyGas` | `Examples.Solmate.ERC4626.LowGas.solvent_nested_anyGas` |
| `EvmLeanSpecs.Refinement.LowGas.supply_eq_sum_any_tx_anyGas` | `Examples.Solmate.ERC4626.LowGas.supply_eq_sum_any_tx_anyGas` |
| `EvmLeanSpecs.Refinement.LowGas.supply_eq_sum_nested_anyGas` | `Examples.Solmate.ERC4626.LowGas.supply_eq_sum_nested_anyGas` |

## `Examples.Solmate.ERC4626.Nested.Invariants` (was `EvmLeanSpecs.Refinement.NestedInvariants`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.Nested.invariant_any_tx` | `Examples.Solmate.ERC4626.Nested.invariant_any_tx` |
| `EvmLeanSpecs.Refinement.Nested.invariant_nested` | `Examples.Solmate.ERC4626.Nested.invariant_nested` |
| `EvmLeanSpecs.Refinement.Nested.lift_any_tx` | `Examples.Solmate.ERC4626.Nested.lift_any_tx` |
| `EvmLeanSpecs.Refinement.Nested.lift_nested` | `Examples.Solmate.ERC4626.Nested.lift_nested` |
| `EvmLeanSpecs.Refinement.Nested.price_mono_any_tx` | `Examples.Solmate.ERC4626.Nested.price_mono_any_tx` |
| `EvmLeanSpecs.Refinement.Nested.price_mono_nested` | `Examples.Solmate.ERC4626.Nested.price_mono_nested` |
| `EvmLeanSpecs.Refinement.Nested.solvent_any_tx` | `Examples.Solmate.ERC4626.Nested.solvent_any_tx` |
| `EvmLeanSpecs.Refinement.Nested.solvent_nested` | `Examples.Solmate.ERC4626.Nested.solvent_nested` |
| `EvmLeanSpecs.Refinement.Nested.supply_eq_sum_any_tx` | `Examples.Solmate.ERC4626.Nested.supply_eq_sum_any_tx` |
| `EvmLeanSpecs.Refinement.Nested.supply_eq_sum_nested` | `Examples.Solmate.ERC4626.Nested.supply_eq_sum_nested` |

## `Examples.Solmate.ERC4626.PermitSpec` (was `EvmLeanSpecs.Refinement.PermitCall`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.Permit.asset_domainSeparator_call` | `Examples.Solmate.ERC4626.Permit.asset_domainSeparator_call` |
| `EvmLeanSpecs.Refinement.Permit.asset_nonces_call` | `Examples.Solmate.ERC4626.Permit.asset_nonces_call` |
| `EvmLeanSpecs.Refinement.Permit.asset_permit_call` | `Examples.Solmate.ERC4626.Permit.asset_permit_call` |
| `EvmLeanSpecs.Refinement.Permit.vault_domainSeparator_call` | `Examples.Solmate.ERC4626.Permit.vault_domainSeparator_call` |
| `EvmLeanSpecs.Refinement.Permit.vault_nonces_call` | `Examples.Solmate.ERC4626.Permit.vault_nonces_call` |
| `EvmLeanSpecs.Refinement.Permit.vault_permit_call` | `Examples.Solmate.ERC4626.Permit.vault_permit_call` |

## `Examples.Solmate.ERC4626.PermitSpec` (was `EvmLeanSpecs.Refinement.PermitSpec`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.Permit.asset_permit_call_refines` | `Examples.Solmate.ERC4626.Permit.asset_permit_call_refines` |
| `EvmLeanSpecs.Refinement.Permit.asset_permit_refines` | `Examples.Solmate.ERC4626.Permit.asset_permit_refines` |
| `EvmLeanSpecs.Refinement.Permit.vault_permit_call_refines` | `Examples.Solmate.ERC4626.Permit.vault_permit_call_refines` |
| `EvmLeanSpecs.Refinement.Permit.vault_permit_refines` | `Examples.Solmate.ERC4626.Permit.vault_permit_refines` |

## `Examples.Solmate.ERC4626.Shares` (was `EvmLeanSpecs.Refinement.Shares`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.Shares.allowance_refines` | `Examples.Solmate.ERC4626.Shares.allowance_refines` |
| `EvmLeanSpecs.Refinement.Shares.approve_refines` | `Examples.Solmate.ERC4626.Shares.approve_refines` |
| `EvmLeanSpecs.Refinement.Shares.balanceOf_refines` | `Examples.Solmate.ERC4626.Shares.balanceOf_refines` |
| `EvmLeanSpecs.Refinement.Shares.decimals_refines` | `Examples.Solmate.ERC4626.Shares.decimals_refines` |
| `EvmLeanSpecs.Refinement.Shares.totalSupply_refines` | `Examples.Solmate.ERC4626.Shares.totalSupply_refines` |
| `EvmLeanSpecs.Refinement.Shares.transferFrom_refines` | `Examples.Solmate.ERC4626.Shares.transferFrom_refines` |
| `EvmLeanSpecs.Refinement.Shares.transfer_refines` | `Examples.Solmate.ERC4626.Shares.transfer_refines` |

## `Examples.Solmate.ERC4626.SharesFrame` (was `EvmLeanSpecs.Refinement.SharesFrameSpec`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.sharesApprove_refines` | `Examples.Solmate.ERC4626.sharesApprove_refines` |
| `EvmLeanSpecs.Refinement.sharesTransferFrom_refines` | `Examples.Solmate.ERC4626.sharesTransferFrom_refines` |
| `EvmLeanSpecs.Refinement.sharesTransfer_refines` | `Examples.Solmate.ERC4626.sharesTransfer_refines` |

## `Examples.Solmate.ERC4626.Strings` (was `EvmLeanSpecs.Refinement.StringsVaultSpec`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.string_call` | `Examples.Solmate.ERC4626.string_call` |
| `EvmLeanSpecs.Refinement.vaultName_call` | `Examples.Solmate.ERC4626.vaultName_call` |
| `EvmLeanSpecs.Refinement.vaultName_refines` | `Examples.Solmate.ERC4626.vaultName_refines` |
| `EvmLeanSpecs.Refinement.vaultSymbol_call` | `Examples.Solmate.ERC4626.vaultSymbol_call` |
| `EvmLeanSpecs.Refinement.vaultSymbol_refines` | `Examples.Solmate.ERC4626.vaultSymbol_refines` |

## `Examples.Solmate.ERC4626.ViewsSpec` (was `EvmLeanSpecs.Refinement.VaultViewsSpec`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.asset_call` | `Examples.Solmate.ERC4626.asset_call` |
| `EvmLeanSpecs.Refinement.asset_refines` | `Examples.Solmate.ERC4626.asset_refines` |
| `EvmLeanSpecs.Refinement.convertToAssets_call` | `Examples.Solmate.ERC4626.convertToAssets_call` |
| `EvmLeanSpecs.Refinement.convertToAssets_refines` | `Examples.Solmate.ERC4626.convertToAssets_refines` |
| `EvmLeanSpecs.Refinement.convertToShares_call` | `Examples.Solmate.ERC4626.convertToShares_call` |
| `EvmLeanSpecs.Refinement.convertToShares_refines` | `Examples.Solmate.ERC4626.convertToShares_refines` |
| `EvmLeanSpecs.Refinement.maxDeposit_call` | `Examples.Solmate.ERC4626.maxDeposit_call` |
| `EvmLeanSpecs.Refinement.maxDeposit_refines` | `Examples.Solmate.ERC4626.maxDeposit_refines` |
| `EvmLeanSpecs.Refinement.maxMint_call` | `Examples.Solmate.ERC4626.maxMint_call` |
| `EvmLeanSpecs.Refinement.maxMint_refines` | `Examples.Solmate.ERC4626.maxMint_refines` |
| `EvmLeanSpecs.Refinement.maxRedeem_call` | `Examples.Solmate.ERC4626.maxRedeem_call` |
| `EvmLeanSpecs.Refinement.maxRedeem_refines` | `Examples.Solmate.ERC4626.maxRedeem_refines` |
| `EvmLeanSpecs.Refinement.maxWithdraw_call` | `Examples.Solmate.ERC4626.maxWithdraw_call` |
| `EvmLeanSpecs.Refinement.maxWithdraw_refines` | `Examples.Solmate.ERC4626.maxWithdraw_refines` |
| `EvmLeanSpecs.Refinement.previewDeposit_call` | `Examples.Solmate.ERC4626.previewDeposit_call` |
| `EvmLeanSpecs.Refinement.previewDeposit_refines` | `Examples.Solmate.ERC4626.previewDeposit_refines` |
| `EvmLeanSpecs.Refinement.previewMint_call` | `Examples.Solmate.ERC4626.previewMint_call` |
| `EvmLeanSpecs.Refinement.previewMint_refines` | `Examples.Solmate.ERC4626.previewMint_refines` |
| `EvmLeanSpecs.Refinement.previewRedeem_call` | `Examples.Solmate.ERC4626.previewRedeem_call` |
| `EvmLeanSpecs.Refinement.previewRedeem_refines` | `Examples.Solmate.ERC4626.previewRedeem_refines` |
| `EvmLeanSpecs.Refinement.previewWithdraw_call` | `Examples.Solmate.ERC4626.previewWithdraw_call` |
| `EvmLeanSpecs.Refinement.previewWithdraw_refines` | `Examples.Solmate.ERC4626.previewWithdraw_refines` |
| `EvmLeanSpecs.Refinement.totalAssets_call` | `Examples.Solmate.ERC4626.totalAssets_call` |
| `EvmLeanSpecs.Refinement.totalAssets_refines` | `Examples.Solmate.ERC4626.totalAssets_refines` |
| `EvmLeanSpecs.Refinement.view_call` | `Examples.Solmate.ERC4626.view_call` |

## `Examples.Solmate.ERC4626.Withdraw` (was `EvmLeanSpecs.Refinement.WithdrawRefines`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.out_call` | `Examples.Solmate.ERC4626.out_call` |
| `EvmLeanSpecs.Refinement.redeem_call` | `Examples.Solmate.ERC4626.redeem_call` |
| `EvmLeanSpecs.Refinement.redeem_refines` | `Examples.Solmate.ERC4626.redeem_refines` |
| `EvmLeanSpecs.Refinement.withdraw_call` | `Examples.Solmate.ERC4626.withdraw_call` |
| `EvmLeanSpecs.Refinement.withdraw_refines` | `Examples.Solmate.ERC4626.withdraw_refines` |

## `Examples.Solmate.ERC4626.WithdrawInternal` (was `EvmLeanSpecs.Refinement.WithdrawSteps`)

| Old name | New name |
|---|---|
| `EvmLeanSpecs.Refinement.Out.previewRedeem_of_refines` | `Examples.Solmate.ERC4626.Out.previewRedeem_of_refines` |
| `EvmLeanSpecs.Refinement.Out.previewWithdraw_of_refines` | `Examples.Solmate.ERC4626.Out.previewWithdraw_of_refines` |
| `EvmLeanSpecs.Refinement.Out.redeemWorld?_refines` | `Examples.Solmate.ERC4626.Out.redeemWorld?_refines` |
| `EvmLeanSpecs.Refinement.Out.tail_refines` | `Examples.Solmate.ERC4626.Out.tail_refines` |
| `EvmLeanSpecs.Refinement.Out.withdrawWorld?_refines` | `Examples.Solmate.ERC4626.Out.withdrawWorld?_refines` |

## Declarations that changed namespace beyond the prefix map

| Old name | New name |
|---|---|
| `EvmLean.Solidity.Examples.SolmateAssetTransfer.transferWorld` (and the abbreviation `EvmLean.Solidity.Erc20.transferWorld`) | `EvmLogic.Solidity.ERC20.transferWorld` |
| `EvmLean.Solidity.Examples.SolmateAssetTransfer.view_transferWorld` | `EvmLogic.Solidity.ERC20.view_transferWorld` |
| `EvmLean.Contracts.StorageType`, `StorageVar`, `slotOf?` | `EvmLogic.Solidity.StorageType`, `StorageVar`, `slotOf?` (module `EvmLogic.Solidity.Layout`) |
| `EvmLean.Contracts.ImmutableRef`, `writeList`, `patchWords` | `EvmLogic.Solidity.ImmutableRef`, `writeList`, `patchWords` (module `EvmLogic.Solidity.Immutables`) |
| `EvmLean.Contracts.selector?` | `EvmLogic.Solidity.selector?` (module `EvmLogic.Solidity.Abi`) |
| `EvmLean.Contracts.chainId`, `deployer` | `Examples.Deployment.chainId`, `deployer` |
| `EvmLean.Contracts.SolmateAsset.*`, `SolmateVault.*`, `solmateDomainSeparator` | `Examples.Solmate.Contracts.*` |
| `EvmLean.Contracts.OzAsset.*`, `OzVault.*` | `Examples.OpenZeppelin.Contracts.*` |
| `EvmLeanSpecs.Refinement.Shares.Rep`, `RepOn`, `rep_*` (Word-level ERC-20 states vs. `Token`) | `Defi.ERC20.Rep`, `RepOn`, `rep_*` |
| `EvmLeanSpecs.Refinement.Invariants.TokAgree`, `AgreeOn`, `UserOp`, `price_*` (model level) | `Defi.ERC4626.TokAgree`, `AgreeOn`, `UserOp`, `price_*` |
| `EvmLeanSpecs.Refinement.transferLog`, … (event logs) | `Defi.ERC4626.transferLog`, … |
| `EvmLeanSpecs.Vault.mulDiv*` and the round-trip lemmas | `Defi.Math.*` |
| `EvmLeanSpecs.Vault.Token`, `PermitToken` | `Defi.ERC20.Token`, `PermitToken` |
| `EvmLean.Program.GasMono.*`, `EvmLean.Program.AbsInt.*` | `EvmLogic.GasMono.*`, `EvmLogic.AbsInt.*` |
| `EvmLean.Solidity.Exec.*`, `EvmLean.Solidity.Patched.*` (tactic internals) | `EvmLogic.Tactic.SolStep.*`, `EvmLogic.Tactic.Patched.*` |

Lemmas about `EvmLean`'s own types and functions (`EvmLean.Interpreter.*`, `EvmLean.Memory.*`,
`EvmLean.Bytes.*`, `EvmLean.Word.*`, …) keep their namespaces so that dot notation works.

## Modules

| Old module | New module |
|---|---|
| `EvmLeanSpecs.Vault.Permit` | `Defi.ERC20.Permit` |
| `EvmLeanSpecs.Refinement.SharesModel` | `Defi.ERC20.Rep` |
| `EvmLeanSpecs.Vault.Token` | `Defi.ERC20.Token` |
| `EvmLeanSpecs.Refinement.InvariantsAgree` | `Defi.ERC4626.Agree` |
| `EvmLeanSpecs.Vault.Events` | `Defi.ERC4626.Events` |
| `EvmLeanSpecs.Vault.InflationAlgebra` | `Defi.ERC4626.Inflation` |
| `EvmLeanSpecs.Vault.Inflation` | `Defi.ERC4626.Inflation` |
| `EvmLeanSpecs.Refinement.EventsLog` | `Defi.ERC4626.Logs` |
| `EvmLeanSpecs.Refinement.EventsTactic` | `Defi.ERC4626.Logs` |
| `EvmLeanSpecs.Vault.MoreProps` | `Defi.ERC4626.MoreProps` |
| `EvmLeanSpecs.Vault.Oz` | `Defi.ERC4626.Oz` |
| `EvmLeanSpecs.Vault.OzProps` | `Defi.ERC4626.OzProps` |
| `EvmLeanSpecs.Refinement.InvariantsPrice` | `Defi.ERC4626.Price` |
| `EvmLeanSpecs.Vault.Solmate` | `Defi.ERC4626.Solmate` |
| `EvmLeanSpecs.Vault.SolmateEffects` | `Defi.ERC4626.Solmate` |
| `EvmLeanSpecs.Vault.SolmateProps` | `Defi.ERC4626.SolmateProps` |
| `EvmLeanSpecs.Vault.Witnesses` | `Defi.ERC4626.Witnesses` |
| `EvmLeanSpecs.Vault.Arith` | `Defi.Math.Arith` |
| `EvmLeanSpecs.Vault.RoundTripAlgebra` | `Defi.Math.Arith` |
| `EvmLeanSpecs.Refinement.Lift` | `Defi.Trace.Lift` |
| `EvmLeanProofs.Program.AbsInt.Check` | `EvmLogic.AbsInt.Check` |
| `EvmLeanProofs.Program.AbsInt.Code` | `EvmLogic.AbsInt.Code` |
| `EvmLeanProofs.Program.AbsInt.CodeRun` | `EvmLogic.AbsInt.Code` |
| `EvmLeanProofs.Program.AbsInt.Domain` | `EvmLogic.AbsInt.Domain` |
| `EvmLeanProofs.Program.AbsInt.Effect` | `EvmLogic.AbsInt.Effect` |
| `EvmLeanProofs.Program.AbsInt.Frame` | `EvmLogic.AbsInt.Frame` |
| `EvmLeanProofs.Bytes` | `EvmLogic.Bytes` |
| `EvmLeanProofs.Program.GasMono.Bump` | `EvmLogic.GasMono.Bump` |
| `EvmLeanProofs.Program.GasMono.CallStep` | `EvmLogic.GasMono.CallStep` |
| `EvmLeanProofs.Program.GasMono.CodeFails` | `EvmLogic.GasMono.CodeFails` |
| `EvmLeanProofs.Program.GasMono.CodeFailsTactic` | `EvmLogic.GasMono.CodeFails` |
| `EvmLeanProofs.Program.GasMono.CodeScan` | `EvmLogic.GasMono.CodeScan` |
| `EvmLeanProofs.Program.GasMono.CallsFedScan` | `EvmLogic.GasMono.CodeScan` |
| `EvmLeanProofs.Program.GasMono.Depth` | `EvmLogic.GasMono.Depth` |
| `EvmLeanProofs.Program.GasMono.Exit` | `EvmLogic.GasMono.Exit` |
| `EvmLeanProofs.Program.GasMono.Interface` | `EvmLogic.GasMono.Interface` |
| `EvmLeanProofs.Program.GasMono.LockstepDefs` | `EvmLogic.GasMono.Lockstep` |
| `EvmLeanProofs.Program.GasMono.Lockstep` | `EvmLogic.GasMono.Lockstep` |
| `EvmLeanProofs.Program.GasMono.LockstepTop` | `EvmLogic.GasMono.Lockstep` |
| `EvmLeanProofs.Program.GasMono.Pc` | `EvmLogic.GasMono.Pc` |
| `EvmLeanProofs.Program.Block` | `EvmLogic.Program.Block` |
| `EvmLeanProofs.Program.Call` | `EvmLogic.Program.Call` |
| `EvmLeanProofs.Program.OutExtraCall` | `EvmLogic.Program.Call` |
| `EvmLeanProofs.Program.InExtraCall` | `EvmLogic.Program.Call` |
| `EvmLeanProofs.Program.Code` | `EvmLogic.Program.Code` |
| `EvmLeanProofs.Decode` | `EvmLogic.Program.JumpDest` |
| `EvmLeanProofs.Program.JumpDest` | `EvmLogic.Program.JumpDest` |
| `EvmLeanProofs.Program.Logic` | `EvmLogic.Program.Logic` |
| `EvmLeanProofs.Program.NestedExtraFrame` | `EvmLogic.Program.Nested.Frame` |
| `EvmLeanProofs.Program.NestedExtraGas` | `EvmLogic.Program.Nested.Gas` |
| `EvmLeanProofs.Program.NestedExtraRun` | `EvmLogic.Program.Nested.Run` |
| `EvmLeanProofs.Program.NestedExtraStep` | `EvmLogic.Program.Nested.Step` |
| `EvmLeanProofs.Program.NestedExtraWp` | `EvmLogic.Program.Nested.Wp` |
| `EvmLeanProofs.Program.PrecompileCall` | `EvmLogic.Program.PrecompileCall` |
| `EvmLeanProofs.Program.PrecompileCallEcrecover` | `EvmLogic.Program.PrecompileCall` |
| `EvmLeanProofs.Program.Run` | `EvmLogic.Program.Run` |
| `EvmLeanProofs.Program.Summary` | `EvmLogic.Program.Summary` |
| `EvmLeanProofs.Program.ExtraLogic` | `EvmLogic.Program.Summary` |
| `EvmLeanProofs.Solidity.Abi` | `EvmLogic.Solidity.Abi` |
| `EvmLeanProofs.Solidity.Call` | `EvmLogic.Solidity.Call` |
| `EvmLeanProofs.Solidity.Dispatch` | `EvmLogic.Solidity.Dispatch` |
| `EvmLeanProofs.Solidity.SharesExtraCall` | `EvmLogic.Solidity.Dispatch` |
| `EvmLeanProofs.Solidity.Erc20` | `EvmLogic.Solidity.ERC20` |
| `EvmLeanProofs.Solidity.SharesExtraErc20` | `EvmLogic.Solidity.ERC20` |
| `EvmLeanProofs.Solidity.EventsExtra` | `EvmLogic.Solidity.Events` |
| `EvmLeanProofs.Contracts.Basic` | `EvmLogic.Solidity.Immutables` |
| `EvmLeanProofs.Solidity.SharesExtraPatch` | `EvmLogic.Solidity.Immutables` |
| `EvmLeanProofs.Solidity.JumpDest` | `EvmLogic.Solidity.JumpDest` |
| `EvmLeanProofs.Solidity.Keccak` | `EvmLogic.Solidity.Keccak` |
| `EvmLeanProofs.Solidity.Layout` | `EvmLogic.Solidity.Layout` |
| `EvmLeanProofs.Solidity.Memory` | `EvmLogic.Solidity.Memory` |
| `EvmLeanProofs.Solidity.ExtraMemory` | `EvmLogic.Solidity.Memory` |
| `EvmLeanProofs.Solidity.PermitExtraMemory` | `EvmLogic.Solidity.Memory` |
| `EvmLeanProofs.Solidity.SimpAttr` | `EvmLogic.Solidity.SimpAttr` |
| `EvmLeanProofs.Solidity.PermitExtraAttr` | `EvmLogic.Solidity.SimpAttr` |
| `EvmLeanProofs.Solidity.Steps` | `EvmLogic.Solidity.Steps` |
| `EvmLeanProofs.Solidity.StringsStep` | `EvmLogic.Solidity.Steps` |
| `EvmLeanProofs.Solidity.Strings` | `EvmLogic.Solidity.Strings` |
| `EvmLeanProofs.Solidity.StringsWord` | `EvmLogic.Solidity.Strings` |
| `EvmLeanProofs.Solidity.StringsEncoding` | `EvmLogic.Solidity.Strings` |
| `EvmLeanProofs.Solidity.Word` | `EvmLogic.Solidity.Word` |
| `EvmLeanProofs.Solidity.ExtraWord` | `EvmLogic.Solidity.Word` |
| `EvmLeanProofs.Solidity.InExtraWord` | `EvmLogic.Solidity.Word` |
| `EvmLeanProofs.Solidity.PermitExtraWord` | `EvmLogic.Solidity.Word` |
| `EvmLeanProofs.State` | `EvmLogic.State` |
| `EvmLeanProofs.StepArith` | `EvmLogic.Step.Arith` |
| `EvmLeanProofs.StepBasic` | `EvmLogic.Step.Basic` |
| `EvmLeanProofs.Call` | `EvmLogic.Step.Basic` |
| `EvmLeanProofs.StepEnv` | `EvmLogic.Step.Env` |
| `EvmLeanProofs.StepFlow` | `EvmLogic.Step.Flow` |
| `EvmLeanProofs.StepLog` | `EvmLogic.Step.Log` |
| `EvmLeanProofs.StepMemory` | `EvmLogic.Step.Memory` |
| `EvmLeanProofs.Program.Memory` | `EvmLogic.Step.Memory` |
| `EvmLeanProofs.StepPush` | `EvmLogic.Step.Push` |
| `EvmLeanProofs.StepStack` | `EvmLogic.Step.Stack` |
| `EvmLeanProofs.StepStorage` | `EvmLogic.Step.Storage` |
| `EvmLeanProofs.Tactic` | `EvmLogic.Tactic.EvmStep` |
| `EvmLeanProofs.KernelRfl` | `EvmLogic.Tactic.KernelRfl` |
| `EvmLeanProofs.Solidity.StringsTactic` | `EvmLogic.Tactic.Mcopy` |
| `EvmLeanProofs.Solidity.PermitExtraTactic` | `EvmLogic.Tactic.Mcopy` |
| `EvmLeanProofs.Solidity.SharesExtraTactic` | `EvmLogic.Tactic.Patched` |
| `EvmLeanProofs.Solidity.ExtraPatchedWP` | `EvmLogic.Tactic.Patched` |
| `EvmLeanProofs.Solidity.ExtraTactic` | `EvmLogic.Tactic.Patched` |
| `EvmLeanProofs.Solidity.Tactic` | `EvmLogic.Tactic.SolStep` |
| `EvmLeanProofs.Program.Tactic` | `EvmLogic.Tactic.WpStep` |
| `EvmLeanProofs.Program.ExtraTactic` | `EvmLogic.Tactic.WpStep` |
| `EvmLeanProofs.Word` | `EvmLogic.Word` |
| `EvmLeanTest.AbsInt` | `EvmTest.AbsInt` |
| `EvmLeanTest.AddressReal` | `EvmTest.AddressReal` |
| `EvmLeanTest.Blake2f` | `EvmTest.Blake2f` |
| `EvmLeanTest.Block` | `EvmTest.Block` |
| `EvmLeanTest.Bls12381Precompile` | `EvmTest.Bls12381Precompile` |
| `EvmLeanTest.Bn254` | `EvmTest.Bn254` |
| `EvmLeanTest.Delegation` | `EvmTest.Delegation` |
| `EvmLeanTest.Gas` | `EvmTest.Gas` |
| `EvmLeanTest.HashUtil` | `EvmTest.HashUtil` |
| `EvmLeanTest.Interpreter` | `EvmTest.Interpreter` |
| `EvmLeanTest.InterpreterCall` | `EvmTest.InterpreterCall` |
| `EvmLeanTest.InterpreterUtil` | `EvmTest.InterpreterUtil` |
| `EvmLeanTest.Keccak` | `EvmTest.Keccak` |
| `EvmLeanProofs.Basic` | `EvmTest.Kernel` |
| `EvmLeanTest.Kzg` | `EvmTest.Kzg` |
| `EvmLeanTest.P256` | `EvmTest.P256` |
| `EvmLeanTest.Precompile` | `EvmTest.Precompile` |
| `EvmLeanTest.PrecompileCall` | `EvmTest.PrecompileCall` |
| `EvmLeanTest.PrecompileHex` | `EvmTest.PrecompileHex` |
| `EvmLeanTest.PrecompileReal` | `EvmTest.PrecompileReal` |
| `EvmLeanTest.Ripemd160` | `EvmTest.Ripemd160` |
| `EvmLeanTest.Secp256k1` | `EvmTest.Secp256k1` |
| `EvmLeanTest.Sha256` | `EvmTest.Sha256` |
| `EvmLeanTest.Trie` | `EvmTest.Trie` |
| `EvmLeanTest.Tx` | `EvmTest.Tx` |
| `EvmLeanTest.TxIntegration` | `EvmTest.TxIntegration` |
| `EvmLeanTest.TxSupport` | `EvmTest.TxSupport` |
| `EvmLeanTest.Word` | `EvmTest.Word` |
| `EvmLeanProofs.Execution` | `Examples.Basic.AddStore` |
| `EvmLeanProofs.Solidity.StringsExamples` | `Examples.Basic.Mcopy` |
| `EvmLeanProofs.Program.Examples.Sum` | `Examples.Basic.Sum` |
| `EvmLeanProofs.Examples.Token` | `Examples.Basic.Token` |
| `EvmLeanProofs.Program.Examples.TwoContracts` | `Examples.Basic.TwoContracts` |
| `EvmLeanProofs.Program.Examples.VaultTotalSupply` | `Examples.Basic.VaultTotalSupply` |
| `Differential.Family` | `Examples.Differential.Family` |
| `Differential.Gen` | `Examples.Differential.Gen` |
| `Differential.Local` | `Examples.Differential.Local` |
| `Differential.Main` | `Examples.Differential.Main` |
| `Differential.Rpc` | `Examples.Differential.Rpc` |
| `EvmLeanProofs.Contracts.OzAsset` | `Examples.OpenZeppelin.Contracts.OzAsset` |
| `EvmLeanProofs.Contracts.OzVault` | `Examples.OpenZeppelin.Contracts.OzVault` |
| `EvmLeanProofs.Contracts.Deploy` | `Examples.Solmate.Contracts.Deploy` |
| `EvmLeanProofs.Contracts.SolmateAsset` | `Examples.Solmate.Contracts.SolmateAsset` |
| `EvmLeanProofs.Contracts.SolmateVault` | `Examples.Solmate.Contracts.SolmateVault` |
| `EvmLeanSpecs.Refinement.AssetApprove` | `Examples.Solmate.ERC20.Approve` |
| `EvmLeanSpecs.Refinement.AssetBalanceOf` | `Examples.Solmate.ERC20.BalanceOf` |
| `EvmLeanSpecs.Refinement.EventsAssetTransfer` | `Examples.Solmate.ERC20.Events` |
| `EvmLeanSpecs.Refinement.EventsAssetTransferFrom` | `Examples.Solmate.ERC20.Events` |
| `EvmLeanSpecs.Refinement.EventsAssetMint` | `Examples.Solmate.ERC20.Events` |
| `EvmLeanSpecs.Refinement.EventsAsset` | `Examples.Solmate.ERC20.Events` |
| `EvmLeanSpecs.Refinement.MalformedAsset` | `Examples.Solmate.ERC20.Malformed` |
| `EvmLeanSpecs.Refinement.AssetMint` | `Examples.Solmate.ERC20.MintBurn` |
| `EvmLeanSpecs.Refinement.AssetBurn` | `Examples.Solmate.ERC20.MintBurn` |
| `EvmLeanSpecs.Refinement.PermitDefs` | `Examples.Solmate.ERC20.Permit` |
| `EvmLeanSpecs.Refinement.PermitAssetDS` | `Examples.Solmate.ERC20.Permit` |
| `EvmLeanSpecs.Refinement.PermitAssetTail` | `Examples.Solmate.ERC20.Permit` |
| `EvmLeanSpecs.Refinement.PermitAssetBody` | `Examples.Solmate.ERC20.Permit` |
| `EvmLeanSpecs.Refinement.PermitAsset` | `Examples.Solmate.ERC20.Permit` |
| `EvmLeanSpecs.Refinement.AssetSpec` | `Examples.Solmate.ERC20.Spec` |
| `EvmLeanSpecs.Refinement.StringsAsset` | `Examples.Solmate.ERC20.Strings` |
| `EvmLeanSpecs.Refinement.StringsAssetLong` | `Examples.Solmate.ERC20.Strings` |
| `EvmLeanSpecs.Refinement.StringsAssetSpec` | `Examples.Solmate.ERC20.Strings` |
| `EvmLeanSpecs.Refinement.StringsCanonical` | `Examples.Solmate.ERC20.Strings` |
| `EvmLeanProofs.Solidity.Examples.SolmateAssetTransfer` | `Examples.Solmate.ERC20.Transfer` |
| `EvmLeanProofs.Solidity.Examples.SolmateAssetTransferSpec` | `Examples.Solmate.ERC20.Transfer` |
| `EvmLeanSpecs.Refinement.AssetTransfer` | `Examples.Solmate.ERC20.Transfer` |
| `EvmLeanSpecs.Refinement.AssetTransferFrom` | `Examples.Solmate.ERC20.TransferFrom` |
| `EvmLeanSpecs.Bridge` | `Examples.Solmate.ERC4626.Abstraction` |
| `EvmLeanSpecs.Refinement.Abstraction` | `Examples.Solmate.ERC4626.Abstraction` |
| `EvmLeanSpecs.Refinement.VaultTotalAssets` | `Examples.Solmate.ERC4626.Convert` |
| `EvmLeanSpecs.Refinement.VaultConvert` | `Examples.Solmate.ERC4626.Convert` |
| `EvmLeanSpecs.Refinement.AssetCallOutGas` | `Examples.Solmate.ERC4626.ConvertGas` |
| `EvmLeanSpecs.Refinement.DepositConvert` | `Examples.Solmate.ERC4626.ConvertGas` |
| `EvmLeanSpecs.Refinement.DepositInternal` | `Examples.Solmate.ERC4626.Deposit` |
| `EvmLeanSpecs.Refinement.DepositModel` | `Examples.Solmate.ERC4626.Deposit` |
| `EvmLeanSpecs.Refinement.Deposit` | `Examples.Solmate.ERC4626.Deposit` |
| `EvmLeanSpecs.Refinement.Mint` | `Examples.Solmate.ERC4626.Deposit` |
| `EvmLeanSpecs.Refinement.DepositCall` | `Examples.Solmate.ERC4626.Deposit` |
| `EvmLeanSpecs.Refinement.Events` | `Examples.Solmate.ERC4626.Events` |
| `EvmLeanSpecs.Refinement.EventsConvert` | `Examples.Solmate.ERC4626.EventsConvert` |
| `EvmLeanSpecs.Refinement.EventsDeposit` | `Examples.Solmate.ERC4626.EventsEntry` |
| `EvmLeanSpecs.Refinement.EventsMint` | `Examples.Solmate.ERC4626.EventsEntry` |
| `EvmLeanSpecs.Refinement.EventsWithdraw` | `Examples.Solmate.ERC4626.EventsEntry` |
| `EvmLeanSpecs.Refinement.EventsRedeem` | `Examples.Solmate.ERC4626.EventsEntry` |
| `EvmLeanSpecs.Refinement.EventsEntry` | `Examples.Solmate.ERC4626.EventsEntry` |
| `EvmLeanSpecs.Refinement.EventsDepositInternal` | `Examples.Solmate.ERC4626.EventsInternal` |
| `EvmLeanSpecs.Refinement.EventsWithdrawInternal` | `Examples.Solmate.ERC4626.EventsInternal` |
| `EvmLeanSpecs.Refinement.EventsShares` | `Examples.Solmate.ERC4626.EventsShares` |
| `EvmLeanSpecs.Refinement.EventsSharesCode` | `Examples.Solmate.ERC4626.EventsSharesCode` |
| `EvmLeanSpecs.Refinement.Invariants` | `Examples.Solmate.ERC4626.Invariants.Deployed` |
| `EvmLeanSpecs.Refinement.InvariantsWithdrawRedeem` | `Examples.Solmate.ERC4626.Invariants.Deployed` |
| `EvmLeanSpecs.Refinement.InvariantsDepositMint` | `Examples.Solmate.ERC4626.Invariants.Deployed` |
| `EvmLeanSpecs.Refinement.InvariantsFinal` | `Examples.Solmate.ERC4626.Invariants.Deployed` |
| `EvmLeanSpecs.Refinement.EventsTrace` | `Examples.Solmate.ERC4626.Invariants.Events` |
| `EvmLeanSpecs.Refinement.InvariantsSystem` | `Examples.Solmate.ERC4626.Invariants.System` |
| `EvmLeanSpecs.Refinement.InvariantsCalls` | `Examples.Solmate.ERC4626.Invariants.System` |
| `EvmLeanSpecs.Refinement.AssetApproveCall` | `Examples.Solmate.ERC4626.Invariants.System` |
| `EvmLeanSpecs.Refinement.AssetMintCall` | `Examples.Solmate.ERC4626.Invariants.System` |
| `EvmLeanSpecs.Refinement.AssetBurnCall` | `Examples.Solmate.ERC4626.Invariants.System` |
| `EvmLeanSpecs.Refinement.LowGasHeadline` | `Examples.Solmate.ERC4626.LowGas.AnyGas` |
| `EvmLeanSpecs.Refinement.LowGas` | `Examples.Solmate.ERC4626.LowGas.Code` |
| `EvmLeanSpecs.Refinement.LowGasMono` | `Examples.Solmate.ERC4626.LowGas.Code` |
| `EvmLeanSpecs.Refinement.LowGasFrames` | `Examples.Solmate.ERC4626.LowGas.Frames` |
| `EvmLeanSpecs.Refinement.LowGasTargets` | `Examples.Solmate.ERC4626.LowGas.Targets` |
| `EvmLeanSpecs.Refinement.MalformedVaultA` | `Examples.Solmate.ERC4626.Malformed` |
| `EvmLeanSpecs.Refinement.MalformedVaultB` | `Examples.Solmate.ERC4626.Malformed` |
| `EvmLeanSpecs.Refinement.MalformedCalldata` | `Examples.Solmate.ERC4626.Malformed` |
| `EvmLeanSpecs.Refinement.MulDiv` | `Examples.Solmate.ERC4626.MulDiv` |
| `EvmLeanSpecs.Refinement.NestedCalls` | `Examples.Solmate.ERC4626.Nested.Calls` |
| `EvmLeanSpecs.Refinement.NestedCoverage` | `Examples.Solmate.ERC4626.Nested.Coverage` |
| `EvmLeanSpecs.Refinement.NestedInvariants` | `Examples.Solmate.ERC4626.Nested.Invariants` |
| `EvmLeanSpecs.Refinement.NestedPermit` | `Examples.Solmate.ERC4626.Nested.Permit` |
| `EvmLeanSpecs.Refinement.NestedSystem` | `Examples.Solmate.ERC4626.Nested.System` |
| `EvmLeanSpecs.Refinement.NestedViews` | `Examples.Solmate.ERC4626.Nested.Views` |
| `EvmLeanSpecs.Refinement.PermitVaultDS` | `Examples.Solmate.ERC4626.Permit` |
| `EvmLeanSpecs.Refinement.PermitVaultTail` | `Examples.Solmate.ERC4626.Permit` |
| `EvmLeanSpecs.Refinement.PermitVaultBody` | `Examples.Solmate.ERC4626.Permit` |
| `EvmLeanSpecs.Refinement.PermitVault` | `Examples.Solmate.ERC4626.Permit` |
| `EvmLeanSpecs.Refinement.PermitCall` | `Examples.Solmate.ERC4626.PermitSpec` |
| `EvmLeanSpecs.Refinement.PermitSpec` | `Examples.Solmate.ERC4626.PermitSpec` |
| `EvmLeanSpecs.Refinement.PermitEvents` | `Examples.Solmate.ERC4626.PermitSpec` |
| `EvmLeanSpecs.Refinement.AssetCallOut` | `Examples.Solmate.ERC4626.SafeTransfer` |
| `EvmLeanSpecs.Refinement.AssetCallIn` | `Examples.Solmate.ERC4626.SafeTransferFrom` |
| `EvmLeanSpecs.Refinement.Shares` | `Examples.Solmate.ERC4626.Shares` |
| `EvmLeanSpecs.Refinement.SharesCode` | `Examples.Solmate.ERC4626.SharesCode` |
| `EvmLeanSpecs.Refinement.SharesTransfer` | `Examples.Solmate.ERC4626.SharesCode` |
| `EvmLeanSpecs.Refinement.SharesApprove` | `Examples.Solmate.ERC4626.SharesCode` |
| `EvmLeanSpecs.Refinement.SharesTransferFrom` | `Examples.Solmate.ERC4626.SharesCode` |
| `EvmLeanSpecs.Refinement.SharesTransferFromRevert` | `Examples.Solmate.ERC4626.SharesCode` |
| `EvmLeanSpecs.Refinement.SharesViews` | `Examples.Solmate.ERC4626.SharesCode` |
| `EvmLeanSpecs.Refinement.SharesFrame` | `Examples.Solmate.ERC4626.SharesFrame` |
| `EvmLeanSpecs.Refinement.SharesFrameSpec` | `Examples.Solmate.ERC4626.SharesFrame` |
| `EvmLeanSpecs.Refinement.SharesFrameViews` | `Examples.Solmate.ERC4626.SharesFrame` |
| `EvmLeanSpecs.Refinement.StringsVault` | `Examples.Solmate.ERC4626.Strings` |
| `EvmLeanSpecs.Refinement.StringsVaultLong` | `Examples.Solmate.ERC4626.Strings` |
| `EvmLeanSpecs.Refinement.StringsVaultSpec` | `Examples.Solmate.ERC4626.Strings` |
| `EvmLeanSpecs.Refinement.UnknownSelectors` | `Examples.Solmate.ERC4626.UnknownSelectors` |
| `EvmLeanSpecs.Refinement.MalformedDefs` | `Examples.Solmate.ERC4626.UnknownSelectors` |
| `EvmLeanSpecs.Refinement.VaultViews` | `Examples.Solmate.ERC4626.Views` |
| `EvmLeanSpecs.Refinement.VaultViewsMax` | `Examples.Solmate.ERC4626.Views` |
| `EvmLeanSpecs.Refinement.VaultViewsSpec` | `Examples.Solmate.ERC4626.ViewsSpec` |
| `EvmLeanSpecs.Refinement.ViewsRest` | `Examples.Solmate.ERC4626.ViewsSpec` |
| `EvmLeanSpecs.Refinement.Withdraw` | `Examples.Solmate.ERC4626.Withdraw` |
| `EvmLeanSpecs.Refinement.Redeem` | `Examples.Solmate.ERC4626.Withdraw` |
| `EvmLeanSpecs.Refinement.WithdrawRefines` | `Examples.Solmate.ERC4626.Withdraw` |
| `EvmLeanSpecs.Refinement.WithdrawSteps` | `Examples.Solmate.ERC4626.WithdrawInternal` |
| `EvmLeanSpecs.Refinement.WithdrawCode` | `Examples.Solmate.ERC4626.WithdrawInternal` |
| `EvmLeanSpecs.Refinement.WithdrawSpend` | `Examples.Solmate.ERC4626.WithdrawInternal` |
| `EvmLeanTest.Contracts` | `Examples.Tests.Contracts` |
| `EvmLeanTest.Solidity` | `Examples.Tests.Solidity` |
| `EvmLeanTest.Strings` | `Examples.Tests.Strings` |
