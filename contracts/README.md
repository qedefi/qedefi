# ERC-4626 verification targets

Pinned Solidity sources, a reproducible build, and the compiled artifacts used by the Lean
proofs (`defi/Examples/Solmate/`), the generated contract modules
(`defi/Examples/{Solmate,OpenZeppelin}/Contracts/`) and the differential tester
(`lake exe difftest`). The verification itself is described in
[docs/erc4626](../docs/erc4626/README.md).

| Target | Asset | Vault |
|---|---|---|
| Solmate | `MockERC20` | `MockERC4626` (`totalAssets = asset.balanceOf(this)`; deposit/withdraw hooks count calls) |
| OpenZeppelin | `ERC20Mock` | `OzVault` (`src/OzVault.sol`: stock `ERC4626`, nothing overridden, `_decimalsOffset() = 0`) |

`src/Targets.sol` is the compilation root.

## Pinned versions

| Component | Version |
|---|---|
| solc | `0.8.28+commit.7893614a` (svm layout, `~/.svm/0.8.28/solc-0.8.28`) |
| Foundry (`forge`, `anvil`, `cast`) | 1.8.5 (`51a52c59`), build tool and reference EVM (revm) |
| Solmate | `transmissions11/solmate` @ [`89365b88`](https://github.com/transmissions11/solmate/tree/89365b880c4f3c786bdd453d4b8e8fe410344a69) (2025-07-21) |
| OpenZeppelin Contracts | `v5.7.0` @ [`cab19933`](https://github.com/OpenZeppelin/openzeppelin-contracts/tree/v5.7.0) |
| forge-std (a16z suite only, not vendored) | `v1.17.0` @ `f3dae6e6` |
| a16z erc4626-tests (not vendored) | `a16z/erc4626-tests` @ `ac485460` (2025-07-29) |

Vendored files in `lib/` are byte-for-byte copies at their upstream paths, licence headers
and `LICENSE` files kept (Solmate AGPL-3.0-only, OpenZeppelin MIT): Solmate's `ERC20`,
`ERC4626`, `FixedPointMathLib`, `SafeTransferLib`, `MockERC20`, `MockERC4626`; the import
closure of OpenZeppelin's `ERC4626` and `ERC20Mock`.

## Build

`foundry.toml`: solc 0.8.28, optimizer on, 200 runs, `evm_version = cancun`, no via-IR,
`bytecode_hash = "none"`, `cbor_metadata = false` (the bytecode depends only on sources and
settings).

```bash
scripts/build-contracts.sh           # rebuild artifacts/ and the generated Lean modules
scripts/build-contracts.sh --check   # also fail if any committed file changed
```

The script compiles with `forge build` and writes, per contract, `artifacts/<Name>/`:
`creation.hex`, `constructorArgs.hex`, `runtime.template.hex` (immutables zeroed),
`runtime.hex` (as deployed), `abi.json`, `methodIdentifiers.json`, `events.json`,
`errors.json`, `storageLayout.json`, `immutableReferences.json`; and
`artifacts/deployment.json`. It deploys everything on a local anvil, checks that the deployed
code equals the template outside the immutable positions, and generates the Lean modules.

| Contract | Runtime | Creation |
|---|---|---|
| `SolmateAsset` (`MockERC20`) | 2,870 B | 3,885 B |
| `SolmateVault` (`MockERC4626`) | 5,248 B | 6,474 B |
| `OzAsset` (`ERC20Mock`) | 1,900 B | 2,366 B |
| `OzVault` | 4,408 B | 5,098 B |

## Canonical deployment

Each family is deployed on its own fresh chain (chain id 1, Cancun) by
`0x1000000000000000000000000000000000000000`: asset at nonce 0, vault at nonce 1.

| | Address | Constructor arguments |
|---|---|---|
| asset | `0x13136008B64FF592819B2FA6d43F2835C452020e` | Solmate `("Solmate Asset", "SAST", 18)`; OZ none (`"ERC20Mock"`, `"E20M"`, 18 decimals) |
| vault | `0x7c5a2c91b22d7A9226523D4Ba717DB6afB741ebd` | Solmate `(asset, "Solmate Vault", "svSAST")`; OZ `(asset)` (`"OZ Vault"`, `"ozVLT"`) |

## Immutables

solc compiles each `immutable` into 32-byte `PUSH32` placeholders filled in by the
constructor. Byte offsets of the values in the runtime code:

| Contract | Immutable | Offsets | Canonical value |
|---|---|---|---|
| SolmateAsset | `decimals` | 345 | 18 |
| | `INITIAL_CHAIN_ID` | 1063 | 1 |
| | `INITIAL_DOMAIN_SEPARATOR` | 1116 | EIP-712 separator (name, chain id, own address) |
| SolmateVault | `decimals` | 623 | 18 (`asset.decimals()`) |
| | `asset` | 688, 1170, 2014, 2169, 2668, 2995 | asset address |
| | `INITIAL_CHAIN_ID` | 1831 | 1 |
| | `INITIAL_DOMAIN_SEPARATOR` | 1879 | `0xfc86b75f…85216` |
| OzVault | `_asset` | 556, 896, 2772, 2924 | asset address |
| | `_underlyingDecimals` | 1276 | 18 (`asset.decimals()`) |

The runtime code of other deployments is obtained either by running the creation code
(`creationCode ++ constructorArgs`; `difftest` does this in evm-lean and anvil) or by
patching by position: `runtimeCodeWith (i : Immutables)`, with `runtimeCodeFor` computing the
immutables from deployment parameters (including Solmate's domain separator,
`solmateDomainSeparator`). `runtimeCodeWith_deployment : runtimeCodeWith deployment =
runtimeCode` is kernel-checked; `difftest` checks `runtimeCodeFor` against a deployment by a
second deployer.

## Lean API

Namespaces `Examples.Solmate.Contracts.{SolmateAsset, SolmateVault}` and
`Examples.OpenZeppelin.Contracts.{OzAsset, OzVault}`, each with `creationCode`,
`constructorArgs`, `runtimeCode` (a literal `ByteArray` that reduces in the kernel),
`address`, `size_runtimeCode`/`size_creationCode`, `selectors`, `events` (topic 0), `errors`,
`storageLayout`, `immutableRefs` and, with immutables, `Immutables`, `deployment`,
`runtimeCodeWith`. Shared: `Examples.Deployment.chainId`, `deployer`;
`EvmLogic.Solidity.slotOf?`, `selector?`, `patchWords`, `eq_of_data_toList_eq` (compare code
in the kernel via `.data.toList`: `ByteArray`'s `DecidableEq` does not reduce well).

Storage slots: Solmate `name 0, symbol 1, totalSupply 2, balanceOf 3, allowance 4, nonces 5`
(vault also `beforeWithdrawHookCalledCounter 6, afterDepositHookCalledCounter 7`);
OpenZeppelin `_balances 0, _allowances 1, _totalSupply 2, _name 3, _symbol 4`. Mappings:
`m[k]` at `keccak(k ‖ slot)`, `allowance[o][s]` at `keccak(s ‖ keccak(o ‖ slot))`.

## Differential testing

`lake exe difftest [--seed N] [--sequences N] [--length N] [--family solmate|oz|all]`
(`defi/Examples/Differential/Main.lean`, run from `defi/`, needs anvil) deploys both families
through their creation code in evm-lean (`processMessageCall`, `Crypto.real`, Cancun) and in
anvil, then runs random call sequences from four actors: asset mint/burn/approve/transfer/
transferFrom, donations, vault deposit/mint/withdraw/redeem with third-party owners, share
transfers and approvals, Solmate `permit` with invalid signatures, every view, random
selectors, malformed calldata; amounts include 0, 1, `2²⁵⁶−1` and near-overflow values.
After every call it compares status, return/revert data, logs, receipt `gasUsed` and every
storage slot either side touched, and shrinks mismatches to a minimal sequence.
`--inject-bug` corrupts evm-lean's `deposit` to self-test the comparison.

A fixed first-depositor scenario runs first (alice deposits 1 wei, donates 10¹⁸, bob
deposits 2·10¹⁸ − 1, alice redeems): both sides agree; on Solmate alice ends with
1.5·10¹⁸ (bob holds 1 share), on OpenZeppelin with 0.6·10¹⁸ (bob holds 3 shares).

Result of `lake exe difftest --seed 2026 --sequences 200 --length 50`: **20,008
transactions** (11,400 successful on both sides), **0 mismatches**, for both families;
deployments from both deployers agree on code, storage and gas (651 s, dominated by JSON-RPC
round trips).

## a16z ERC-4626 property suite

`contracts/run-a16z.sh` fetches the pinned forge-std and erc4626-tests into `ext/` and runs
`a16z/ERC4626Std.t.sol` (profile `a16z`, 1,000 fuzz runs, seed `0x4626`) against both
targets (it tests the contracts, not evm-lean):

| Target | Result |
|---|---|
| Solmate (`_vaultMayBeEmpty = false`, `_unlimitedAmount = false`) | 25 / 26; **`test_maxWithdraw` fails** |
| OpenZeppelin (`_vaultMayBeEmpty = true`, `_unlimitedAmount = true`) | 26 / 26 |

The Solmate failure is a genuine deviation from EIP-4626 ("`maxWithdraw` MUST NOT revert"):
`maxWithdraw(owner) = convertToAssets(balanceOf[owner])`, and `mulDivDown` reverts when
`shares · totalAssets ≥ 2²⁵⁶` (e.g. an owner with ~4.3·10⁶⁵ shares). `convertToAssets`,
`previewRedeem`, `convertToShares`, `previewDeposit` and the corresponding `deposit`/`redeem`
paths revert the same way; the model makes these operations partial accordingly
(`Defi.ERC4626.Solmate.maxWithdraw_reverts_of_overflow`).
