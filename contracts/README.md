# ERC-4626 verification targets

Pinned Solidity sources, a reproducible build, and the compiled artifacts that the Lean
proofs (`EvmLeanProofs/Contracts/`) and the differential tester (`lake exe difftest`) use.
See `docs/erc4626-plan.md` for the overall plan.

| Target | Asset | Vault |
|---|---|---|
| Solmate | `MockERC20` | `MockERC4626` (`totalAssets = asset.balanceOf(this)`, deposit/withdraw hooks count calls) |
| OpenZeppelin | `ERC20Mock` | `OzVault` (`src/OzVault.sol`: stock `ERC4626`, nothing overridden, `_decimalsOffset() = 0`) |

## Pinned versions

| Component | Version |
|---|---|
| solc | `0.8.28+commit.7893614a` (svm layout, `~/.svm/0.8.28/solc-0.8.28`) |
| Foundry (`forge`, `anvil`, `cast`) | 1.8.5 (`51a52c59cffd940f76eddd0b4bb1791aa4b5ac7f`), used to build and as the reference EVM (revm) |
| Solmate | `transmissions11/solmate` @ [`89365b880c4f3c786bdd453d4b8e8fe410344a69`](https://github.com/transmissions11/solmate/tree/89365b880c4f3c786bdd453d4b8e8fe410344a69) (2025-07-21, `main`) |
| OpenZeppelin Contracts | `v5.7.0` @ [`cab19933c33c2ad1d4c7a84864a3601dddfd16f3`](https://github.com/OpenZeppelin/openzeppelin-contracts/tree/v5.7.0) |
| forge-std (a16z suite only, not vendored) | `v1.17.0` @ `f3dae6e6ee381f25eb6a246f7da9b85c91a68219` |
| a16z erc4626-tests (not vendored) | `a16z/erc4626-tests` @ `ac485460e014f22807c1ff687e0b4dc3af96ee40` (2025-07-29) |

Vendored files are byte-for-byte copies (license headers kept; `LICENSE` files copied:
Solmate is AGPL-3.0-only, OpenZeppelin MIT), at the upstream paths:

- `lib/solmate/` ← `https://github.com/transmissions11/solmate/blob/89365b88…/`
  `src/tokens/ERC20.sol`, `src/tokens/ERC4626.sol`, `src/utils/FixedPointMathLib.sol`,
  `src/utils/SafeTransferLib.sol`, `src/test/utils/mocks/MockERC20.sol`,
  `src/test/utils/mocks/MockERC4626.sol`, `LICENSE`.
- `lib/openzeppelin-contracts/` ← `https://github.com/OpenZeppelin/openzeppelin-contracts/blob/v5.7.0/`
  `contracts/token/ERC20/{ERC20,IERC20}.sol`, `contracts/token/ERC20/extensions/{ERC4626,IERC20Metadata}.sol`,
  `contracts/token/ERC20/utils/SafeERC20.sol`, `contracts/mocks/token/ERC20Mock.sol`,
  `contracts/interfaces/{IERC20,IERC20Metadata,IERC4626,IERC165,IERC1363,draft-IERC6093}.sol`,
  `contracts/utils/{Context,Panic}.sol`, `contracts/utils/introspection/IERC165.sol`,
  `contracts/utils/math/{Math,SafeCast}.sol`, `LICENSE` (the import closure of `ERC4626` and `ERC20Mock`).

## Build

`foundry.toml`: solc 0.8.28, optimizer on, 200 runs, `evm_version = cancun`, no via-IR,
`bytecode_hash = "none"`, `cbor_metadata = false` (no metadata trailer: the bytecode depends
only on the sources and settings).

```bash
scripts/build-contracts.sh           # rebuild artifacts/ and EvmLeanProofs/Contracts/*.lean
scripts/build-contracts.sh --check   # also fail if the committed files changed
```

The script compiles with `forge build`, extracts per contract (in `artifacts/<Name>/`):
`creation.hex` (init code), `constructorArgs.hex`, `runtime.template.hex` (solc's runtime
code, immutables zeroed), `runtime.hex` (code as deployed), `abi.json`,
`methodIdentifiers.json`, `events.json`, `errors.json`, `storageLayout.json`
(`forge inspect … storageLayout`) and `immutableReferences.json` (names, offsets and deployed
values); `artifacts/deployment.json` records the deployment. It then deploys everything on a
local anvil, checks that the deployed code equals the template except at the immutable
positions, and generates the Lean modules.

| Contract | Runtime | Creation |
|---|---|---|
| `SolmateAsset` (`MockERC20`) | 2,870 B | 3,885 B |
| `SolmateVault` (`MockERC4626`) | 5,248 B | 6,474 B |
| `OzAsset` (`ERC20Mock`) | 1,900 B | 2,366 B |
| `OzVault` | 4,408 B | 5,098 B |

## Canonical deployment

Each family is deployed on its own fresh chain (chain id **1**, Cancun) by the deployer
`0x1000000000000000000000000000000000000000`: asset at nonce 0, vault at nonce 1.

| | Address | Constructor arguments |
|---|---|---|
| asset | `0x13136008B64FF592819B2FA6d43F2835C452020e` | Solmate: `("Solmate Asset", "SAST", 18)`; OZ: none (`"ERC20Mock"`, `"E20M"`, 18 decimals) |
| vault | `0x7c5a2c91b22d7A9226523D4Ba717DB6afB741ebd` | Solmate: `(asset, "Solmate Vault", "svSAST")`; OZ: `(asset)` (`"OZ Vault"`, `"ozVLT"`) |

## Immutables

solc compiles each `immutable` into 32-byte `PUSH32` placeholders in the runtime code, which
the constructor fills in. Offsets (byte index of the 32-byte value in the runtime code):

| Contract | Immutable | Offsets | Canonical value |
|---|---|---|---|
| SolmateAsset | `decimals` | 345 | 18 |
| | `INITIAL_CHAIN_ID` | 1063 | 1 |
| | `INITIAL_DOMAIN_SEPARATOR` | 1116 | EIP-712 separator (name, chain id, own address) |
| SolmateVault | `decimals` | 623 | 18 (`asset.decimals()`) |
| | `asset` | 688, 1170, 2014, 2169, 2668, 2995 | asset address |
| | `INITIAL_CHAIN_ID` | 1831 | 1 |
| | `INITIAL_DOMAIN_SEPARATOR` | 1879 | `0xfc86b75f…85216` |
| OzAsset | — | | |
| OzVault | `_asset` | 556, 896, 2772, 2924 | asset address |
| | `_underlyingDecimals` | 1276 | 18 (`asset.decimals()`) |

Two ways to obtain the runtime code of a deployment:

1. **Deploy through the creation code** (preferred in tests): run `creationCode ++
   constructorArgs` as a creation message; `lake exe difftest` does this in evm-lean and in
   anvil and checks the result.
2. **Patch by position**: `runtimeCodeWith (i : Immutables)` in each generated module
   overwrites the placeholders; `Contracts.Deploy` computes the immutables from deployment
   parameters (`SolmateVault.runtimeCodeFor keccak chainId asset self`,
   `OzVault.runtimeCodeFor asset`, …, including Solmate's domain separator). The theorem
   `runtimeCodeWith_deployment : runtimeCodeWith deployment = runtimeCode` is checked by the
   kernel; `difftest` checks `runtimeCodeFor` against a deployment by a second deployer.

## Lean API (`EvmLeanProofs/Contracts/`)

Namespaces `EvmLean.Contracts.{SolmateAsset, SolmateVault, OzAsset, OzVault}`, each with
`creationCode`, `constructorArgs`, `runtimeCode : ByteArray` (canonical, literal
`⟨⟨b₀ :: b₁ :: … :: []⟩⟩`, elaborates in ~1 s and reduces in the kernel), `address`,
`size_runtimeCode`/`size_creationCode` (kernel-checked), `selectors : List (String ×
UInt32)`, `events : List (String × Word)` (topic 0), `errors`, `storageLayout : List
StorageVar`, `immutableRefs`, and, with immutables, `Immutables`, `deployment`,
`runtimeCodeWith`. Shared: `Contracts.chainId`, `Contracts.deployer`, `slotOf?`,
`selector?`, `patchWords`, `eq_of_data_toList_eq` (`Contracts.Basic`). Note: compare code in
the kernel via `.data.toList` (`ByteArray`'s `DecidableEq` does not reduce well).

Storage slots: Solmate `name 0, symbol 1, totalSupply 2, balanceOf 3, allowance 4, nonces 5`
(+ vault `beforeWithdrawHookCalledCounter 6, afterDepositHookCalledCounter 7`); OpenZeppelin
`_balances 0, _allowances 1, _totalSupply 2, _name 3, _symbol 4`. Mappings: `m[k]` at
`keccak(k ‖ slot)`, `allowance[o][s]` at `keccak(s ‖ keccak(o ‖ slot))`.

## Differential testing (`lake exe difftest`)

See `Differential/Main.lean`. Deploys both families through their creation code in evm-lean
(`Interpreter.processMessageCall`, `Crypto.real`, Cancun) and in anvil, then runs random call
sequences from four actors (asset mint/burn/approve/transfer/transferFrom, donations, vault
deposit/mint/withdraw/redeem with third-party owners, share transfers/approvals, Solmate
`permit` with invalid signatures, every view, random calls of any selector, malformed
calldata; amounts include 0, 1, `2²⁵⁶-1` and other near-overflow values, balances ± 1). After
every call it compares status, return/revert data, logs, receipt `gasUsed` and the storage
slots either side touched. Mismatches are shrunk to a minimal sequence. `--inject-bug`
corrupts evm-lean's `deposit` to self-test the comparison (detected and shrunk to 3 calls).

Before the random sequences, a fixed first-depositor inflation-attack scenario runs on both
sides (alice deposits 1 wei, donates 10¹⁸, bob deposits 2·10¹⁸ − 1, alice redeems): both
agree; on Solmate alice ends with 1.5·10¹⁸ (profit ≈ 0.5·10¹⁸, bob holds 1 share), on
OpenZeppelin with 0.6·10¹⁸ (loss ≈ 0.4·10¹⁸, bob holds 3 shares).

Result (`lake exe difftest --seed 2026 --sequences 200 --length 50`, 2026-10-19): **20,008
transactions** (11,400 successful on both sides), **0 mismatches** in status, return data,
logs, `gasUsed` or storage, for both families; deployments from both deployers agree on code,
storage and gas. 651 s (~33 ms per transaction, dominated by the JSON-RPC round trips).

## a16z ERC-4626 property suite

`contracts/run-a16z.sh` fetches the pinned forge-std and erc4626-tests into `ext/` and runs
`a16z/ERC4626Std.t.sol` (profile `a16z`, 1,000 fuzz runs, seed `0x4626`) against both targets.
It checks the targets, not evm-lean.

| Target | Result |
|---|---|
| Solmate `MockERC4626` (`_vaultMayBeEmpty = false`, `_unlimitedAmount = false`, `_delta_ = 0`) | 25 / 26 pass; **`test_maxWithdraw` fails** |
| OpenZeppelin `OzVault` (`_vaultMayBeEmpty = true`, `_unlimitedAmount = true`, `_delta_ = 0`) | 26 / 26 pass |

The Solmate failure is a genuine deviation from EIP-4626 ("`maxWithdraw` MUST NOT revert"):
`maxWithdraw(owner) = convertToAssets(balanceOf[owner]) = shares.mulDivDown(totalAssets,
totalSupply)`, and `FixedPointMathLib.mulDivDown` reverts when `shares · totalAssets ≥ 2²⁵⁶`
(counterexample: an owner with ~4.3·10⁶⁵ shares). `convertToAssets`, `previewRedeem`,
`convertToShares`, `previewDeposit` (and the corresponding `deposit`/`redeem` paths) revert
the same way on overflowing products. The abstract model must make these partial (revert iff
the product overflows), or theorems must assume bounded totals.
