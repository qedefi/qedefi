# Status

What is proved, what comes next, and how the repository is organised. The [README](../README.md)
has the short version.

## Verified contracts

| Contract                                                             | Code                   | Proved                                                                                                                                                                                                      | Where                                  |
| -------------------------------------------------------------------- | ---------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------- |
| Solmate `ERC4626` over `ERC20`                                       | compiled (solc 0.8.28) | every function refines the model; the model's invariants hold on the bytecode after any transaction, at any gas and call depth                                                                              | `qedefi/Verified/Solmate/`             |
| OpenZeppelin `ERC20` v5.7.0                                          | compiled               | `transfer`, `transferFrom`, `approve`, `mint`, `burn` and the views refine the model, with events; callee summaries for contracts that call it                                                              | `qedefi/Verified/OpenZeppelin/ERC20/`  |
| OpenZeppelin `TransparentUpgradeableProxy` + `ProxyAdmin` v5.7.0     | compiled               | no transaction not sent by the owner changes the implementation or the owner, over any sequence of transactions                                                                                             | `qedefi/Verified/OpenZeppelin/Proxy/`  |
| the same, owned by Safe v1.5.0                                       | Safe: mainnet bytecode | no transaction signed by fewer than `threshold` owners changes the implementation, ProxyAdmin's owner or the Safe's configuration                                                                           | `qedefi/Verified/Safe/Bytecode/`       |
| WETH9                                                                | mainnet bytecode       | ether backs the tokens after any transaction (`Σ balanceOf ≤ address(this).balance`); `withdraw` refines the model for any gas, depth and recipient                                                         | `qedefi/Verified/WETH9/`               |
| Reentrancy demonstrators: `CEIBank`, `GuardedBank`, `VulnerableBank` | compiled               | the two defended banks stay solvent after any transaction, through arbitrary reentrant callees; the attack drains the vulnerable one                                                                        | `qedefi/Examples/Reentrancy/`          |
| OpenZeppelin `VestingWallet`                                         | compiled               | the schedule, views and `release` refine a time-indexed model; released ≤ vested over any sequence of blocks                                                                                                | `qedefi/Verified/OpenZeppelin/VestingWallet/` |
| Aave V3 aEthWETH (`AToken` rev. 5 behind its proxy)                  | mainnet bytecode       | the Pool-only entry points have no effect for any other caller, also through the proxy; `mint`/`burn` by the Pool keep the scaled ledger balanced; views exact                                              | `qedefi/Verified/AaveV3/`              |
| OpenZeppelin `ERC4626` (decimals offset 0 and 3)                     | compiled               | model level: EIP-4626 properties, inflation-attack bounds                                                                                                                                                   | `qedefi/QEDefi/ERC4626/`               |
| USDT, BNB, STA, AMPL, Solady `ERC20`                                 | mainnet / compiled     | model level: each token's quirks, ledger invariants, how they break vaults that hold them                                                                                                                   | `qedefi/QEDefi/ERC20/Variant*.lean`    |
| GUSD, YAMv2, LEND, ZRX                                               | mainnet                | bytecode pinned and difftested; proofs open                                                                                                                                                                 | `qedefi/Verified/WeirdERC20/`          |
| Synthetix `StakingRewards`                                           | model                  | solvency at every time and no dilution; bytecode open                                                                                                                                                       | `qedefi/QEDefi/Staking/`               |
| Aave V3 Pool (v3.7)                                                  | model                  | ray math exact, indexes monotone, reserve backing within half a wei per accrual, health-factor guarantees; a proved counterexample to exact backing, and the live reserves' backing gap traced to its cause | `qedefi/QEDefi/Aave/`                  |

For Solmate's vault the headline theorems and every hypothesis are in
[docs/erc4626](erc4626/README.md).

## Next

- Now: the token zoo (USDT, BNB, STA, AMPL, Solady), OpenZeppelin ERC-4626 and StakingRewards on bytecode.
- H1 2027: vaults over real token bytecode. Aave V3 reserve backing on the deployed bytecode. Uniswap V2. Who controls what in a deployed system, read from chain state at a block.
- Later: Uniswap V3/V4, Curve, oracles and liquidations. Re-running the proofs when a proxy is upgraded. Proof CI that protocols run before they deploy.

## The EVM semantics

- **One definition.** Core + Std only (Lean v4.35.0): no FFI, `opaque`, `partial`, `@[extern]`,
  `@[implemented_by]`, `native_decide` or `axiom`.
- **Crypto is a parameter** (`Context.crypto : Crypto`). Theorems quantify over it, so hashes stay
  uninterpreted; tests run `Crypto.real`, built from pure-Lean Keccak-256, SHA-256, RIPEMD-160,
  BLAKE2F, secp256k1, secp256r1, BN254 and BLS12-381 (KZG, EIP-2537).
- **Small-step interpreter** with an explicit call stack: `step` is total and non-recursive; only
  `run` takes fuel. Cancun, Prague and Osaka, with the fork as a parameter.

**Conformance.** Full block processing (state, receipts, header roots), 0 failures:

| Suite                                          | Networks                        | Passed     | Failed |
| ---------------------------------------------- | ------------------------------- | ---------- | ------ |
| `ethereum/tests` BlockchainTests @ `08839f54`  | Cancun                          | **22,332** | 0      |
| execution-spec-tests v5.4.0 `blockchain_tests` | Cancun                          | **17,685** | 0      |
|                                                | Prague, CancunToPragueAtTime15k | **20,957** | 0      |
|                                                | Osaka, PragueToOsakaAtTime15k   | **21,644** | 0      |

82,618 fixtures in all; the 626 `ethereum/tests` fixtures of other forks are skipped, none is
unparseable. The ERC-20 and ERC-4626 targets are also differential-tested against Foundry's
anvil (status, return data, logs, gas, every touched slot, ether balances): 240,460 transactions
over 16 contract families, 0 mismatches.

## Build

Install [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain`.

```bash
# Root package: semantics, program logic, conformance runner
lake build                         # EvmLean, EvmLogic, Conformance, Snapshot and their executables
lake test                          # EvmTest: #guard unit tests on official vectors
scripts/check-trust.sh             # no escape hatches

# Conformance
scripts/fetch-fixtures.sh          # ethereum/tests @ 08839f54 into tests/fixtures
lake exe conform --threads 8       # Cancun BlockchainTests (about 10 minutes)
lake exe conform --filter sar      # a subset
scripts/fetch-eest-fixtures.sh     # execution-spec-tests v5.4.0 into tests/fixtures-eest
lake exe conform tests/fixtures-eest/fixtures/blockchain_tests --fork Osaka   # Cancun|Prague|Osaka|all

# qedefi package: models, proofs, differential tester
cd qedefi
lake exe cache get                 # Mathlib's build cache
lake build                         # QEDefi, Verified, Examples, difftest (a few minutes)
lake test                          # QEDefiTest
lake exe difftest --seed 1 --sequences 30   # needs Foundry (anvil)
```

`scripts/build-contracts.sh --check` (needs solc 0.8.28 and Foundry) rebuilds the contract
artifacts and the generated Lean modules and fails if anything committed changes.

## Depending on QEDefi

Lake clones the repository and builds the package in `subDir`; its `require evm-lean` path
`".."` resolves inside that clone:

```toml
[[require]]
name = "qedefi"
git = "https://github.com/totomanov/qedefi"
rev = "main"
subDir = "qedefi"
```

Then `import QEDefi` (or a module such as `QEDefi.ERC4626.Solmate`) and run `lake exe cache get`.
For the semantics and program logic alone, require the root package (`name = "evm-lean"`, no
`subDir`).

## Layout

Two Lake packages: `evm-lean` at the root (core + Std only: the semantics and the program logic)
and `qedefi` in `qedefi/` (Mathlib: models and verified contracts). Projects that need only the
semantics can depend on the root package and stay free of Mathlib.

```
EvmLean/        the semantics: words, RLP, opcodes, forks, state, memory, gas, interpreter,
                precompiles, pure-Lean crypto, transactions, blocks, trie
EvmLogic/       program logic: step lemmas, frame-local WP logic, calls, Solidity layer, nested
                simulation, reentrancy, relays, time, gas monotonicity, certified abstract
                interpretation, tactics
EvmTest/        #guard unit tests
Conformance/    fixture runner (lake exe conform)
Snapshot/       deployed contracts at a pinned block, fetched once, replayed offline; transaction
                sequences against an anvil fork (lake exe snapshot)
qedefi/
  QEDefi/       models and their theorems: Math, ERC20, ERC4626, Aave, Actor (access control),
                Vesting, Staking, Solvency, Trace (incl. time-indexed lifting)
  Verified/     one directory per deployed system, its generated code (Contracts/) and proofs:
                Solmate, OpenZeppelin, Safe, WETH9, AaveV3, Solady, WeirdERC20
  Examples/     demos: Basic, Actor models, Reentrancy demonstrators
  Difftest/     differential testing against anvil (lake exe difftest)
  QEDefiTest/   #guard tests of the contract data
contracts/      pinned Solidity sources, build configuration, artifacts, mainnet bytecode
scripts/        fixtures, contract build, trust and statement checks, benchmarks
docs/           documentation (below)
```

## Documentation

| Document                                         | Contents                                                                                                                   |
| ------------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------- |
| [architecture.md](architecture.md)     | design principles, representations, interpreter, packages, testing                                                         |
| [proving.md](proving.md)               | writing proofs with `EvmLogic`: tactics, untrusted callees and reentrancy, time and multiple blocks, pitfalls, performance |
| [erc4626/](erc4626/README.md)          | the ERC-4626 case study: theorems, hypotheses, findings, property catalogue                                                |
| [tokens.md](tokens.md)                 | ERC-20 targets, their quirks, the variant model and integration theorems                                                   |
| [aave-v3.md](aave-v3.md)               | Aave V3 mainnet targets and what is proved on their bytecode                                                               |
| [aave-v3-model.md](aave-v3-model.md)   | the Aave v3.7 accounting model: theorems, findings, scope                                                                  |
| [access-control.md](access-control.md) | the actor model: who can cause an effect                                                                                   |
| [actor-bytecode.md](actor-bytecode.md) | access control on bytecode: relays, the proxy and Safe upgrade guards                                                      |
| [contracts/README.md](../contracts/README.md)       | pinned targets, build, deployments, snapshots, differential testing                                                        |
| [AGENTS.md](../AGENTS.md)                           | quickstart and rules for AI agents contributing proofs                                                                     |
| [CONTRIBUTING.md](../CONTRIBUTING.md)               | workflow, checks, conventions, adding a contract, open problems                                                            |

## Licenses

The Lean code is Apache-2.0 ([LICENSE](../LICENSE)). Vendored and fetched contract sources under
`contracts/` keep their own licenses (Solmate AGPL-3.0-only, OpenZeppelin and Solady MIT,
mainnet sources as published, among them Aave's BUSL-1.1); they are inputs to the build, not
part of the Lean libraries.
