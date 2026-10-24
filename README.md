# QEDefi

*DeFi, quod erat demonstrandum.* Machine-checked theorems about deployed EVM bytecode, in Lean 4.

The repository holds two Lake packages:

- **`evm-lean`** (root, core + Std only): an executable formal semantics of the EVM (`EvmLean`)
  and a program logic for proving things about bytecode (`EvmLogic`). The definition the
  conformance tests execute is the one the kernel reasons about.
- **`qedefi`** (`qedefi/`, Mathlib + evm-lean): abstract models of DeFi building blocks (ERC-20,
  ERC-4626, access control) with their properties (`QEDefi`), and contracts verified against them
  byte for byte (`Examples`).

The aim is a growing collection of verified contracts: each new one reuses the semantics, the
program logic and the models, and makes the next one cheaper. See
[CONTRIBUTING.md](CONTRIBUTING.md) for how to add one.

## The semantics

- **One definition.** Core + Std only (Lean v4.35.0): no FFI, `opaque`, `partial`, `@[extern]`,
  `@[implemented_by]`, `native_decide` or `axiom`.
- **Crypto is a parameter** (`Context.crypto : Crypto`). Theorems quantify over it, so hashes stay
  uninterpreted; tests run `Crypto.real`, built from pure-Lean Keccak-256, SHA-256, RIPEMD-160,
  BLAKE2F, secp256k1, secp256r1, BN254 and BLS12-381 (KZG, EIP-2537).
- **Small-step interpreter** with an explicit call stack: `step` is total and non-recursive; only
  `run` takes fuel. Cancun, Prague and Osaka, with the fork as a parameter.

**Conformance.** Full block processing (state, receipts, header roots), 0 failures:

| Suite | Networks | Passed | Failed |
|---|---|---|---|
| `ethereum/tests` BlockchainTests @ `08839f54` | Cancun | **22,332** | 0 |
| execution-spec-tests v5.4.0 `blockchain_tests` | Cancun | **17,685** | 0 |
| | Prague, CancunToPragueAtTime15k | **20,957** | 0 |
| | Osaka, PragueToOsakaAtTime15k | **21,644** | 0 |

82,618 fixtures in all; the 626 `ethereum/tests` fixtures of other forks are skipped, none is
unparseable. The ERC-20 and ERC-4626 targets below are also differential-tested against Foundry's
anvil (status, return data, logs, gas, every touched slot, ether balances): 240,460 transactions
over 16 contract families, 0 mismatches.

## Verified contracts

| Contract | Code | Proved | Where |
|---|---|---|---|
| Solmate `ERC4626` over `ERC20` | compiled (solc 0.8.28) | every function refines the model; the model's invariants hold on the bytecode after any transaction, at any gas and call depth | `qedefi/Examples/Solmate/` |
| OpenZeppelin `ERC20` v5.7.0 | compiled | `transfer`, `transferFrom`, `approve`, `mint`, `burn` and the views refine the model, with events; callee summaries for contracts that call it | `qedefi/Examples/OpenZeppelin/ERC20/` |
| OpenZeppelin `TransparentUpgradeableProxy` + `ProxyAdmin` v5.7.0 | compiled | no transaction not sent by the owner changes the implementation or the owner, over any sequence of transactions | `qedefi/Examples/Actor/Bytecode/` |
| the same, owned by Safe v1.5.0 | Safe: mainnet bytecode | no transaction signed by fewer than `threshold` owners changes the implementation, ProxyAdmin's owner or the Safe's configuration | `qedefi/Examples/Safe/Bytecode/` |
| WETH9 | mainnet bytecode | ether backs the tokens after any transaction (`Σ balanceOf ≤ address(this).balance`); `withdraw` refines the model for any gas, depth and recipient | `qedefi/Examples/Reentrancy/Solvency/` |
| Reentrancy demonstrators: `CEIBank`, `GuardedBank`, `VulnerableBank` | compiled | the two defended banks stay solvent after any transaction, through arbitrary reentrant callees; the attack drains the vulnerable one | `qedefi/Examples/Reentrancy/` |
| OpenZeppelin `VestingWallet` | compiled | the schedule, views and `release` refine a time-indexed model; released ≤ vested over any sequence of blocks | `qedefi/Examples/Time/` |
| OpenZeppelin `ERC4626` (decimals offset 0 and 3) | compiled | model level: EIP-4626 properties, inflation-attack bounds | `qedefi/QEDefi/ERC4626/` |
| USDT, BNB, STA, AMPL, Solady `ERC20` | mainnet / compiled | model level: each token's quirks, ledger invariants, how they break vaults that hold them | `qedefi/QEDefi/ERC20/Variant*.lean` |
| GUSD, YAMv2, LEND, ZRX | mainnet | bytecode pinned and difftested; proofs open | `qedefi/Examples/WeirdERC20/` |
| Synthetix `StakingRewards` | model | solvency at every time and no dilution; bytecode open | `qedefi/QEDefi/Staking/` |

**ERC-4626, the headline.** For the deployed bytecode of Solmate `MockERC4626` over `MockERC20`,
with any immutables (`qedefi/Examples/Solmate/ERC4626/LowGas/AnyGas.lean`):

| Theorem | Statement, read from the final world's storage |
|---|---|
| `supply_eq_sum_any_tx_anyGas` | share and asset `totalSupply` = Σ balances |
| `solvent_any_tx_anyGas` | the vault's assets cover every holder's shares at the current price |
| `price_mono_any_tx_anyGas` | user operations never lower assets per share |
| `invariant_any_tx_anyGas` | every model invariant transfers to the bytecode |
| `donation_attack_deployed` | on a trace of top-level calls, the first-depositor attack plays out exactly as the model predicts |

"Any transaction" means any EOA calling any code: routers and attackers calling the vault at any
depth, enclosing frames that revert afterwards, EIP-2612 `permit`, every view, unknown selectors
and malformed calldata. The hypotheses are explicit and finite (Keccak freshness of the slots of
the actors involved, never global injectivity; no EIP-7702 authorizations), listed in
[docs/erc4626](docs/erc4626/README.md). The models also prove the EIP-4626, a16z and crytic
properties for OpenZeppelin's vault, refute several of them for Solmate, and quantify the
inflation attack on both.

## Quickstart

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
lake build                         # QEDefi, Examples, difftest (a few minutes)
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
Projects that need only the semantics and the program logic can require the root package
(`name = "evm-lean"`, no `subDir`) and stay free of Mathlib.

## Layout

```
EvmLean/        the semantics: words, RLP, opcodes, forks, state, memory, gas, interpreter,
                precompiles, pure-Lean crypto, transactions, blocks, trie
EvmLogic/       program logic: step lemmas, frame-local WP logic, calls, Solidity layer, nested
                simulation, reentrancy, relays, time, gas monotonicity, certified abstract
                interpretation, tactics
EvmTest/        #guard unit tests
Conformance/    fixture runner (lake exe conform)
Snapshot/       deployed contracts at a pinned block, fetched once, replayed offline (lake exe snapshot)
qedefi/
  QEDefi/       models and their theorems: Math, ERC20, ERC4626, Actor (access control),
                Vesting, Staking, Trace (incl. time-indexed lifting)
  Examples/     verified contracts (Solmate, OpenZeppelin, Actor, Safe, Reentrancy, Time),
                mainnet token data, Basic demos, Differential (lake exe difftest)
  QEDefiTest/   #guard tests of the contract data
contracts/      pinned Solidity sources, build configuration, artifacts, mainnet bytecode
scripts/        fixtures, contract build, trust and statement checks, benchmarks
docs/           documentation (below)
```

## Trust

Every theorem depends only on the Lean kernel, the `EvmLean` definitions and the axioms
`propext`, `Classical.choice` and `Quot.sound`. The semantics uses no `sorry`, `axiom`, `opaque`,
`partial`, `unsafe`, `@[extern]`, `@[implemented_by]`, `native_decide`, `panic!` or `!`-indexing;
the proofs use no `sorry`, `axiom`, `native_decide` or `bv_decide` (`scripts/check-trust.sh`, run
in CI). Cryptographic assumptions (hash freshness, signature unforgeability) are never axioms:
they are hypotheses of the theorems that need them, about the finitely many values involved.

What remains to trust is that `EvmLean` is the EVM. The conformance suites and the differential
tests are the evidence; [docs/architecture.md](docs/architecture.md) maps each definition to the
`ethereum/execution-specs` function it mirrors.

## Documentation

| Document | Contents |
|---|---|
| [docs/architecture.md](docs/architecture.md) | design principles, representations, interpreter, packages, testing |
| [docs/proving.md](docs/proving.md) | writing proofs with `EvmLogic`: tactics, untrusted callees and reentrancy, time and multiple blocks, pitfalls, performance |
| [docs/erc4626/](docs/erc4626/README.md) | the ERC-4626 case study: theorems, hypotheses, findings, property catalogue |
| [docs/tokens.md](docs/tokens.md) | ERC-20 targets, their quirks, the variant model and integration theorems |
| [docs/access-control.md](docs/access-control.md) | the actor model: who can cause an effect |
| [docs/actor-bytecode.md](docs/actor-bytecode.md) | access control on bytecode: relays, the proxy and Safe upgrade guards |
| [contracts/README.md](contracts/README.md) | pinned targets, build, deployments, snapshots, differential testing |
| [CONTRIBUTING.md](CONTRIBUTING.md) | workflow, checks, conventions, adding a contract, open problems |

## License

Apache-2.0 ([LICENSE](LICENSE)). Vendored and fetched contract sources under `contracts/` keep
their own licenses (Solmate AGPL-3.0-only, OpenZeppelin and Solady MIT, mainnet sources as
published); they are inputs to the build, not part of the Lean libraries.
