# evm-lean

An executable, proof-grade formal semantics of the Ethereum Virtual Machine in pure Lean 4,
a program logic for proving things about bytecode, and an end-to-end verification of a real
DeFi contract (Solmate's ERC-4626 vault) on top of it.

- **One definition.** What the conformance tests execute is exactly what the kernel reasons
  about: core + Std only (Lean v4.35.0), no FFI, no `opaque`, `partial`, `@[extern]`,
  `@[implemented_by]`, `native_decide` or `axiom`.
- **Crypto is a parameter** (`Context.crypto : Crypto`). Theorems quantify over it, so hashes
  stay uninterpreted; tests run `Crypto.real`, built from pure-Lean Keccak-256, SHA-256,
  RIPEMD-160, BLAKE2F, secp256k1, secp256r1, BN254 and BLS12-381 (KZG, EIP-2537).
- **Small-step interpreter** with an explicit call stack: `step` is total and non-recursive;
  only `run` takes fuel. Cancun, Prague and Osaka, with the fork as a parameter.

## Results

**Conformance.** Full block processing (state, receipts, header roots), 0 failures:

| Suite | Networks | Passed | Failed |
|---|---|---|---|
| `ethereum/tests` BlockchainTests @ `08839f54` | Cancun | **22,332** | 0 |
| execution-spec-tests v5.4.0 `blockchain_tests` | Cancun | **17,685** | 0 |
| | Prague, CancunToPragueAtTime15k | **20,957** | 0 |
| | Osaka, PragueToOsakaAtTime15k | **21,644** | 0 |

82,618 fixtures in all; 626 `ethereum/tests` fixtures of other forks are skipped, none is
unparseable. A planted bug (SAR as a logical shift) makes the corresponding fixtures fail.
The compiled ERC-4626 targets are also differential-tested against Foundry's anvil (status,
return data, logs, gas, storage): 20,008 transactions, 0 mismatches.

**ERC-4626.** The deployed bytecode of Solmate `MockERC4626` over `MockERC20` (solc 0.8.28,
any immutables) refines an abstract Mathlib model call by call, and the model's invariants
hold on the bytecode after arbitrary transactions, at any gas and call depth
(`qedefi/Examples/Solmate/ERC4626/LowGas/AnyGas.lean`):

| Theorem | Statement, read from the final world's storage |
|---|---|
| `supply_eq_sum_any_tx_anyGas` | share and asset `totalSupply` = Σ balances |
| `solvent_any_tx_anyGas` | the vault's assets cover every holder's shares at the current price |
| `price_mono_any_tx_anyGas` | user operations never lower assets per share |
| `invariant_any_tx_anyGas` | every model invariant transfers to the bytecode |
| `donation_attack_deployed` | on a trace of top-level calls, the first-depositor attack plays out exactly as the model predicts |

"Arbitrary transactions" means any EOA calling any code: routers and attackers calling the
vault at any depth, enclosing frames that revert afterwards, EIP-2612 `permit`, every view,
unknown selectors and malformed calldata. Hypotheses are explicit and finite (Keccak
freshness of the slots of the actors involved, never global injectivity; no EIP-7702
authorizations); the full list is in [docs/erc4626](docs/erc4626/README.md). The model level
proves the rounding, round-trip, solvency and price properties of EIP-4626 / a16z / crytic
for OpenZeppelin's vault, refutes several of them for Solmate, and quantifies the inflation
attack on both.

## Quickstart

```bash
export PATH="$HOME/.elan/bin:$PATH"

# Root package (core + Std): semantics, program logic, conformance runner
lake build                         # EvmLean, EvmLogic, Conformance, conform
lake test                          # EvmTest: #guard unit tests on official vectors
scripts/check-trust.sh             # no escape hatches (docs/conventions.md)

# Conformance
scripts/fetch-fixtures.sh          # ethereum/tests @ 08839f54 into tests/fixtures
lake exe conform --threads 8       # Cancun BlockchainTests (~10 min on 11 threads)
lake exe conform --filter sar      # a subset
scripts/fetch-eest-fixtures.sh     # execution-spec-tests v5.4.0 into tests/fixtures-eest
lake exe conform tests/fixtures-eest/fixtures/blockchain_tests --fork Osaka   # Cancun|Prague|Osaka|all

# QEDefi package (Mathlib + evm-lean): models, proofs, examples, difftest
(cd qedefi && lake exe cache get && lake build)
(cd qedefi && lake exe difftest --seed 1 --sequences 30)   # needs Foundry (anvil)
scripts/build-contracts.sh --check # artifacts and generated Lean reproduce (needs solc 0.8.28)
```

## QEDefi

*QEDefi: DeFi, quod erat demonstrandum.*

QEDefi is the DeFi verification layer on top of evm-lean: a second Lake package, `qedefi`, in
the `qedefi/` directory of this repository (Mathlib v4.35.0 + evm-lean). Its library `QEDefi`
holds the reusable kits (`Math`, `ERC20` and `ERC4626` models and properties, `Trace` lifting);
`Examples` holds the verified contracts (Solmate, OpenZeppelin, Solady, mainnet tokens) and the
differential tester. The repository stays one monorepo with two packages; the root package
never depends on Mathlib or on `qedefi/`.

Other projects can depend on QEDefi directly from git; Lake clones the repository and builds
the package in `subDir` (its `require evm-lean` path `".."` resolves inside that clone):

```toml
[[require]]
name = "qedefi"
git = "https://github.com/<owner>/evm-lean"   # this repository
rev = "main"
subDir = "qedefi"
```

Then `import QEDefi` (or a module such as `QEDefi.ERC4626.Solmate`), and run
`lake exe cache get` for Mathlib's cache.

## Layout

```
EvmLean/        the semantics: words, RLP, opcodes, forks, state, memory, gas,
                interpreter, precompiles, pure-Lean crypto, transactions, blocks, trie
EvmLogic/       program logic: step lemmas, frame-local WP logic, calls, Solidity layer,
                gas monotonicity (GasMono), certified abstract interpretation (AbsInt), tactics
EvmTest/        #guard unit tests
Conformance/    fixture runner (lake exe conform)
Snapshot/       deployed contracts at a pinned block: code, sources, state (lake exe snapshot)
qedefi/         Lake package QEDefi (Mathlib + evm-lean)
  QEDefi/       reusable kits: Math, ERC20, ERC4626 models and theorems, Trace lifting
  Examples/     Basic demos, Solmate (refinement and invariants), OpenZeppelin (contracts),
                Differential (lake exe difftest), Tests
contracts/      pinned Solidity sources, build configuration, compiled artifacts, snapshots
scripts/        fixtures, contract build, trust and comment-only checks
docs/           documentation (below)
```

## Trust

Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. The semantics
uses no `sorry`, `axiom`, `opaque`, `partial`, `unsafe`, `@[extern]`, `@[implemented_by]`,
`native_decide`, `panic!` or `!`-indexing; the proof libraries use no `sorry`, `axiom` or
`native_decide` (`scripts/check-trust.sh`, run in CI), and no `bv_decide`. Cryptographic
assumptions (hash freshness, signature unforgeability) are never axioms: they are hypotheses
of the theorems that need them, about the finitely many values involved.

## Documentation

| Document | Contents |
|---|---|
| [docs/architecture.md](docs/architecture.md) | design principles, representations, interpreter, packages, testing |
| [docs/proving.md](docs/proving.md) | writing proofs with `EvmLogic` |
| [docs/conventions.md](docs/conventions.md) | Lean style, trust rules, contribution workflow |
| [docs/erc4626/README.md](docs/erc4626/README.md) | the ERC-4626 case study: theorems, hypotheses, findings |
| [docs/erc4626/properties.md](docs/erc4626/properties.md) | ERC-4626 property catalogue with Lean names |
| [docs/erc4626/details.md](docs/erc4626/details.md) | technical notes per component of the verification |
| [docs/renames.md](docs/renames.md) | old → new module and declaration names |
| [contracts/README.md](contracts/README.md) | pinned targets, build, deployment, difftest |
