# evm-lean

An executable, proof-grade formal semantics of the Ethereum Virtual Machine in Lean 4.

- **Pure Lean** (core + Std, Lean v4.35.0): no Mathlib, no FFI, no Python, no `opaque`,
  no `partial`, no `axiom`. Everything depends only on `propext`, `Classical.choice`,
  `Quot.sound`. What the conformance tests run is exactly what the kernel reasons about.
- **Crypto is a parameter** (`Context.crypto : Crypto`). Theorems can quantify over it, so
  hashes stay uninterpreted; tests use `Crypto.real`: Keccak-256, SHA-256, RIPEMD-160,
  BLAKE2F, secp256k1, secp256r1, BN254 pairing, BLS12-381 (KZG and the EIP-2537
  precompiles), all implemented in Lean.
- **Small-step interpreter** with an explicit call stack: `step` is total and
  non-recursive, `run` is the only place fuel appears.
- **Cancun, Prague and Osaka**, with the fork as a parameter (`if ctx.fork ≥ .prague …`).

## Conformance

`ethereum/tests` BlockchainTests @ `08839f54` (Cancun refill), full block processing
including state, receipts and header roots:

| | PASSED | FAILED | SKIPPED (other forks) | UNPARSEABLE |
|---|---|---|---|---|
| evm-lean | **22,332** | **0** | 626 | 0 |

execution-spec-tests `v5.4.0` (`fixtures_develop`, `blockchain_tests`; fetch with
`scripts/fetch-eest-fixtures.sh`):

| `--fork` | networks | PASSED | FAILED | UNPARSEABLE |
|---|---|---|---|---|
| Cancun | Cancun | **17,685** | 0 | 0 |
| Prague | Prague, CancunToPragueAtTime15k | **20,957** | 0 | 0 |
| Osaka | Osaka, PragueToOsakaAtTime15k | **21,644** | 0 | 0 |

For comparison, EVMYulLean (the model that motivated this rewrite) passes 22,267 / 22,302
of its Cancun run on macOS. A planted bug (SAR as a logical shift) makes the
corresponding fixtures fail, so passes are meaningful.

## ERC-4626: an end-to-end DeFi verification

The deployed bytecode of Solmate's `ERC4626` (`MockERC4626` over `MockERC20`, solc 0.8.28,
any immutables) is proved to refine an abstract Mathlib model of the vault, call by call:
`deposit`, `mint`, `withdraw`, `redeem`, every view, the share token's ERC-20 functions and
the asset's `transfer`/`transferFrom`/`approve`/`mint`/`burn`. The model's invariants are
then lifted to the bytecode along arbitrary traces
(`specs/EvmLeanSpecs/Refinement/InvariantsFinal.lean`):

| Theorem | Statement, on the deployed contracts |
|---|---|
| `supply_eq_sum_deployed` | share and asset `totalSupply` = Σ balances |
| `solvent_deployed` | the vault's assets cover all shares at the current price |
| `no_dilution_deployed` | a user operation never lowers assets per share |
| `price_mono_deployed` | along user operations, assets per share never decreases |
| `donation_attack_deployed` | the first-depositor attack plays out exactly as the model predicts |

Hypotheses are explicit and listed in the file docstring and
`specs/EvmLeanSpecs/Refinement/INVARIANTS.md`: enough gas, no ETH, no EIP-7702 authorizations,
Keccak freshness of the finitely many slots involved (never global injectivity), well-formed
initial ledgers, top-level calls (nested calls are covered at frame level for the entry
points and views). The model level (`specs/`, 315+ theorems) also proves the a16z/crytic
round-trip properties and refutes several for Solmate (`docs/erc4626-invariants.md`).
Everything depends only on `propext`, `Classical.choice`, `Quot.sound`.

The compiled contracts are differential-tested against Foundry/anvil (`lake exe difftest`):
0 mismatches over 20,008 + 2,430 transactions, checking status, return data, logs, gas and
storage.

## Usage

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build                       # the semantics
lake test                        # unit tests (#guard, official vectors)
lake build EvmLeanProofs         # kernel-checked theorems
scripts/fetch-fixtures.sh        # pinned ethereum/tests into tests/fixtures
lake exe conform --threads 8     # conformance suite (~10 min on 11 threads)
lake exe conform --filter sar    # a subset
scripts/fetch-eest-fixtures.sh   # execution-spec-tests v5.4.0 into tests/fixtures-eest
lake exe conform tests/fixtures-eest/fixtures/blockchain_tests --fork Osaka   # or Prague, Cancun, all
scripts/check-trust.sh           # no sorry/opaque/partial/extern/axiom/panic in EvmLean/
(cd specs && lake exe cache get && lake build)   # Mathlib specs + ERC-4626 refinement (~5 min)
scripts/build-contracts.sh --check               # contract artifacts reproduce
lake exe difftest --seed 1 --sequences 30        # evm-lean vs. anvil on the vaults
```

## Layout

| Path | Contents |
|---|---|
| `EvmLean/Prelude` | words (`BitVec 256`), bytes, RLP |
| `EvmLean/Opcode.lean`, `Fork.lean` | total opcode decoding; forks |
| `EvmLean/State`, `EvmLean/Machine` | accounts and world (`Std.ExtTreeMap`), memory, message interface |
| `EvmLean/Gas.lean` | gas schedule |
| `EvmLean/Interpreter` | jumpdest analysis, frames, instructions, `step`, `run`, `processMessageCall` |
| `EvmLean/Precompile.lean`, `EvmLean/Crypto` | precompiles and pure-Lean cryptography |
| `EvmLean/Tx`, `Block.lean`, `Trie.lean` | transactions, blocks, Merkle-Patricia trie |
| `EvmLeanTest` | unit tests |
| `EvmLeanProofs` | kernel-checked theorems (e.g. executing bytecode in the kernel) |
| `Conformance` | fixture runner |

See `DESIGN.md` for the architecture and principles, `CONVENTIONS.md` for Lean style,
`AGENTS.md` for the development workflow.
