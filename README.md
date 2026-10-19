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
