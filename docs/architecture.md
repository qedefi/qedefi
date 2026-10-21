# Architecture

evm-lean is a ground-up rewrite inspired by Nethermind's EVMYulLean, designed so that the
semantics that passes the conformance tests is the one proofs reason about.

## Principles

1. **One definition per concept, and the kernel sees it.** No `opaque`, `partial def`,
   `@[extern]`, `@[implemented_by]`, `unsafe`, FFI, subprocesses or `axiom`. Cryptography is
   a parameter (below), implemented in pure Lean for testing.
2. **Total and honest.** No `!`-indexing, `get!`, `panic!`, or `default` standing in for
   "cannot happen". Every failure is an explicit constructor (`ExceptionalHalt`, `Option`,
   `Except`). Matches over `Opcode`, `Fork` and other growing enums are exhaustive, so a
   missing case is a compile error, not a silent success.
3. **Fuel only at the top.** `Interpreter.step` is total and non-recursive over an explicit
   call stack. Only `run` takes fuel, and running out is a separate result (`OutOfFuel`) that
   never mixes with EVM state.
4. **Every number is the reference's.** Names, gas constants and control flow follow
   `ethereum/execution-specs` (`src/ethereum/forks/{cancun,prague,osaka}/`); docstrings cite
   the spec function where the correspondence is not obvious.
5. **Forks are a parameter.** `Fork` (`cancun`, `prague`, `osaka`) lives in `Context`;
   fork-specific behaviour is `if ctx.fork ≥ .prague then … else …`.

## Representations

| Concept | Type | Why |
|---|---|---|
| Word, address | `BitVec 256`, `BitVec 160` | core automation: `bv_omega`, `grind`, simp sets |
| Gas, nonce, sizes, offsets | `Nat` | `omega`; no overflow reasoning |
| Refund counter | `Int` | can go negative within a transaction |
| Bytes, memory | `ByteArray` (memory size = 32 · words) | fast, `DecidableEq`; `MSIZE` = size |
| World, storage | `Std.ExtTreeMap … compare` | extensional equality, `DecidableEq` |
| Storage invariant | zero values are never stored | `Storage.set k 0` = erase, so equal states are `=` |
| Stack | `List Word`, head = top | structural lemmas |

## Semantics

| Module | Contents |
|---|---|
| `EvmLean/Prelude` | words (one def per arithmetic opcode), bytes, RLP |
| `EvmLean/Opcode.lean`, `Fork.lean` | total opcode decoding; forks |
| `EvmLean/State`, `EvmLean/Machine` | accounts, world, memory; `Context`, `Message`, `MessageResult`, `Crypto` |
| `EvmLean/Gas.lean` | gas schedule |
| `EvmLean/Interpreter` | jump destinations, frames, instructions, `step`, `run`, `processMessageCall`, EIP-7702 delegation |
| `EvmLean/Precompile.lean`, `EvmLean/Crypto` | precompiles with exact gas; pure-Lean cryptography; `Crypto.real` |
| `EvmLean/Tx`, `Tx.lean`, `Block.lean`, `Trie.lean` | transaction validation and execution, block processing, Merkle-Patricia trie |

**Interpreter.** A `Machine` holds the context, precompile implementations, world, transient
storage, the executing `Frame` and its suspended `parents`. `step` does one of three things:
execute one instruction of the executing frame; finish that frame (halt, revert, exceptional
halt, code deposit, rollback to the frame's snapshot) and resume the parent or return the
`MessageResult`; or start a child (precompiles run to completion inside the same step;
calls and creates push a frame). `run fuel m` iterates `step`;
`processMessageCall fuel ctx world transient msg : Except OutOfFuel MessageResult` is the
top-level entry, applying EIP-7702 authorizations from Prague on. With enough fuel every
message terminates, since gas bounds execution.

**Crypto.** `structure Crypto` bundles every primitive (Keccak-256, SHA-256, RIPEMD-160,
BLAKE2F, ecrecover, BN254, KZG, BLS12-381, P-256). The semantics only calls `ctx.crypto.*`,
so theorems hold for every `Crypto` and hashes stay uninterpreted. `Crypto.real`
(`EvmLean/Crypto/Real.lean`) wires in the pure-Lean implementations, which the unit tests check
against official vectors (NIST/FIPS, EIP test cases, go-ethereum precompile JSONs, c-kzg).
Facts about the real functions that a proof needs (e.g. that two slots do not collide) are
hypotheses, never axioms.

**Transactions and blocks.** `EvmLean.Tx` validates and executes transactions (intrinsic
gas, fee checks, EIP-7623 floor, blobs, set-code authorizations; every rejection a
constructor of `InvalidTx`); `EvmLean.Block` applies bodies and checks state, receipt and
header roots.

## Packages and layering

| Package | Library | Depends on | Contents |
|---|---|---|---|
| `evm-lean` (root) | `EvmLean` | core + Std | the semantics; `linter.missingDocs` on |
| | `EvmLogic` | `EvmLean` | generic program logic and proof library ([proving.md](proving.md)) |
| | `EvmTest` | `EvmLean`, `EvmLogic`, `Conformance.Hex` | `#guard` unit tests (`lake test`) |
| | `Conformance` | `EvmLean` | `lake exe conform` |
| | `Snapshot` | `EvmLean`, `Conformance.Hex` | `lake exe snapshot`: deployed contracts at a pinned block ([contracts/README.md](../contracts/README.md#snapshots)) |
| `qedefi` (`qedefi/`) | `QEDefi` | Mathlib v4.35.0, `EvmLogic` | reusable kits: `Math` (`uint256` `mulDiv`), `ERC20` ledgers, `ERC4626` models and properties, `Trace` lifting |
| | `Examples` | `QEDefi` | `Basic` demos, `Solmate` and `OpenZeppelin` targets, `Differential` (`lake exe difftest`) |
| | `QEDefiTest` | `Examples` | `#guard` tests of the contract constants (`lake test` in `qedefi/`; not a default target) |

Rules: the root package never depends on Mathlib or on `qedefi/`; `EvmLean` never imports
`EvmLogic`; generic results go to `EvmLogic` or `QEDefi`, contract-specific ones to
`Examples`. Namespaces mirror directories (`EvmLogic.Solidity.Keccak` is
`EvmLogic/Solidity/Keccak.lean`); lemmas about `EvmLean`'s own types keep the `EvmLean.*`
namespaces so that dot notation works. Model files in `QEDefi` use the Lean module system
(`module`, `public import`) as Mathlib does. The `qedefi` package (QEDefi, the DeFi layer)
requires the root by path (`..`); both packages live in this one repository, and external
projects depend on QEDefi with a Lake git requirement and `subDir = "qedefi"` (see the
README).

## Testing

- **Unit tests** (`EvmTest/`, `qedefi/QEDefiTest/`): `#guard` and kernel `example`s, one file
  per module, on official vectors where they exist.
- **Conformance** (`Conformance/`): `lake exe conform [dirs] [--threads N] [--filter S]
  [--fork Cancun|Prague|Osaka|all] [--parse-only] [--results FILE]` runs BlockchainTests
  fixtures with `Crypto.real` and prints PASSED / FAILED / SKIPPED / UNPARSEABLE counts per
  network; nothing is dropped silently, and the exit code is non-zero on any failure.
  Fixtures: `ethereum/tests` @ `08839f54` (`scripts/fetch-fixtures.sh`), the suite
  EVMYulLean reports against (it passes 22,267 / 22,302 there); execution-spec-tests v5.4.0
  (`scripts/fetch-eest-fixtures.sh`). Transition networks (`<A>To<B>AtTime15k`) switch fork
  per block by timestamp. Results are in the [README](../README.md#results).
- **Differential** (`qedefi/Examples/Differential/`): `lake exe difftest` deploys the compiled
  ERC-4626 targets in evm-lean and in anvil and compares random call sequences
  ([contracts/README.md](../contracts/README.md#differential-testing)).

## EVMYulLean issues this design fixes

| EVMYulLean | evm-lean |
|---|---|
| precompiles logically `default` (ecrecover provably constant) | pure-Lean crypto behind the `Crypto` parameter |
| `ByteArray.zeroes` opaque, memory unprovable | `Bytes.zeros` is plain Lean |
| JUMPDEST analysis `partial` | total, `termination_by` |
| MODEXP truncated bases over 32 bytes | the base is a `Nat` |
| wildcard arms returning `.ok default` | exhaustive matches, explicit errors |
| CREATE swallowed fuel exhaustion and wiped state | fuel only in `run` |
| EIP-161 touched-account clearing missing | `touchedAccounts` in the substate |
| transaction validation in the test harness | part of `EvmLean.Tx` |
| Python and C dependencies | none |
