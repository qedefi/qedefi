# evm-lean design

An executable, proof-grade formal semantics of the EVM in Lean 4 (core + Std only, no
Mathlib), validated against the official Ethereum conformance tests.

It is a ground-up rewrite inspired by Nethermind's EVMYulLean, fixing the problems an
audit found there.

## Non-negotiable principles

1. **One definition per concept, and the kernel sees it.** Crypto is a parameter
   (`Context.crypto : Crypto`): proofs quantify over it; tests use `Crypto.real`, built
   from pure-Lean implementations. No `opaque`, no `partial def`, no `@[extern]`, no `@[implemented_by]`, no `unsafe`, no FFI, no subprocesses, no
   `axiom`. What the conformance tests execute is exactly what proofs reason about.
   (EVMYulLean's precompiles were logically `default`, so ecrecover was provably constant.)
2. **Total and honest.** No `!`-indexing, `get!`, `panic!` or `default` used as a stand-in
   for "can't happen" in the semantics. Every failure is an explicit constructor:
   `ExceptionalHalt`, `Option`, `Except`. A missing match arm must be a compile error, not a
   silent success, so avoid wildcard `_ =>` arms over `Opcode`.
3. **Fuel only at the top.** `Interpreter.step` is a total, non-recursive function on an
   explicit call stack. Only `run` takes fuel, and running out is a distinct result
   (`OutOfFuel`) that never mixes with EVM state.
4. **Every number is the reference's.** Field names, gas constants and control flow follow
   `ethereum/execution-specs` (`src/ethereum/forks/cancun/…`). Cite the spec function in
   docstrings where the correspondence is not obvious.
5. **Forks are a parameter.** `Fork` is threaded through `Context`. Fork-specific behaviour
   is `if ctx.fork ≥ .prague then … else …`. Cancun is implemented first; Prague and Osaka
   must slot in without restructuring.

## Representations

| Concept | Type | Why |
|---|---|---|
| Word | `BitVec 256` | Core automation: `bv_decide`, `bv_omega`, `grind`, simp sets |
| Address | `BitVec 160` | Same |
| Gas, nonce, sizes, offsets | `Nat` | `omega`; no overflow reasoning |
| Refund counter | `Int` | Can go negative within a transaction |
| Bytes | `ByteArray` | Fast, `DecidableEq`, lemmas via `.data` |
| World, storage | `Std.ExtTreeMap … compare` | Extensional equality, insert/get lemmas, `DecidableEq` |
| Storage invariant | zero values never stored | `Storage.set k 0 = erase k`, so equal states are `=` |
| Stack | `List Word`, head = top | Structural lemmas |
| Memory | `ByteArray`, size = 32·words | `MSIZE = bytes.size` |

## Status (2026-10-19)

- Cancun, Prague and Osaka implemented. Conformance: ethereum/tests Cancun 22,332/22,332;
  execution-spec-tests v5.4.0 blockchain tests for Cancun, Prague, Osaka and the
  Cancun→Prague, Prague→Osaka transitions all pass (see README).
- Proof library (`EvmLeanProofs`): per-opcode step lemmas, memory/storage/word lemmas,
  `evm_step`/`evm_steps` symbolic execution, `kernel_rfl`/`kernel_decide` for kernel-only
  evaluation with free variables. Theorems hold for every `Crypto`.
- Next: loops/invariants (CFG lemmas), CALL/CREATE frame lemmas, Solidity ABI and keccak
  mapping slots under explicit non-collision hypotheses.

## Module map and ownership (initial build)

| Module | Contents | Owner |
|---|---|---|
| `EvmLean/Prelude/Word.lean` | EVM word arithmetic (one def per opcode) | scaffold |
| `EvmLean/Prelude/Bytes.lean` | padded reads, big-endian conversions | scaffold |
| `EvmLean/Prelude/Rlp.lean` | RLP encode | scaffold |
| `EvmLean/Fork.lean`, `Opcode.lean` | forks; total opcode decode | scaffold |
| `EvmLean/State/Account.lean` | `Account`, `Storage`, `World` | scaffold |
| `EvmLean/Machine/Types.lean` | `Context`, `Message`, `MessageResult`, `ExceptionalHalt`, `Log` | scaffold (interface, change only by agreement) |
| `EvmLean/Machine/Memory.lean` | memory | scaffold |
| `EvmLean/Crypto/{Keccak,Sha256,Ripemd160,Blake2f}.lean` | hashes in pure Lean | agent **hashes** |
| `EvmLean/Crypto/{Secp256k1,Bn254}.lean`, `EvmLean/Precompile.lean` | EC crypto, all precompile wrappers and gas | agent **precompiles** |
| `EvmLean/Crypto/Kzg.lean` (+ BLS12-381) | KZG point evaluation | agent **kzg** |
| `EvmLean/Gas.lean`, `EvmLean/Interpreter.lean`, `EvmLean/Interpreter/*` | gas schedule, frames, `step`, `run`, `processMessageCall` | agent **interpreter** |
| `EvmLean/Tx.lean`, `EvmLean/Tx/*`, `EvmLean/Block.lean`, `Conformance/*` | transactions, block glue, fixture runner | agent **tx-harness** |
| `EvmLeanTest/*` | `#guard` unit tests, one file per module | each owner |
| `EvmLeanProofs/*` | kernel-checked sanity theorems | later phase |

## Interfaces between agents

The signatures below are frozen; bodies are `sorry` until their owner fills them in.

- `structure Crypto` (in `Machine/Types.lean`) bundles every primitive; `Context.crypto`
  carries it. The semantics never calls a hash implementation directly, only `ctx.crypto.*`.
  `Crypto.real` (`Crypto/Real.lean`) wires in the implementations below.
- `Keccak.hash256 : ByteArray → Word`
- `Sha256.hash : ByteArray → ByteArray` (32 B), `Ripemd160.hash : ByteArray → ByteArray` (20 B)
- `Blake2.compress : Nat → Vector UInt64 8 → Vector UInt64 16 → UInt64 → UInt64 → Bool → Vector UInt64 8`
- `Secp256k1.recover : ByteArray → Nat → Nat → Nat → Option ByteArray`
- `Bn254.add / mul : ByteArray → Option ByteArray`, `Bn254.pairingCheck : ByteArray → Option Bool`
- `Kzg.verifyProof : ByteArray → ByteArray → ByteArray → ByteArray → Option Bool`
- `Precompile.isPrecompile : Fork → Address → Bool`, `Precompile.run : Crypto → Fork → Address → ByteArray → Nat → Precompile.Result`
- `Interpreter.processMessageCall : Nat → Context → World → TransientStorage → Message → Except OutOfFuel MessageResult`
- `Interpreter.createAddress`, `Interpreter.create2Address` (take `keccak256` as an argument)

## Conformance

`lake exe conform <fixtures-dir> [threads]` runs `ethereum/tests` BlockchainTests (pinned
commit `08839f54`, Cancun-only refill), the same suite EVMYulLean reports against. It
prints pass/fail/skipped/unparseable counts; nothing is dropped silently. The baseline
to beat is 22,267 / 22,302 passed in EVMYulLean's main phase on macOS. Prague and Osaka are
checked against the execution-spec-tests `blockchain_tests` (pinned release v5.4.0,
`scripts/fetch-eest-fixtures.sh`) with `--fork Prague|Osaka|all`; transition networks
(`<A>To<B>AtTime15k`) switch fork per block by timestamp.

## Known issues in EVMYulLean that this design fixes

- Precompiles defined as `default` in the logic (ecrecover provably constant) → pure-Lean crypto.
- `ByteArray.zeroes` opaque, so memory was unprovable → `Bytes.zeros` is plain Lean.
- JUMPDEST analysis `partial` → total definition with `termination_by`.
- MODEXP truncated bases over 32 bytes → base is a `Nat`.
- Wildcard arms returned `.ok default` → exhaustive matches, explicit errors.
- CREATE swallowed fuel exhaustion and wiped state → fuel only in `run`.
- EIP-161 touched-account clearing missing → `MessageResult.touchedAccounts`.
- Transaction validation lived in the test harness → part of `EvmLean.Tx`.
- Python and C dependencies → none.
