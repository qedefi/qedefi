# Proof performance

Measurements of how long the proofs take to check, and what made them faster. The trust base
did not change: the Lean kernel, the unchanged `EvmLean` semantics, and the axioms `propext`,
`Classical.choice`, `Quot.sound`. No `native_decide`, `bv_decide`, axioms, `sorry`,
`implemented_by`/`extern`, or kernel-skipping options were added. Every theorem keeps its exact
statement.

## Method

- **(a) Clean builds**: `scripts/bench-build.sh OUTDIR`. It deletes `.lake/build` and
  `qedefi/.lake/build` but keeps `qedefi/.lake/packages` (Mathlib comes from its cache). It builds
  `EvmLean` without timing it, then times `lake build --wfail EvmLogic` (root package) and
  `lake build --wfail QEDefi Examples` (`qedefi/`) at Lake's default parallelism, on a 12-core
  Apple machine.
  The timed `qedefi` targets are the proof libraries `QEDefi Examples` only. Since the
  low-hanging-fruit changes below, the `#guard` evaluation tests (formerly `Examples.Tests.*`,
  ~28 s of interpretation) live in the separate `QEDefiTest` library (`lake test` in `qedefi/`)
  and are no longer part of this measurement; earlier rows include them.
- **(b) Per-file times**: Lake's `Built … (t)` lines from the same logs. These times come from
  the parallel build, so contention inflates them. A single file built alone takes about half as
  long.
- **(c) Symbolic execution**: `scripts/bench-symexec.sh`. It elaborates `mintShares_wp`,
  `afterDeposit_wp` and `deposit_refines` (the whole `deposit` path of the Solmate vault, with
  its revert branches) as one standalone file, and also an empty file with the same imports.
  The time per instruction is the difference between the two (best of 3) divided by the
  instructions the symbolic-execution tactics executed. The count comes from
  `trace.EvmLean.symStep`, and that trace is on during the timed run.
- **Statements**: a dump of every theorem in `EvmLogic`/`QEDefi`/`Examples`. Each entry is a deep
  hash of the statement plus every definition reachable from it, and the 267 headline
  statements are also pretty-printed. The dump ran before the work and again after each step.

Baseline: `85ff30d` (`main` when the work started). Final: branch `perf`.

## Results

### (a) Clean, cache-free builds

| | baseline wall | final wall | speedup | baseline CPU (user) | final CPU (user) |
|---|---:|---:|---:|---:|---:|
| `EvmLogic` | 81.8 s | 50.1 s | 1.6× | 183 s | 247 s |
| `QEDefi Examples` | 2572.0 s | 171.3 s | **15.0×** | 10121 s | 1195 s |
| both | 2653.8 s | 221.4 s | **12.0×** | 10304 s | 1443 s (7.1×) |

Repeated clean builds of the same tree vary by about ±5 s (`qedefi`: 166–171 s).

### (b) The 20 heaviest files of the baseline

Times are in-build seconds. "→" marks files whose proofs moved into new modules (same
namespaces).

| file | baseline | final |
|---|---:|---:|
| ERC4626/SharesCode | 752 | 50 |
| ERC4626/Malformed | 631 | 23 |
| ERC4626/EventsSharesCode | 406 | 39 |
| ERC4626/EventsInternal | 391 | 28 |
| ERC4626/Permit | 390 | 41 |
| ERC4626/SharesFrame | 385 | 48 |
| ERC4626/EventsEntry | 291 | 14 |
| ERC20/Permit | 282 | 33 |
| ERC20/Events | 282 | 14 (→ EventsTransfer 33) |
| ERC20/Malformed | 241 | 16 |
| ERC4626/Strings | 208 | 4.6 (→ StringsCode{Short,Long,} 34+64+6) |
| ERC4626/Deposit | 204 | 13 (→ DepositInternal 12) |
| ERC4626/Withdraw | 200 | 16 |
| ERC4626/WithdrawInternal | 198 | 31 |
| ERC20/Transfer | 183 | 22 |
| ERC20/MintBurn | 174 | 31 |
| ERC20/Strings | 149 | 5.0 (→ StringsCode{Short,Long,} 33+62+6) |
| ERC4626/Views | 143 | 10 |
| ERC20/TransferFrom | 132 | 31 |
| ERC4626/UnknownSelectors | 113 | 20 |

The sum of per-module times fell from 6832 s to 1448 s. The longest chain of dependent
modules is now about 160 s. It runs through `SolmateVault` → `Convert` → `Views` →
`Abstraction` → the ERC-20 refinement and event modules. Several other chains are within a few
seconds of it.

### (c) Symbolic execution on `deposit`

| | instructions | time beyond imports | per instruction |
|---|---:|---:|---:|
| baseline | 611 | 91.0 s | 149 ms |
| final | 611 | 5.0 s | 8.2 ms (**18×**) |

The baseline has no step trace, so its count is taken from the final run (same bytecode, same
path). The kernel still spends about 20 ms per step (as before). The three proofs elaborate in
parallel, which is why the wall time per instruction is lower than that.

## What changed

1. **Code tables** (`EvmLogic/Program/CodeTable.lean`, the `code_table` command). Code facts
   used to be decided on list-backed `ByteArray` literals, which costs O(size + pc) per fact.
   Each contract now gets a binary trie of its bytes and jump destinations, built and checked
   once (`CodeTable.Ok`, proved by `Eq.refl`). Facts are then read off the trie by
   `get_ofList`/`mem_of_get_ofKeys` (`table_decide`, `codeFact`, `wordFact`, `bytesFact`,
   `jumpDestMem?`). Where no table exists, the old kernel `decide` is used.
2. **Fast stepper** (`EvmLogic/Tactic/FastStep.lean`, used by `sol_steps`, `psol_steps`,
   `pwp_steps`, `pwp_msteps`, `psol_msteps`). It builds each step's proof from the existing
   step lemmas (`WP.of_step`, `run_succ_of_running`) and normalizes only the fields that
   changed. Gas side conditions are discharged by proved bounds (`le_sub_chain`,
   `BoundedBy`, `sloadCost_le`, `sstoreCost_le`). Any unexpected shape falls back to the
   previous step tactic. Every step is still a kernel-checked term over the same semantics.
3. **No auxiliary declarations inside proofs**. `kernel_rfl`, `kernel_decide` and the
   tactics' internal decides now assign the proof term inline. Previously each one added a
   declaration, and that made the file's parallel proof elaboration wait on the kernel.
4. **Parallel elaboration**. Lean checks the theorems of one module one after another in the
   kernel, and a definition placed after a theorem waits for that theorem's kernel check. So:
   - modules were split along what their importers use (`LowGas/Certify`, `SharesBase`,
     `SharesRep`, `StringsCommon`, `Strings{Code,CodeShort,CodeLong,Vault}`, `EventsTransfer`,
     `DepositInternal`, `Invariants/Calldata`, `ERC20/SpecView`, `Nested/Domain`);
   - imports were reduced to what each module needs, so independent chains build side by side;
   - definitions were placed before proofs;
   - per-opcode case analyses (`exec_bump_wp`, `exec_setDepth_wp`, `exec_frame`,
     `execCall_frame`) were split into group lemmas, and the original theorems dispatch to
     them.
   All of this is namespace-preserving: every theorem keeps its name and statement.

## Soundness checks (final tree)

- `git diff main -- EvmLean` is empty.
- Statement dump: 3528 theorems before, 3635 after. 0 changed, 0 missing (no lemma deleted).
  The 107 new theorems are the code-table, fast-stepper and group lemmas. The 267 headline
  statements pretty-print identically.
- Axiom scan over all 4126 project theorems (4019 at baseline): each one uses exactly the
  axioms it used before, and the union is `{propext, Classical.choice, Quot.sound}`.
- `scripts/check-trust.sh` passes. Both packages build with `--wfail`.
- `lake exe conform --threads 11 tests/fixtures` gives 22,334 passed / 0 failed. That is
  BlockchainTests 22,332 / 0, the same set as `main`, plus 2 EIPTests examples.
- `cd qedefi && lake exe difftest --seed 3 --sequences 10 --length 30` gives 0 mismatching
  sequences (630 transactions).

## Low-hanging fruit (branch `perf/lowhang`)

Clean `scripts/bench-build.sh` run, same machine, after four changes:

| | before | after |
|---|---:|---:|
| `QEDefi Examples` wall | 171.3 s (199 s in a contended run the same day) | **129.3 s** |
| `QEDefi Examples` CPU (user) | 1195 s (1332 s contended) | 1079 s |
| sum of `QEDefi`/`Examples` module times | 1653 s (contended run) | 1204 s |
| longest module chain in the `qedefi` phase | ≈ 180 s | 117 s |
| `EvmLogic` wall / CPU (unchanged code) | 50.1 s / 247 s | 51.2 s / 247 s |

1. **Per-file Mathlib imports.** `QEDefi.Math.Arith` and `QEDefi.ERC4626.Inflation` imported all
   of Mathlib, so every `QEDefi`/`Examples` module loaded it. Each module-system file now imports
   the Mathlib modules its declarations reference (from a dump of the constants each module
   uses, reduced along Mathlib's import graph) and the tactic frontends it calls; the
   non-module example files get the four remaining modules through `Examples.MathlibDeps`.
   Loading the imports of a module went from 3.3–4.4 s to 1.0–1.5 s (e.g. `Arith` 3.31 → 0.96 s,
   `ERC20.Approve` 4.37 → 1.52 s, `ERC4626.EventsEntry` 4.44 → 1.50 s; measured alone).
2. **Shorter chains.** Example imports were reduced to the modules whose constants they use
   (keeping their `EvmLogic` imports for tactics), and the few early definitions importers needed
   were moved earlier, namespaces unchanged (`sharesOf`, `FmpAfterTransfer` → `Convert`;
   `ApproveOk` → `SpecView`; `TransferAllowances` → `TransferFrom`; `allowanceSlot_solmate` →
   `BalanceOf`; `Deployed.asset_ne` → `Abstraction`). The ERC-20 refinement and event modules no
   longer wait for the vault's views (`SolmateVault` → … → `Views` → `Abstraction`), `Approve`
   no longer waits for `transfer`/`transferFrom`, `DepositInternal` no longer waits for
   `safeTransferFrom`, and `Deposit` no longer waits for `Withdraw`. Each generated contract is
   split into `<Name>Data` (bytes, immutables, selectors, layout) and `<Name>` (sizes, code
   table, deployment theorem), so `Deploy`, `SharesRep`, `Nested.Domain`, `LowGas.Certify` and
   the tests do not wait for the code table. The longest chain is now
   `SolmateAssetData` 6 → `SolmateAsset` 4 → `BalanceOf` 4 → `TransferFrom` 38 →
   `EventsTransfer` 30 → `EventsInternal` 21 → `EventsEntry` 10 → `Invariants.Events` 2 s
   (117 s); the events, `EventsSharesCode` and `LowGas` chains are within 11 s of it.
3. **Tests out of the proof build**: `QEDefiTest` (see Method).
4. **Lake noise.** `qedefi/lake-manifest.json` already used the lakefile's `https` URLs. The
   `remote URL changed` lines come from a global `url.ssh://git@github.com/.insteadOf
   https://github.com/` git setting, which makes the package clones report `ssh` URLs; nothing in
   the repository changes that.

The contributions were not measured separately (one clean build). Statement dump: 3640
theorems before, 0 missing, 0 statement changes, 0 axiom changes; one new auto-generated lemma
(`Finsupp.equivFunOnFinite.congr_simp`, generated locally now that its Mathlib module is not
loaded).

## Limits

- Each module that imports Mathlib pays about 1–1.5 s to load its imports (4.5 s before the
  per-file imports).
- The kernel checks the theorems of one module sequentially. Files whose kernel time is
  20–30 s (`SharesCode`, `SharesFrame`, `LowGas/Certify`, `Basic/TwoContracts`) would need
  further splitting.
- Single proofs such as `assetLongTail_wp` (16 s of elaboration) would need block summaries.
- The `EvmLogic` build is bound by a chain of large case analyses over 84 opcodes, which is
  why it gained only 1.6×.
