---
name: lean-evm
description: How to write, debug and speed up Lean proofs in this repo (evm-lean / qedefi). Use for any edit to .lean files, new proofs about EVM bytecode or DeFi models, build failures, slow files, or refactors that must not change theorem statements.
---

# Lean work in evm-lean

Two Lake packages: the root `evm-lean` (core + Std: `EvmLean` semantics, `EvmLogic` proof
library, `EvmTest`, `Conformance`) and `qedefi/` (Mathlib v4.35.0 + evm-lean: `QEDefi` models,
`Examples` incl. the Solmate verification, `QEDefiTest`). Toolchain:
`export PATH="$HOME/.elan/bin:$PATH"`. Background: `docs/proving.md`, `docs/conventions.md`, `CONTRIBUTING.md`.

## Interactive first: the `lean-lsp` MCP tools

Prefer these over builds. They keep the file elaborated and answer in seconds.

| Need | Tool |
|---|---|
| Errors of one file, no build | `lean_diagnostic_messages` |
| Goal at a line / term | `lean_goal`, `lean_term_goal` |
| Try several tactics at once | `lean_multi_attempt` |
| Find a name in this repo | `lean_local_search` (do this before guessing a lemma name) |
| Find a Mathlib/core lemma | `lean_loogle` (by type shape), `lean_leansearch` (natural language) |
| Type / docs of a constant | `lean_hover_info` |
| What is slow in a proof | `lean_profile_proof` |

Don't use `lean_build`: it runs whole-package builds.

Without the MCP: `lake env lean <file>` from the package directory that owns the file
(`qedefi/` for `qedefi/...`). It re-elaborates the whole file, so batch edits.

## Build discipline

- Incremental only: `lake build <Module>` for what you changed; never delete `.lake/build`
  unless you are taking a deliberate clean measurement (`scripts/bench-build.sh`).
- Clean builds: root about 1 min, `qedefi` about 2 min. Run anything over 2 minutes in the
  background. Run at most one heavy build at a time; side work uses `nice -n 19`.
- Parallel agents: one git worktree each (`git worktree add -b <branch> <path> main`), then
  clone the caches with `cp -cR .lake <wt>/.lake && cp -cR qedefi/.lake <wt>/qedefi/.lake`
  (copy-on-write on APFS, so instant; builds stay incremental). Use a scratch folder named after
  the task, never a shared `brief.md` or `bench/`.
- Generated files (`*/Contracts/*.lean`): edit `scripts/build-contracts.sh`, then
  `scripts/build-contracts.sh --check`.

## Trust rules (non-negotiable)

- Never: `sorry`, `axiom`, `native_decide`, `bv_decide` (adds `Lean.ofReduceBool`),
  `@[implemented_by]`/`@[extern]`/`opaque`/`partial`/`unsafe` in `EvmLean`, `debug.skipKernelTC`
  or anything that skips the kernel. Never weaken a statement to make a proof go through.
- `EvmLean/` (the semantics) only changes deliberately, then re-run conformance.
- Checks: `scripts/check-trust.sh`; statement identity with
  `scripts/dump-statements.sh before.tsv` … `scripts/dump-statements.sh after.tsv` and
  `scripts/compare-statements.py before.tsv after.tsv` (0 missing, 0 changed, 0 axiom changes);
  comment-only edits with `scripts/check-comment-only.py <base> <paths>`.

## Pitfalls seen repeatedly (with fixes)

- **`decide` hangs** on ByteArray/interpreter terms (it uses the elaborator's reducer). Use
  `decide +kernel`, or `kernel_decide`/`kernel_rfl` when free variables are present but not
  inspected. Plain `rfl` on whole-program runs hits recursion depth or heartbeats.
- **Max recursion / heartbeats**: don't raise limits first. Use the step tactics, block
  summaries (`FunctionSummary`, `WP.call` callee summaries), and code tables. Never `subst` a
  `validJumpDests` of large code: use `wp_intro` (keeps a `JumpTable` hypothesis).
- **Code facts**: read bytes via the contract's `code_table` (`table_decide`, `codeFact`,
  `pcode_fact`), not by deciding on `ByteArray` literals. Compare code via `.data.toList`.
- **Unknown identifier**: search (`lean_local_search`, `lean_loogle`) instead of guessing.
  Inside `namespace Word`, `x.f` resolves to `Word.f` first: write `BitVec.f x y`.
- **Mathlib quirks**: `to` is a keyword (name recipients `dst`); import only what the file
  uses (`#min_imports`), never `import Mathlib` (4.8 s per importing module vs ~1.2 s).
- **`omega`** can hit recursion limits on `(n - k) * c`: write `c * (n - k)`.
- **Slow modules**: the kernel checks one module's theorems sequentially, and a definition
  after a theorem waits for that theorem's check. Put definitions first; split large files;
  import only what is needed so chains build in parallel. Profile with
  `scripts/profile-file.sh <file>`.
- **Shell**: in zsh quote globs (`grep --include='*.lean'`).

## Where things are (EvmLogic)

| Area | Module(s) |
|---|---|
| Per-opcode step lemmas | `EvmLogic/Step/*` |
| WP / `Halts` / `Triple`, run composition | `Program/Logic`, `Program/Run` |
| Calls, callee summaries, precompiles | `Program/Call`, `Program/PrecompileCall` |
| Function summaries, blocks | `Program/Summary`, `Program/Block` |
| Code tables | `Program/Code`, `Program/CodeTable` |
| Nested-call simulation | `Program/Nested/*` |
| Solidity: layout, keccak freshness, ABI, dispatch, immutables, strings, ERC-20 view | `Solidity/*` |
| Gas lockstep (low-gas frames) | `GasMono/*` |
| Certified abstract interpretation (call targets) | `AbsInt/*` |

Tactics: `evm_step(s)` (generic), `sol_step(s)`/`sol_dispatch` (literal code),
`psol_step(s)`/`psol_dispatch`/`pwp_step(s)`/`pwp_run_to` (patched code with symbolic
immutables), `pwp_msteps`/`psol_msteps` (with `MCOPY`), `wp_intro`/`wp_step(s)`/`wp_run_to`/
`wp_finish`/`wp_generalize_gas` (frame WP), `fails_steps` (revert/OOG paths), `kernel_rfl`/
`kernel_decide`, `evm_gas`/`evm_norm`. Worked examples: `qedefi/Examples/Basic/*`, then
`Examples/Solmate/ERC20/Transfer.lean`.
