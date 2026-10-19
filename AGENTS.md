# Working on evm-lean (for humans and AI agents)

Read `DESIGN.md` (architecture, principles, ownership) and `CONVENTIONS.md` (Lean style)
before writing code.

## Toolchain

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build EvmLean                 # the semantics
lake build EvmLeanTest             # unit tests (#guard), also `lake test`
lake build EvmLeanProofs           # kernel-checked theorems
lake exe conform tests/fixtures    # conformance suite (after scripts/fetch-fixtures.sh)
```

Lean `v4.35.0`, core + Std only. Do not add dependencies.

## Rules

- Stay inside the files you own (see `DESIGN.md`). You may add new files under your own
  modules. Shared root files (`EvmLean.lean`, `EvmLeanTest.lean`) may only gain `import` lines.
- Interfaces listed in `DESIGN.md` are frozen. If one is wrong, say so in your report
  instead of changing it.
- Before you finish, all of these must hold for your files:
  - No `sorry`.
  - No `opaque`, `partial`, `@[extern]`, `@[implemented_by]`, `unsafe`, `axiom`,
    `native_decide`, `panic!`, `!`-indexing, `get!`, `.get!`, `head!`, `getLast!`.
  - `lake build EvmLean EvmLeanTest` is green, with no warnings in your files.
- Every definition has a docstring. Every module starts with a `/-! … -/` doc.
- Tests live in `EvmLeanTest/<Module>.lean` as `#guard` checks, using official test
  vectors where they exist.
- Reference implementation: `ethereum/execution-specs`, checked out read-only at
  `../_refs/execution-specs` (Cancun: `src/ethereum/forks/cancun/`).
- Commit early and often on your branch.
