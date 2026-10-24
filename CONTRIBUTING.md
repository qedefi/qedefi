# Contributing

Contributions of every size are welcome: a new verified contract, a lemma that shortens a proof,
a faster tactic, a conformance fix, a correction to the docs. Open an issue first for anything
that changes `EvmLean` (the semantics) or one of the stable interfaces listed in
[docs/conventions.md](docs/conventions.md#organisation).

## Setup

```bash
lake build && lake test                                   # root package (about a minute)
(cd qedefi && lake exe cache get && lake build && lake test)
```

The toolchain (Lean v4.35.0) is pinned in `lean-toolchain`; the root package uses core + Std only,
`qedefi/` adds Mathlib v4.35.0. Do not add dependencies. Builds are incremental: build the module
you changed (`lake build EvmLogic.Program.Call`, from the package that owns it).

Editors and agents get goals, per-file diagnostics and name search without builds from the
[`lean-lsp-mcp`](https://github.com/oOo0oOo/lean-lsp-mcp) server configured in `.mcp.json` (needs
[`uv`](https://docs.astral.sh/uv/)). `.claude/skills/lean-evm/SKILL.md` collects the workflow and
the pitfalls that come up most often; it is written for AI agents but reads as a checklist.

## Before opening a pull request

- `lake build` and `lake test` pass with no warnings in your files (CI builds both packages with
  `--wfail`); also `(cd qedefi && lake build)` if you touched `EvmLogic` or `qedefi/`.
- `scripts/check-trust.sh` passes: no `sorry`, `axiom`, `native_decide`, `bv_decide` or
  kernel-skipping option anywhere, and none of the escape hatches listed in
  [docs/conventions.md](docs/conventions.md#trust-rules) in `EvmLean/`.
- Refactors keep every statement: `scripts/dump-statements.sh before.tsv` on the base,
  `scripts/dump-statements.sh after.tsv` on your branch, then
  `scripts/compare-statements.py before.tsv after.tsv` (0 missing, 0 changed, 0 axiom changes).
  A theorem statement is never weakened to make a proof go through.
- Documentation-only edits to Lean files: `scripts/check-comment-only.py <base-rev> [paths…]`.
- Changes under `contracts/` or to generated `Contracts` modules:
  `scripts/build-contracts.sh --check` (needs solc 0.8.28 and Foundry).
- Changes to `EvmLean/`: rerun conformance (`lake exe conform`) and the differential tester.

Commits: an imperative summary line, a body explaining why. Style, naming and file organisation
are in [docs/conventions.md](docs/conventions.md).

## Adding a verified contract

The Solmate vault (`qedefi/Examples/Solmate/`) and the proxy guard
(`qedefi/Examples/Actor/Bytecode/`) are the templates.

1. **Pin the code** ([contracts/README.md](contracts/README.md)). A compiled target: vendor its
   sources unmodified under `contracts/lib/` (or write a wrapper in `contracts/src/`), import it
   from `contracts/src/Targets.sol`, and add it to `scripts/build-contracts.sh`. A deployed
   target: `scripts/fetch-mainnet.sh <Name> <address>`, then hand-write `storageLayout.json` and
   `genesis.json`. Either way the build script generates
   `qedefi/Examples/<Project>/Contracts/<Name>.lean` with the code as a kernel-reducible literal.
2. **Check the semantics agree** before proving anything: add a `difftest` family
   (`qedefi/Examples/Differential/`) and run it against anvil.
3. **Pick or write the model.** Reuse `QEDefi.ERC20.Token` or a `QEDefi.ERC20.Variant`
   instance, the `QEDefi.ERC4626` vaults, or the `QEDefi.Actor` components; anything
   contract-independent goes into `QEDefi`, with its properties proved there.
4. **Refine call by call**: a `WP`/`Halts` summary per external function, by symbolic execution
   of the bytecode ([docs/proving.md](docs/proving.md)). Summaries about any frame double as
   callee summaries for contracts that call this one.
5. **Lift**: `QEDefi.Trace.Lift` for sequences of top-level calls, `EvmLogic.Program.Nested` for
   arbitrary transactions, `EvmLogic.Program.Reentrancy` for contracts that call untrusted code,
   `EvmLogic.GasMono` and `EvmLogic.AbsInt` for any gas and depth,
   `EvmLogic.Program.Nested.Guard` for who-can statements over several contracts, and
   `QEDefi.Trace.Time` for time-dependent contracts across blocks.
6. **Document** the headline theorems and every hypothesis: a row in the README's table and a
   section in the relevant document under `docs/`.

## Open problems

Each of these is a self-contained piece of work; the documents linked give the details.

- **Token bytecode refinements** against their `Variant` instances, including the
  `INVALID`/`REVERT` distinction and empty return data: USDT, BNB, STA, AMPL, Solady, WETH9
  beyond `withdraw`, and models for GUSD, YAMv2, LEND, ZRX
  ([docs/tokens.md](docs/tokens.md#open-work)).
- **`StakingRewards` on bytecode**: the model and its solvency and no-dilution theorems are in
  `QEDefi.Staking`.
- **OpenZeppelin `ERC4626` on bytecode**, written once with the decimals offset symbolic and
  instantiated for δ = 0 and δ = 3, so that the model's inflation bounds transfer.
- **OpenZeppelin `ERC20`, the rest**: revert data, calls with value, `name`/`symbol`, malformed
  calldata, arbitrary callers.
- **Vaults over real assets on bytecode**: the integration theorems
  (`QEDefi.ERC4626.Integration`) with USDT, STA or AMPL bytecode as the vault's asset.
- **Actor model to bytecode**: every capability a transaction exercises is derivable from its
  keys, for multi-contract systems ([docs/actor-bytecode.md](docs/actor-bytecode.md#7-connecting-to-qedefiactorderives)).
- **Safe with modules and guards**, and contract owners as further relays.
- **Proxies** (USDC, UUPS, beacons): a `WP.delegatecall` callee-summary rule and the proxy's
  dispatch theorem.
- **Snapshots**: evaluate the actor configuration from fetched chain state and report who
  controls each effect of a deployed system at a block.
- **The transaction layer**: prove, rather than state, that nonce, gas purchase and refund
  change no storage of the contracts involved.
- **Proof performance**: block summaries for the slowest single proofs, splitting the files
  whose kernel check dominates ([docs/proving.md](docs/proving.md#proof-performance)).

## License

By contributing you agree that your contributions are licensed under the Apache License 2.0
([LICENSE](LICENSE)).
