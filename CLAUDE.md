# QEDefi / evm-lean

Proof-grade EVM semantics in Lean 4 (`EvmLean`), a generic proof library (`EvmLogic`), and the
`qedefi/` package (DeFi models plus contracts verified on bytecode, such as Solmate's ERC-4626).
See `README.md`, `CONTRIBUTING.md`, `docs/architecture.md`, `docs/proving.md`,
`docs/conventions.md`.

- For any Lean work, use the `lean-evm` skill (`.claude/skills/lean-evm/SKILL.md`): it covers
  the `lean-lsp` MCP tools, incremental builds, trust rules and known pitfalls.
- Trust base: Lean kernel + `EvmLean` + {propext, Classical.choice, Quot.sound}. Never add
  `sorry`, axioms, `native_decide`, `bv_decide` or kernel-skipping options; never weaken a
  theorem statement. Run `scripts/check-trust.sh` before committing.
- Builds are incremental (`lake build <Module>`); clean builds only for measurements.
