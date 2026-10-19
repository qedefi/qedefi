# evm-lean

An executable, proof-grade formal semantics of the Ethereum Virtual Machine in Lean 4.

- Pure Lean (core + Std): no Mathlib, no FFI, no Python, no `opaque`, no `partial`.
- What the conformance tests run is exactly what the kernel reasons about.
- Cryptography is a parameter (`Crypto`): theorems quantify over it; tests use `Crypto.real`.
- Cancun first; Prague and Osaka are designed in.

See `DESIGN.md` for the architecture, `CONVENTIONS.md` for Lean style, `AGENTS.md` for
the development workflow.
