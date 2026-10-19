# Lean conventions for evm-lean

Distilled from Lean core/Std, the Mathlib style and naming guides, Cedar-Lean's GUIDE and
LNSym, and checked against Lean v4.35.0.

## Naming
- Types, structures, inductives, classes, `Prop`-valued defs: `UpperCamelCase`.
- Functions, fields, constructors: `lowerCamelCase`. Opcode constructors are lower-cased
  mnemonics (`Opcode.sstore`); keywords are escaped (`Opcode.«return»`).
- Theorems: `snake_case`, named after the conclusion: `size_readPadded`, `get_set_self`,
  `step_add`, `foo_of_bar`, `foo_iff_bar`.
- Use namespaces and dot notation: `Memory.read`, `World.transfer`, `Word.smod`.
  Inside `namespace Word`, `x.f` resolves to `Word.f` first, so call clashing `BitVec`
  operations as `BitVec.f x y`.
- `protected` for names that clash with root or core names; `private` for helpers.

## Definitions
- `abbrev` only for genuine aliases (`Word`, `Address`, `Storage`, `World`). Semantics
  uses `def`, with unfolding/`@[simp]` lemmas where proofs need them.
- No `partial`. Use structural recursion where possible (it reduces in the kernel, so
  `decide`/`rfl` work); otherwise `termination_by` + `decreasing_by omega`. If something
  must reduce in the kernel and wf-recursion gets in the way, use explicit structural fuel
  that provably suffices, e.g. `fuel := code.size + 1`.
- Total accessors only: `if h : i < a.size then a[i] else 0`, `a[i]?.getD 0`, `m.getD k 0`.
  Never `a[i]!`, `get!`, `head!`, `panic!`.
- Match exhaustively on `Opcode`, `Fork` and other enums. No `_ =>` catch-all over
  constructors whose set may grow.
- Errors are data: `Option`, `Except ε`, explicit result constructors. Never `default` as an
  error stand-in.
- Prefer pure functions (`State → Except Halt State`) or `StateT σ (Except ε)` in the spec.
  Proofs unfold with `simp only [bind, …]` + `split`; `fun_induction` / `fun_cases` work on
  generated induction principles.

## Words and bytes (Lean core facts that bite)
- `x % 0 = x` and `x.srem 0 = x` for `BitVec`: the EVM needs `0`. Use `Word.mod`/`Word.smod`.
- `BitVec.smod` is floor-mod (sign of the divisor): never use it for `SMOD`.
- `x <<< n` with a huge `n : Nat` panics at runtime. Clamp (`Word.shl`), or shift by a
  `BitVec` amount (`x >>> s`, `x.sshiftRight' s`), which is safe.
- Never `^` on words or large `Nat` exponents: use `Nat.powMod` (kernel square-and-multiply).
- `bv_decide` (import `Std.Tactic.BVDecide`) is great for bitwise/add/compare goals, too
  slow for 256-bit `*` and `/`. `bv_omega` / `grind` cover linear `toNat` reasoning.
- `ByteArray` has `DecidableEq` and decent lemmas (`size_extract`, `getElem_extract`,
  `size_append`, `copySlice_eq_append`); fall back to `.data : Array UInt8`. It has no `Repr`,
  so write hex `Repr`/`ToString` where needed.

## Maps
- `Std.ExtTreeMap … compare` everywhere: it is extensional (`ext_getElem?`) and has
  `DecidableEq`. Nest maps instead of using pair keys (no global `Ord (α × β)`).
- Keep storage canonical: zero values are never stored.

## Docs
- Every file starts with a `/-! # Title … -/` module doc that explains the design.
- Every public declaration has a `/-- … -/` docstring (`linter.missingDocs` is on). Cite the
  reference function, e.g. "Mirrors `generic_call` in `cancun/vm/instructions/system.py`."
- Comments explain *why*, not *what*.

## Simp and grind hygiene
- `@[simp]` only on lemmas whose left side is in simp normal form and whose right side is
  simpler. Use `simp only [...]` in proofs, except as a terminal tactic.
- `@[grind]` annotations sparingly.

## Tests
- `#guard` for executable checks, `example … := by decide +kernel` (or `rfl`) for kernel
  checks. Plain `decide` uses the elaborator's reducer and can hang on `ByteArray` code,
  `#guard_msgs in #eval` for printed output. One test file per module in `EvmLeanTest/`.
- Use official vectors: NIST/FIPS, EIP test cases, go-ethereum precompile JSONs, c-kzg vectors.

## Trust
- Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`. Nothing else (`#print axioms`).
- Banned: `sorry` (in finished code), `axiom`, `opaque`, `partial`, `unsafe`, `@[extern]`,
  `@[implemented_by]`, `native_decide`, `IO` in the semantics.
