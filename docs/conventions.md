# Conventions

Lean style for this repository, distilled from Lean core/Std, the Mathlib style and naming
guides, Cedar-Lean and LNSym. The workflow and the checks to run are in
[CONTRIBUTING.md](../CONTRIBUTING.md).

## Trust rules

- Allowed axioms: `propext`, `Classical.choice`, `Quot.sound` (check with `#print axioms`).
- Everywhere: no `sorry`, `axiom`, `native_decide`, `bv_decide` (it adds `Lean.ofReduceBool`), and
  no option that skips the kernel.
- In the semantics (`EvmLean/`) additionally: no `opaque`, `partial`, `unsafe`, `@[extern]`,
  `@[implemented_by]`, `panic!`, `!`-indexing, `get!`, `.get!`, `head!`, `getLast!`, no `IO`.
- Hash, signature and other cryptographic facts are hypotheses of the theorems that use them,
  stated for finitely many values; never global injectivity
  ([proving.md](proving.md#4-the-solidity-layer-evmlogicsolidity)).

## Organisation

- Namespaces mirror directories. Generic results go to `EvmLogic` (root package) or `QEDefi`;
  anything about a specific contract goes to `qedefi/Verified/<Project>/`, one directory per
  deployed system, its generated code in `Contracts/`. `qedefi/Examples/` is for demos only.
- Root files (`EvmLean.lean`, `EvmLogic.lean`, `EvmTest.lean`, `QEDefi.lean`)
  contain only `import`s and a module doc.
- Stable interfaces: `Crypto` and `Context.crypto`, `Interpreter.processMessageCall`,
  `OutOfFuel`, `createAddress`/`create2Address`, `Precompile.isPrecompile`/`Precompile.run`
  and the hash primitives' signatures. If one is wrong, raise it rather than change it in
  passing.
- Reference implementation: `ethereum/execution-specs` (`src/ethereum/forks/<fork>/`). Cite
  the function mirrored, e.g. "Mirrors `generic_call` in `vm/instructions/system.py`."

## Naming

- Types, structures, inductives, classes, `Prop`-valued defs: `UpperCamelCase`.
- Functions, fields, constructors: `lowerCamelCase`. Opcode constructors are lower-cased
  mnemonics (`Opcode.sstore`); keywords are escaped (`Opcode.«return»`).
- Theorems: `snake_case`, named after the conclusion (`size_readPadded`, `get_set_self`,
  `step_add`, `foo_of_bar`, `foo_iff_bar`).
- Namespaces and dot notation: `Memory.read`, `World.transfer`, `Word.smod`. Inside
  `namespace Word`, `x.f` resolves to `Word.f` first: call clashing `BitVec` operations as
  `BitVec.f x y`. `protected` for names clashing with core; `private` for helpers.

## Definitions

- `abbrev` only for genuine aliases (`Word`, `Address`, `Storage`, `World`); semantics uses
  `def` with unfolding / `@[simp]` lemmas where proofs need them.
- No `partial`. Prefer structural recursion (it reduces in the kernel); otherwise
  `termination_by` + `decreasing_by omega`, or explicit structural fuel that provably
  suffices (`fuel := code.size + 1`) when something must reduce in the kernel.
- Total accessors only: `if h : i < a.size then a[i] else 0`, `a[i]?.getD 0`, `m.getD k 0`.
- Exhaustive matches on `Opcode`, `Fork` and other enums; no `_ =>` over constructors whose
  set may grow.
- Errors are data (`Option`, `Except ε`, explicit result constructors); never `default` as an
  error stand-in.
- Pure functions or `StateT σ (Except ε)`. Proofs unfold with `simp only [bind, …]` + `split`;
  `fun_induction` / `fun_cases` use generated induction principles.

## Words and bytes (core facts that bite)

- `x % 0 = x` and `x.srem 0 = x` for `BitVec`; the EVM needs `0`: use `Word.mod`/`Word.smod`.
- `BitVec.smod` is floor-mod (sign of the divisor): never use it for `SMOD`.
- `x <<< n` with a huge `n : Nat` panics at runtime: clamp (`Word.shl`) or shift by a
  `BitVec` amount.
- No `^` on words or large `Nat` exponents in executable code: use `Nat.powMod`.
- `ByteArray` has `DecidableEq` and lemmas (`size_extract`, `getElem_extract`, `size_append`);
  fall back to `.data : Array UInt8`. It has no `Repr`: write hex `Repr`/`ToString`.

## Maps

- `Std.ExtTreeMap … compare` everywhere (extensional, `DecidableEq`). Nest maps instead of
  pair keys. Keep storage canonical: zero values are never stored.

## Docs and comments

- Every file starts with a `/-! # Title … -/` module doc explaining the design.
- Every public declaration has a `/-- … -/` docstring (`linter.missingDocs` is on in
  `EvmLean`).
- Comments explain *why*, not *what*, and describe the code as it is (no history).

## Simp and grind

- `@[simp]` only on lemmas whose left side is in simp normal form and whose right side is
  simpler; `simp only [...]` in proofs except as a terminal tactic. `@[grind]` sparingly.

## Tests

- `#guard` for executable checks; `example … := by decide +kernel` (or `kernel_rfl`) for
  kernel checks (plain `decide` uses the elaborator and can hang on `ByteArray` code);
  `#guard_msgs in #eval` for printed output. One test file per module in `EvmTest/`
  (`qedefi/QEDefiTest/` in the `qedefi` package, its `lake test`).
- Use official vectors: NIST/FIPS, EIP test cases, go-ethereum precompile JSONs, c-kzg.
