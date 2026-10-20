# Proving things about bytecode with EvmLogic

`EvmLogic` is a generic proof library over the `EvmLean` semantics. Every execution theorem
in it holds for an **arbitrary `Crypto`** and every fork unless stated, and depends only on
`propext`, `Classical.choice`, `Quot.sound`. Worked examples are in
`defi/Examples/Basic/`:

| Example | Shows |
|---|---|
| `AddStore.lean` | `kernel_rfl` and `evm_steps` on tiny programs (`addStore_slot0`, `ret42_output`) |
| `Token.lean` | a hand-assembled token `transfer` with symbolic caller, amounts, balances, gas (`transfer_ok`, `transfer_spec`) |
| `Sum.lean` | a solc loop with the loop rule (`loop`, `sum_halts`, `sum_processMessageCall`) |
| `TwoContracts.lean` | a call through a separately proved callee summary (`getSummary`, `f_halts`) |
| `VaultTotalSupply.lean` | `wp_steps` on 5 kB of real solc output (`totalSupply_halts`) |
| `Mcopy.lean` | `MCOPY` in the symbolic executors (`copy42_output`, `copy42_wp`) |

## 1. Concrete runs: kernel evaluation

When inputs are concrete and the free variables (typically `crypto`) are never inspected by
the run, let the kernel evaluate it:

```lean
theorem addStore_slot0 (crypto : Crypto) :
    (result crypto).map (fun r => (r.success, r.world.sload contract 0)) = some (true, 5) := by
  kernel_rfl
```

`kernel_rfl` / `kernel_decide` abstract the local context into an auxiliary theorem checked
**only by the kernel**. Do not use plain `rfl` or `decide`: they check definitional equality
in the elaborator (`Meta.isDefEq`/`whnf`), which does not finish on a whole-program run (over
150 s even for `Crypto.real`); `decide +kernel` is fast but refuses free variables. Prefer
`kernel_decide` when both sides only meet after evaluating to numbers (gas arithmetic):
`kernel_rfl`'s lazy unfolding of `Nat.sub` can recurse too deeply. If the run *does* inspect
a free variable (a `JUMPI` on a symbolic value), the kernel gets stuck and reports a type
mismatch: switch to symbolic execution.

## 2. Symbolic execution with step lemmas

`EvmLogic/Step/` has one lemma per instruction, `step_<mnemonic>` (`_of_<cond>` for
conditional variants, `_top` for top-level halting). Hypotheses come in a fixed order the
tactics rely on: `hcode : m.frame.code[m.frame.pc]? = some <byte>` first (fails fast for the
wrong opcode), then `hstk : m.frame.stack = x :: y :: rest` (operands become unification
variables), then side conditions (stack bound, `hstatic`, valid jump, `hgas`). The conclusion
is `step m = .running { m with … }` (or `.done …` / `finishFrame …`) with the exact gas.

| Module | Contents |
|---|---|
| `Step.Basic` | `step_of_binOp`/`unOp`/`ternOp`/`pushValue`, `run_succ_of_running`, `run_succ_of_done`, `processMessageCall_eq_run`, `initMachine_call` |
| `Step.Arith`, `Stack`, `Push`, `Env`, `Log` | arithmetic, `PUSH`/`DUP`/`SWAP`/`POP`, environment opcodes, `LOG0`–`LOG4` |
| `Step.Memory`, `Storage`, `Flow` | `MLOAD`/`MSTORE`/`KECCAK256`, `SLOAD`/`SSTORE` (+ `sloadCost_le`, `sstoreCost_le`), jumps and halts, `topLevelResult_*` |
| `Bytes`, `State`, `Word` | calldata decoding, memory read/write, `World.sload_sstore*`, balances, word facts (`Word.lt_eq_zero_iff`, …) |

A top-level proof has this shape (`Examples/Basic/Token.lean`):

```lean
  rw [processMessageCall_transfer hdeleg hpre]  -- 1. reduce to `run fuel m₀` (processMessageCall_eq_run)
  simp only [start, Frame.init, transferCall]    -- 2. make m₀ a machine literal
  evm_steps [calldata_to, calldata_amount]       -- 3. execute up to a symbolic JUMPI
  have hlt : Word.lt (w.sload token (Word.ofAddress caller)) amount = 0 := …
  simp only [hlt]                                -- 4. decide the branch
  evm_steps [calldata_to, calldata_amount]       -- 5. execute to STOP
  refine ⟨_, rfl, ?_, ?_⟩                        -- 6. read off the result
```

`evm_steps [h, …]` repeats `evm_step`: rewrite `run (n + 1) m` with `run_succ_of_running`,
prove the `step` equation with the first step lemma whose side conditions `evm_disch`
discharges, and normalize with `evm_norm` (literal code bytes via the `reduceByteArrayGetElem`
simproc, numerals, gas constants, memory costs, warm sets, plus the given lemmas). Fuel must
be `k + n` with `n` at least the number of steps. `evm_gas` closes gas goals with symbolic
`SLOAD`/`SSTORE` costs; give theorems a generous gas lower bound. Top-level call theorems
need `ctx.fork < .prague ∨ ctx.tx.authorizations = []` (EIP-7702).

**Tactic families.** All share the step lemmas; pick by goal shape and code:

| Goal | Small literal code | Compiled code (literal) | Code with symbolic immutables |
|---|---|---|---|
| `run (k + n) m = …` | `evm_step(s)` | `sol_step(s)` | `psol_step(s)` |
| `WP m Q H` (frame-local) | `wp_step(s)`, `wp_run_to`, `wp_intro` | `wp_steps` with code facts | `pwp_step(s)`, `pwp_run_to` |
| with `MCOPY` | | `psol_msteps` | `pwp_msteps` |

`sol_step` reads the opcode at `pc` itself and discharges code bytes, `PUSH` immediates
(`reduceCodeImm`) and jump destinations by `decide +kernel` on list scans
(`EvmLogic/Solidity/JumpDest.lean`), never by evaluating `validJumpDests` on a 5 kB
`ByteArray`. `psol_step`/`pwp_step` handle `patchWords base ps` code (`runtimeCodeWith i`):
bytes outside the patched windows come from the literal `base` (`reducePatchedRead`), jump
destinations from a `JumpDestsAgree code base` hypothesis in context; reads inside a patch
(an immutable being pushed) need a per-contract lemma passed as `pwp_steps [h]`.
`EvmLogic/Program/Code.lean` provides kernel-checked code facts (`codeFact`, `kernelFact`,
`jdCheck`) so the elaborator never evaluates large code. To extend the search:
``macro_rules | `(tactic| evm_step_core) => `(tactic| evm_apply my_step_lemma)``.

## 3. The frame-local logic: `WP`, `Halts`, `Triple`

Because the machine has an explicit call stack, `EvmLogic/Program/Logic.lean` reasons about
**one frame** at a time:

- `SameFrame m m'`: `m'` still executes `m`'s frame (same parents, message, code, snapshot);
- `Halts m H`: the frame of `m` finishes with outcome `o` at machine `mf`, `H mf o`;
- `WP m Q H`: either reach `Q` in the same frame, or finish satisfying `H`;
  `Triple P Q H := ∀ m, P m → WP m Q H`.

All are total-correctness statements. `WP.bind` sequences, `WP.mono` weakens, `WP.loop` (a
measure) and `WP.loop_nat` (a counter) are loop rules, `Halts.run` turns a top-level `Halts`
into a `run` result, and `processMessageCall_of_halts` (`Program/Summary.lean`) turns a frame
summary into a `processMessageCall` theorem. A `Halts` statement about *any* machine whose
frame has the right shape (any parents, depth, world, `Crypto`) serves both as a top-level
theorem and as a callee summary.

**Loops** (`Examples/Basic/Sum.lean`): state the invariant at the loop head with the
iteration counter, prove one iteration with `wp_run_to <head>`, close with `WP.loop_nat`. Gas
is part of the invariant (`55 (n - k) + 26` in the example).

**Function summaries.** `FunctionSummary code` (`Program/Summary.lean`) splits an external
function as solc compiles it: `dispatch` (from a `Fresh` frame to the body's `entry` pc) and
`body` (from `entry` to the end of the frame). `FunctionSummary.halts` glues them; internal
functions are summarised as `WP` statements from their entry pc with the return address on
the stack and composed with `WP.bind_mono` (`Machine.resumeAt`/`resumeWith` describe the
return).

**Calls** (`Program/Call.lean`). `step_call`, `step_staticcall`, `step_delegatecall` push the
child with the exact charges (`callCost`: access cost, all-but-1/64, stipend, memory).
`WP.call` / `WP.staticcall` are the callee-summary rules: given `Halts` of the fresh child
frame (e.g. a `FunctionSummary` of the callee), the caller continues from
`resumeAfter_success` / `_revert` / `_halt` (flag pushed, output copied, unused gas returned,
world or snapshot, logs merged on success). Precompile calls run within one step
(`Program/PrecompileCall.lean`: `WP.staticcall_precompile`, and `WP.staticcall_ecrecover` for
solc's `ecrecover`). See `Examples/Basic/TwoContracts.lean`.

## 4. The Solidity layer (`EvmLogic/Solidity/`)

- **Layout** (`Layout.lean`): `Field` (packed value types, `get`/`set`/`read`/`write`),
  `mappingSlot` (`keccak(pad(k) ‖ pad(p))`), `mappingSlot2` (nested), `arraySlot`. Slots use
  the context's `crypto.keccak256`, so everything holds for every `Crypto`.
- **Keccak freshness** (`Keccak.lean`). Global injectivity of Keccak is false for every
  `Crypto` (pigeonhole), so it is **never** assumed. Hypotheses are about the specific
  preimages a theorem touches: `KeccakFresh crypto S x` (no other preimage in `S` hashes to
  `keccak x`: one target against a large candidate set, plausible),
  `KeccakAvoids crypto S fixed` (no preimage in `S` hits a fixed slot), over sets like
  `AddressKeyed [3]` (all `pad(a) ‖ 3`). Reading needs no hypothesis; only writes do.
- **ERC-20 view** (`ERC20.lean`): `ERC20.view crypto L w token` reads `totalSupply`,
  `balanceOf`, `allowance` through a `Layout` (`Layout.solmate`); `view_sstore_balanceSlot`
  updates it pointwise under `BalanceSlotOk` (the slot is fresh among address-keyed rows and
  is not the supply slot); `AllowanceSlotOk` for allowances.
- **ABI** (`Abi.lean`): selectors are literal numbers from the compiler output, never computed
  with `crypto`; `encodeCall`, `size_encodeCall`, `calldataload_encodeCall`,
  `shr_calldataload_zero`. Strings: `Abi.encodeString`, `stringAt` (`Strings.lean`).
- **Dispatch** (`Dispatch.lean`): `Reaches code sel entry n cost` packages solc's
  dispatcher as a rewrite rule for every machine; proved per selector by `sol_dispatch` /
  `psol_dispatch`.
- **Immutables** (`Immutables.lean`): `patchWords`, `ImmutableRef`; generated contract modules
  expose `runtimeCodeWith i` so theorems hold for every deployment.
- **Events** (`Events.lean`): `eventLog`, logs through child calls, and
  `processMessageCall_logs_of_fail` (a failed top-level result has no logs, for any code).

## 5. Arbitrary callers: the nested simulation (`EvmLogic/Program/Nested/`)

To prove that protected accounts `P` keep a storage property `Good` under *any* transaction:
`exec_frame` is the frame condition of every opcode (a frame writes storage only of its own
non-static account; `CREATE` only deploys at code-less accounts); the invariant `MInv` holds
of machines whose executing frame is not *dangerous* (non-static at a protected account), and
every rollback snapshot is `Good`, so a revert of any enclosing frame restores a `Good` world.
`minv_step`, `run_good` and `processMessageCall_good` reduce the whole transaction to frame
summaries of the dangerous frames (`DangerStart`). `step_gas`/`stepN_gas`: the stack's total
gas never increases.

## 6. Gas monotonicity and abstract interpretation

**`EvmLogic/GasMono/`.** Every instruction except `GAS`, `CALL*`, `CREATE*` commutes with
adding gas (`exec_bump`). `monoFrom_of_code`: under code conditions `CodeOk` — `GasFeedsCall`
(each `GAS` is immediately followed by a call), `RegionOk` (execution stays below the final
`INVALID`), `FailureReverts` at each call return point (a failed call makes the frame fail),
and every child gas-monotone (`CallsTo`) — a frame with less gas fails or ends exactly as with
more. `depth_lockstep`: at depth 1024 a frame runs in lockstep with itself one level up until
its first call fails. The code conditions are decided on a structural instruction scan
(`CodeScan.lean`); failure paths are proved with `Fails` and the `fails_steps` tactic
(`CodeFails.lean`), which absorbs every exceptional halt per instruction shape.

**`EvmLogic/AbsInt/`.** A certified explicit-state abstract interpreter (exact stack depth;
values `top`, `const n` or a symbolic address immutable `sym k`) runs in the kernel
(`decide +kernel` on a worklist over a balanced tree of the scan). `certify_sound` and
`absint_frame`: every machine of a frame up to its exit is described by a recorded abstract
state, giving call targets (`absint_call`) and the absence of `CREATE` (`absint_no_create`)
for all immutables at once.

## Pitfalls

- **No `bv_decide`**: it closes goals through `Lean.ofReduceBool`, an extra axiom. Use
  `bv_omega`, `omega` or `BitVec` lemmas.
- **`rfl` in dischargers only on equalities**: on `a ≤ b` it tries `Nat.le.refl` and unfolds
  symbolic gas; use `exact rfl`. No `simp_all` in dischargers (slow, and it runs per failed
  lemma).
- **`first | … | last`** recovers from errors in its last alternative by admitting the goal;
  end every `first` in a tactic with `fail "…"`.
- **Literal code** must be `⟨#[0x60, …]⟩` in a named constant; a `ByteArray` built otherwise is
  opaque to `reduceByteArrayGetElem`. Compare large code in the kernel via `.data.toList`;
  scan lists, not `Bytes.getD` (each lookup walks the list).
- **`dsimp only` runs no simprocs**: list them (`evm_norm` does).
- **Structure literals** in statements: continuation lines indented less than `{` fail to
  parse; define the machine as a `def … where`.
- **Large contexts**: clear hypotheses mentioning large code (`hcode`) before stepping to a
  `JUMP` with a symbolic target (`assumption` would unfold them); after a call, replace the
  remaining gas by a variable with `wp_generalize_gas` + one `evm_gas`; generalize big
  postconditions (`generalize hQ : (fun m' => …) = Q`) before `pwp_steps`.
- **Memory with symbolic size**: `evm_gas` does not handle it; state each expansion as
  `Gas.memoryCost new - Gas.memoryCost old`, generalize the atoms and let `omega` telescope.
  `omega` can hit the recursion limit on `(n - k) * c`; write `c * (n - k)`.
