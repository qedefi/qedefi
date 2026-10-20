# EvmLeanProofs: proving things about bytecode

Kernel-checked theorems about the `EvmLean` semantics, and the library for writing them.
Everything here depends only on `propext`, `Classical.choice` and `Quot.sound`, and every
execution theorem is stated for an **arbitrary `Crypto`** (hashes stay uninterpreted).

## Two ways to prove what bytecode does

| Situation | Tool | Cost |
|---|---|---|
| Concrete inputs; free variables (e.g. `crypto`) that the run never inspects | `kernel_rfl` / `kernel_decide` | < 1 s for small programs |
| Symbolic inputs (caller, calldata, balances, gas, warm sets) | `evm_steps` + step lemmas | ~0.3 s per instruction |

### Kernel evaluation with free variables

```lean
theorem addStore_slot0 (crypto : Crypto) :
    (result crypto).map (fun r => (r.success, r.world.sload contract 0)) = some (true, 5) := by
  kernel_rfl
```

`kernel_rfl` (and `kernel_decide`, which evaluates `decide p` instead of comparing both
sides) abstracts the local context into an auxiliary theorem and lets **only the kernel**
check it. If the run does inspect a free variable (a `JUMPI` on a symbolic value, a hash
compared to something), the kernel gets stuck and reports a type mismatch: switch to
symbolic execution.

### Symbolic execution

```lean
theorem transfer_ok … :
    ∃ r, processMessageCall (k + 22) ctx w tr (transferCall token caller to amount gas …) = .ok r ∧
      r.success = true ∧ r.world = transferWorld w token caller to amount := by
  rw [processMessageCall_transfer hdeleg hpre]     -- 1. reduce to `run fuel m₀`
  simp only [start, Frame.init, transferCall]       -- 2. make `m₀` a literal machine
  evm_steps [calldata_to, calldata_amount]          -- 3. execute up to the JUMPI
  have hlt : Word.lt (w.sload token (Word.ofAddress caller)) amount = 0 := …
  simp only [hlt]                                   -- 4. decide the branch
  evm_steps [calldata_to, calldata_amount]          -- 5. execute to STOP
  refine ⟨_, rfl, ?_, ?_⟩                           -- 6. read off the result
  …
```

1. **Start.** `processMessageCall_eq_run` (`Call.lean`) turns a top-level call into
   `run fuel m₀` when EIP-7702 delegation does nothing (`ctx.fork < .prague ∨
   ctx.tx.authorizations = []`) and the code is not a delegation designator;
   `initMachine_call` computes `m₀` for a call to a non-precompile with zero value.
2. **Literal machine.** Unfold `m₀` so the goal shows a `Machine` structure literal with
   the code as a named `ByteArray` literal constant, a numeral `pc` and a list-literal stack.
   Values may be symbolic.
3. **`evm_steps [h₁, …]`** repeats `evm_step`: rewrite `run (n + 1) m` with
   `run_succ_of_running` (or `run_succ_of_done` for `STOP`/`RETURN`/`REVERT`), prove the
   `step` equation with the first step lemma whose side conditions `evm_disch` can discharge,
   then normalize the new machine (`evm_norm`): literal code bytes (`reduceByteArrayGetElem`),
   numerals, gas constants, memory costs, warm-set bookkeeping, and the extra simp lemmas
   `h₁, …` (e.g. what `CALLDATALOAD` returns for the calldata at hand). Fuel must have the
   form `k + n` with `n` at least the number of steps.
4. **Branches.** `evm_steps` stops at a `JUMPI` whose condition is symbolic. Split on the
   condition and rewrite it to `0` (`step_jumpi_of_eq_zero`) or a non-zero numeral
   (`step_jumpi_of_ne_zero`); `Word.lt_eq_zero_iff` etc. (`Word.lean`) help.
5. **Result.** After the halting instruction the goal contains `.ok (topLevelResult …)`;
   `refine ⟨_, rfl, …⟩` and the `topLevelResult_*`, `World.sload_sstore*` and memory lemmas
   finish.

`EvmLeanProofs/Examples/Token.lean` is the worked example (a token `transfer` with symbolic
everything); `Execution.lean` has smaller ones (`addStore`, `ret42`).

## Lemma inventory

| File | Contents |
|---|---|
| `StepBasic` | `step_eq_of_code`, `step_of_exec_*`, generic `step_of_binOp`/`unOp`/`ternOp`/`pushValue`, `run_succ_of_running`, `run_succ_of_done`, `run_add_of_ok`, `readBytes_zero` |
| `StepArith` | `step_add` … `step_sar`, `step_iszero`, `step_not`, `step_addmod`, `step_mulmod`, `step_exp` |
| `StepStack`, `StepPush` | `step_push` (any n), `step_push0/1/2` (immediates evaluated), `step_pop`, `step_dup1..16`, `step_swap1..16`, `decode_push/dup/swap/log` |
| `StepEnv` | `step_caller`, `step_callvalue`, `step_calldataload`, `step_calldatasize`, `step_address`, `step_origin`, `step_gas`, `step_pc`, `step_msize`, block fields, … |
| `StepMemory` | `step_mload`, `step_mstore`, `step_mstore8`, `step_keccak256` (result is `ctx.crypto.keccak256 …`), `Memory.expand_storeWord_self` |
| `StepStorage` | `step_sload`, `step_sstore`, `run_accessStorageKey`, cost bounds `sloadCost_le`, `sstoreCost_le` |
| `StepFlow` | `step_jumpdest`, `step_jump`, `step_jumpi(_of_eq_zero/_of_ne_zero)`, `step_stop(_top)`, `step_return(_top)`, `step_revert(_top)`, `step_invalid`, `finishFrame_*_top`, `topLevelResult_*` |
| `StepLog` | `step_log` (generic), `step_log0..4`, `run_popN` |
| `Bytes` | `toNat_eq_foldl`, `toWord_ofWord`, `toNat_ofNatBE`, calldata decoding (`toWord_readBytes_ofWord_append_left/right`), `Memory.loadWord_storeWord` (all offsets), `Memory.size_storeWord`, disjoint-write lemmas |
| `State` | `Storage.get_set(_self/_ne)`, `World.sload_sstore(_self/_ne_key/_ne_addr)`, `World.balance_transfer`, `balance_add_balance_transfer`, `balance_moveEther`, `storageKeyWarm_addStorageKey`, `addStorageKey_of_warm` |
| `Word` | `mod_zero`, `smod_zero`, `div_zero`, `sdiv_zero`, `toNat_addmod/mulmod`, `toNat_exp` (= `b ^ e % 2²⁵⁶`), `lt_eq_one_iff`, `iszero_eq_one_iff`, `ofAddress_injective`, … |
| `Decode` | `decode_eq_decode_cancun` (fork-independence except `0x1e`), `decode_toByte(_osaka)`, `isValidJumpDest_validJumpDests`, `lt_size_of_isValidJumpDest` |
| `Call` | `applyTopLevelDelegation_eq`, `processMessageCall_eq_run`, `initMachine_call` |
| `KernelRfl`, `Tactic` | `kernel_rfl`, `kernel_decide`, `evm_step(s)`, `evm_norm`, `evm_disch`, `evm_gas`, `evm_apply` |

### Shape and naming of step lemmas

`step_<mnemonic>` (Mathlib-style: named after the instruction the conclusion is about),
`_of_<condition>` for conditional variants, `_top` for top-level halting. Hypotheses come
in a fixed order, which the tactics rely on:

1. `hcode : m.frame.code[m.frame.pc]? = some <byte>` — always first (checked by `rfl`,
   fails fast for the wrong opcode);
2. `hstk : m.frame.stack = x :: y :: rest` — operands become *unification variables*,
   assigned by `rfl`;
3. side conditions: `hlen` (no stack overflow), `hstatic`, `hdest` (valid jump), `hgas`.

The conclusion is `step m = .running { m with frame := { m.frame with … } }` (or
`.done …` / `finishFrame …`), with the exact gas charged. All lemmas hold for every fork
(decoding is fork-independent except `CLZ`) and every `Crypto`.

To add a lemma to the search: ``macro_rules | `(tactic| evm_step_core) => `(tactic| evm_apply my_step_lemma)``.

## Pitfalls

- **`rfl`/`decide` vs the kernel.** `rfl` and plain `decide` check definitional equality in
  the *elaborator* (`Meta.isDefEq`/`whnf`). On a whole-program run that does not finish
  (> 150 s even for `Crypto.real`). `decide +kernel` is fast but refuses goals with free
  variables, which is why the original `Execution.lean` theorems had to fix
  `Crypto.real`. Use `kernel_rfl`/`kernel_decide` for runs with free but uninspected
  variables. Use `kernel_decide` when both sides only meet after evaluating to numbers
  (e.g. gas arithmetic): `kernel_rfl`'s lazy unfolding of `Nat.sub` can hit deep recursion.
- **No `bv_decide`.** It closes goals through `Lean.ofReduceBool` (an extra axiom trusting
  the compiler). Use `bv_omega`, `omega` or `BitVec` lemmas.
- **`rfl` in dischargers only on equalities.** `rfl` on `a ≤ b` tries `Nat.le.refl`
  and unfolds symbolic gas expressions; `evm_disch` uses `exact rfl`.
- **`first | … | last` recovers from errors in its last alternative** (logging the error
  and admitting the goal). Every `first` in `Tactic.lean` ends with `fail "…"`; do the same
  in extensions.
- **No `simp_all` in dischargers.** With a large context it can time out, and it would run
  for every failed lemma.
- **Symbolic costs.** `SLOAD`/`SSTORE` costs depend on symbolic warmness and values;
  `evm_gas` adds `sloadCost_le`/`sstoreCost_le` for each occurrence before `omega`. Give the
  theorem a generous lower bound on gas (e.g. `50000 ≤ gas`).
- **Literal code.** Define code as `⟨#[0x60, …]⟩` in a named constant. Immediates and opcode
  bytes are evaluated by the `reduceByteArrayGetElem` simproc; a `ByteArray` built any other
  way stays opaque to it.
- **Structure-instance syntax.** In statements, a multi-line `{ … }` whose continuation
  lines are indented *less* than the opening brace fails to parse; define the machine as a
  `def` with `where` instead.
- **`dsimp only` has no simprocs.** List them explicitly (`evm_norm` does).
- **Prague.** A top-level call first applies EIP-7702 authorizations; theorems about calls
  take `ctx.fork < .prague ∨ ctx.tx.authorizations = []`.
