# Proving things about bytecode with EvmLogic

`EvmLogic` is a generic proof library over the `EvmLean` semantics. Every execution theorem
in it holds for an **arbitrary `Crypto`** and every fork unless stated, and depends only on
`propext`, `Classical.choice`, `Quot.sound`. Worked examples are in
`qedefi/Examples/Basic/`:

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

`kernel_rfl` / `kernel_decide` close the goal with a proof term (`Eq.refl`, `of_decide_eq_true`)
checked **only by the kernel**, with the enclosing declaration (no auxiliary declaration). Do not
use plain `rfl` or `decide`: they check definitional equality in the elaborator
(`Meta.isDefEq`/`whnf`), which does not finish on a whole-program run (over 150 s even for
`Crypto.real`); `decide +kernel` is fast but refuses free variables. Prefer
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
`WP.call` / `WP.staticcall` / `WP.delegatecall` are the callee-summary rules: given `Halts` of
the fresh child frame (e.g. a `FunctionSummary` of the callee; for `DELEGATECALL` the child
`delegateChild` runs the target's code at the caller's address, with the caller's `CALLER` and
`CALLVALUE`), the caller continues from `resumeAfter_success` / `_revert` / `_halt` (flag
pushed, output copied, unused gas returned, world or snapshot, logs merged on success). A
proxy's forwarding is summarised once for all implementations
(`Examples/AaveV3/ATokenProxy/Forward.lean`, `forward_halts`). Precompile calls run within one step
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
(each `GAS` is immediately followed by `CALL`, `STATICCALL` or `DELEGATECALL`), `RegionOk` (execution stays below the final
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

## 7. Untrusted callees and reentrancy (`EvmLogic/Program/Reentrancy/`)

Section 5 assumes protected frames are atomic. `Reentrancy/` lifts this: a protected frame may
call code it does not trust, which may call back into protected contracts at any depth. The
callee is never explored; the untrusted call is **one symbolic step**.

**Per instruction.** `exec_strict` (`Exec.lean`): every step that continues the frame strictly
lowers its gas, and a requested child gets strictly less than the caller gave up; with at most
`Gas.callStipend` gas an instruction leaves the world unchanged and requests neither a creation
nor a value transfer (`SSTORE` sentry, `CALL` value cost 9000, `CREATE` 32000, `SELFDESTRUCT`
5000). `exec_world` (`World.lean`): the world changes only by an `SSTORE`, nonce increment or
`SELFDESTRUCT` of the executing non-static account, and requested value transfers are
affordable and leave static frames only to themselves.

**World-safe tails for any gas** (`NoWrite.lean`, `Certified.lean`). `WorldSafe b`: the byte is
not `SSTORE`/`CREATE*`/`CALL*`/`SELFDESTRUCT`; `exec_worldSafe` shows such an instruction keeps
the world and starts no child. `noWrite_halts`: a frame whose reachable instructions — localised
by an AbsInt certificate (§6) — are all world-safe halts with its world unchanged for **any
gas**, no gas bound. This is the tail of a checks-effects-interactions function after its single
external call.

**The any-gas prefix calculus** (`Prefix.lean`, `PrefixOps.lean`). A protected function's body
up to its untrusted call is a *prefix*, run under symbolic gas: `FailOk Good mf o` is
`Good (frameResult mf o).2.1` (the snapshot, hence `Good`, on a revert or halt), and each rule
takes the instruction when gas and stack allow and otherwise absorbs the failure
(`wp_fail_of_error`, `wp_fail_of_revert`): `pwp_push`, `pwp_dup`, `pwp_swap`, `pwp_pop`, one rule
per arithmetic/comparison/environment opcode (`pwp_add`, `pwp_eq`, `pwp_caller`, …), `pwp_jump`,
`pwp_jumpi` (both branches), `pwp_mload_val`, `pwp_mstore`, `pwp_keccak256`, `pwp_codecopy`,
`pwp_returndatacopy` (memory left unknown), `pwp_calldataload`, `pwp_sload`, `pwp_sstore`; the
frame ends with `pwp_revert`/`pwp_invalid` (always fine) or `pwp_stop`/`pwp_return` (the world
must be `Good`). They mirror `GasMono.CodeFails` with a forward goal, so no gas lower bound.
**`apwp_steps [h₁, …]`** (`Tactic/PrefixStep.lean`) drives them over literal code from a
`Machine.mk … (Frame.mk …)` goal: it splits `JUMPI` on symbolic conditions (closing branches the
normalization decides), closes reverts, generalizes gas and substate after each step (keeping a
bound `g ≤ B`), and stops at `STOP`/`RETURN`/`CALL`/`LOG` (and, with `stop_at [q₁, …]`, on
reaching one of the pcs `qᵢ`, e.g. a loop left to a certified tail). A dispatcher and all paths of a
function run in seconds (`CEIBank`: 8 s for the whole contract).

**The untrusted call of a prefix** (`PrefixCall.lean`). `pwp_call_v`: a `CALL` to an unprotected
account for **any gas and any outcome** (out of gas, soft failure, precompile, child): given the
call-site invariant `Gc` (a `GoodOps` invariant, which may differ from the frame's `Good`) before
and after the value transfer and `CoversV` for every gas below the caller's, the caller resumes
at `pc + 1` with one word on the popped stack in some `Gc` world. `pwp_call_stipend`: a callee
with at most 2300 gas, no invariant (`halts_low`): the caller resumes with the flag `x` and the
world before the call (`x = 0`) or after the affordable transfer (`x ≠ 0`).

**Value-moving dangerous frames** (`Value.lean`). `DStart` does not record that the value of a
dangerous frame arrived; a payable function crediting `msg.value` needs it. `exec_value`: a
non-static request to another account transfers its value (only `CALL`). `DStartV`/`CoversV`
add it and a context predicate `C` (e.g. the transaction's `Crypto`, on which a storage layout
depends); `halts_inv_v`, `processMessageCall_good_v` (top-level messages with
`shouldTransferValue`).

**Certified tails** (`Tail.lean`). `noWrite_halts` needs every *table entry* of a `Cert` explored
from pc `0` to be world-safe, which no function containing an `SSTORE` satisfies. `certifyAt`
explores from the tail's pc; `tailCheck` checks by evaluation that every **reached**
instruction is world-safe; `noWrite_halts_tail` and `Halts.failOk` close a frame after its call.
`pwp_safe`: any world-safe popping instruction (`LOG*`) once the world is `Good`.

**The havoc theorem** (`Halts.lean`). `Covers P Good G`: every dangerous frame start with at most
`G` gas, *with any parents* (callbacks have dangerous ancestors), halts in a `Good` world.
`halts_inv`: under `Covers`, any non-dangerous frame (`Inv`: `Good` world and snapshot) halts in a
`Good` world, by strong induction on the frame's gas. Corollaries: `halts_any` (every frame
halts), `halts_static` (a static frame keeps `Good` with no summaries) and `halts_low` (**the
stipend lemma**: a frame with ≤ 2300 gas, and everything it starts, returns the world it started
with). `covers_of_lt`: summaries may be proved by induction on gas, since a reentrant frame has
less gas than its ancestors.

**Rules** (`Havoc.lean`), for the frame-local logic of section 3:

| Rule | Call site | Continuation sees |
|---|---|---|
| `WP.call_havoc` | `CALL` to an unprotected account, call-site invariant `Good m.world`, `Covers` | any return whose world is `Good`, any flag and return data |
| `WP.call_stipend` | `CALL` whose child gets ≤ 2300 gas, any target | the callee's final world equals its initial world |
| `WP.staticcall_havoc` | any `STATICCALL` | any return whose world is `Good` |
| `WP.call_frozen` | `CALL` under a held guard: `Covers` for `Frozen P m.world` | protected storage and code exactly as at the call |

Checks-effects-interactions is `WP.call_havoc` with the contract's invariant as `Good`; a
reentrancy guard is `WP.call_frozen`, whose `Covers` (`covers_frozen`) asks that a frame
started while the lock is held fails or writes no protected storage. `processMessageCall_covers`
is the any-transaction theorem.

**Ether** (`Ether.lean`). Invariants such as `Σ balances ≤ address(this).balance` depend on
balances that arbitrary code changes. `GoodOps` replaces `GoodOk` by closure under the world
changes of `exec_world`; `DStart` records the value transfer that started a dangerous frame.
`halts_inv_e`, `WP.call_havoc_e`, `processMessageCall_good_e` are the counterparts.

**Demonstrators** (`qedefi/Examples/Reentrancy/`, sources `contracts/src/reentrancy/Banks.sol`).
`Exploit.lean`: `VulnerableBank` (send before debit) and an `Attacker` contract, both compiled;
the attack transaction is evaluated by the kernel with the real Keccak (`exploit_run`) and leaves
the bank owing the victim 2 ether while holding none (`exploit_insolvent`). `Defended.lean`: the
same attack replayed against `CEIBank` (debit before the call) and `GuardedBank` (OpenZeppelin
`ReentrancyGuard`) leaves the bank solvent (`cei_solvent`; the guarded run reverts,
`guarded_solvent`), while `VulnerableBank` is drained (`vulnerable_drained`), all
kernel-evaluated on bytecode against a re-enter-once attacker. `NoWrite.lean`/`Certified.lean`:
`noWrite_halts` — a certified tail with no storage-writing or calling instruction keeps the
world for any gas.

**Solvency after any transaction** (`qedefi/Examples/Reentrancy/Solvency/`), on bytecode, for any
gas. `Model.lean`: `Solvent crypto base code bank` (what the bank owes, the sum of its balance
entries **over their slots** — no Keccak hypothesis — is at most its ether, and all ether is below
`2²⁵⁶`) is closed under everything arbitrary code does (`goodOps_solvent`); `Locked` (bank
storage frozen, ether floor) likewise. `CEI.lean`: `cei_frame` runs every function with
`apwp_steps`, the `withdraw()` call with `pwp_call_v` (`Gc = Solvent`), the tail with a certified
tail; `cei_covers` by `coversV_of_lt`; **`cei_solvent`** (any top-level message call that moves
its value, hashing with the world's `crypto`) and `cei_backed` (`Σₐ balances[a] ≤ balance`
under slot injectivity). `Guarded.lean`: under the held lock every bank frame reverts or only
reads (`locked_covers`, no induction), so the call of `withdraw()` is `pwp_call_v` with
`Gc = Locked` and the post-call tail (debit, unlock) runs with `apwp_steps`; **`guarded_solvent`**
assumes the ERC-7201 status slot is not a balance slot. `WETH9.lean` (mainnet bytecode):
`withdraw_frame`/**`withdraw_halts_refines`**: `withdraw(wad)` debits, sends with the stipend
(`pwp_call_stipend`), and ends in the world it started from or in the checked withdrawal, which
refines `Variant.weth9.withdraw … true` (any gas, any depth, any recipient).
`WETH9Backed.lean`: **`weth9_solvent`**/**`weth9_backed`**, the any-transaction ether backing of
mainnet WETH9 (`Σₐ balanceOf[a] ≤ address(weth).balance`, the sum below `2²⁵⁶`, over all
addresses under slot injectivity). `weth_frame` runs the whole dispatcher with one
`apwp_steps`: deposit (and the fallback), `transfer`, `transferFrom` (every allowance branch),
`approve` and the word views end at their `LOG`/`STOP`/`RETURN` (`pwp_safe`, then the
continuation), `withdraw` at its stipend `CALL`; the string views (storage-copy loops) and
`decimals`/`totalSupply` (`EXP`, `BALANCE`, which have no prefix rule) are stopped at their
entries with **`apwp_steps stop_at [q₁, …]`** and closed by certified world-safe tails
(`view_wp`). solc 0.4's unchecked `+=` is safe because a credit is backed by the ether, which
fits a word (`solvent_credit_unchecked`); `transferFrom` is `solvent_move` (debit, then credit).
The only Keccak hypothesis is `Disjoint (allowanceSlots crypto) (balanceSlots crypto 3)`: no
`allowance[a][b]` slot is a `balanceOf` slot (two finite families, not Keccak injectivity).
`weth_covers` needs no induction: the stipend call cannot reach WETH9 again.
Pitfalls met there: compare literal slots as `3#256` (the simp normal form) so `with_reducible`
matching works; look up branch hypotheses with `with_reducible assumption` (at default
transparency a failed match unfolds Keccak slots); close a long list of goals with one bullet
each, not `first | …` over all goals (failed alternatives on deep terms are slow).

## Time and multiple blocks

Modules: `EvmLogic/Program/Time.lean` (block environments), `qedefi/QEDefi/Trace/Time.lean`
(EVM-independent lifting), `qedefi/QEDefi/Vesting/Model.lean` and
`qedefi/Examples/Time/` (OpenZeppelin `VestingWallet`, Solmate across blocks).

**Principle: the block context stays symbolic.** Per-call theorems hold for every `ctx`, so
`TIMESTAMP`, `NUMBER`, `PREVRANDAO`, the base fee … are free variables of the bytecode proof,
and the code's own branches on them are the only case splits. A multi-block trace is a list
of block environments with the calls of each block; the only assumptions relating blocks are
hypotheses on the list:

- `NextBlock b b'` / `BlockChain bs`: same chain id, number `+1`, strictly increasing
  timestamp, ancestor hashes shifted by the parent's hash; everything else arbitrary.
  `nextBlock_stateTransition` checks them against the semantics: the environments in which
  `Block.stateTransition` runs two consecutive valid blocks are `NextBlock`.
  `BlockChain.timestamp_lt`, `number_eq`, `chainId_eq` are what proofs use.

**Time-indexed models** (`QEDefi.Trace.Time`). The model step is `step now s op`; behaviour
over time is a closed form in `now` (e.g. `Vesting.Schedule.vested total t`), proved
monotone once, for a symbolic `t`. Executions take timed operations (`Timed`, `texec`), and
`Monotone`/`Within` state that times do not decrease. A **time invariant** `I t s`
(`TimeInvariant`: kept by a step at time `t`, and by advancing the clock `t ≤ t'`) is carried
along any monotone execution by one induction (`texec_timeInvariant`); `texec_quantity_mono`
does the same for a quantity that never decreases. Nothing is enumerated: the induction is
over the trace, the time facts are `≤` lemmas.

**Lifting** (`TSystem`): as `Lift.System`, with `call t w op w'` (a concrete call at time `t`)
and the refinement obligations stated for a symbolic `t` (`TSystem.Refinement`).
`TSystem.untimed` reduces it to `Lift`, so all of `Lift` applies. `BlockTrace step bs w w'`
runs blocks in order, each a sequence of `step b` transitions; with
`BlockStep σ time b` (admissible calls at `time b`, or environment steps):

- `Refinement.lift_blocks`: the final abstraction agrees with `texec` of the blocks' calls
  stamped with their blocks' times (`stamp`), for any blocks;
- `Refinement.timeInvariant_blocks`: a time invariant stable under `Agree` holds at any
  `t₁` after the last block, given block times monotone and in `[t₀, t₁]`.

Time-independent systems are the constant case (`TSystem.const`, `refinement_const`,
`texec_const`). For a protocol whose trace theorems are already proved, a multi-block trace
is just a trace: `BlockTrace.induction_on` (`Examples/Time/Solmate.lean` turns
`BlockTrace (BlockTxStep …)` into `TxTrace` and gets `supply_eq_sum_multiBlock`,
`solvent_multiBlock`, … for any sequence of blocks, unchanged statements, no time reasoning).

**Recipe for a time-dependent contract** (`Examples/Time/VestingWallet/`):

1. Model with `now` (`Vesting.step`, mirroring the contract's reverts) and its closed form;
   prove its laws once (`vested_mono_time`, `vested_mono_total`, `vested_le`) and the time
   invariant (`timeInvariant_released`).
2. Prove the time-dependent internal function once with the timestamp on the stack symbolic
   (`vested_wp`: `ts :: r :: rest`, three code branches, checked `+ - *`), then the external
   functions compose it (`releasable_halts`, `vestedAmount_halts`, `release_halts`). Note
   `uint64(block.timestamp)`: the clock is `timestamp mod 2⁶⁴` (`clock`), and monotone only
   while timestamps fit in 64 bits (a stated hypothesis).
3. Top level (`Spec.lean`): `result_of_halts` turns a frame summary into the result of any
   terminating `processMessageCall`, for every block environment.
4. The system (`System.lean`): calls at `clock ctx.block`, inflows as calls of a `deposit`
   operation (any transition adding ether), environment steps keeping the abstraction; the
   obligations are one `cases` on the call (`wallet_refinement`); the multi-block theorems are
   one-line instances (`released_le_vested_blocks`, `total_blocks`, `vested_mono_blocks`).

A second, model-level demonstrator is Synthetix `StakingRewards` (`QEDefi/Staking/Model.lean`):
`rewardPerToken` in closed form (piecewise linear, constant after `periodFinish`), a time-free
solvency invariant (`Funded`: claims + stored rewards + unstored accrual + what is still to
stream ≤ funded), giving `claimed_add_earned_le` at every time, and no dilution
(`entitlement_step`: every action at time `t`, by anyone, keeps each user's earned + claimed;
`entitlement_mono` along any monotone execution). Its bytecode refinement is not done.

A plain ether payment (`Address.sendValue`) to an account without code is one rule,
`WP.call_codeless` (`EvmLogic/Program/CallCodeless.lean`: the child halts at once; with
`callCost_le`, `le_gas_after_call'` for the gas). Payments to contracts re-enter: see section
7.

Cost: the `VestingWallet` bytecode proofs (schedule, three views, `release`) elaborate in
about 20 s; the multi-block layer adds no per-block or per-time work. `lake exe difftest
--family vesting` compares the wallet with anvil across blocks with `evm_increaseTime`.

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
  remaining gas by a variable with `wp_generalize_gas` + one `evm_gas` (or `wp_abstract gas`,
  `wp_abstract memory`, whose cost does not grow with the goal); generalize big
  postconditions (`generalize hQ : (fun m' => …) = Q`) before `pwp_steps`.
- **Memory with symbolic size**: `evm_gas` does not handle it; state each expansion as
  `Gas.memoryCost new - Gas.memoryCost old`, generalize the atoms and let `omega` telescope.
  Copies of symbolic size: `step_calldatacopy_any` / `step_returndatacopy_any` (empty or not,
  memory `copyMemory`), `extendMemory_cost_le` / `extendMemory_cost_eq_zero` for the costs.
  `omega` can hit the recursion limit on `(n - k) * c`; write `c * (n - k)`.
