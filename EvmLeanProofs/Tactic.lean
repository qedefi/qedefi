import Lean
import EvmLeanProofs.KernelRfl
import EvmLeanProofs.StepArith
import EvmLeanProofs.StepEnv
import EvmLeanProofs.StepFlow
import EvmLeanProofs.StepMemory
import EvmLeanProofs.StepPush
import EvmLeanProofs.StepStack
import EvmLeanProofs.StepStorage

/-!
# Symbolic execution: `evm_step`

`evm_step` advances a goal containing `run (n + 1) m` by one instruction, where `m` is a
machine whose code, pc and stack shape are known (concrete bytecode, symbolic values):

1. it rewrites with `run_succ_of_running ?h` (or `run_succ_of_done ?h` for a halting
   instruction), leaving the side goal `?h : step m = .running ?m'`;
2. it solves `?h` by trying the step lemmas of `EvmLeanProofs.Step*` one after another
   (`evm_step_core`), discharging each lemma's hypotheses with `evm_disch`:
   * `rfl` for the opcode byte (`code[pc]? = some b`), the stack shape
     (`stack = ?x :: ?y :: ?rest`, which *assigns* the operands), immediates and
     `parents = []`;
   * `decide` for stack bounds and jump-destination validity;
   * `evm_gas` for gas: unfolds the `Gas` constants, adds the bounds `sstoreCost_le` and
     `sloadCost_le` for every symbolic cost in the goal, and calls `omega`;
   * `assumption` (e.g. `isStatic = false` from a hypothesis);
3. it normalizes the new machine with `dsimp only` plus `reduceByteArrayGetElem` (which
   evaluates `code[i]` for literal bytecode, so `PUSH` immediates become numerals).

`evm_steps` repeats `evm_step` as long as it succeeds. Branches (`JUMPI` on a symbolic
condition) are not taken automatically: split on the condition first, then
`step_jumpi_of_ne_zero` / `step_jumpi_of_eq_zero` apply.

New step lemmas can be added to the search with
`macro_rules | `(tactic| evm_step_core) => `(tactic| apply my_step_lemma; all_goals evm_disch)`.
-/

namespace EvmLean.Tactic

open Lean Elab Tactic Meta Simp
open EvmLean.Interpreter

/-! ## Evaluating bytes of literal bytecode -/

/-- The elements of a literal byte array `⟨#[b₀, b₁, …]⟩` (after unfolding definitions). -/
def byteArrayLit? (c : Expr) : MetaM (Option (List Expr)) := do
  let c ← whnfD c
  let_expr ByteArray.mk arr := c | return none
  if let some (_, l) := Expr.arrayLit? arr then return some l
  let_expr Array.mk _ l := arr | return none
  return (Expr.listLit? l).map (·.2)

/-- Evaluate `c[i]?` and `c[i]` for a literal byte array `c` and a numeral `i`. -/
dsimproc_decl reduceByteArrayGetElem (_) := fun e => do
  if e.isAppOfArity ``GetElem?.getElem? 7 then
    let args := e.getAppArgs
    unless (← isDefEq args[0]! (mkConst ``ByteArray)) do return .continue
    let some i ← (evalNat args[6]!).run | return .continue
    let some bytes ← byteArrayLit? args[5]! | return .continue
    match bytes[i]? with
    | some b => return .done (mkApp2 (mkConst ``Option.some [0]) (mkConst ``UInt8) b)
    | none => return .done (mkApp (mkConst ``Option.none [0]) (mkConst ``UInt8))
  else if e.isAppOfArity ``GetElem.getElem 8 then
    let args := e.getAppArgs
    unless (← isDefEq args[0]! (mkConst ``ByteArray)) do return .continue
    let some i ← (evalNat args[6]!).run | return .continue
    let some bytes ← byteArrayLit? args[5]! | return .continue
    match bytes[i]? with
    | some b => return .done b
    | none => return .continue
  else return .continue

/-! ## Gas side conditions -/

/-- Add `sstoreCost_le` / `sloadCost_le` for every symbolic cost occurring in the goal. -/
elab "evm_gas_bounds" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let found ← IO.mkRef (#[] : Array Expr)
  forEachExpr t fun e => do
    if e.isAppOfArity ``sloadCost 1 then
      found.modify (·.push (← mkAppM ``sloadCost_le #[e.getArg! 0]))
    else if e.isAppOfArity ``Prod.fst 3 && (e.getArg! 2).isAppOfArity ``sstoreCostRefund 3 then
      let s := e.getArg! 2
      found.modify (·.push (← mkAppM ``sstoreCost_le #[s.getArg! 0, s.getArg! 1, s.getArg! 2]))
    else if e.isAppOfArity ``Prod.fst 3 && (e.getArg! 2).isAppOfArity ``Gas.sstoreCostRefund 4 then
      let s := e.getArg! 2
      found.modify (·.push (← mkAppM ``Gas.sstoreCostRefund_fst_le
        #[s.getArg! 0, s.getArg! 1, s.getArg! 2, s.getArg! 3]))
  let mut g ← getMainGoal
  for pf in ← found.get do
    let (_, g') ← (← g.assert `hcost (← inferType pf) pf).intro1
    g := g'
  replaceMainGoal [g]

/-- Prove a gas side condition: unfold the `Gas` constants, bound symbolic costs, `omega`. -/
macro "evm_gas" : tactic => `(tactic| (
  evm_gas_bounds
  try dsimp only at *
  try simp only [Gas.base, Gas.veryLow, Gas.low, Gas.mid, Gas.high, Gas.jumpdest, Gas.fastStep,
    Gas.callStipend, Gas.warmAccess, Gas.coldStorageAccess, List.length_cons,
    List.length_nil] at *
  omega))

/-! ## Side conditions -/

/-- Discharge a side condition of a step lemma. -/
syntax "evm_disch" : tactic

macro_rules
  | `(tactic| evm_disch) => `(tactic| first
    | exact rfl
    | decide
    | (dsimp only; decide)
    | evm_gas
    | assumption
    | fail "evm_disch: cannot discharge side condition")

/-! ## Step lemma search -/

/-- Prove `step m = r` for the next instruction of `m` using a step lemma. Extensible with
`macro_rules`. -/
syntax "evm_step_core" : tactic

macro_rules | `(tactic| evm_step_core) => `(tactic| first
  | (apply step_push0; all_goals evm_disch) | (apply step_push1; all_goals evm_disch)
  | (apply step_push2; all_goals evm_disch)
  | (apply step_add; all_goals evm_disch) | (apply step_mul; all_goals evm_disch)
  | (apply step_sub; all_goals evm_disch) | (apply step_div; all_goals evm_disch)
  | (apply step_sdiv; all_goals evm_disch) | (apply step_mod; all_goals evm_disch)
  | (apply step_smod; all_goals evm_disch) | (apply step_addmod; all_goals evm_disch)
  | (apply step_mulmod; all_goals evm_disch) | (apply step_exp; all_goals evm_disch)
  | (apply step_signextend; all_goals evm_disch)
  | (apply step_lt; all_goals evm_disch) | (apply step_gt; all_goals evm_disch)
  | (apply step_slt; all_goals evm_disch) | (apply step_sgt; all_goals evm_disch)
  | (apply step_eq; all_goals evm_disch) | (apply step_iszero; all_goals evm_disch)
  | (apply step_and; all_goals evm_disch) | (apply step_or; all_goals evm_disch)
  | (apply step_xor; all_goals evm_disch) | (apply step_not; all_goals evm_disch)
  | (apply step_byte; all_goals evm_disch) | (apply step_shl; all_goals evm_disch)
  | (apply step_shr; all_goals evm_disch) | (apply step_sar; all_goals evm_disch)
  | fail "no arithmetic step lemma applies")

macro_rules | `(tactic| evm_step_core) => `(tactic| first
  | (apply step_address; all_goals evm_disch) | (apply step_origin; all_goals evm_disch)
  | (apply step_caller; all_goals evm_disch) | (apply step_callvalue; all_goals evm_disch)
  | (apply step_calldataload; all_goals evm_disch) | (apply step_calldatasize; all_goals evm_disch)
  | (apply step_codesize; all_goals evm_disch) | (apply step_gasprice; all_goals evm_disch)
  | (apply step_returndatasize; all_goals evm_disch) | (apply step_coinbase; all_goals evm_disch)
  | (apply step_timestamp; all_goals evm_disch) | (apply step_number; all_goals evm_disch)
  | (apply step_prevrandao; all_goals evm_disch) | (apply step_gaslimit; all_goals evm_disch)
  | (apply step_chainid; all_goals evm_disch) | (apply step_selfbalance; all_goals evm_disch)
  | (apply step_basefee; all_goals evm_disch) | (apply step_pc; all_goals evm_disch)
  | (apply step_msize; all_goals evm_disch) | (apply step_gas; all_goals evm_disch)
  | fail "no environment step lemma applies")

macro_rules | `(tactic| evm_step_core) => `(tactic| first
  | (apply step_pop; all_goals evm_disch)
  | (apply step_dup1; all_goals evm_disch) | (apply step_dup2; all_goals evm_disch)
  | (apply step_dup3; all_goals evm_disch) | (apply step_dup4; all_goals evm_disch)
  | (apply step_dup5; all_goals evm_disch) | (apply step_dup6; all_goals evm_disch)
  | (apply step_dup7; all_goals evm_disch) | (apply step_dup8; all_goals evm_disch)
  | (apply step_swap1; all_goals evm_disch) | (apply step_swap2; all_goals evm_disch)
  | (apply step_swap3; all_goals evm_disch) | (apply step_swap4; all_goals evm_disch)
  | (apply step_swap5; all_goals evm_disch) | (apply step_swap6; all_goals evm_disch)
  | (apply step_swap7; all_goals evm_disch) | (apply step_swap8; all_goals evm_disch)
  | fail "no stack step lemma applies")

macro_rules | `(tactic| evm_step_core) => `(tactic| first
  | (apply step_jumpdest; all_goals evm_disch) | (apply step_jump; all_goals evm_disch)
  | (apply step_jumpi_of_eq_zero; all_goals evm_disch) | (apply step_jumpi_of_ne_zero; all_goals evm_disch)
  | (apply step_sload; all_goals evm_disch) | (apply step_sstore; all_goals evm_disch)
  | (apply step_mload; all_goals evm_disch) | (apply step_mstore; all_goals evm_disch)
  | (apply step_mstore8; all_goals evm_disch)
  | fail "no control-flow, storage or memory step lemma applies")

/-- Prove `step m = .done r` for a halting instruction of a top-level call frame. -/
syntax "evm_halt_core" : tactic

macro_rules | `(tactic| evm_halt_core) => `(tactic| first
  | (apply step_stop_top; all_goals evm_disch)
  | (apply step_return_top; all_goals evm_disch)
  | (apply step_revert_top; all_goals evm_disch)
  | fail "no halting step lemma applies")

/-! ## The driver -/

/-- Normalize the machine after a step: evaluate bytes of literal code, numerals, gas
constants, and costs of zero-length memory accesses. -/
syntax "evm_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| evm_norm) => `(tactic| evm_norm [])
  | `(tactic| evm_norm [$extra,*]) => `(tactic| simp only [reduceByteArrayGetElem,
    UInt8.reduceToNat, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, BitVec.reduceOfNat,
    BitVec.reduceToNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceMul, Gas.base,
    Gas.veryLow, Gas.low, Gas.mid, Gas.high, Gas.jumpdest, Gas.fastStep, sstoreCostRefund,
    outputCost_zero, outputData_zero, outputMachine_zero, Substate.warmKey_warmKey,
    Substate.accessedStorageKeys_warmKey, Substate.accessedStorageKeys_addRefund,
    storageKeyWarm_addStorageKey_self, getStorageOriginal_empty, $extra,*])


/-- Advance `run (n + 1) m` in the goal by one instruction (see the module docstring).
`evm_step [h₁, …]` adds simp lemmas to the normalization of the new machine (e.g. facts about
calldata). -/
syntax "evm_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| evm_step) => `(tactic| evm_step [])
  | `(tactic| evm_step [$extra,*]) => `(tactic| (
  first
    | (rw [run_succ_of_running ?h]; case h => evm_step_core)
    | (rw [run_succ_of_done ?h]; case h => evm_halt_core)
    | fail "evm_step: no step lemma applies to the next instruction"
  try evm_norm [$extra,*]))

/-- Repeat `evm_step` while it succeeds. -/
syntax "evm_steps" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| evm_steps) => `(tactic| repeat evm_step)
  | `(tactic| evm_steps [$extra,*]) => `(tactic| repeat evm_step [$extra,*])

end EvmLean.Tactic
