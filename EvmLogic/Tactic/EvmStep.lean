import Lean
import EvmLogic.Tactic.KernelRfl
import EvmLogic.Bytes
import EvmLogic.Step.Arith
import EvmLogic.Step.Env
import EvmLogic.Step.Flow
import EvmLogic.Step.Log
import EvmLogic.Step.Memory
import EvmLogic.Step.Push
import EvmLogic.Step.Stack
import EvmLogic.Step.Storage

/-!
# Symbolic execution: `evm_step`

`evm_step` rewrites `run (n + 1) m` with `run_succ_of_running` / `run_succ_of_done`, proves the
`step` equation with the first step lemma (`evm_step_core`, extensible by `macro_rules`) whose
side conditions `evm_disch` closes, and normalizes the new machine with `evm_norm`. `evm_steps`
repeats it; split a symbolic `JUMPI` condition by hand. See `docs/proving.md` §2.
-/

namespace EvmLogic.Tactic
open EvmLean Lean Elab Tactic EvmLogic.Tactic Meta Simp EvmLean.Interpreter

/-! ## Evaluating bytes of literal bytecode -/

def byteArrayLit? (c : Expr) : MetaM (Option (List Expr)) := do
  let c ← whnfD c
  let_expr ByteArray.mk arr := c | return none
  if let some (_, l) := Expr.arrayLit? arr then return some l
  let_expr Array.mk _ l := arr | return none
  return (Expr.listLit? l).map (·.2)

/-- Evaluate `c[i]?` and `c[i]` for a literal byte array `c` and a numeral `i`. -/
dsimproc_decl reduceByteArrayGetElem (_) := fun e => do
  match_expr e with
  | GetElem?.getElem? coll _ _ _ _ xs i =>
    unless (← isDefEq coll (mkConst ``ByteArray)) do return .continue
    let some n ← (evalNat i).run | return .continue
    let some bytes ← byteArrayLit? xs | return .continue
    match bytes[n]? with
    | some b => return .done (mkApp2 (mkConst ``Option.some [0]) (mkConst ``UInt8) b)
    | none => return .done (mkApp (mkConst ``Option.none [0]) (mkConst ``UInt8))
  | GetElem.getElem coll _ _ _ _ xs i _ =>
    unless (← isDefEq coll (mkConst ``ByteArray)) do return .continue
    let some n ← (evalNat i).run | return .continue
    let some bytes ← byteArrayLit? xs | return .continue
    match bytes[n]? with
    | some b => return .done b
    | none => return .continue
  | _ => return .continue

/-! ## Gas side conditions -/

/-- Add `sstoreCost_le` / `sloadCost_le` for every symbolic cost occurring in the goal. -/
elab "evm_gas_bounds" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let found ← IO.mkRef (#[] : Array Expr)
  forEachExpr t fun e => do
    match_expr e with
    | sloadCost w => found.modify (·.push (mkApp (mkConst ``sloadCost_le) w))
    | Prod.fst _ _ p =>
      match_expr p with
      | sstoreCostRefund m x y =>
        found.modify (·.push (mkApp3 (mkConst ``sstoreCost_le) m x y))
      | Gas.sstoreCostRefund o c n w =>
        found.modify (·.push (mkApp4 (mkConst ``Gas.sstoreCostRefund_fst_le) o c n w))
      | _ => pure ()
    | _ => pure ()
  let mut g ← getMainGoal
  for pf in ← found.get do
    let (_, g') ← (← g.assert `hcost (← inferType pf) pf).intro1
    g := g'
  replaceMainGoal [g]

/-- Prove a gas side condition: unfold the `Gas` constants, bound symbolic costs, `omega`. -/
macro "evm_gas" : tactic => `(tactic| (
  evm_gas_bounds
  try dsimp only at *
  try simp only [memoryCost, outputCost, Gas.extendMemory, List.foldl, Gas.ceil32,
    Gas.memoryCost, Gas.words, Gas.memoryPerWord, Memory.size_storeWord, Memory.size_expand,
    Memory.size_empty, Memory.wordsAfter, Memory.words, Gas.logCost, Gas.logBase,
    Gas.logDataPerByte, Gas.logTopic, Gas.keccak256Cost, Gas.keccak256Base, Gas.keccak256PerWord,
    BitVec.reduceToNat, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub,
    Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.max_def, ↓reduceIte] at *
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

/-- Apply a step lemma: check its opcode-byte hypothesis by `rfl` first (fails fast for the wrong
opcode), then discharge the rest with `evm_disch`. -/
macro "evm_apply " l:ident : tactic =>
  `(tactic| (apply $l; exact rfl; all_goals evm_disch))

/-- Prove `step m = r` for the next instruction of `m`. Extensible with `macro_rules`. -/
syntax "evm_step_core" : tactic

macro_rules | `(tactic| evm_step_core) => `(tactic| first
  | evm_apply step_push0 | evm_apply step_push1
  | evm_apply step_push2
  | evm_apply step_add | evm_apply step_mul
  | evm_apply step_sub | evm_apply step_div
  | evm_apply step_sdiv | evm_apply step_mod
  | evm_apply step_smod | evm_apply step_addmod
  | evm_apply step_mulmod | evm_apply step_exp
  | evm_apply step_signextend
  | evm_apply step_lt | evm_apply step_gt
  | evm_apply step_slt | evm_apply step_sgt
  | evm_apply step_eq | evm_apply step_iszero
  | evm_apply step_and | evm_apply step_or
  | evm_apply step_xor | evm_apply step_not
  | evm_apply step_byte | evm_apply step_shl
  | evm_apply step_shr | evm_apply step_sar
  | fail "no arithmetic step lemma applies")

macro_rules | `(tactic| evm_step_core) => `(tactic| first
  | evm_apply step_address | evm_apply step_origin
  | evm_apply step_caller | evm_apply step_callvalue
  | evm_apply step_calldataload | evm_apply step_calldatasize
  | evm_apply step_codesize | evm_apply step_gasprice
  | evm_apply step_returndatasize | evm_apply step_coinbase
  | evm_apply step_timestamp | evm_apply step_number
  | evm_apply step_prevrandao | evm_apply step_gaslimit
  | evm_apply step_chainid | evm_apply step_selfbalance
  | evm_apply step_basefee | evm_apply step_pc
  | evm_apply step_msize | evm_apply step_gas
  | fail "no environment step lemma applies")

macro_rules | `(tactic| evm_step_core) => `(tactic| first
  | evm_apply step_pop
  | evm_apply step_dup1 | evm_apply step_dup2
  | evm_apply step_dup3 | evm_apply step_dup4
  | evm_apply step_dup5 | evm_apply step_dup6
  | evm_apply step_dup7 | evm_apply step_dup8
  | evm_apply step_swap1 | evm_apply step_swap2
  | evm_apply step_swap3 | evm_apply step_swap4
  | evm_apply step_swap5 | evm_apply step_swap6
  | evm_apply step_swap7 | evm_apply step_swap8
  | evm_apply step_dup9 | evm_apply step_dup10
  | evm_apply step_dup11 | evm_apply step_dup12
  | evm_apply step_dup13 | evm_apply step_dup14
  | evm_apply step_dup15 | evm_apply step_dup16
  | evm_apply step_swap9 | evm_apply step_swap10
  | evm_apply step_swap11 | evm_apply step_swap12
  | evm_apply step_swap13 | evm_apply step_swap14
  | evm_apply step_swap15 | evm_apply step_swap16
  | fail "no stack step lemma applies")

macro_rules | `(tactic| evm_step_core) => `(tactic| first
  | evm_apply step_jumpdest | evm_apply step_jump
  | evm_apply step_jumpi_of_eq_zero | evm_apply step_jumpi_of_ne_zero
  | evm_apply step_sload | evm_apply step_sstore
  | evm_apply step_mload | evm_apply step_mstore
  | evm_apply step_mstore8 | evm_apply step_keccak256
  | evm_apply step_log0 | evm_apply step_log1
  | evm_apply step_log2 | evm_apply step_log3
  | evm_apply step_log4
  | fail "no control-flow, storage or memory step lemma applies")

/-- Prove `step m = .done r` for a halting instruction of a top-level call frame. -/
syntax "evm_halt_core" : tactic

macro_rules | `(tactic| evm_halt_core) => `(tactic| first
  | evm_apply step_stop_top
  | evm_apply step_return_top
  | evm_apply step_revert_top
  | fail "no halting step lemma applies")

/-! ## The driver -/

/-- Normalize the machine after a step (literal code bytes, numerals, gas constants). -/
syntax "evm_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| evm_norm) => `(tactic| evm_norm [])
  | `(tactic| evm_norm [$extra,*]) => `(tactic| simp only [reduceByteArrayGetElem,
    UInt8.reduceToNat, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, BitVec.reduceOfNat,
    BitVec.reduceToNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceMul, Gas.base,
    Gas.veryLow, Gas.low, Gas.mid, Gas.high, Gas.jumpdest, Gas.fastStep, sstoreCostRefund,
    outputCost_zero, outputData_zero, outputMachine_zero, Substate.warmKey_warmKey,
    Substate.accessedStorageKeys_warmKey, Substate.accessedStorageKeys_addRefund,
    storageKeyWarm_addStorageKey_self, getStorageOriginal_empty, memoryCost, outputCost,
    outputData, Gas.extendMemory, List.foldl, Gas.ceil32, Gas.memoryCost, Gas.words,
    Gas.memoryPerWord, Memory.size_storeWord, Memory.size_expand, Memory.size_empty,
    Memory.wordsAfter, Memory.words, Nat.reduceDiv, Nat.reduceLeDiff, Nat.reduceEqDiff,
    Nat.max_def, ↓reduceIte, Memory.expand_storeWord_self, readBytes_bytes, $extra,*])


/-- Advance `run (n + 1) m` by one instruction; `evm_step [h₁, …]` adds simp lemmas to the
normalization (e.g. calldata facts). -/
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

end EvmLogic.Tactic
