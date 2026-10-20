import Lean
import EvmLogic.Tactic.EvmStep
import EvmLogic.Solidity.JumpDest
import EvmLogic.Solidity.Steps
import EvmLogic.Solidity.Memory
import EvmLogic.Solidity.Word

/-!
# Symbolic execution of compiled contracts: `sol_step`

`evm_step` (`EvmLeanProofs.Tactic`) tries every step lemma in turn and checks the opcode
byte with `exact rfl`. That is fine for hand-written programs of a few dozen bytes; on
solc output (1–25 kB) it breaks down:

* long bytecode literals are elaborated as chains of `have`s (Lean's list-literal macro
  chunks long lists), which `reduceByteArrayGetElem` does not see through, so pushed
  immediates stay unevaluated;
* `exact rfl` on `code[pc]? = some b` unfolds the list in the elaborator, hitting the
  recursion limit (an error `first` cannot recover from) for large `pc`;
* jump-destination side conditions evaluate `validJumpDests` (minutes in the kernel for
  1.6 kB, see `EvmLeanProofs.Solidity.JumpDest`);
* `PUSH3`–`PUSH32` and `CODECOPY` are not in the lemma search.

`sol_step` reads the opcode byte at `pc` itself (zeta-reducing the literal once per step),
applies only the step lemmas for that byte, and discharges side goals with `sol_disch`:

* code bytes `code[i]? = some b` by `decide +kernel` (closed after projecting the machine
  literal; the kernel indexes the literal in microseconds);
* jump destinations by `isValidJumpDest_of_mem` + `decide +kernel` on the list scan;
* other closed goals (literal `JUMPI` conditions, stack bounds) by `decide +kernel`;
* everything else by `evm_disch` (runtime errors such as the recursion limit are turned into
  ordinary failures, so that the next candidate lemma is tried).

The new machine is normalized by `evm_norm` plus `reduceCodeImm`, which evaluates
`Bytes.toWord (readBytes code i n)` (pushed immediates) and `readBytes code i 32`
(`CODECOPY` of a word) for literal code, each by a kernel-checked `decide` (a `dsimproc`
would leave the kernel to compare the two sides by lazy unfolding, which recurses too deeply
on numerals such as 4-byte selectors). `sol_steps [h₁, …]` repeats `sol_step` until no
lemma applies (a symbolic `JUMPI` condition, or a halt).

Everything `sol_step` produces is checked by the kernel: code bytes, jump destinations and
immediates are auxiliary theorems proved by kernel evaluation.
-/

namespace EvmLean.Solidity.Exec

open Lean Elab Tactic Meta Simp
open EvmLean.Interpreter

/-! ## Reading literal bytecode -/

/-- The value of a byte literal `(n : UInt8)` (as elaborated: `OfNat.ofNat n`). -/
def byteLit? (e : Expr) : Option Nat :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit?
  | _ => e.rawNatLit?

/-- The bytes of a `ByteArray` given by a literal `⟨#[b₀, b₁, …]⟩` (after unfolding
definitions and zeta-reducing the `have` chain of long list literals). -/
def codeBytes? (c : Expr) : MetaM (Option (Array Nat)) :=
  -- Long literals are deep terms (`b₀ :: b₁ :: …` or nested `have`s); Meta traversals count
  -- their depth against `maxRecDepth`.
  withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := 1000000 }) do
  let c ← whnfD c
  let_expr ByteArray.mk arr := c | return none
  let arr ← whnfR arr
  let l ← match_expr arr with
    | Array.mk _ l => pure l
    | _ => return none
  let l ← if l.isLet then zetaReduce l else pure l
  let some (_, elems) := l.listLit? | return none
  let mut out : Array Nat := Array.mkEmpty elems.length
  for e in elems do
    let some v := byteLit? e | return none
    out := out.push v
  return some out

/-- Big-endian value of `n` bytes of `bytes` at `off`, zero-padded past the end. -/
def readNat (bytes : Array Nat) (off n : Nat) : Nat :=
  (List.range n).foldl (fun acc j => acc * 256 + bytes.getD (off + j) 0) 0

/-- A kernel-checked proof of the closed equation `lhs = rhs` by evaluation (`decide`),
stored as an auxiliary theorem so that the kernel evaluates it once, by `whnf` (comparing
the two sides by lazy unfolding instead can recurse deeply on large numerals). -/
def kernelEq (lhs rhs : Expr) : MetaM Expr := do
  let eq ← mkEq lhs rhs
  return mkConst (← mkAuxLemma [] eq (← mkDecideProof eq))

/-- Evaluate pushed immediates `Bytes.toWord (readBytes code i n)` and word-sized code reads
`readBytes code i 32` for literal `code` and numerals `i`, `n`. Each rewrite is proved by a
kernel evaluation (`kernelEq`). -/
simproc_decl reduceCodeImm (_) := fun e => do
  match_expr e with
  | Bytes.toWord b =>
    let_expr readBytes c i n := b | return .continue
    let some i ← (evalNat i).run | return .continue
    let some n ← (evalNat n).run | return .continue
    let some bytes ← codeBytes? c | return .continue
    let v := readNat bytes i n % 2 ^ 256
    let rhs := mkApp2 (mkConst ``BitVec.ofNat) (mkRawNatLit 256) (mkRawNatLit v)
    return .visit { expr := rhs, proof? := some (← kernelEq e rhs) }
  | readBytes c i n =>
    let some n' ← (evalNat n).run | return .continue
    unless n' == 32 do return .continue
    let some i ← (evalNat i).run | return .continue
    let some bytes ← codeBytes? c | return .continue
    let v := readNat bytes i 32
    let w := mkApp2 (mkConst ``BitVec.ofNat) (mkRawNatLit 256) (mkRawNatLit v)
    let rhs := mkApp (mkConst ``Bytes.ofWord) w
    return .visit { expr := rhs, proof? := some (← kernelEq e rhs) }
  | _ => return .continue

/-! ## Side conditions -/

/-- Discharge a side goal of a step lemma applied to a machine with literal code: code
bytes and jump destinations in the kernel, the rest with `evm_disch`. -/
elab "sol_disch" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let lhs? := match_expr t with
    | Eq _ lhs _ => some lhs
    | _ => none
  let isCodeByte ← match lhs? with
    | some lhs => match_expr lhs with
      | GetElem?.getElem? coll _ _ _ _ _ _ => pure (coll == mkConst ``ByteArray)
      | _ => pure false
    | none => pure false
  let isJumpDest := match lhs? with
    | some lhs => lhs.isAppOf ``isValidJumpDest
    | none => false
  if isCodeByte then
    evalTactic (← `(tactic| (try dsimp only); decide +kernel))
  else if isJumpDest then
    evalTactic (← `(tactic| (try dsimp only)))
    evalTactic (← `(tactic| apply EvmLean.Solidity.isValidJumpDest_of_mem))
    evalTactic (← `(tactic| decide +kernel))
  else
    -- Closed side goals (literal JUMPI conditions, stack bounds) are evaluated by the kernel:
    -- the elaborator's `rfl`/`decide` can unfold large numerals until the recursion limit,
    -- a runtime error that `first` does not catch.
    if !t.hasFVar && !t.hasMVar then
      let s ← saveState
      try
        evalTactic (← `(tactic| decide +kernel))
        return
      catch _ => s.restore
    tryCatchRuntimeEx (evalTactic (← `(tactic| evm_disch))) fun e =>
      throwError "sol_disch: {e.toMessageData}"

/-! ## Lemma selection by opcode -/

/-- The step lemmas (for a running machine) that can apply to opcode byte `b`, as tactic
scripts. -/
def stepTactics (b : Nat) : MetaM (List (TSyntax `tactic)) := do
  let app (n : Name) : MetaM (TSyntax `tactic) :=
    `(tactic| (apply $(mkIdent (`EvmLean.Interpreter ++ n)); all_goals sol_disch))
  let names : List Name := match b with
    | 0x01 => [`step_add] | 0x02 => [`step_mul] | 0x03 => [`step_sub]
    | 0x04 => [`step_div] | 0x05 => [`step_sdiv] | 0x06 => [`step_mod]
    | 0x07 => [`step_smod] | 0x08 => [`step_addmod] | 0x09 => [`step_mulmod]
    | 0x0a => [`step_exp] | 0x0b => [`step_signextend]
    | 0x10 => [`step_lt] | 0x11 => [`step_gt] | 0x12 => [`step_slt] | 0x13 => [`step_sgt]
    | 0x14 => [`step_eq] | 0x15 => [`step_iszero] | 0x16 => [`step_and] | 0x17 => [`step_or]
    | 0x18 => [`step_xor] | 0x19 => [`step_not] | 0x1a => [`step_byte] | 0x1b => [`step_shl]
    | 0x1c => [`step_shr] | 0x1d => [`step_sar] | 0x20 => [`step_keccak256]
    | 0x30 => [`step_address] | 0x32 => [`step_origin] | 0x33 => [`step_caller]
    | 0x34 => [`step_callvalue] | 0x35 => [`step_calldataload]
    | 0x36 => [`step_calldatasize] | 0x38 => [`step_codesize] | 0x39 => [`step_codecopy]
    | 0x3a => [`step_gasprice] | 0x3d => [`step_returndatasize] | 0x41 => [`step_coinbase]
    | 0x42 => [`step_timestamp] | 0x43 => [`step_number] | 0x44 => [`step_prevrandao]
    | 0x45 => [`step_gaslimit] | 0x46 => [`step_chainid] | 0x47 => [`step_selfbalance]
    | 0x48 => [`step_basefee]
    | 0x50 => [`step_pop] | 0x51 => [`step_mload] | 0x52 => [`step_mstore]
    | 0x53 => [`step_mstore8] | 0x54 => [`step_sload] | 0x55 => [`step_sstore]
    | 0x56 => [`step_jump] | 0x57 => [`step_jumpi_of_eq_zero, `step_jumpi_of_ne_zero]
    | 0x58 => [`step_pc] | 0x59 => [`step_msize] | 0x5a => [`step_gas]
    | 0x5b => [`step_jumpdest] | 0x5f => [`step_push0]
    | 0xa0 => [`step_log0] | 0xa1 => [`step_log1] | 0xa2 => [`step_log2]
    | 0xa3 => [`step_log3] | 0xa4 => [`step_log4]
    | _ => []
  if 0x60 ≤ b ∧ b ≤ 0x7f then
    let n := Syntax.mkNumLit (toString (b - 0x5f))
    return [← `(tactic| (apply EvmLean.Interpreter.step_pushN $n; all_goals sol_disch))]
  if 0x80 ≤ b ∧ b ≤ 0x8f then
    return [← app (Name.mkSimple s!"step_dup{b - 0x7f}")]
  if 0x90 ≤ b ∧ b ≤ 0x9f then
    return [← app (Name.mkSimple s!"step_swap{b - 0x8f}")]
  names.mapM app

/-- The halting step lemmas (top-level frame) for opcode byte `b`. -/
def haltTactics (b : Nat) : MetaM (List (TSyntax `tactic)) := do
  let app (n : Name) : MetaM (TSyntax `tactic) :=
    `(tactic| (apply $(mkIdent (`EvmLean.Interpreter ++ n)); all_goals sol_disch))
  match b with
  | 0x00 => return [← app `step_stop_top]
  | 0xf3 => return [← app `step_return_top]
  | 0xfd => return [← app `step_revert_top]
  | _ => return []

/-- The machine `m` of the first `run n m` in `e`. -/
def findRunMachine? (e : Expr) : Option Expr :=
  match e.find? fun x => x.isAppOfArity ``EvmLean.Interpreter.run 2 with
  | some (.app _ m) => some m
  | _ => none

/-- The opcode byte at the `pc` of the machine in the goal's `run n m`. -/
def currentByte : TacticM Nat := withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some m := findRunMachine? t | throwError "sol_step: no `run _ m` in the goal"
  let fr ← mkAppM ``Machine.frame #[m]
  let pc ← whnfD (← mkAppM ``Frame.pc #[fr])
  let some pc ← (evalNat pc).run | throwError "sol_step: pc is not a numeral: {pc}"
  let some bytes ← codeBytes? (← mkAppM ``Frame.code #[fr])
    | throwError "sol_step: the code is not a byte-array literal"
  let some b := bytes[pc]? | throwError "sol_step: pc {pc} past the end of the code"
  return b

/-- Combine alternatives with `first`, failing with `msg` if none applies. -/
def firstOf (tacs : List (TSyntax `tactic)) (msg : String) : TacticM Unit := do
  for t in tacs do
    let s ← saveState
    try
      evalTactic t
      return
    catch _ => s.restore
  throwError msg

/-- Advance `run (n + 1) m` by one instruction of literal bytecode (see the module doc).
`sol_step [h₁, …]` adds simp lemmas to the normalization of the new machine. -/
syntax "sol_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| sol_step) => do evalTactic (← `(tactic| sol_step []))
  | `(tactic| sol_step [$extra,*]) => do
    let b ← currentByte
    let halts ← haltTactics b
    if halts.isEmpty then
      let tacs ← stepTactics b
      if tacs.isEmpty then throwError "sol_step: no step lemma for opcode {b}"
      evalTactic (← `(tactic| rw [EvmLean.Interpreter.run_succ_of_running ?h]))
      let gs ← getGoals
      let some hg ← gs.findM? (fun g => return (← g.getTag).eraseMacroScopes == `h)
        | throwError "sol_step: no side goal"
      let rest := gs.filter (· != hg)
      setGoals [hg]
      firstOf tacs s!"sol_step: no step lemma applies to opcode {b}"
      setGoals rest
    else
      evalTactic (← `(tactic| rw [EvmLean.Interpreter.run_succ_of_done ?h]))
      let gs ← getGoals
      let some hg ← gs.findM? (fun g => return (← g.getTag).eraseMacroScopes == `h)
        | throwError "sol_step: no side goal"
      let rest := gs.filter (· != hg)
      setGoals [hg]
      firstOf halts s!"sol_step: no halting lemma applies to opcode {b}"
      setGoals rest
    evalTactic (← `(tactic| try evm_norm [EvmLean.Solidity.Exec.reduceCodeImm, sol_norm,
      Nat.reduceMod, Nat.reducePow, Nat.reduceLT, $extra,*]))

/-- Repeat `sol_step` while it succeeds. -/
syntax "sol_steps" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| sol_steps) => `(tactic| repeat sol_step)
  | `(tactic| sol_steps [$extra,*]) => `(tactic| repeat sol_step [$extra,*])

end EvmLean.Solidity.Exec

attribute [sol_norm] BitVec.ofNat_eq_ofNat EvmLean.Interpreter.ofNat List.length_cons
  List.length_nil List.set_cons_zero List.set_cons_succ true_or or_true false_or or_false
