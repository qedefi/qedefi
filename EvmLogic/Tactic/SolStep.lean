import Lean
import EvmLogic.Tactic.EvmStep
import EvmLogic.Solidity.JumpDest
import EvmLogic.Solidity.Steps
import EvmLogic.Solidity.Memory
import EvmLogic.Solidity.Word
import EvmLogic.Program.Code
import EvmLogic.Tactic.FastStep

/-!
# Symbolic execution of compiled contracts: `sol_step`

`evm_step` does not scale to solc output (1–25 kB). `sol_step` reads the opcode byte at `pc`
itself, applies only the step lemmas for that byte, and checks code bytes, jump destinations
and pushed immediates by kernel evaluation (`decide +kernel`, auxiliary theorems): the
elaborator's `rfl`/`decide` hit the recursion limit on long literals.
-/

namespace EvmLogic.Tactic.SolStep
open EvmLean EvmLogic.Solidity Lean Elab Tactic EvmLogic.Tactic Meta Simp EvmLean.Interpreter

/-! ## Reading literal bytecode -/

def byteLit? (e : Expr) : Option Nat :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit?
  | _ => e.rawNatLit?

/-- The bytes of a literal `ByteArray` (zeta-reducing the `have` chain of long list literals). -/
def codeBytes? (c : Expr) : MetaM (Option (Array Nat)) :=
  -- Long literals are deep terms; Meta traversals count their depth against `maxRecDepth`.
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

def readNat (bytes : Array Nat) (off n : Nat) : Nat :=
  (List.range n).foldl (fun acc j => acc * 256 + bytes.getD (off + j) 0) 0

/-- A proof of the closed `lhs = rhs` by `decide`, checked by the kernel with the enclosing
declaration (comparing the sides by lazy unfolding instead recurses too deeply on large
numerals). -/
def kernelEq (lhs rhs : Expr) : MetaM Expr := do
  trace[EvmLean.wp] "kernelEq: {lhs}"
  let eq ← mkEq lhs rhs
  -- inline (no auxiliary declaration: adding one waits for all earlier kernel checks)
  mkDecideProof eq

/-- Evaluate `Bytes.toWord (readBytes code i n)` and `readBytes code i 32` for literal code. -/
simproc_decl reduceCodeImm (_) := fun e => do
  match_expr e with
  | Bytes.toWord b =>
    let_expr readBytes c i n := b | return .continue
    let some i ← (evalNat i).run | return .continue
    let some n ← (evalNat n).run | return .continue
    let some bytes ← codeBytes? c | return .continue
    let v := readNat bytes i n % 2 ^ 256
    let rhs := mkApp2 (mkConst ``BitVec.ofNat) (mkRawNatLit 256) (mkRawNatLit v)
    if n ≤ 32 then
      if let some (tab, ok, _) ← EvmLogic.Program.codeTable? c then
        let pf ← EvmLogic.Program.wordFact c tab ok i n v
        return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint pf (← mkEq e rhs)) }
    return .visit { expr := rhs, proof? := some (← kernelEq e rhs) }
  | readBytes c i n =>
    let some n' ← (evalNat n).run | return .continue
    unless n' == 32 do return .continue
    let some i ← (evalNat i).run | return .continue
    let some bytes ← codeBytes? c | return .continue
    let v := readNat bytes i 32
    let w := mkApp2 (mkConst ``BitVec.ofNat) (mkRawNatLit 256) (mkRawNatLit v)
    let rhs := mkApp (mkConst ``Bytes.ofWord) w
    if let some (tab, ok, _) ← EvmLogic.Program.codeTable? c then
      if let some pbytes ← EvmLogic.Program.codeBytes? c then
        -- `readBytes c i 32 = ⟨⟨l⟩⟩` by lookups, `Bytes.ofWord w = ⟨⟨l⟩⟩` by evaluation
        let h1 ← EvmLogic.Program.bytesFact c tab ok pbytes i 32
        let some (_, _, lit) := (← inferType h1).eq? | return .continue
        let h2 ← EvmLogic.Program.kernelFact (← mkEq rhs lit) lit
        let pf ← mkEqTrans h1 (← mkEqSymm h2)
        return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint pf (← mkEq e rhs)) }
    return .visit { expr := rhs, proof? := some (← kernelEq e rhs) }
  | _ => return .continue

/-! ## Side conditions -/

/-- Discharge a step-lemma side goal on literal code: code bytes and jump destinations in the
kernel, the rest with `evm_disch`. -/
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
    evalTactic (← `(tactic| (try dsimp only); table_decide))
  else if isJumpDest then
    evalTactic (← `(tactic| (try dsimp only)))
    evalTactic (← `(tactic| apply EvmLogic.Solidity.isValidJumpDest_of_mem))
    evalTactic (← `(tactic| table_decide))
  else
    -- Closed goals go to the kernel: the elaborator's `rfl`/`decide` can hit the recursion
    -- limit on large numerals, a runtime error that `first` does not catch.
    if !t.hasFVar && !t.hasMVar then
      let s ← saveState
      try
        evalTactic (← `(tactic| table_decide))
        return
      catch _ => s.restore
    tryCatchRuntimeEx (evalTactic (← `(tactic| evm_disch))) fun e =>
      throwError "sol_disch: {e.toMessageData}"

/-! ## Lemma selection by opcode -/

/-- The step lemmas that can apply to opcode byte `b`, as tactic scripts. -/
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

/-- Advance `run (n + 1) m` by one instruction of literal bytecode; `sol_step [h₁, …]` adds
simp lemmas to the normalization. -/
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
    trace[EvmLean.symStep] "byte {b}"
    evalTactic (← `(tactic| try evm_norm [EvmLogic.Tactic.SolStep.reduceCodeImm, sol_norm,
      Nat.reduceMod, Nat.reducePow, Nat.reduceLT, $extra,*]))

/-- Repeat `sol_step` while it succeeds. -/
syntax "sol_steps" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

/-- The fast stepper's configuration for a goal with `run _ m` on literal code: the
normalization and side conditions of `sol_step`. -/
def solFastCfg (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TacticM (Option FastStep.Cfg) := withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some m := findRunMachine? t | return none
  let code ← whnfR (mkApp (mkConst ``Frame.code) (← whnfR (mkApp (mkConst ``Machine.frame) m)))
  let some bytes ← EvmLogic.Program.codeBytes? code | return none
  let normStx ← `(tactic| evm_norm [EvmLogic.Tactic.SolStep.reduceCodeImm, sol_norm,
      Nat.reduceMod, Nat.reducePow, Nat.reduceLT, $extra,*])
  let some simpStx ← liftMacroM <| expandMacro? normStx | return none
  let r ← mkSimpContext simpStx (eraseLocal := false)
  return some {
    simpCtx := r.ctx, simprocs := r.simprocs
    codeFact := fun c pc b => EvmLogic.Program.codeFact c pc b
    pushFact := fun c pc n => do
      let some bs ← EvmLogic.Program.codeBytes? c | return none
      return some (← EvmLogic.Program.pushFact c bs pc n)
    bytes := fun c => do
      if c == code then return some bytes
      EvmLogic.Program.codeBytes? c
    disch := do evalTactic (← `(tactic| sol_disch)) }

elab_rules : tactic
  | `(tactic| sol_steps $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let one : TacticM Bool := do
      let s ← saveState
      try
        evalTactic (← `(tactic| sol_step [$extra,*]))
        return true
      catch _ =>
        s.restore
        return false
    let cfg ← solFastCfg extra
    let mut first := true
    for _ in [0:1000000] do
      if let some c := cfg then
        discard <| FastStep.fastRunSteps c first
      first := false
      unless ← one do return

end EvmLogic.Tactic.SolStep

attribute [sol_norm] BitVec.ofNat_eq_ofNat EvmLean.Interpreter.ofNat List.length_cons
  List.length_nil List.set_cons_zero List.set_cons_succ true_or or_true false_or or_false
