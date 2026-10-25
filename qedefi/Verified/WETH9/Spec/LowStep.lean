import Verified.WETH9.Spec.LowGas

/-!
# `low_step`: driving `LowOK` goals over literal code

`low_step [h₁, …]` advances a goal `LowOK Hf M` (the code of `M` a byte-array literal, its pc a
numeral) by one instruction: it reads the opcode byte, applies `LowOK.step` with the step lemmas
`sol_step` uses (and `step_balance`), discharges their side conditions with `sol_disch`, and
normalizes the next machine as `sol_step` does (plus the given lemmas). At `STOP`, `RETURN` and
`REVERT` it applies `LowOK.stop`/`LowOK.revert` and leaves the goal `Hf M' o`. `low_steps`
repeats while an instruction continues the frame.
-/

namespace Verified.WETH9.Spec
open Lean Elab Tactic Meta EvmLean EvmLean.Interpreter EvmLogic.Tactic.SolStep

/-- The machine of a goal `LowOK Hf M`. -/
def lowMachine? (t : Expr) : MetaM (Option Expr) := do
  let t := (← instantiateMVars t).cleanupAnnotations
  if t.isAppOfArity ``LowOK 2 then return some t.appArg! else return none

/-- The opcode byte at the pc of the machine of the main goal. -/
def lowByte : TacticM Nat := withMainContext do
  let some m ← lowMachine? (← getMainTarget) | throwError "low_step: not a `LowOK` goal"
  let fr ← mkAppM ``Machine.frame #[m]
  let pc ← whnfD (← mkAppM ``Frame.pc #[fr])
  let some pc ← (evalNat pc).run | throwError "low_step: pc is not a numeral: {pc}"
  let some bytes ← codeBytes? (← mkAppM ``Frame.code #[fr])
    | throwError "low_step: the code is not a byte-array literal"
  let some b := bytes[pc]? | throwError "low_step: pc {pc} past the end of the code"
  return b

/-- Run `t` on the first main goal whose type satisfies `p`, keeping the others. -/
def onGoal (p : Expr → MetaM Bool) (what : String) (t : TacticM Unit) : TacticM Unit := do
  let gs ← getGoals
  let some g ← gs.findM? (fun g => do
      if ← g.isAssigned then return false
      p (← instantiateMVars (← g.getType)).cleanupAnnotations)
    | throwError "low_step: no goal {what}"
  setGoals [g]
  t
  let rest ← getGoals
  setGoals (rest ++ gs.filter (· != g))

def lowNorm (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Unit := do
  evalTactic (← `(tactic| try evm_norm [EvmLogic.Tactic.SolStep.reduceCodeImm, sol_norm,
    Nat.reduceMod, Nat.reducePow, Nat.reduceLT, Nat.sub_sub, Memory.loadWord_expand,
    Memory.read_expand, Memory.loadWord_storeWord, Memory.read_storeWord,
    Memory.loadWord_storeWord_of_disjoint, Memory.read_storeWord_of_disjoint,
    EvmLogic.Program.reduceClosedWord, Bytes.size_ofWord, Bytes.toWord_ofWord,
    EvmLogic.Solidity.iszero_zero, EvmLogic.Solidity.iszero_one, $extra,*]))

/-- One `low_step`; `false` if no rule applies (a `JUMPI` on an undecided condition, …). -/
def lowStep (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Bool := do
  let b ← lowByte
  let bS := Syntax.mkNumLit (toString b)
  let s ← saveState
  try
    if b == 0xf3 then
      evalTactic (← `(tactic| refine LowOK.stop (b := $bS) (by sol_disch)
        (readsGasB_decode_false _ _ (by decide)) (exec_return rfl (by sol_disch)) ?_))
      return true
    if b == 0xfd then
      evalTactic (← `(tactic| refine LowOK.revert (b := $bS) (by sol_disch)
        (readsGasB_decode_false _ _ (by decide)) (exec_revert rfl (by sol_disch)) ?_))
      return true
    if b == 0x00 then
      evalTactic (← `(tactic| refine LowOK.stop (b := $bS) (by sol_disch)
        (readsGasB_decode_false _ _ (by decide)) (exec_stop _) ?_))
      return true
    let tacs ← if b == 0x31 then
        pure [← `(tactic| (apply Verified.WETH9.Spec.step_balance; all_goals sol_disch))]
      else stepTactics b
    if tacs.isEmpty then throwError "low_step: no step lemma for opcode {b}"
    evalTactic (← `(tactic| refine' LowOK.step (b := $bS) ?_
      (readsGasB_decode_false _ _ (by decide)) ?_ ?_ ?_))
    onGoal (fun t => return t.isAppOf ``Eq && (t.getArg! 1).isAppOf ``GetElem?.getElem?) "code"
      (evalTactic (← `(tactic| sol_disch)))
    onGoal (fun t => return t.isAppOf ``Eq && (t.getArg! 1).isAppOf ``EvmLean.Interpreter.step)
      "step" (firstOf tacs s!"low_step: no step lemma applies to opcode {b}")
    onGoal (fun t => return t.isAppOf ``EvmLogic.Program.SameFrame) "same frame"
      (evalTactic (← `(tactic| same_frame)))
    onGoal (fun t => return t.isAppOf ``LowOK) "next" (lowNorm extra)
    pruneSolvedGoals
    return true
  catch e =>
    trace[EvmLean.symStep] "low_step failed at byte {b}: {e.toMessageData}"
    s.restore
    return false

/-- Advance a `LowOK` goal by one instruction. -/
syntax "low_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| low_step $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    unless ← lowStep extra do throwError "low_step: no rule applies to the next instruction"

/-- Repeat `low_step` while the next instruction continues the frame. -/
syntax "low_steps" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| low_steps $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    for _ in [0:100000] do
      let b ← lowByte
      if b == 0xf3 || b == 0xfd || b == 0x00 then return
      unless ← lowStep extra do return

/-- At an `SSTORE` of a static frame: every version fails (`LowOK.error`); leaves the goal
`∀ e, Hf M (.halt e)`. -/
macro "low_static " h:term : tactic => `(tactic| (
  refine LowOK.error (b := 0x55) (by sol_disch) (readsGasB_decode_false _ _ (by decide))
    (exec_sstore_static rfl $h (by sol_disch) (by sol_disch)) ?_))

end Verified.WETH9.Spec
