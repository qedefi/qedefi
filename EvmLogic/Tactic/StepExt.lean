import EvmLogic.Tactic.Mcopy
import EvmLogic.Tactic.Abstract
import EvmLogic.Program.Call

/-!
# Extensible stepping: `pwp_step_ext`, `pwp_xsteps`, `pwp_xrun_to`

`pwp_steps` steps the instructions of `stepLemmasFor` (a fixed table) and stops at anything
else. Compiled code also has `EXTCODESIZE` (solc's check before a call that returns nothing),
`RETURNDATACOPY` (decoding a call's result), `CALLDATACOPY`, `CODECOPY` (32-byte constants such
as event topics) and `MCOPY`, whose step lemmas need their own side conditions and
normalization. They used to be applied by hand (`WP.of_step` + `pwp_norm`).

`pwp_step_ext [h, …]` is an **extension point**, like `evm_step_core`: every rule added by

```
macro_rules | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| …)
```

is tried (latest first) when the table has no lemma for the next instruction. A rule must fail
quickly when it does not apply (start with the code byte, `pcode_fact`). This file registers
`EXTCODESIZE`, `RETURNDATACOPY`/`CALLDATACOPY` (empty or not, literal length), `CODECOPY` and
`MCOPY`.

`pwp_xsteps [h, …]` / `pwp_xrun_to pc, … [h, …]` are `pwp_steps` / `pwp_run_to` that also try
the extensions. The plain tactics are unchanged (so proofs that step an instruction by hand
after `pwp_steps` keep their goals).
-/

namespace EvmLogic.Program
open EvmLean Lean Elab Tactic EvmLogic.Tactic Meta EvmLean.Interpreter

/-- Extension point of `pwp_xsteps`: one instruction outside the table of `pwp_step`. -/
syntax "pwp_step_ext" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| pwp_step_ext [$_,*]) => `(tactic| fail "pwp_step_ext: no extension applies")

/-- Gas side condition of a copy: `3 + 3 · ⌈z / 32⌉ + memoryCost … ≤ gas`. -/
macro "copy_gas_disch" : tactic =>
  `(tactic| first | (simp only [memoryCost]; evm_gas) | assumption | fail "copy_gas_disch")

/-- Length side condition of a copy (`z.toNat ≠ 0`, `z.toNat = 0`, `y + z ≤ returnData.size`). -/
macro "copy_len_disch" : tactic =>
  `(tactic| first | decide | (simp only [Bytes.size_ofWord, BitVec.reduceToNat]; decide) |
    (dsimp only; omega) | assumption | fail "copy_len_disch")

-- `EXTCODESIZE`: the access cost is at most 2600 (`accessCost_le`).
macro_rules
  | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| (
    apply WP.of_step
    case h =>
      refine step_extcodesize (by pcode_fact) rfl (by pwp_disch)
        (Nat.le_trans (accessCost_le _) (by pwp_disch))
    case hs => same_frame
    pwp_norm [$extra,*]))

-- `CODECOPY` of a literal window (`pwp_codecopy`).
macro_rules
  | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| (
    pwp_codecopy
    pwp_norm [$extra,*]))

-- `CALLDATACOPY` of a non-empty literal length.
macro_rules
  | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| (
    apply WP.of_step
    case h =>
      apply EvmLean.Interpreter.step_calldatacopy
      case hcode => pcode_fact
      case hstk => exact rfl
      case hz => copy_len_disch
      case hgas => copy_gas_disch
    case hs => same_frame
    pwp_norm [$extra,*]))

-- `CALLDATACOPY` of nothing.
macro_rules
  | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| (
    apply WP.of_step
    case h =>
      apply EvmLean.Interpreter.step_calldatacopy_zero
      case hcode => pcode_fact
      case hstk => exact rfl
      case hz => copy_len_disch
      case hgas => pwp_disch
    case hs => same_frame
    pwp_norm [$extra,*]))

-- `RETURNDATACOPY` of a non-empty literal length inside the return data.
macro_rules
  | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| (
    apply WP.of_step
    case h =>
      apply EvmLean.Interpreter.step_returndatacopy
      case hcode => pcode_fact
      case hstk => exact rfl
      case hz => copy_len_disch
      case hrd => copy_len_disch
      case hgas => copy_gas_disch
    case hs => same_frame
    pwp_norm [Memory.ofWord_extract_zero_32, Memory.write_ofWord, $extra,*]))

-- `RETURNDATACOPY` of nothing.
macro_rules
  | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| (
    apply WP.of_step
    case h =>
      apply EvmLean.Interpreter.step_returndatacopy_zero
      case hcode => pcode_fact
      case hstk => exact rfl
      case hz => copy_len_disch
      case hrd => copy_len_disch
      case hgas => pwp_disch
    case hs => same_frame
    pwp_norm [$extra,*]))

-- `MCOPY`, empty or not (`pwp_mcopy`, `pwp_mcopy_zero`).
macro_rules
  | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| pwp_mcopy [$extra,*])

macro_rules
  | `(tactic| pwp_step_ext [$extra,*]) => `(tactic| pwp_mcopy_zero [$extra,*])

/-- One step of `pwp_xsteps`: the fast stepper, the table, then the extensions. -/
def pwpStepExt (cfg : Option FastStep.Cfg) (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma))
    (normAll : Bool) : TacticM Bool := do
  if ← pwpStepFast cfg extra normAll then return true
  tryTac (evalTactic (← `(tactic| pwp_step_ext [$extra,*])))

/-- `pwp_steps` that also steps the instructions registered with `pwp_step_ext`. -/
syntax "pwp_xsteps" (ppSpace num)? (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| pwp_xsteps $[$n]? $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let limit := (n.map (·.getNat)).getD 1000000
    let cfg ← pwpFastCfg extra
    runChunked (limit := limit) fun i => pwpStepExt cfg extra (normAll := i == 0)

/-- `pwp_run_to` that also steps the instructions registered with `pwp_step_ext`. -/
syntax "pwp_xrun_to " num,+ (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| pwp_xrun_to $pcs,* $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let pcs := pcs.getElems.toList.map (·.getNat)
    let cfg ← pwpFastCfg extra
    runChunked fun i => do
      if i > 0 then
        if let some pc ← wpGoalPc? (← getMainGoal) then
          if pcs.contains pc then return false
      pwpStepExt cfg extra (normAll := i == 0)

end EvmLogic.Program
