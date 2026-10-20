import EvmLogic.GasMono.CodeFails
import EvmLogic.Tactic.Patched

/-!
# `fails_step`: driving the `Fails` rules over compiled code

A goal `Fails code pc s` (`GasMono.CodeFails`) with literal `pc`, `code` a literal or patched
(symbolic immutables) code constant, and `s` a list whose relevant prefix is explicit, is
advanced by `fails_step`:

* the opcode byte at `pc` is read at the meta level, and the fact `code[pc]? = some b` is a
  kernel-checked `pcode_fact` (`EvmLeanProofs.Solidity.ExtraPatchedWP`);
* the `Fails` rule for that opcode is applied (`hop_*` below identify the instruction shapes
  `unOp`, `binOp`, `pushValue`); `PUSHn` immediates come from `ppushFact?`, `JUMPI` conditions
  are decided by `fails_cond`, values the rules quantify over are introduced;
* the new goal is normalized (pc arithmetic, `toNat` of pushed jump targets, `List.set`).

`fails_steps` repeats `fails_step` until the goal is closed (`REVERT`, `INVALID`) or no rule
applies.
-/

namespace EvmLean.Program.GasMono

open Interpreter

/-! ## Instruction shapes -/

/-- `ADD` is a `binOp`. -/
theorem hop_add : ∀ fk, exec (Opcode.decode fk 0x01) = binOp Gas.veryLow (· + ·) := by
  intro fk; cases fk <;> rfl
/-- `MUL` is a `binOp`. -/
theorem hop_mul : ∀ fk, exec (Opcode.decode fk 0x02) = binOp Gas.low (· * ·) := by
  intro fk; cases fk <;> rfl
/-- `SUB` is a `binOp`. -/
theorem hop_sub : ∀ fk, exec (Opcode.decode fk 0x03) = binOp Gas.veryLow (· - ·) := by
  intro fk; cases fk <;> rfl
/-- `DIV` is a `binOp`. -/
theorem hop_div : ∀ fk, exec (Opcode.decode fk 0x04) = binOp Gas.low Word.div := by
  intro fk; cases fk <;> rfl
/-- `LT` is a `binOp`. -/
theorem hop_lt : ∀ fk, exec (Opcode.decode fk 0x10) = binOp Gas.veryLow Word.lt := by
  intro fk; cases fk <;> rfl
/-- `GT` is a `binOp`. -/
theorem hop_gt : ∀ fk, exec (Opcode.decode fk 0x11) = binOp Gas.veryLow Word.gt := by
  intro fk; cases fk <;> rfl
/-- `EQ` is a `binOp`. -/
theorem hop_eq : ∀ fk, exec (Opcode.decode fk 0x14) = binOp Gas.veryLow Word.eq := by
  intro fk; cases fk <;> rfl
/-- `AND` is a `binOp`. -/
theorem hop_and : ∀ fk, exec (Opcode.decode fk 0x16) = binOp Gas.veryLow (· &&& ·) := by
  intro fk; cases fk <;> rfl
/-- `OR` is a `binOp`. -/
theorem hop_or : ∀ fk, exec (Opcode.decode fk 0x17) = binOp Gas.veryLow (· ||| ·) := by
  intro fk; cases fk <;> rfl
/-- `XOR` is a `binOp`. -/
theorem hop_xor : ∀ fk, exec (Opcode.decode fk 0x18) = binOp Gas.veryLow (· ^^^ ·) := by
  intro fk; cases fk <;> rfl
/-- `SHL` is a `binOp`. -/
theorem hop_shl : ∀ fk, exec (Opcode.decode fk 0x1b) = binOp Gas.veryLow Word.shl := by
  intro fk; cases fk <;> rfl
/-- `SHR` is a `binOp`. -/
theorem hop_shr : ∀ fk, exec (Opcode.decode fk 0x1c) = binOp Gas.veryLow Word.shr := by
  intro fk; cases fk <;> rfl
/-- `ISZERO` is a `unOp`. -/
theorem hop_iszero : ∀ fk, exec (Opcode.decode fk 0x15) = unOp Gas.veryLow Word.iszero := by
  intro fk; cases fk <;> rfl
/-- `NOT` is a `unOp`. -/
theorem hop_not : ∀ fk, exec (Opcode.decode fk 0x19) = unOp Gas.veryLow (~~~ ·) := by
  intro fk; cases fk <;> rfl
/-- `RETURNDATASIZE` is a `pushValue`. -/
theorem hop_returndatasize : ∀ fk, exec (Opcode.decode fk 0x3d) =
    pushValue Gas.base fun m => ofNat m.frame.returnData.size := by
  intro fk; cases fk <;> rfl
/-- `CALLER` is a `pushValue`. -/
theorem hop_caller : ∀ fk, exec (Opcode.decode fk 0x33) =
    pushValue Gas.base fun m => Word.ofAddress m.frame.msg.caller := by
  intro fk; cases fk <;> rfl
/-- `ADDRESS` is a `pushValue`. -/
theorem hop_address : ∀ fk, exec (Opcode.decode fk 0x30) =
    pushValue Gas.base fun m => Word.ofAddress m.frame.msg.currentTarget := by
  intro fk; cases fk <;> rfl

/-! ## The tactic -/

open Lean Elab Tactic Meta

/-- The `Fails` rule and shape lemma for an opcode of shape `unOp`/`binOp`/`pushValue`. -/
def shapeRule (b : Nat) : Option (Name × Name) :=
  let bin : List (Nat × Name) := [(0x01, ``hop_add), (0x02, ``hop_mul), (0x03, ``hop_sub),
    (0x04, ``hop_div), (0x10, ``hop_lt), (0x11, ``hop_gt), (0x14, ``hop_eq), (0x16, ``hop_and),
    (0x17, ``hop_or), (0x18, ``hop_xor), (0x1b, ``hop_shl), (0x1c, ``hop_shr)]
  let un : List (Nat × Name) := [(0x15, ``hop_iszero), (0x19, ``hop_not)]
  let pv : List (Nat × Name) := [(0x3d, ``hop_returndatasize), (0x33, ``hop_caller),
    (0x30, ``hop_address)]
  match bin.lookup b, un.lookup b, pv.lookup b with
  | some h, _, _ => some (``Fails.binOp, h)
  | _, some h, _ => some (``Fails.unOp, h)
  | _, _, some h => some (``Fails.pushValue, h)
  | _, _, _ => none

/-- `x AND 0 = 0` (a failed call's flag masks any other condition). -/
theorem word_and_zero (x : Word) : x &&& 0 = 0 := BitVec.and_zero

/-- `0 AND x = 0`. -/
theorem word_zero_and (x : Word) : 0 &&& x = 0 := BitVec.zero_and

/-- Decide a `JUMPI` condition `y = 0` or `y ≠ 0`, simplifying `x &&& 0` first. -/
macro "fails_cond" : tactic =>
  `(tactic| first
    | rfl
    | decide
    | (simp only [word_and_zero, word_zero_and, BitVec.and_zero, BitVec.zero_and]
       first | rfl | decide))

/-- Normalize a `Fails` goal: pc arithmetic, jump targets, stack updates. -/
macro "fails_norm" : tactic =>
  `(tactic| try simp only [Nat.reduceAdd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    List.set_cons_zero, List.set_cons_succ])

/-- Advance a goal `Fails code pc s` by one instruction. Returns `false` (goal unchanged) if no
rule applies. -/
def failsStep : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let_expr Fails code pcE _ := t | return false
  let some pc ← (evalNat pcE).run | return false
  let some (bytes, pinfo) ← codeInfo? code | return false
  let some b := bytes[pc]? | return false
  let hb ← Term.exprToSyntax (← pcodeFact code pinfo pc b)
  let bn := b.toNat
  let saved ← saveState
  let attempt (t : TSyntax `tactic) : TacticM Bool := do
    tryCatchRuntimeEx
      (do withoutRecover (evalTactic t); return true)
      (fun _ => do saved.restore; return false)
  let tacs : List (TSyntax `tactic) ←
    if bn = 0xfd then pure [← `(tactic| exact Fails.revert $hb)]
    else if bn = 0xfe then pure [← `(tactic| exact Fails.invalid $hb)]
    else if bn = 0x50 then pure [← `(tactic| refine Fails.pop $hb ?_)]
    else if bn = 0x56 then pure [← `(tactic| refine Fails.jump $hb ?_)]
    else if bn = 0x57 then pure [← `(tactic| refine Fails.jumpi_zero $hb (by fails_cond) ?_),
      ← `(tactic| refine Fails.jumpi_ne_zero $hb (by fails_cond) ?_)]
    else if bn = 0x5b then pure [← `(tactic| refine Fails.jumpdest $hb ?_)]
    else if bn = 0x51 then pure [← `(tactic| (refine Fails.mload $hb ?_; intro))]
    else if bn = 0x52 then pure [← `(tactic| refine Fails.mstore $hb ?_)]
    else if bn = 0x3e then pure [← `(tactic| refine Fails.returndatacopy $hb ?_)]
    else if 0x5f ≤ bn ∧ bn ≤ 0x7f then do
      let n := bn - 0x5f
      let some hv ← ppushFact? code pinfo bytes pc n | pure []
      let hv ← Term.exprToSyntax hv
      let nS := Syntax.mkNumLit (toString n)
      pure [← `(tactic| refine Fails.push $nS (by decide) $hb $hv ?_)]
    else if 0x80 ≤ bn ∧ bn < 0x90 then do
      let kS := Syntax.mkNumLit (toString (bn - 0x80))
      pure [← `(tactic| refine Fails.dup ⟨$kS, by decide⟩ $hb rfl ?_)]
    else if 0x90 ≤ bn ∧ bn < 0xa0 then do
      let kS := Syntax.mkNumLit (toString (bn - 0x90))
      pure [← `(tactic| refine Fails.swap ⟨$kS, by decide⟩ $hb rfl ?_)]
    else match shapeRule bn with
      | some (rule, hop) =>
        let ruleI := mkIdent rule
        let hopI := mkIdent hop
        if rule == ``Fails.pushValue then
          pure [← `(tactic| (refine $ruleI $hopI $hb ?_; intro))]
        else pure [← `(tactic| refine $ruleI $hopI $hb ?_)]
      | none => pure []
  for tac in tacs do
    if ← attempt tac then
      if (← getGoals).isEmpty then return true
      evalTactic (← `(tactic| fails_norm))
      return true
  return false

/-- Advance a goal `Fails code pc s` by one instruction (see the module docstring). -/
elab "fails_step" : tactic => do
  unless ← failsStep do throwError "fails_step: no rule applies to the next instruction"

/-- Repeat `fails_step` until the goal is closed or no rule applies. -/
elab "fails_steps" : tactic => do
  for _ in [0:100000] do
    if (← getGoals).isEmpty then return
    unless ← failsStep do return

end EvmLean.Program.GasMono
