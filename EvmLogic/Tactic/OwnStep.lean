import EvmLogic.Program.Nested.Own
import EvmLogic.Program.Nested.OwnG
import EvmLogic.Tactic.SolStep

/-!
# Symbolic execution for `Own` and `OwnG`: `own_step`

A goal `Own S C m` (or `OwnG Halt G R S C Dm D m`) with a hypothesis `hF : Fr k m pc st mem w` (literal code `k.code`, numeral
`pc`) is advanced by one instruction: `own_step` reads the opcode byte at `pc`, applies the
matching rule of `EvmLogic.Program.Nested.Own` and normalizes the new `Fr` hypothesis (same
name). `S` must be `SstoreOk K`: away from an `SSTORE` it is discharged from the code byte; at
an `SSTORE` the goal `K key` is left for the user. A `JUMPI` leaves two goals (fall-through
with `hc : cond = 0`, jump with `hc : cond ≠ 0`); a decided condition closes the infeasible
one. A precompile `STATICCALL` leaves its side conditions. `own_steps` repeats while the next
instruction is neither an `SSTORE`, a symbolic `JUMPI` nor a call.

For `OwnG` goals also: `EXP`, `EXTCODESIZE`, `CALLER`, `ORIGIN`, `GASPRICE`, `SELFBALANCE`,
`LOG0`–`LOG4`, and `CALL`/`STATICCALL`/`DELEGATECALL` to any target (the issuance goal `?call`
and the doom-point goal `?doom` are left; the frame continues with the result `res`, output
`out` and world `w'`). A `STATICCALL` whose target is a literal at most `0x11` uses the
precompile rule. `STOP`/`RETURN` leave the goal `Halt` unless it is `True`.
-/

namespace EvmLogic.Program.Nested.OwnTac
open Lean Elab Tactic Meta EvmLean EvmLean.Interpreter EvmLogic.Program.Nested
open EvmLogic.Tactic.SolStep

/-- Side conditions of conditional normalization lemmas (memory disjointness, no overflow):
`decide`, then `omega` after unfolding word arithmetic on numerals. Extend with `macro_rules`. -/
syntax "own_disch" : tactic

macro_rules
  | `(tactic| own_disch) => `(tactic| first
      | decide
      | omega
      | (simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_mul, Nat.reducePow,
          Nat.reduceMod, Nat.reduceAdd] at *; omega))

/-- The normalization after a step (numerals, list updates, memory, code immediates), with
extra lemmas. -/
syntax "own_norm " ident (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| own_norm $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (try simp (disch := own_disch) only [Nat.reduceAdd, Nat.reduceMod,
      Nat.reduceSub, Nat.reduceMul, Fin.val_mk, Fin.isValue, BitVec.reduceToNat,
      BitVec.reduceOfNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceAnd,
      BitVec.reduceOr, BitVec.reduceNot, EvmLogic.Program.reduceClosedWord,
      List.set_cons_zero, List.set_cons_succ, reduceCodeImm, Fix.code,
      Memory.size_storeWord, Memory.size_expand, Memory.loadWord_expand, Memory.read_expand,
      Memory.loadWord_storeWord, Memory.read_storeWord, $extra,*] at $h:ident))

/-- Close `k.code[pc]? = some b` for literal code (kernel table lookup). -/
macro "own_code" : tactic => `(tactic| ((try simp only [Fix.code]); table_decide))

/-- The hypothesis `Fr k m pc st mem w` about the goal's machine: its name, `k` and `pc`. -/
def findFr (m : Expr) : TacticM (Option (FVarId × Name × Expr × Expr)) := withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let_expr Fr k m' pc _ _ _ := ty | continue
    if ← isDefEq m' m then return some (d.fvarId, d.userName, k, pc)
  return none

/-- A goal `Own S C m` (`false`) or `OwnG Halt G R S C Dm D m` (`true`), and its machine. -/
def ownGoal? (t : Expr) : MetaM (Option (Bool × Expr)) := do
  let t ← whnfR t.cleanupAnnotations
  if t.isAppOfArity ``Own 3 then return some (false, t.appArg!)
  else if t.isAppOfArity ``OwnB 9 then return some (true, t.appArg!)
  else return none

/-- A goal `OwnG Halt G R S C Dm D m` (the coinductive judgment). -/
def ownGGoal? (t : Expr) : MetaM Bool := do
  let t ← whnfR t.cleanupAnnotations
  return t.isAppOfArity ``OwnG 8

/-- The stack of the `Fr` hypothesis `h`. -/
def frStack? (h : FVarId) : MetaM (Option Expr) := do
  let ty ← instantiateMVars (← h.getType)
  let_expr Fr _ _ _ st _ _ := ty | return none
  return some st

/-- The leading elements of a list expression `a :: b :: …`. -/
partial def listElems (e : Expr) : List Expr :=
  match e.getAppFnArgs with
  | (``List.cons, #[_, a, rest]) => a :: listElems rest
  | _ => []

/-- A word literal (`n#256`, `OfNat`). -/
def wordLit? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  match_expr e with
  | BitVec.ofNat _ n => (evalNat n).run
  | OfNat.ofNat _ n _ => (evalNat n).run
  | _ => return none

/-- The rule script for opcode byte `b` at the goal; `none`: not supported. -/
def ruleFor (g : Bool) (b pc : Nat) (h mI : Ident) (pushVal : Option Nat) (preTarget : Bool)
    (sTriv : Bool := false) :
    MetaM (Option (TSyntax `tactic)) := do
  let ns : Name := if g then `OwnB else `Own
  let r (n : String) : Ident := mkIdent (ns ++ Name.mkSimple n)
  let hc := mkIdent (Name.mkSimple s!"hc{pc}")
  let memI := mkIdent `mem'
  let resI := mkIdent `res
  let hres := mkIdent `hres
  let bS := Syntax.mkNumLit (toString b)
  let ne : TSyntax `term ← if sTriv then `(True.intro)
    else `(Own.sstoreOk_of_ne (b := $bS) $h (by own_code) (by decide))
  if g then
    if b == 0x0a then
      return some (← `(tactic| refine OwnB.exp $h (by own_code) $ne (fun $mI $h => ?_)))
    let hRI := mkIdent (Name.mkSimple s!"hR{pc}")
    if b == 0x3b then
      return some (← `(tactic| refine OwnB.extcodesizeR $h (by own_code) $ne
        (fun $mI $h $hRI => ?_)))
    if b == 0x54 then
      return some (← `(tactic| refine OwnB.sloadR $h (by own_code) $ne (fun $mI $h $hRI => ?_)))
    if b == 0x53 then
      return some (← `(tactic| refine OwnB.mstore8 $h (by own_code) $ne (fun $mI $h => ?_)))
    if b == 0x33 then
      return some (← `(tactic| refine OwnB.pushValue (b := $bS) (fun fk => by cases fk <;> rfl)
        (fun _ h1 _ => by rw [h1]) $h (by own_code) $ne (fun $mI $h => ?_)))
    if b == 0x32 || b == 0x3a then
      return some (← `(tactic| refine OwnB.pushValue (b := $bS) (fun fk => by cases fk <;> rfl)
        (fun _ _ h2 => by rw [h2]) $h (by own_code) $ne (fun $mI $h => ?_)))
    if b == 0x47 then
      return some (← `(tactic| refine OwnB.pushAny (b := $bS) (fun fk => by cases fk <;> rfl)
        $h (by own_code) $ne (fun _ $mI $h => ?_)))
    if 0xa0 ≤ b ∧ b ≤ 0xa4 then
      let holes : Array (TSyntax `term) := Array.replicate (b - 0xa0) (← `(term| _))
      let ts ← `(term| [$holes,*])
      let lemma := mkIdent (Name.mkStr `OwnB s!"exec_log{b - 0xa0}")
      return some (← `(tactic| refine OwnB.log (b := $bS) (ts := $ts) $h (by own_code)
        $lemma $ne (fun $mI $h => ?_)))
    let outI := mkIdent `out
    let wI := mkIdent `w'
    -- Side-goal names unique in the proof (a pc may be reached on several paths).
    let used : Name → MetaM Bool := fun n => return ((← getMCtx).findUserName? n).isSome
    let mut sfx := ""
    let mut k := 0
    while (← used (Name.mkSimple s!"call{pc}{sfx}")) || (← used (Name.mkSimple s!"pre{pc}{sfx}"))
        || (← used (Name.mkSimple s!"halt{pc}{sfx}")) do
      k := k + 1
      sfx := s!"_{k}"
    let nm (base : String) : Ident := mkIdent (Name.mkSimple s!"{base}{pc}{sfx}")
    let callI := nm "call"
    let doomI := nm "doom"
    let haltI := nm "halt"
    let nodoomI := nm "nodoom"
    let preI := nm "pre"
    let delI := nm "del"
    if b == 0xf1 then
      return some (← `(tactic| refine OwnB.call $h (by own_code) $ne ?$callI
        (fun $mI $resI $outI $wI $h => ?_) ?$doomI))
    if b == 0xf4 then
      return some (← `(tactic| refine OwnB.delegatecall $h (by own_code) $ne ?$callI
        (fun $mI $resI $outI $wI $h => ?_) ?$doomI))
    if b == 0xfa && !preTarget then
      return some (← `(tactic| refine OwnB.staticcall $h (by own_code) $ne ?$callI
        (fun $mI $resI $outI $wI $h => ?_) ?$doomI))
    if b == 0xfa then
      return some (← `(tactic| refine OwnB.staticcallPre $h (by own_code) $ne ?$nodoomI ?$preI ?$delI
        ?$callI (fun $mI $resI $memI $h $hres => ?_)))
    if b == 0xf3 then
      return some (← `(tactic| refine OwnB.haltStop $h (by own_code)
        (.inl (Own.decode_halts _).1) ?$haltI $ne))
    if b == 0x00 then
      return some (← `(tactic| refine OwnB.haltStop $h (by own_code)
        (.inr (Own.decode_halts _).2.2.1) ?$haltI $ne))
    if b == 0xfd then
      return some (← `(tactic| exact OwnB.haltRevert $h (by own_code)
        (.inl (Own.decode_halts _).2.1) $ne))
    if b == 0xfe then
      return some (← `(tactic| exact OwnB.haltRevert $h (by own_code)
        (.inr (Own.decode_halts _).2.2.2) $ne))
  let binop := [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x0a, 0x0b, 0x10, 0x11, 0x12, 0x13,
    0x14, 0x16, 0x17, 0x18, 0x1a, 0x1b, 0x1c, 0x1d]
  if binop.contains b then
    return some (← `(tactic| refine $(r "binOp") (b := $bS) (fun fk => by cases fk <;> rfl) $h (by own_code)
      $ne (fun $mI $h => ?_)))
  if b == 0x15 || b == 0x19 then
    return some (← `(tactic| refine $(r "unOp") (b := $bS) (fun fk => by cases fk <;> rfl) $h (by own_code)
      $ne (fun $mI $h => ?_)))
  if 0x5f ≤ b ∧ b ≤ 0x7f then
    let n := b - 0x5f
    let nS := Syntax.mkNumLit (toString n)
    let some v := pushVal | return none
    let vS := Syntax.mkNumLit (toString v)
    return some (← `(tactic| refine $(r "push") ⟨$nS, by decide⟩ (v := BitVec.ofNat 256 $vS) $h
      (by own_code) (by simp only [Fix.code, reduceCodeImm, Bytes.toWord_ofWord]) $ne
      (fun $mI $h => ?_)))
  if 0x80 ≤ b ∧ b < 0x90 then
    let nS := Syntax.mkNumLit (toString (b - 0x80))
    return some (← `(tactic| refine $(r "dup") ⟨$nS, by decide⟩ $h (by own_code) rfl $ne
      (fun $mI $h => ?_)))
  if 0x90 ≤ b ∧ b < 0xa0 then
    let nS := Syntax.mkNumLit (toString (b - 0x90))
    return some (← `(tactic| refine $(r "swap") ⟨$nS, by decide⟩ $h (by own_code) rfl $ne
      (fun $mI $h => ?_)))
  match b with
  | 0x50 => return some (← `(tactic| refine $(r "pop") $h (by own_code) $ne (fun $mI $h => ?_)))
  | 0x5b => return some (← `(tactic| refine $(r "jumpdest") $h (by own_code) $ne (fun $mI $h => ?_)))
  | 0x56 => return some (← `(tactic| refine $(r "jump") $h (by own_code) $ne (fun $mI $h => ?_)))
  | 0x57 => return some (← `(tactic| refine $(r "jumpi") $h (by own_code) $ne
      (fun $hc $mI $h => ?_) (fun $hc $mI $h => ?_)))
  | 0x35 => return some (← `(tactic| refine $(r "calldataload") $h (by own_code) $ne
      (fun $mI $h => ?_)))
  | 0x51 => return some (← `(tactic| refine $(r "mload") $h (by own_code) $ne (fun $mI $h => ?_)))
  | 0x52 => return some (← `(tactic| refine $(r "mstore") $h (by own_code) $ne (fun $mI $h => ?_)))
  | 0x54 => return some (← `(tactic| refine $(r "sload") $h (by own_code) $ne (fun $mI $h => ?_)))
  | 0x55 =>
    if sTriv then
      return some (← `(tactic| refine $(r "sstore") $h (by own_code) True.intro (fun $mI $h => ?_)))
    if g then
      let keyI := mkIdent (Name.mkSimple s!"key{pc}")
      return some (← `(tactic| refine $(r "sstore") $h (by own_code)
        (Own.sstoreOk_of_key $h ?$keyI) (fun $mI $h => ?_)))
    return some (← `(tactic| refine $(r "sstore") $h (by own_code)
      (Own.sstoreOk_of_key $h ?key) (fun $mI $h => ?_)))
  | 0x20 => return some (← `(tactic| refine $(r "keccak256") $h (by own_code) $ne
      (fun $mI $h => ?_)))
  | 0x37 => return some (← `(tactic| refine $(r "calldatacopy") $h (by own_code) $ne
      (fun $mI $h => ?_)))
  | 0x3e => return some (← `(tactic| refine $(r "returndatacopy") $h (by own_code) $ne
      (fun $memI $mI $h => ?_)))
  | 0x34 => return some (← `(tactic| refine $(r "pushValue") (b := $bS) (fun fk => by cases fk <;> rfl)
      (fun _ h1 _ => by rw [h1]) $h (by own_code) $ne
      (fun $mI $h => ?_)))
  | 0x36 => return some (← `(tactic| refine $(r "pushValue") (b := $bS) (fun fk => by cases fk <;> rfl)
      (fun _ h1 _ => by rw [h1]) $h (by own_code) $ne (fun $mI $h => ?_)))
  | 0x46 => return some (← `(tactic| refine $(r "pushValue") (b := $bS) (fun fk => by cases fk <;> rfl)
      (fun _ _ h2 => by rw [h2]) $h (by own_code) $ne (fun $mI $h => ?_)))
  | 0x30 => return some (← `(tactic| refine $(r "pushValue") (b := $bS) (fun fk => by cases fk <;> rfl)
      (fun _ h1 _ => by rw [h1]) $h (by own_code) $ne (fun $mI $h => ?_)))
  | 0x5a | 0x3d => return some (← `(tactic| refine $(r "pushAny") (b := $bS) (fun fk => by cases fk <;> rfl)
      $h (by own_code) $ne (fun _ $mI $h => ?_)))
  | 0xfa => return some (← `(tactic| refine $(r "staticcallPre") $h (by own_code) $ne ?pre ?del ?call
      (fun $mI $resI $memI $h $hres => ?_)))
  | 0xf3 => return some (← `(tactic| exact Own.halt $h (by own_code)
      (.inl (Own.decode_halts _).1) $ne))
  | 0xfd => return some (← `(tactic| exact Own.halt $h (by own_code)
      (.inr (.inl (Own.decode_halts _).2.1)) $ne))
  | 0x00 => return some (← `(tactic| exact Own.halt $h (by own_code)
      (.inr (.inr (.inl (Own.decode_halts _).2.2.1))) $ne))
  | 0xfe => return some (← `(tactic| exact Own.halt $h (by own_code)
      (.inr (.inr (.inr (Own.decode_halts _).2.2.2))) $ne))
  | _ => return none

/-- Advance a goal `Own S C m` by one instruction; `false` if it does not apply. -/
def ownStep (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]) : TacticM Bool :=
    withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  -- The coinductive judgment: explore with itself at the leaves.
  if ← ownGGoal? t then
    try evalTactic (← `(tactic| refine OwnG.ofSelf ?_)) catch _ => return false
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (isG, m) ← ownGoal? t | return false
  let some (hId, hName, k, pcE) ← findFr m | return false
  let preTarget ← do
    let some st ← frStack? hId | pure false
    let some t2 := (listElems st)[1]? | pure false
    match ← wordLit? t2 with
    | some n => pure (decide (n ≤ 0x11))
    | none => pure false
  let some pc ← (evalNat (← instantiateMVars pcE)).run | return false
  let codeE ← whnfR (mkApp (mkConst ``Fix.code) k)
  let some bytes ← EvmLogic.Tactic.SolStep.codeBytes? codeE | return false
  let some b := bytes[pc]? | return false
  let pushVal : Option Nat :=
    if 0x5f ≤ b ∧ b ≤ 0x7f then some (readNat bytes (pc + 1) (b - 0x5f)) else none
  let mName ← match m with
    | .fvar id => pure (← id.getDecl).userName
    | _ => pure `m
  let h := mkIdent hName
  let mI := mkIdent mName
  trace[EvmLean.wp] "own_step: pc {pc}, byte {b}"
  let sTriv ← do
    let t' ← whnfR (← instantiateMVars t)
    if isG && t'.getAppNumArgs == 9 then
      let sArg := t'.getAppArgs[3]!
      match sArg with
      | .lam _ _ body _ => pure (body.isConstOf ``True)
      | _ => pure false
    else pure false
  let some tac ← ruleFor isG b pc h mI pushVal preTarget sTriv | return false
  let s ← saveState
  let ok ← tryCatchRuntimeEx (do withoutRecover (evalTactic tac); return true)
    (fun _ => do s.restore; return false)
  unless ok do return false
  let mut out : List MVarId := []
  for g' in ← getGoals do
    if ← g'.isAssigned then continue
    let mut g' := g'
    let isOwn := (← ownGoal? (← instantiateMVars (← g'.getType))).isSome
    if isOwn then
      g' ← g'.tryClear hId
      if let .fvar mId := m then g' ← g'.tryClear mId
    setGoals [g']
    if isOwn then
      try evalTactic (← `(tactic| own_norm $h [$extra,*])) catch _ => pure ()
      if b == 0x57 then
        -- A decided condition: close the infeasible branch.
        let closed ← withMainContext do
          let some d := (← getLCtx).findFromUserName? (Name.mkSimple s!"hc{pc}") | return false
          let ty ← instantiateMVars d.type
          if ty.hasFVar || ty.hasMVar then return false
          let s ← saveState
          try
            withoutRecover <| evalTactic
              (← `(tactic| exact absurd $(mkIdent (Name.mkSimple s!"hc{pc}")) (by decide)))
            return (← getGoals).isEmpty
          catch _ => s.restore; return false
        if closed then continue
    else
      -- Side conditions: close the trivial ones (`1 = 1`, `True`).
      let s ← saveState
      try evalTactic (← `(tactic| first | exact rfl | exact True.intro | (intros; exact True.intro)))
      catch _ => s.restore
    out := out ++ (← getGoals)
  setGoals out
  return true

/-- Advance a goal `Own S C m` by one instruction (see the module docstring). -/
elab "own_step" : tactic => do
  unless ← ownStep do throwError "own_step: no rule applies to the next instruction"

/-- Repeat `own_step` on the main goal while it applies and leaves a single goal. -/
elab "own_steps" : tactic => do
  for _ in [0:100000] do
    let gs ← getGoals
    if gs.isEmpty then return
    let s ← saveState
    unless ← ownStep do s.restore; return
    if (← getGoals).length != gs.length then return

/-- The pc of the goal's machine, from its `Fr` hypothesis. -/
def goalPc? (g : MVarId) : TacticM (Option Nat) := do
  setGoals [g]
  withMainContext do
    let t ← instantiateMVars (← g.getType)
    let some (_, m) ← ownGoal? t | return none
    let some (_, _, _, pcE) ← findFr m | return none
    (evalNat (← instantiateMVars pcE)).run

/-- `own_explore [p₁, …]`: step every goal (and every branch it splits into) until it ends, no
rule applies, or its pc is one of the `pᵢ` (after at least one step). -/
syntax "own_explore" (" [" num,* "]")? (&" using" " [" Lean.Parser.Tactic.simpLemma,* "]")? :
  tactic

elab_rules : tactic
  | `(tactic| own_explore $[[$pcs,*]]? $[using [$extra,*]]?) => do
    let stops := ((pcs.map (·.getElems.toList)).getD []).map (·.getNat)
    let extra := (extra.map (·.getElems)).getD #[]
    let mut work := (← getGoals).map (·, true)
    let mut done : List MVarId := []
    let mut fuel := 1000000
    while !work.isEmpty && fuel > 0 do
      fuel := fuel - 1
      let (g, first) :: rest := work | break
      work := rest
      if ← g.isAssigned then continue
      if !first then
        if let some pc ← goalPc? g then
          if stops.contains pc then done := done ++ [g]; continue
      setGoals [g]
      if ← ownStep extra then
        work := (← getGoals).map (·, false) ++ work
      else done := done ++ [g]
    setGoals (done ++ work.map (·.1))

end EvmLogic.Program.Nested.OwnTac
