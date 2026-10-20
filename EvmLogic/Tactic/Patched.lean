import EvmLogic.Solidity.Dispatch
import EvmLogic.Solidity.Immutables
import EvmLogic.Tactic.WpStep
import EvmLogic.Tactic.SolStep
import EvmLogic.Tactic.FastStep

/-!
# `psol_step` / `pwp_step`: symbolic execution of code with symbolic immutables

The runtime code of a deployment with arbitrary immutables is `patchWords base ps`, not a byte
literal. `psol_step` (`run` goals) and `pwp_step` (`WP` goals) read bytes from the literal `base`
when they lie outside every patch (offsets computed at the meta level, disjointness by a closed
`decide`), and check jump destinations with a `JumpDestsAgree code base` hypothesis.
-/

section

namespace EvmLogic.Tactic.Patched
open EvmLean EvmLogic.Solidity Lean Elab Tactic EvmLogic.Tactic Meta Simp EvmLean.Interpreter

/-! ## Recognising patched code -/

/-- `(base, ps)` if `e` unfolds (through head constants) to `patchWords base ps`. -/
def patched? (e : Expr) : MetaM (Option (Expr × Expr)) := withTransparency .default do
  let mut e ← instantiateMVars e
  for _ in [0:16] do
    e := e.consumeMData
    if let some (base, ps) := e.app2? ``Solidity.patchWords then
      return some (base, ps)
    match ← unfoldDefinition? e with
    | some e' => e := e'
    | none => return none
  return none

/-- The (numeral) offsets of a patch list. -/
def patchOffsets? (ps : Expr) : MetaM (Option (List Nat)) := do
  let mut cur := ps
  let mut out : Array Nat := #[]
  for _ in [0:65536] do
    let c ← whnfD cur
    if c.isAppOfArity ``List.nil 1 then return some out.toList
    let some (_, hd, tl) := c.app3? ``List.cons | return none
    let hd ← whnfD hd
    let some (_, _, o, _) := hd.app4? ``Prod.mk | return none
    let some n ← (evalNat o).run | do
      let some n ← (evalNat (← whnfD o)).run | return none
      out := out.push n
      cur := tl
      continue
    out := out.push n
    cur := tl
  return none

def natListLit (l : List Nat) : Expr :=
  l.foldr (fun n acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Nat) (mkNatLit n) acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Nat))

/-- A proof of `ps.map Prod.fst = offs`, checked by the kernel (by evaluation). -/
def offsetsProof (ps : Expr) (offs : List Nat) : MetaM Expr := do
  let fst ← mkAppOptM ``Prod.fst #[mkConst ``Nat, mkConst ``EvmLean.Word]
  let lhs ← mkAppM ``List.map #[fst, ps]
  let rhs := natListLit offs
  return mkExpectedPropHint (← mkEqRefl rhs) (← mkEq lhs rhs)

/-! ## Reads of code -/

/-- Rewrite `readBytes (patchWords base ps) off n` to `readBytes base off n` when the literal
range avoids every patch. -/
simproc_decl reducePatchedRead (readBytes _ _ _) := fun e => do
  let_expr readBytes code off n := e | return .continue
  let some offN ← (evalNat off).run | return .continue
  let some nN ← (evalNat n).run | return .continue
  let some (base, ps) ← patched? code | return .continue
  let some offs ← patchOffsets? ps | return .continue
  unless offs.all (fun o => offN + nN ≤ o ∨ o + 32 ≤ offN) do return .continue
  let offsE := natListLit offs
  let hdisj ← mkDecideProof (← withLocalDeclD `o (mkConst ``Nat) fun o => do
    let mem ← mkAppM ``Membership.mem #[offsE, o]
    let body ← mkAppM ``Or
      #[← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[mkNatLit offN, mkNatLit nN], o],
      ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[o, mkNatLit 32], mkNatLit offN]]
    mkForallFVars #[o] (← mkArrow mem body))
  let pf := mkAppN (mkConst ``readBytes_patchWords_of_offsets)
    #[base, ps, mkNatLit offN, mkNatLit nN, offsE, ← offsetsProof ps offs, hdisj]
  let rhs := mkApp3 (mkConst ``readBytes) base (mkNatLit offN) (mkNatLit nN)
  let pf ← mkExpectedTypeHint pf (← mkEq e rhs)
  return .visit { expr := rhs, proof? := some pf }

/-! ## Side conditions -/

def dischCodeByte (g : MVarId) : TacticM Unit := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let_expr Eq ty lhs rhs := t | throwError "psol_disch: not an equation"
  let_expr GetElem?.getElem? coll idx elem valid inst code jE := lhs
    | throwError "psol_disch: not a code byte"
  let some j ← (evalNat jE).run | throwError "psol_disch: symbolic code index"
  let some (base, ps) ← patched? code | throwError "psol_disch: code is not patched"
  let some offs ← patchOffsets? ps | throwError "psol_disch: unknown patch offsets"
  unless offs.all (fun o => j < o ∨ o + 32 ≤ j) do
    throwError "psol_disch: code byte {j} lies in a patched window"
  let offsE := natListLit offs
  let hdisj ← mkDecideProof (← withLocalDeclD `o (mkConst ``Nat) fun o => do
    let mem ← mkAppM ``Membership.mem #[offsE, o]
    let body ← mkAppM ``Or #[← mkAppM ``LT.lt #[mkNatLit j, o],
      ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[o, mkNatLit 32], mkNatLit j]]
    mkForallFVars #[o] (← mkArrow mem body))
  let lhs' := mkAppN lhs.getAppFn #[coll, idx, elem, valid, inst, base, jE]
  let heq := mkAppN (mkConst ``getElem?_patchWords_of_offsets)
    #[base, ps, mkNatLit j, offsE, ← offsetsProof ps offs, hdisj]
  let heq ← mkExpectedTypeHint heq (← mkEq lhs lhs')
  let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``Eq [1]) ty lhs' rhs)
  let .mvar gid := g' | throwError "psol_disch: internal error"
  g.assign (← mkEqTrans heq g')
  setGoals [gid]
  evalTactic (← `(tactic| table_decide))

def dischJumpDest (g : MVarId) : TacticM Unit := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let_expr Eq _ lhs _ := t | throwError "psol_disch: not an equation"
  let_expr isValidJumpDest jd d := lhs | throwError "psol_disch: not a jump destination"
  let jd ← whnfR jd
  let some code := jd.app1? ``validJumpDests | throwError "psol_disch: unknown jump table"
  let mut hyp : Option (Expr × Expr) := none
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if let some (c, base) := ty.app2? ``JumpDestsAgree then
      if c == code then hyp := some (decl.toExpr, base)
  let some (h, base) := hyp
    | throwError "psol_disch: no `JumpDestsAgree` hypothesis for the code"
  let gs ← g.apply (mkAppN (mkConst ``isValidJumpDest_of_agree) #[code, base, d, h])
  setGoals gs
  evalTactic (← `(tactic| table_decide))

/-- `sol_disch` for patched code (code bytes, jump destinations). -/
elab "psol_disch" : tactic => withMainContext do
  let s ← saveState
  try
    evalTactic (← `(tactic| try dsimp only))
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let isJump := match t.eq? with
      | some (_, lhs, _) => lhs.isAppOf ``isValidJumpDest
      | none => false
    if isJump then dischJumpDest g else dischCodeByte g
    return
  catch _ => s.restore
  evalTactic (← `(tactic| sol_disch))

/-! ## The step -/

def swapDisch (t : TSyntax `tactic) : TacticM (TSyntax `tactic) := do
  let k := (← `(tactic| sol_disch)).raw.getKind
  let p ← `(tactic| psol_disch)
  return ⟨← t.raw.replaceM fun s => pure (if s.getKind == k then some p.raw else none)⟩

def currentByte : TacticM Nat := withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some m := SolStep.findRunMachine? t | throwError "psol_step: no `run _ m` in the goal"
  let fr ← mkAppM ``Machine.frame #[m]
  let pc ← whnfD (← mkAppM ``Frame.pc #[fr])
  let some pc ← (evalNat pc).run | throwError "psol_step: pc is not a numeral: {pc}"
  let code ← whnfR (← mkAppM ``Frame.code #[fr])
  let code ← match ← patched? code with
    | some (base, _) => pure base
    | none => pure code
  let some bytes ← SolStep.codeBytes? code
    | throwError "psol_step: the code is not a (patched) byte-array literal"
  let some b := bytes[pc]? | throwError "psol_step: pc {pc} past the end of the code"
  return b

/-- `sol_step` for code `patchWords base ps` with symbolic patches. -/
syntax "psol_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| psol_step) => do evalTactic (← `(tactic| psol_step []))
  | `(tactic| psol_step [$extra,*]) => do
    let b ← currentByte
    let halts ← (← SolStep.haltTactics b).mapM swapDisch
    if halts.isEmpty then
      let tacs ← (← SolStep.stepTactics b).mapM swapDisch
      if tacs.isEmpty then throwError "psol_step: no step lemma for opcode {b}"
      evalTactic (← `(tactic| rw [EvmLean.Interpreter.run_succ_of_running ?h]))
      let gs ← getGoals
      let some hg ← gs.findM? (fun g => return (← g.getTag).eraseMacroScopes == `h)
        | throwError "psol_step: no side goal"
      let rest := gs.filter (· != hg)
      setGoals [hg]
      SolStep.firstOf tacs s!"psol_step: no step lemma applies to opcode {b}"
      setGoals rest
    else
      evalTactic (← `(tactic| rw [EvmLean.Interpreter.run_succ_of_done ?h]))
      let gs ← getGoals
      let some hg ← gs.findM? (fun g => return (← g.getTag).eraseMacroScopes == `h)
        | throwError "psol_step: no side goal"
      let rest := gs.filter (· != hg)
      setGoals [hg]
      SolStep.firstOf halts s!"psol_step: no halting lemma applies to opcode {b}"
      setGoals rest
    trace[EvmLean.symStep] "byte {b}"
    evalTactic (← `(tactic| try evm_norm [EvmLogic.Tactic.Patched.reducePatchedRead,
      EvmLogic.Tactic.SolStep.reduceCodeImm, sol_norm, Nat.reduceMod, Nat.reducePow, Nat.reduceLT,
      $extra,*]))


/-- Repeat `psol_step` while it succeeds (after the first step, by the fast stepper when it
applies). -/
syntax "psol_steps" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

/-- `sol_dispatch` for patched code (needs `JumpDestsAgree code base` in the context). -/
macro "psol_dispatch" : tactic => `(tactic| (
  intro m k hcode hjd hpc hstk hmem hval hsel hsz hsz' hgas
  obtain ⟨ctx, pre, w, tr, ow, ca,
    ⟨msg, c, jd, pc, stk, mem, gas, rd, sub, snap, kind⟩, parents⟩ := m
  simp only at hcode hjd hpc hstk hmem hval hsel hsz hsz' hgas ⊢
  subst hpc hstk hmem
  subst c
  subst jd
  have hlt := Dispatch.lt_calldatasize_four hsz hsz'
  have hsel' := Dispatch.selector_eq hsel
  generalize hR : run k _ = R
  psol_steps [hval, hlt, hsel']
  subst hR
  simp only [initMemory, BitVec.ofNat_eq_ofNat, Nat.sub_sub, Nat.reduceAdd]))

end EvmLogic.Tactic.Patched

end

section

/-! ## `pwp_step`: `wp_step` on literal or patched code -/

namespace EvmLogic.Program
open EvmLean Lean Elab Tactic EvmLogic.Tactic Meta EvmLean.Interpreter EvmLogic.Solidity

theorem isValidJumpDest_of_jumpTable_agree {jd : Array Bool} {code base : ByteArray} {d : Nat}
    (hjd : JumpTable jd code) (h : JumpDestsAgree code base)
    (hd : d ∈ Solidity.jumpDestList (base.size + 1) base.data.toList 0) :
    isValidJumpDest jd d = true := by
  rw [hjd]; exact isValidJumpDest_of_agree h hd

def patchedCode? (code : Expr) : MetaM (Option (Expr × Expr × List Nat)) := do
  let some (base, ps) ← Tactic.Patched.patched? code | return none
  let some offs ← Tactic.Patched.patchOffsets? ps | return none
  return some (base, ps, offs)

def offsDisjProof (offs : List Nat) (mkBody : Expr → MetaM Expr) : MetaM Expr := do
  let offsE := Tactic.Patched.natListLit offs
  mkDecideProof (← withLocalDeclD `o (mkConst ``Nat) fun o => do
    let mem ← mkAppM ``Membership.mem #[offsE, o]
    mkForallFVars #[o] (← mkArrow mem (← mkBody o)))

def codeInfo? (code : Expr) : MetaM (Option (Array UInt8 × Option (Expr × Expr × List Nat))) := do
  match ← patchedCode? code with
  | some (base, ps, offs) =>
    let some bytes ← codeBytes? base | return none
    return some (bytes, some (base, ps, offs))
  | none =>
    let some bytes ← codeBytes? code | return none
    return some (bytes, none)

def pcodeFact (code : Expr) (pinfo : Option (Expr × Expr × List Nat)) (pc : Nat) (b : UInt8) :
    MetaM Expr := do
  match pinfo with
  | none => codeFact code pc b
  | some (base, ps, offs) =>
    unless offs.all (fun o => pc < o ∨ o + 32 ≤ pc) do
      throwError "pcode_fact: code byte {pc} lies in a patched window"
    let hdisj ← offsDisjProof offs fun o => do
      mkAppM ``Or #[← mkAppM ``LT.lt #[mkNatLit pc, o],
        ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[o, mkNatLit 32], mkNatLit pc]]
    let heq := mkAppN (mkConst ``getElem?_patchWords_of_offsets)
      #[base, ps, mkNatLit pc, Tactic.Patched.natListLit offs,
        ← Tactic.Patched.offsetsProof ps offs, hdisj]
    mkEqTrans heq (← codeFact base pc b)

def ppushFact? (code : Expr) (pinfo : Option (Expr × Expr × List Nat)) (bytes : Array UInt8)
    (pc n : Nat) : MetaM (Option Expr) := do
  match pinfo with
  | none => return some (← pushFact code bytes pc n)
  | some (base, ps, offs) =>
    let off := pc + 1
    unless offs.all (fun o => off + n ≤ o ∨ o + 32 ≤ off) do return none
    let hdisj ← offsDisjProof offs fun o => do
      mkAppM ``Or #[← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[mkNatLit off, mkNatLit n], o],
        ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[o, mkNatLit 32], mkNatLit off]]
    let heq := mkAppN (mkConst ``readBytes_patchWords_of_offsets)
      #[base, ps, mkNatLit off, mkNatLit n, Tactic.Patched.natListLit offs,
        ← Tactic.Patched.offsetsProof ps offs, hdisj]
    let heq' ← mkCongrArg (mkConst ``Bytes.toWord) heq
    return some (← mkEqTrans heq' (← pushFact base bytes pc n))

/-- Close `code[pc]? = some b` for literal or patched code and a numeral `pc`. -/
elab "pcode_fact" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let_expr Eq _ lhs rhs := t | throwError "pcode_fact: not an equation"
  let_expr GetElem?.getElem? _ _ _ _ _ coll i := lhs | throwError "pcode_fact: not `code[pc]?`"
  let code ← whnfR coll
  let some pc ← (evalNat (← whnfR i)).run | throwError "pcode_fact: pc is not a numeral"
  let some (bytes, pinfo) ← codeInfo? code | throwError "pcode_fact: unknown code"
  let some b := bytes[pc]? | throwError "pcode_fact: pc out of range"
  let_expr Option.some _ v := rhs | throwError "pcode_fact: right side is not `some b`"
  let some v ← uint8Lit? v | throwError "pcode_fact: right side is not a literal"
  unless v = b.toNat do throwError "pcode_fact: the byte at {pc} is {b}, not {v}"
  let pf ← pcodeFact code pinfo pc b
  g.assign (← mkExpectedTypeHint pf t)
  replaceMainGoal []

/-- Close `isValidJumpDest jd d = true` given `JumpTable jd code` (and `JumpDestsAgree code
base` for patched code). -/
elab "pjumpdest_disch" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let_expr Eq _ lhs _ := t | throwError "pjumpdest_disch: not an equation"
  let_expr isValidJumpDest jd d := lhs | throwError "pjumpdest_disch: not a jump destination"
  let jd ← whnfR jd
  let some dn ← (evalNat (← whnfD d)).run | throwError "pjumpdest_disch: symbolic destination"
  let mut src : Option (Expr × Expr) := none
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if let some (jd', code) := ty.app2? ``JumpTable then
      if jd' == jd then src := some (code, decl.toExpr)
  let some (code, hjd) := src | throwError "pjumpdest_disch: unknown jump table"
  match ← patchedCode? code with
  | none => evalTactic (← `(tactic| jumpdest_disch))
  | some (base, _, _) =>
    let mut agree : Option Expr := none
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      if let some (c, b) := ty.app2? ``JumpDestsAgree then
        if (← isDefEq c code) && (← isDefEq b base) then agree := some decl.toExpr
    let some hag := agree | throwError "pjumpdest_disch: no `JumpDestsAgree` hypothesis"
    let some bytes ← codeBytes? base | throwError "pjumpdest_disch: base is not a literal"
    unless (jumpDestsOf bytes).contains dn do
      throwError "pjumpdest_disch: {dn} is not a JUMPDEST"
    let memTy ← mkAppM ``Membership.mem #[← mkAppM ``Solidity.jumpDestList
      #[← mkAppM ``HAdd.hAdd #[← mkAppM ``ByteArray.size #[base], mkNatLit 1],
        ← mkAppM ``Array.toList #[← mkAppM ``ByteArray.data #[base]], mkNatLit 0], d]
    let hmem ← match ← jumpDestMem? base d with
      | some h => mkExpectedTypeHint h memTy
      | none => mkDecideProof memTy
    g.assign (mkAppN (mkConst ``isValidJumpDest_of_jumpTable_agree)
      #[jd, code, base, d, hjd, hag, hmem])
    replaceMainGoal []

/-- `wp_disch` with `pjumpdest_disch` for jump destinations. -/
def pwpDisch : TacticM Unit := withMainContext do
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  let isIneq := t.isAppOf ``LE.le || t.isAppOf ``LT.lt
  let isJd := match t.eq? with
    | some (_, lhs, _) => lhs.isAppOf ``isValidJumpDest
    | none => false
  let alts : List (TSyntax `tactic) ←
    if isJd then pure [← `(tactic| pjumpdest_disch), ← `(tactic| assumption)]
    else if isIneq then
      pure [← `(tactic| evm_gas), ← `(tactic| decide), ← `(tactic| assumption)]
    else pure [← `(tactic| exact rfl), ← `(tactic| decide), ← `(tactic| assumption)]
  for a in alts do
    if ← tryTac (evalTactic a) then return
  throwError "pwp_disch: cannot discharge side condition"

/-- `pwp_disch`: see `pwpDisch`. -/
elab "pwp_disch" : tactic => pwpDisch

/-- `wpStep` for literal or patched code. A `PUSH32` of a patched word uses `step_pushN`; the
caller rewrites it with a per-contract lemma (`pwp_steps [h, …]`). -/
def pwpStep (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Bool :=
  withMainContext do
  let g ← getMainGoal
  let some m ← wpGoalMachine? g | return false
  let code ← whnfR (mkApp (mkConst ``Frame.code) (← whnfR (mkApp (mkConst ``Machine.frame) m)))
  let pcE ← whnfR (mkApp (mkConst ``Frame.pc) (← whnfR (mkApp (mkConst ``Machine.frame) m)))
  let some pc ← (evalNat (← instantiateMVars pcE)).run | return false
  let some (bytes, pinfo) ← codeInfo? code | return false
  let some b := bytes[pc]? | return false
  let hb ← Term.exprToSyntax (← pcodeFact code pinfo pc b)
  let saved ← saveState
  let attempt (t : TSyntax `tactic) : TacticM Bool := do
    tryCatchRuntimeEx
      (do withoutRecover (evalTactic t); return true)
      (fun e => do
        trace[EvmLean.wp] "pc {pc}, byte {b}: {e.toMessageData}"
        saved.restore
        return false)
  let norm : TacticM Unit := do
    trace[EvmLean.symStep] "pc {pc}, byte {b}"
    try evalTactic (← `(tactic| evm_norm [List.set_cons_zero, List.set_cons_succ, Nat.sub_sub,
      Memory.loadWord_expand, Memory.read_expand, Memory.loadWord_storeWord, Memory.read_storeWord,
      Memory.loadWord_storeWord_of_disjoint, Memory.read_storeWord_of_disjoint, true_or, or_true,
      reduceClosedWord, Bytes.size_ofWord, Bytes.toWord_ofWord, $extra,*]))
    catch _ => pure ()
  if 0x5f ≤ b.toNat ∧ b.toNat ≤ 0x7f then
    let n := b.toNat - 0x5f
    let nS := Syntax.mkNumLit (toString n)
    match ← ppushFact? code pinfo bytes pc n with
    | some hvE =>
      let hv ← Term.exprToSyntax hvE
      if ← attempt (← `(tactic| (
          apply WP.of_step
          case h =>
            apply step_push_val $nS (by decide)
            case hcode => exact $hb
            case hval => exact $hv
            all_goals pwp_disch
          case hs => same_frame))) then
        norm
        return true
      return false
    | none =>
      if ← attempt (← `(tactic| (
          apply WP.of_step
          case h =>
            apply EvmLean.Interpreter.step_pushN $nS (by decide)
            case hcode => exact $hb
            all_goals pwp_disch
          case hs => same_frame))) then
        norm
        return true
      return false
  let (lemmas, halts) := stepLemmasFor b.toNat
  for l in lemmas do
    let lS := mkIdent l
    let t ← if halts then
      `(tactic| (
        apply WP.halt_of_step
        case h =>
          apply $lS
          case hcode => exact $hb
          all_goals pwp_disch
        case hs => same_frame))
    else
      `(tactic| (
        apply WP.of_step
        case h =>
          apply $lS
          case hcode => exact $hb
          all_goals pwp_disch
        case hs => same_frame))
    if ← attempt t then
      norm
      return true
  return false

/-- The fast stepper's configuration for the main goal `WP m Q H` (`none` if the code is not
known): the normalization of `pwpStep` and its code facts. -/
def pwpFastCfg (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TacticM (Option FastStep.Cfg) := withMainContext do
  let g ← getMainGoal
  let some m ← wpGoalMachine? g | return none
  let code ← whnfR (mkApp (mkConst ``Frame.code) (← whnfR (mkApp (mkConst ``Machine.frame) m)))
  let some (bytes, pinfo) ← codeInfo? code | return none
  let normStx ← `(tactic| evm_norm [List.set_cons_zero, List.set_cons_succ, Nat.sub_sub,
      Memory.loadWord_expand, Memory.read_expand, Memory.loadWord_storeWord, Memory.read_storeWord,
      Memory.loadWord_storeWord_of_disjoint, Memory.read_storeWord_of_disjoint, true_or, or_true,
      reduceClosedWord, Bytes.size_ofWord, Bytes.toWord_ofWord, $extra,*])
  let some simpStx ← liftMacroM <| expandMacro? normStx | return none
  let r ← mkSimpContext simpStx (eraseLocal := false)
  return some {
    simpCtx := r.ctx, simprocs := r.simprocs
    codeFact := fun c pc b => pcodeFact c pinfo pc b
    pushFact := fun c pc n => ppushFact? c pinfo bytes pc n
    bytes := fun c => do
      if c == code then return some bytes
      return (← codeInfo? c).map (·.1)
    disch := pwpDisch }

/-- One step: the fast stepper if it applies, else `pwpStep`. -/
def pwpStepFast (cfg : Option FastStep.Cfg)
    (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (normAll : Bool := false) :
    TacticM Bool := do
  if let some c := cfg then
    if ← FastStep.fastWpStep c normAll then return true
  pwpStep extra

/-- Advance a goal `WP m Q H` by one instruction (literal or patched code). -/
syntax "pwp_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| pwp_step $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    unless ← pwpStep extra do
      throwError "pwp_step: no step lemma applies to the next instruction"

/-- Repeat `pwp_step` while it succeeds (at most `n` times if a bound is given). -/
syntax "pwp_steps" (ppSpace num)? (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| pwp_steps $[$n]? $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let limit := (n.map (·.getNat)).getD 1000000
    -- the first step normalizes the whole goal (as every step of `pwpStep` does), the rest
    -- only what they change
    let mut cfg : Option FastStep.Cfg := none
    for i in [0:limit] do
      if i == 0 then cfg ← pwpFastCfg extra
      unless ← pwpStepFast cfg extra (normAll := i == 0) do return

/-- `wp_run_to` for literal or patched code. -/
syntax "pwp_run_to " num,+ (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| pwp_run_to $pcs,* $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let pcs := pcs.getElems.toList.map (·.getNat)
    let mut cfg : Option FastStep.Cfg := none
    for i in [0:1000000] do
      let g ← getMainGoal
      if i > 0 then
        if let some pc ← wpGoalPc? g then
          if pcs.contains pc then return
      if i == 0 then cfg ← pwpFastCfg extra
      unless ← pwpStepFast cfg extra (normAll := i == 0) do return

end EvmLogic.Program

end

section

/-! ## `CODECOPY` in the frame-local logic (solc loads 32-byte constants with it) -/

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter

/-- Execute a `CODECOPY` of a non-empty literal range (avoiding the patches) in a `WP` goal,
turning the copied word into a `Memory.write_ofWord`. -/
macro "pwp_codecopy" : tactic => `(tactic| (
  apply WP.of_step
  case h =>
    apply EvmLean.Interpreter.step_codecopy (by pcode_fact) rfl (by decide) (by evm_gas)
  case hs => same_frame
  simp only [EvmLogic.Tactic.Patched.reducePatchedRead, EvmLogic.Tactic.SolStep.reduceCodeImm,
    Memory.write_ofWord, BitVec.reduceToNat,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub, memoryCost, Gas.extendMemory,
    List.foldl, Gas.ceil32, Gas.memoryCost, Gas.words, Gas.memoryPerWord, Memory.size_storeWord,
    Memory.size_expand, Memory.size_empty, Memory.wordsAfter, Memory.words, Nat.reduceLeDiff,
    Nat.reduceEqDiff, Nat.max_def, ↓reduceIte]))

end EvmLogic.Program

end

section

/-! ## `psol_steps` with the fast stepper -/

namespace EvmLogic.Tactic.Patched
open EvmLean EvmLogic.Solidity Lean Elab Tactic EvmLogic.Tactic Meta EvmLean.Interpreter

/-- The fast stepper's configuration for a goal with `run _ m`: the normalization and side
conditions of `psol_step`. -/
def psolFastCfg (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TacticM (Option FastStep.Cfg) := withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some m := SolStep.findRunMachine? t | return none
  let code ← whnfR (mkApp (mkConst ``Frame.code) (← whnfR (mkApp (mkConst ``Machine.frame) m)))
  let some (bytes, pinfo) ← EvmLogic.Program.codeInfo? code | return none
  let normStx ← `(tactic| evm_norm [EvmLogic.Tactic.Patched.reducePatchedRead,
      EvmLogic.Tactic.SolStep.reduceCodeImm, sol_norm, Nat.reduceMod, Nat.reducePow, Nat.reduceLT,
      $extra,*])
  let some simpStx ← liftMacroM <| expandMacro? normStx | return none
  let r ← mkSimpContext simpStx (eraseLocal := false)
  return some {
    simpCtx := r.ctx, simprocs := r.simprocs
    codeFact := fun c pc b => EvmLogic.Program.pcodeFact c pinfo pc b
    pushFact := fun c pc n => EvmLogic.Program.ppushFact? c pinfo bytes pc n
    bytes := fun c => do
      if c == code then return some bytes
      return (← EvmLogic.Program.codeInfo? c).map (·.1)
    disch := do evalTactic (← `(tactic| psol_disch))
    foldGas := false }

elab_rules : tactic
  | `(tactic| psol_steps $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let one : TacticM Bool := do
      let s ← saveState
      try
        evalTactic (← `(tactic| psol_step [$extra,*]))
        return true
      catch _ =>
        s.restore
        return false
    let mut cfg : Option FastStep.Cfg := none
    for i in [0:1000000] do
      if i == 0 then cfg ← psolFastCfg extra
      if let some c := cfg then
        if ← FastStep.fastRunStep c (normAll := i == 0) then continue
      unless ← one do return

end EvmLogic.Tactic.Patched

end
