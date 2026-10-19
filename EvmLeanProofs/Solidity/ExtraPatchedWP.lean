import EvmLeanProofs.Program.Tactic
import EvmLeanProofs.Program.ExtraTactic
import EvmLeanProofs.Solidity.SharesExtraTactic

/-!
# `pwp_step`: the frame-local symbolic executor on code with symbolic immutables

`wp_step` (`EvmLeanProofs.Program.Tactic`) reads code bytes, pushed immediates and jump
destinations from a literal code constant. The runtime code of a contract deployed with
*arbitrary* immutables is `Contracts.patchWords base ps` with symbolic patched words (e.g.
`SolmateVault.runtimeCodeWith i`), which is not a literal. `pwp_step` is `wp_step` for such
code, using the patched-code lemmas of `EvmLeanProofs.Solidity.SharesExtraPatch` (as
`psol_step` does for `run` goals):

* the opcode byte at `pc` is read from the literal `base`; the fact `code[pc]? = some b` is
  `getElem?_patchWords_of_offsets` (the byte lies outside every patch) composed with the
  kernel-checked fact about `base`;
* a `PUSHn` whose immediate avoids every patch pushes the value read from `base`
  (`readBytes_patchWords_of_offsets`); a `PUSH32` of a patched word (an immutable) uses
  `step_pushN`, leaving `Bytes.toWord (readBytes code off 32)` on the stack, which the caller
  rewrites with a per-contract lemma passed as `pwp_steps [h, …]`
  (`readBytes_patchWords_last`);
* jump destinations: from hypotheses `JumpTable jd code` and `JumpDestsAgree code base` in the
  local context (`isValidJumpDest_of_jumpTable_agree`, membership in the scan of `base` by
  kernel evaluation);
* on literal code everything falls back to `wp_step`'s facts, so `pwp_step` can be used
  everywhere.

`pcode_fact` proves `code[pc]? = some b` (for `WP.staticcall`'s `hcode`) and
`pjumpdest_disch` jump destinations, both for literal and patched code.
-/

namespace EvmLean.Program

open Lean Elab Tactic Meta
open Interpreter Contracts

/-- A jump destination of patched code with the canonical scan. -/
theorem isValidJumpDest_of_jumpTable_agree {jd : Array Bool} {code base : ByteArray} {d : Nat}
    (hjd : JumpTable jd code) (h : JumpDestsAgree code base)
    (hd : d ∈ Solidity.jumpDestList (base.size + 1) base.data.toList 0) :
    isValidJumpDest jd d = true := by
  rw [hjd]; exact isValidJumpDest_of_agree h hd

/-- `(base, ps)` if `code` unfolds to `patchWords base ps`, with the patch offsets. -/
def patchedCode? (code : Expr) : MetaM (Option (Expr × Expr × List Nat)) := do
  let some (base, ps) ← Solidity.Patched.patched? code | return none
  let some offs ← Solidity.Patched.patchOffsets? ps | return none
  return some (base, ps, offs)

/-- A kernel-checked proof of `∀ o ∈ offs, P o` for a decidable closed `P`, built by
`mkBody o`. -/
def offsDisjProof (offs : List Nat) (mkBody : Expr → MetaM Expr) : MetaM Expr := do
  let offsE := Solidity.Patched.natListLit offs
  mkDecideProof (← withLocalDeclD `o (mkConst ``Nat) fun o => do
    let mem ← mkAppM ``Membership.mem #[offsE, o]
    mkForallFVars #[o] (← mkArrow mem (← mkBody o)))

/-- The bytes of the code (of `base` if patched), and the patch data. -/
def codeInfo? (code : Expr) : MetaM (Option (Array UInt8 × Option (Expr × Expr × List Nat))) := do
  match ← patchedCode? code with
  | some (base, ps, offs) =>
    let some bytes ← codeBytes? base | return none
    return some (bytes, some (base, ps, offs))
  | none =>
    let some bytes ← codeBytes? code | return none
    return some (bytes, none)

/-- The fact `code[pc]? = some b`, for literal or patched code (`pc` outside the patches). -/
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
      #[base, ps, mkNatLit pc, Solidity.Patched.natListLit offs,
        ← Solidity.Patched.offsetsProof ps offs, hdisj]
    mkEqTrans heq (← codeFact base pc b)

/-- The fact `Bytes.toWord (readBytes code (pc + 1) n) = v` for a `PUSHn` whose immediate
avoids the patches, or `none` if it does not. -/
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
      #[base, ps, mkNatLit off, mkNatLit n, Solidity.Patched.natListLit offs,
        ← Solidity.Patched.offsetsProof ps offs, hdisj]
    let heq' ← mkCongrArg (mkConst ``Bytes.toWord) heq
    return some (← mkEqTrans heq' (← pushFact base bytes pc n))

/-- Close `code[pc]? = some b` for literal or patched code (behind projections of a literal
machine) and a numeral `pc`. -/
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

/-- Close `isValidJumpDest jd d = true` for a numeral `d`, where `JumpTable jd code` is in the
context: by `jumpdest_disch` for literal code, and with a `JumpDestsAgree code base`
hypothesis for patched code. -/
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
    let hmem ← mkDecideProof memTy
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

/-- Advance a goal `WP m Q H` by one instruction, for literal or patched code. Returns
`false` (leaving the goal unchanged) if no step lemma applies. -/
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
    for _ in [0:limit] do
      unless ← pwpStep extra do return

/-- `pwp_run_to pc₁, … [h₁, …]`: step until the pc is one of the `pcᵢ` (after at least one
step), or no step lemma applies. -/
syntax "pwp_run_to " num,+ (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| pwp_run_to $pcs,* $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let pcs := pcs.getElems.toList.map (·.getNat)
    for i in [0:1000000] do
      let g ← getMainGoal
      if i > 0 then
        if let some pc ← wpGoalPc? g then
          if pcs.contains pc then return
      unless ← pwpStep extra do return

end EvmLean.Program
