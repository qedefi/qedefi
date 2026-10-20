import EvmLogic.Solidity.Dispatch
import EvmLogic.Solidity.Immutables
import EvmLogic.Tactic.WpStep
import EvmLogic.Tactic.SolStep

/-!
# `psol_step`: symbolic execution of code with symbolic immutables

`sol_step` (`EvmLogic.Tactic.SolStep`) needs the executed code to be a byte literal.
The runtime code of a deployment with *arbitrary* immutables is `patchWords base ps`
(`runtimeCodeWith i` for a symbolic `i`), which is not. `psol_step` is `sol_step` for such
code; outside the patched windows it is exactly as fast:

* the opcode byte at `pc` is read from the literal `base` (the head constants of the code are
  unfolded until `Contracts.patchWords base ps` appears);
* code-byte side goals `code[pc]? = some b` are reduced to `base[pc]? = some b` by
  `getElem?_patchWords_of_offsets` and then checked by `decide +kernel`;
* jump destinations use a hypothesis `JumpDestsAgree code base` from the local context
  (proved once per contract, for all immutables, by `kernel_decide`) and the scan of `base`;
* the simproc `reducePatchedRead` rewrites `readBytes code off n` (pushed immediates,
  `CODECOPY`) to `readBytes base off n` when the range avoids every patch, after which
  `reduceCodeImm` evaluates it. Reads *inside* a patch (an immutable being pushed) are left to
  per-contract simp lemmas passed as `psol_steps [h, …]` (`readBytes_patchWords_last`).

The patch offsets are computed at the meta level by unfolding `ps` (they are literals even when
the patched words are symbolic); the equation `ps.map Prod.fst = offs` is left to the kernel
(`mkExpectedPropHint`), and the disjointness of the range from `offs` is a closed `decide`.

Otherwise `psol_step` is `sol_step`: the step lemmas (`Exec.stepTactics`) and normalisation are
shared, with the discharger `sol_disch` replaced by `psol_disch` (which falls back to it).
`psol_dispatch` is `sol_dispatch` with `psol_steps`.
-/

section

namespace EvmLogic.Tactic.Patched
open EvmLean EvmLogic.Solidity

open Lean Elab Tactic EvmLogic.Tactic Meta Simp
open EvmLean.Interpreter EvmLogic.Solidity

/-! ## Recognising patched code -/

/-- `(base, ps)` if `e` unfolds (through head constants) to `Contracts.patchWords base ps`. -/
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

/-- The offsets of a patch list (a list of pairs whose first components are numerals, after
unfolding). -/
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

/-- The literal list of offsets as an expression. -/
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

/-- `readBytes code off n` with `code = patchWords base ps` and literal `off`, `n` avoiding
every patch: `readBytes base off n` (`readBytes_patchWords_of_offsets`). -/
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
    let body ← mkAppM ``Or #[← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[mkNatLit offN, mkNatLit nN], o],
      ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[o, mkNatLit 32], mkNatLit offN]]
    mkForallFVars #[o] (← mkArrow mem body))
  let pf := mkAppN (mkConst ``readBytes_patchWords_of_offsets)
    #[base, ps, mkNatLit offN, mkNatLit nN, offsE, ← offsetsProof ps offs, hdisj]
  let rhs := mkApp3 (mkConst ``readBytes) base (mkNatLit offN) (mkNatLit nN)
  let pf ← mkExpectedTypeHint pf (← mkEq e rhs)
  return .visit { expr := rhs, proof? := some pf }

/-! ## Side conditions -/

/-- Reduce `code[j]? = rhs` for patched `code` to `base[j]? = rhs` and close it in the kernel.
Fails if the goal is not of this form or `j` lies in a patch. -/
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
  evalTactic (← `(tactic| decide +kernel))

/-- Close `isValidJumpDest (validJumpDests code) d = true` with a hypothesis
`JumpDestsAgree code base` from the context and the scan of the literal `base`. -/
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
  evalTactic (← `(tactic| decide +kernel))

/-- Side goals of step lemmas on patched code (code bytes, jump destinations); everything else
by `sol_disch`. -/
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

/-- Replace the discharger `sol_disch` in a step-lemma script by `psol_disch`. -/
def swapDisch (t : TSyntax `tactic) : TacticM (TSyntax `tactic) := do
  let k := (← `(tactic| sol_disch)).raw.getKind
  let p ← `(tactic| psol_disch)
  return ⟨← t.raw.replaceM fun s => pure (if s.getKind == k then some p.raw else none)⟩

/-- The opcode byte at the `pc` of the machine in the goal's `run n m`, read from the literal
base code if the code is patched. -/
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

/-- `sol_step` for code `patchWords base ps` with symbolic patches (see the module doc). -/
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
    evalTactic (← `(tactic| try evm_norm [EvmLogic.Tactic.Patched.reducePatchedRead,
      EvmLogic.Tactic.SolStep.reduceCodeImm, sol_norm, Nat.reduceMod, Nat.reducePow, Nat.reduceLT,
      $extra,*]))

/-- Repeat `psol_step` while it succeeds. -/
syntax "psol_steps" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| psol_steps) => `(tactic| repeat psol_step)
  | `(tactic| psol_steps [$extra,*]) => `(tactic| repeat psol_step [$extra,*])

/-- `sol_dispatch` for patched code: prove `Dispatch.Reaches code sel entry n cost` with a
hypothesis `JumpDestsAgree code base` in the context. -/
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

/-!
## `pwp_step`: the frame-local symbolic executor on code with symbolic immutables

`wp_step` (`EvmLogic.Tactic.WpStep`) reads code bytes, pushed immediates and jump
destinations from a literal code constant. The runtime code of a contract deployed with
*arbitrary* immutables is `Contracts.patchWords base ps` with symbolic patched words (e.g.
`SolmateVault.runtimeCodeWith i`), which is not a literal. `pwp_step` is `wp_step` for such
code, using the patched-code lemmas of `EvmLogic.Solidity.Immutables` (as
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

namespace EvmLogic.Program
open EvmLean

open Lean Elab Tactic EvmLogic.Tactic Meta
open EvmLean.Interpreter EvmLogic.Solidity

/-- A jump destination of patched code with the canonical scan. -/
theorem isValidJumpDest_of_jumpTable_agree {jd : Array Bool} {code base : ByteArray} {d : Nat}
    (hjd : JumpTable jd code) (h : JumpDestsAgree code base)
    (hd : d ∈ Solidity.jumpDestList (base.size + 1) base.data.toList 0) :
    isValidJumpDest jd d = true := by
  rw [hjd]; exact isValidJumpDest_of_agree h hd

/-- `(base, ps)` if `code` unfolds to `patchWords base ps`, with the patch offsets. -/
def patchedCode? (code : Expr) : MetaM (Option (Expr × Expr × List Nat)) := do
  let some (base, ps) ← Tactic.Patched.patched? code | return none
  let some offs ← Tactic.Patched.patchOffsets? ps | return none
  return some (base, ps, offs)

/-- A kernel-checked proof of `∀ o ∈ offs, P o` for a decidable closed `P`, built by
`mkBody o`. -/
def offsDisjProof (offs : List Nat) (mkBody : Expr → MetaM Expr) : MetaM Expr := do
  let offsE := Tactic.Patched.natListLit offs
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
      #[base, ps, mkNatLit pc, Tactic.Patched.natListLit offs,
        ← Tactic.Patched.offsetsProof ps offs, hdisj]
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
      #[base, ps, mkNatLit off, mkNatLit n, Tactic.Patched.natListLit offs,
        ← Tactic.Patched.offsetsProof ps offs, hdisj]
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

end EvmLogic.Program

end

section

/-!
## `CODECOPY` in the frame-local logic

`wp_step` (`EvmLogic.Tactic.WpStep`) has no lemma for `CODECOPY`, which solc uses to
load 32-byte constants (event topics, revert strings) from the end of the code.
`pwp_codecopy` performs one `CODECOPY` of a literal range of literal or patched code
(`EvmLogic.Tactic.Patched`; the range must avoid the patches): it applies
`step_codecopy`, then evaluates the copied bytes with `reducePatchedRead` and `reduceCodeImm`
(kernel-checked evaluations, as `psol_step` does) and turns the copied word into an `MSTORE`
(`Memory.write_ofWord`), so that later reads of it reduce.
-/

namespace EvmLogic.Program
open EvmLean

open EvmLean.Interpreter

/-- Execute a `CODECOPY` of a non-empty literal range in a `WP` goal (see the module
docstring). -/
macro "pwp_codecopy" : tactic => `(tactic| (
  apply WP.of_step
  case h =>
    apply EvmLean.Interpreter.step_codecopy (by pcode_fact) rfl (by decide) (by evm_gas)
  case hs => same_frame
  simp only [EvmLogic.Tactic.Patched.reducePatchedRead, EvmLogic.Tactic.SolStep.reduceCodeImm, Memory.write_ofWord, BitVec.reduceToNat,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub, memoryCost, Gas.extendMemory,
    List.foldl, Gas.ceil32, Gas.memoryCost, Gas.words, Gas.memoryPerWord, Memory.size_storeWord,
    Memory.size_expand, Memory.size_empty, Memory.wordsAfter, Memory.words, Nat.reduceLeDiff,
    Nat.reduceEqDiff, Nat.max_def, ↓reduceIte]))

end EvmLogic.Program

end
