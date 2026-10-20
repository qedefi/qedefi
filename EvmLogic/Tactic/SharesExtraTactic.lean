import EvmLogic.Solidity.Dispatch
import EvmLogic.Solidity.Immutables

/-!
# `psol_step`: symbolic execution of code with symbolic immutables

`sol_step` (`EvmLeanProofs.Solidity.Tactic`) needs the executed code to be a byte literal.
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

namespace EvmLean.Solidity.Patched

open Lean Elab Tactic Meta Simp
open EvmLean.Interpreter EvmLean.Contracts

/-! ## Recognising patched code -/

/-- `(base, ps)` if `e` unfolds (through head constants) to `Contracts.patchWords base ps`. -/
def patched? (e : Expr) : MetaM (Option (Expr × Expr)) := withTransparency .default do
  let mut e ← instantiateMVars e
  for _ in [0:16] do
    e := e.consumeMData
    if let some (base, ps) := e.app2? ``Contracts.patchWords then
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
  let some m := Exec.findRunMachine? t | throwError "psol_step: no `run _ m` in the goal"
  let fr ← mkAppM ``Machine.frame #[m]
  let pc ← whnfD (← mkAppM ``Frame.pc #[fr])
  let some pc ← (evalNat pc).run | throwError "psol_step: pc is not a numeral: {pc}"
  let code ← whnfR (← mkAppM ``Frame.code #[fr])
  let code ← match ← patched? code with
    | some (base, _) => pure base
    | none => pure code
  let some bytes ← Exec.codeBytes? code
    | throwError "psol_step: the code is not a (patched) byte-array literal"
  let some b := bytes[pc]? | throwError "psol_step: pc {pc} past the end of the code"
  return b

/-- `sol_step` for code `patchWords base ps` with symbolic patches (see the module doc). -/
syntax "psol_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| psol_step) => do evalTactic (← `(tactic| psol_step []))
  | `(tactic| psol_step [$extra,*]) => do
    let b ← currentByte
    let halts ← (← Exec.haltTactics b).mapM swapDisch
    if halts.isEmpty then
      let tacs ← (← Exec.stepTactics b).mapM swapDisch
      if tacs.isEmpty then throwError "psol_step: no step lemma for opcode {b}"
      evalTactic (← `(tactic| rw [EvmLean.Interpreter.run_succ_of_running ?h]))
      let gs ← getGoals
      let some hg ← gs.findM? (fun g => return (← g.getTag).eraseMacroScopes == `h)
        | throwError "psol_step: no side goal"
      let rest := gs.filter (· != hg)
      setGoals [hg]
      Exec.firstOf tacs s!"psol_step: no step lemma applies to opcode {b}"
      setGoals rest
    else
      evalTactic (← `(tactic| rw [EvmLean.Interpreter.run_succ_of_done ?h]))
      let gs ← getGoals
      let some hg ← gs.findM? (fun g => return (← g.getTag).eraseMacroScopes == `h)
        | throwError "psol_step: no side goal"
      let rest := gs.filter (· != hg)
      setGoals [hg]
      Exec.firstOf halts s!"psol_step: no halting lemma applies to opcode {b}"
      setGoals rest
    evalTactic (← `(tactic| try evm_norm [EvmLean.Solidity.Patched.reducePatchedRead,
      EvmLean.Solidity.Exec.reduceCodeImm, sol_norm, Nat.reduceMod, Nat.reducePow, Nat.reduceLT,
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

end EvmLean.Solidity.Patched
