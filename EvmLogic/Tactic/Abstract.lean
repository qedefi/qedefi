import Lean
import EvmLogic.Program.Call
import EvmLogic.Step.Memory

/-!
# Cheap abstraction of machine fields, and access-cost bounds

* `wp_abstract`: replace a field of a `WP` goal's machine by a variable, cheaply;
* `access_bounds`: bound every `Gas.accessCost` in the goal.

## `wp_abstract`

`wp_abstract memory M h` (also `gas`, `sub`, `world`) turns the goal `WP m Q H`, whose machine is a
structure literal, into `WP m' Q H` with the field replaced by a fresh variable `M` and
`h : <old value> = M` in context. Unlike `wp_generalize_mem`/`wp_generalize_gas` (which call
`generalize`, i.e. `kabstract` over the whole goal), it rebuilds the machine at the known
argument position and closes the original goal by `abstract_elim` (`rfl`), so its cost does not
depend on the size of the goal: on the Aave AToken's `mint` path, after three `SSTORE`s and four
mapping reads, `generalize` did not finish in minutes. The abstraction survives into the proof
term (a constant applied to a `fun`, not a beta-redex), so the kernel also checks the remaining
steps against the variable.
-/

namespace EvmLogic.Tactic
open EvmLean EvmLean.Interpreter EvmLogic.Program Lean Elab Tactic Meta

/-- Generalize `a` in `P a` (the proof term of `wp_abstract`). Applying a constant keeps the
abstraction in the final proof: `(fun x h => …) a rfl` would be beta-reduced by
`instantiateMVars`, putting `a` back everywhere, and the kernel would then re-check every step
against the concrete term (for a memory, evaluating its bytes). -/
theorem abstract_elim.{u} {α : Sort u} {P : α → Prop} (a : α) (h : ∀ x, a = x → P x) : P a :=
  h a rfl

/-- See the module doc. -/
elab "wp_abstract " fld:ident x:ident h:ident : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let_expr WP m q hh := t | throwError "wp_abstract: not a WP goal"
  unless m.isAppOfArity ``Machine.mk 8 do throwError "wp_abstract: machine is not a literal"
  let margs := m.getAppArgs
  let fr := margs[6]!
  unless fr.isAppOfArity ``Frame.mk 11 do throwError "wp_abstract: frame is not a literal"
  let fargs := fr.getAppArgs
  let mkFrame (i : Nat) (v : Expr) : Expr :=
    mkAppN (mkConst ``Machine.mk)
      (margs.set! 6 (mkAppN (mkConst ``Frame.mk) (fargs.set! i v)))
  let (val, mk) ← match fld.getId.eraseMacroScopes with
    | `memory => pure (fargs[5]!, mkFrame 5)
    | `gas => pure (fargs[6]!, mkFrame 6)
    | `sub => pure (fargs[8]!, mkFrame 8)
    | `world => pure (margs[2]!, fun v => mkAppN (mkConst ``Machine.mk) (margs.set! 2 v))
    | _ => throwError "wp_abstract: field must be memory, gas, sub or world"
  let ty ← inferType val
  let newTy ← withLocalDeclD x.getId ty fun xv => do
    let eq ← mkEq val xv
    withLocalDeclD h.getId eq fun hv => do
      mkForallFVars #[xv, hv] (mkApp3 (mkConst ``WP) (mk xv) q hh)
  let ng ← mkFreshExprSyntheticOpaqueMVar newTy
  let motive ← withLocalDeclD x.getId ty fun xv => do
    mkLambdaFVars #[xv] (mkApp3 (mkConst ``WP) (mk xv) q hh)
  let u ← getLevel ty
  g.assign (mkAppN (mkConst ``abstract_elim [u]) #[ty, motive, val, ng])
  let (_, ng') ← ng.mvarId!.introN 2 [x.getId, h.getId]
  replaceMainGoal [ng']

/-- Hypotheses `Memory.size M = n` and `Memory.loadWord M 64 = v` of the context (`M` a
variable, `n`, `v` closed), as simp lemmas. -/
def memFactLemmas : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := withMainContext do
  let mut out := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let some (_, lhs, rhs) := ty.eq? | continue
    let ok := (lhs.isAppOfArity ``Memory.size 1 && lhs.appArg!.isFVar) ||
      (lhs.isAppOfArity ``Memory.loadWord 2 && lhs.appFn!.appArg!.isFVar)
    unless ok && !rhs.hasFVar && !rhs.hasMVar do continue
    let t ← Term.exprToSyntax decl.toExpr
    out := out.push (← `(Lean.Parser.Tactic.simpLemma| $t:term))
  return out

/-- `wp_abstract_mem M`: `wp_abstract memory`, keeping what later steps need about the old
memory as hypotheses `M_size : M.size = n` (its size, when a numeral) and
`M_fp : M.loadWord 64 = v` (solc's free-memory pointer, when a closed word), computed from the
old memory term and the facts already known about earlier abstracted memories; the equation
`<old term> = M` is dropped, or kept as `h` with `wp_abstract_mem M with h` (to read the
memory's contents later, e.g. a call's input). `pwp_steps` uses `M_size` and `M_fp` by itself
(`memSizeLemmas`), so a memory size never has to be passed by hand. -/
syntax "wp_abstract_mem " ident (" with " ident)? : tactic

elab_rules : tactic | `(tactic| wp_abstract_mem $M:ident $[with $k]?) => withMainContext do
  let h := k.getD (mkIdent (M.getId.appendAfter "_eq"))
  let hs := mkIdent (M.getId.appendAfter "_size")
  let hf := mkIdent (M.getId.appendAfter "_fp")
  let facts ← memFactLemmas
  evalTactic (← `(tactic| wp_abstract memory $M $h))
  evalTactic (← `(tactic| have $hs := congrArg Memory.size $h:ident))
  evalTactic (← `(tactic| have $hf := congrArg (Memory.loadWord · 64) $h:ident))
  if k.isNone then evalTactic (← `(tactic| clear $h:ident))
  evalTactic (← `(tactic| try simp only [Memory.size_storeWord, Memory.size_expand,
    Memory.size_empty, Memory.size_write, Memory.size_read, returnMemory, ByteArray.size_extract,
    Bytes.size_ofWord, Nat.sub_zero, Nat.zero_le, Nat.min_eq_left, Nat.min_def,
    Memory.wordsAfter, Memory.words, BitVec.reduceToNat, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceDiv, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff,
    Nat.max_def, ↓reduceIte, Nat.zero_add, $facts,*] at $hs:ident))
  evalTactic (← `(tactic| try simp (disch := decide) only [Memory.loadWord_expand,
    Memory.loadWord_storeWord, returnMemory, ByteArray.size_extract, Bytes.size_ofWord,
    Nat.sub_zero, Nat.zero_le, Nat.min_eq_left, Nat.min_def, ↓reduceIte, BitVec.reduceToNat,
    Memory.loadWord_storeWord_of_disjoint, $facts,*] at $hf:ident))
  -- keep a fact only if its left side became closed; turn it around
  for n in [hs, hf] do
    withMainContext do
      let some decl := (← getLCtx).findFromUserName? n.getId | return
      let ty ← instantiateMVars decl.type
      let some (_, lhs, rhs) := ty.eq? | return
      let closed (e : Expr) := !e.hasFVar && !e.hasMVar
      if closed lhs then
        evalTactic (← `(tactic| replace $n:ident := Eq.symm $n:ident))
      else unless closed rhs do
        replaceMainGoal [← (← getMainGoal).clear decl.fvarId]

/-- Add `Gas.accessCost b ≤ 2600` for every access cost `Gas.accessCost b` in the goal (the
warm set after a few storage accesses is a large term; `evm_gas` does not bound it). -/
elab "access_bounds" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let found ← IO.mkRef (#[] : Array Expr)
  forEachExpr t fun e => do
    if e.isAppOfArity ``Gas.accessCost 1 then found.modify (·.push e.appArg!)
  for b in ← found.get do
    let pf ← mkAppM ``accessCost_le #[b]
    let g ← getMainGoal
    let (_, g') ← (← g.assert `hacc (← inferType pf) pf).intro1P
    replaceMainGoal [g']

end EvmLogic.Tactic
