import EvmLogic.Tactic.WpStep
import EvmLogic.Program.Code

/-!
# Fast symbolic steps: building the step proof instead of rewriting the goal

`wp_step` proves one instruction by `apply WP.of_step`, `apply step_<op>`, and then normalizes
the **whole goal** `WP m Q H` with `simp` — the machine, the postconditions and every unchanged
field — at every instruction; its proof term repeats the goal at every step. `fastWpStep` does
the same step with the same step lemmas, but builds the proof term directly:

* the step lemma is instantiated with the literal machine `m = Machine.mk … (Frame.mk …)`
  (stack operands by first-order matching against the stack literal, code bytes and pushed
  immediates by table lookups, constant gas costs from a `L ≤ G` hypothesis by `Nat.ble`);
* only the **changed fields** of the next machine are normalized, with the same simp set as
  `wp_step`, and joined to the step equation by congruence;
* the step is `WP.of_step h (SameFrame.of_update …) ?next`, so the new goal is `WP m' Q H` with
  `Q` and `H` untouched.

Everything is checked by the kernel as before: the speedup only changes how the proof is
found, never what is proved. Side conditions it cannot close cheaply are handed to the old
discharger, and instructions it does not handle (halts, calls, patched immediates) to the old
step, so it is a drop-in accelerator.
-/

namespace EvmLogic.Tactic.FastStep
open EvmLean Lean Meta Elab Tactic EvmLean.Interpreter EvmLogic.Program

/-- Type-check every proof term the fast stepper builds (debugging). -/
register_option fastStep.check : Bool := {
  defValue := false
  descr := "type-check each proof term built by the fast symbolic stepper" }

/-- Use the fast stepper (`false`: the original one-lemma-per-step tactics only; for
comparison). -/
register_option fastStep.enable : Bool := {
  defValue := true
  descr := "use the fast symbolic stepper in pwp_steps/psol_steps" }

register_option fastStep.debugSorry : Nat := { defValue := 0, descr := "debug" }

/-! ## Gas side conditions -/

theorem le_gas_sub {L G n c : Nat} (hL : L ≤ G) (h : Nat.ble (c + n) L = true) : c ≤ G - n := by
  have := Nat.le_of_ble_eq_true h; omega

theorem lt_gas_sub {L G n c : Nat} (hL : L ≤ G) (h : Nat.ble (c + n + 1) L = true) :
    c < G - n := by
  have := Nat.le_of_ble_eq_true h; omega

theorem le_gas {L G c : Nat} (hL : L ≤ G) (h : Nat.ble c L = true) : c ≤ G := by
  have := Nat.le_of_ble_eq_true h; omega

theorem lt_gas {L G c : Nat} (hL : L ≤ G) (h : Nat.ble (c + 1) L = true) : c < G := by
  have := Nat.le_of_ble_eq_true h; omega

/-- Each element of `l` is at most the matching element of `bs`. -/
def BoundedBy : List Nat → List Nat → Prop
  | [], [] => True
  | a :: l, b :: bs => a ≤ b ∧ BoundedBy l bs
  | _, _ => False

theorem le_sub_chain' {c : Nat} : ∀ (l bs : List Nat) {L G : Nat}, BoundedBy l bs → L ≤ G →
    c + bs.sum ≤ L → c ≤ l.foldl (· - ·) G
  | [], [], _, _, _, hL, h => by simp only [List.sum_nil, List.foldl_nil] at h ⊢; omega
  | a :: l, b :: bs, L, G, hb, hL, h => by
    simp only [List.sum_cons] at h
    simp only [List.foldl_cons]
    exact le_sub_chain' l bs (L := L - b) (G := G - a) hb.2 (by have := hb.1; omega) (by omega)
  | [], _ :: _, _, _, hb, _, _ => hb.elim
  | _ :: _, [], _, _, hb, _, _ => hb.elim

/-- `c ≤ G - a₁ - … - aₖ` from `L ≤ G` and bounds `c ≤ bc`, `aᵢ ≤ bᵢ` with `bc + Σ bᵢ ≤ L`. -/
theorem le_sub_chain {L G c bc : Nat} (l bs : List Nat) (hb : BoundedBy l bs) (hL : L ≤ G)
    (hc : c ≤ bc) (h : Nat.ble (bc + bs.sum) L = true) : c ≤ l.foldl (· - ·) G :=
  Nat.le_trans hc (le_sub_chain' l bs hb hL (Nat.le_of_ble_eq_true h))

theorem lt_sub_chain {L G c bc : Nat} (l bs : List Nat) (hb : BoundedBy l bs) (hL : L ≤ G)
    (hc : c ≤ bc) (h : Nat.ble (bc + bs.sum + 1) L = true) : c < l.foldl (· - ·) G :=
  Nat.lt_of_le_of_lt hc (le_sub_chain' (c := bc + 1) l bs hb hL
    (by have := Nat.le_of_ble_eq_true h; omega))

theorem sub_le_sub_of {l H a b : Nat} (h1 : l ≤ H) (h2 : a ≤ b) : l - b ≤ H - a := by omega

theorem le_of_le_add {L X G c : Nat} (h1 : L ≤ X) (h2 : X ≤ G + c) : L - c ≤ G := by omega

theorem foldl_sub_eq (G : Nat) : ∀ l : List Nat, l.foldl (· - ·) G = G - l.sum
  | [] => by simp
  | a :: l => by
    simp only [List.foldl_cons, List.sum_cons, foldl_sub_eq (G - a) l, Nat.sub_sub]

theorem chain_sub (G k s : Nat) (l : List Nat) (h : l.sum + k = s) :
    l.foldl (· - ·) G - k = G - s := by
  rw [foldl_sub_eq, Nat.sub_sub, h]

theorem sub_sub_lit (G n k s : Nat) (h : n + k = s) : G - n - k = G - s := by
  rw [Nat.sub_sub, h]

theorem length_lt_of_tail {α : Type} (pre rest : List α) {K k : Nat} (h : rest.length ≤ K)
    (hk : Nat.ble (pre.length + K + 1) k = true) : (pre ++ rest).length < k := by
  have := Nat.le_of_ble_eq_true hk
  rw [List.length_append]; omega

/-- The per-run configuration of the fast stepper. -/
structure Cfg where
  /-- The normalization simp set (that of `wp_step`, with the caller's extra lemmas). -/
  simpCtx : Simp.Context
  /-- Its simprocs. -/
  simprocs : Simp.SimprocsArray
  /-- `code[pc]? = some b`, for the code and pc of the goal. -/
  codeFact : Expr → Nat → UInt8 → MetaM Expr
  /-- `Bytes.toWord (readBytes code (pc + 1) n) = v` for a `PUSHn`, if the immediate is known. -/
  pushFact : Expr → Nat → Nat → MetaM (Option Expr)
  /-- The bytes of a code expression. -/
  bytes : Expr → MetaM (Option (Array UInt8))
  /-- The fallback discharger (on the main goal). -/
  disch : TacticM Unit
  /-- Fold gas into `G - n` (the normal form of `wp_step`'s simp set, which has `Nat.sub_sub`)
  rather than keep the chain `G - a₁ - … - aₖ` (that of `sol_step`). -/
  foldGas : Bool := true

/-- The value of a closed gas cost (`Gas.veryLow`, `if 2 = 0 then … else …`, …). -/
def closedNat? (c : Expr) : MetaM (Option Nat) := do
  if c.hasFVar || c.hasMVar then return none
  if let some n ← (evalNat c).run then return some n
  let r ← withTransparency .default <| reduce c
  (evalNat r).run

/-- An upper bound `b` of a gas cost `e` (a numeral expression) and a proof of `e ≤ b`:
closed costs, `sloadCost`, `SSTORE` costs, sums of these. -/
def costBound (norm : Expr → MetaM (Option (Expr × Option Expr))) :
    Nat → Expr → MetaM (Option (Expr × Expr))
  | 0, _ => return none
  | fuel + 1, e => do
    if let some _ ← closedNat? e then
      return some (e, mkApp (mkConst ``Nat.le_refl) e)
    match_expr e with
    | sloadCost w => return some (mkNatLit 2100, mkApp (mkConst ``sloadCost_le) w)
    | Prod.fst _ _ p =>
      match_expr p with
      | sstoreCostRefund m x y =>
        return some (mkNatLit 22100, mkApp3 (mkConst ``sstoreCost_le) m x y)
      | Gas.sstoreCostRefund o c n w =>
        return some (mkNatLit 22100, mkApp4 (mkConst ``Gas.sstoreCostRefund_fst_le) o c n w)
      | _ => return none
    | HAdd.hAdd _ _ _ _ a b =>
      let some (ba, pa) ← costBound norm fuel a | return none
      let some (bb, pb) ← costBound norm fuel b | return none
      return some (← mkAdd ba bb, mkAppN (mkConst ``Nat.add_le_add) #[a, ba, b, bb, pa, pb])
    | _ =>
      -- memory expansion and the like: normalize the cost alone to a numeral
      let some (v, p) ← norm e | return none
      let some _ ← closedNat? v | return none
      match p with
      | some p => return some (v, ← mkAppM ``Nat.le_of_eq #[p])
      | none => return some (v, mkApp (mkConst ``Nat.le_refl) v)

/-- The gas field as `G - a₁ - … - aₖ` with bounded `aᵢ`: `(G, [aᵢ], [bᵢ], proof of BoundedBy)`. -/
def gasChain (norm : Expr → MetaM (Option (Expr × Option Expr))) (g : Expr) :
    MetaM (Option (Expr × Array Expr × Array Expr × Expr)) := do
  let mut cur := g.consumeMData
  let mut subs : Array (Expr × Expr × Expr) := #[]
  for _ in [0:100000] do
    if cur.isFVar then
      -- `subs` is outermost first; the list is innermost first
      let ordered := subs.reverse
      -- `BoundedBy [a₁, …] [b₁, …]` as nested `And.intro`, built from the end
      let mut pf := mkConst ``True.intro
      for (_, _, p) in subs do
        pf ← mkAppM ``And.intro #[p, pf]
      return some (cur, ordered.map (·.1), ordered.map (·.2.1), pf)
    let_expr HSub.hSub _ _ _ _ x a := cur | return none
    let some (b, p) ← costBound norm 4096 a | return none
    subs := subs.push (a, b, p)
    cur := x.consumeMData
  return none

/-- `G - a₁ - … - aₖ` (`k ≥ 2`, closed `aᵢ`) as `(G, [a₁, …, aₖ])`. -/
def closedChain? (g : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let mut cur := g.consumeMData
  let mut subs : Array Expr := #[]
  for _ in [0:100000] do
    if cur.isFVar then
      if subs.size < 2 then return none
      return some (cur, subs.reverse)
    let_expr HSub.hSub _ _ _ _ x a := cur | return none
    if (← closedNat? a).isNone then return none
    subs := subs.push a
    cur := x.consumeMData
  return none

/-- `(G, n)` if the gas field is `G - n` with a numeral `n`, or `(G, 0)` for a variable `G`. -/
def gasShape (g : Expr) : MetaM (Option (Expr × Nat)) := do
  let g := g.consumeMData
  if g.isFVar then return some (g, 0)
  let_expr HSub.hSub _ _ _ _ G n := g | return none
  let some n ← (evalNat n).run | return none
  unless G.isFVar do return none
  return some (G, n)

/-- A lower bound of a numeral-valued term `X` (a numeral, a variable with a bound, or
`H - a` for a numeral `a`): `(proof of L ≤ X, L)`. -/
def termBound (bound : Expr → MetaM (Option (Expr × Nat))) (X : Expr) :
    MetaM (Option (Expr × Nat)) := do
  let X := X.consumeMData
  if let some v ← (evalNat X).run then return some (mkApp (mkConst ``Nat.le_refl) X, v)
  if X.isFVar then return ← bound X
  let_expr HSub.hSub _ _ _ _ H a := X | return none
  unless H.isFVar do return none
  let some (pH, l) ← bound H | return none
  match ← (evalNat a).run with
  | some av =>
    -- `l - a ≤ H - a`
    let pf := mkApp4 (mkConst ``Nat.sub_le_sub_right) (mkNatLit l) H pH a
    return some (← mkExpectedTypeHint pf (← mkLE (mkNatLit (l - av)) X), l - av)
  | none =>
    -- `l - b ≤ H - a` for a bounded cost `a ≤ b`
    let some (b, pa) ← costBound (fun _ => pure none) 4096 a | return none
    let some bv ← closedNat? b | return none
    let pf := mkAppN (mkConst ``sub_le_sub_of) #[mkNatLit l, H, a, b, pH, pa]
    return some (← mkExpectedTypeHint pf (← mkLE (mkNatLit (l - bv)) X), l - bv)

/-- A lower bound `L ≤ G` (numeral `L`) with its proof, from hypotheses `L ≤ G` and, through
at most `depth` summaries, `X ≤ G + c` with a lower bound of `X` (the gas a call or an internal
function returns). -/
def gasBoundN : Nat → Expr → MetaM (Option (Expr × Nat))
  | 0, _ => return none
  | depth + 1, G => do
    let mut best : Option (Expr × Nat) := none
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      let_expr LE.le _ _ X R := ty | continue
      if R == G then
        if let some v ← (evalNat X).run then
          if best.all (·.2 < v) then best := some (decl.toExpr, v)
        continue
      let_expr HAdd.hAdd _ _ _ _ G' c := R | continue
      unless G' == G do continue
      let some cv ← (evalNat c).run | continue
      if X == G then continue
      let some (pX, l) ← termBound (gasBoundN depth) X | continue
      if l ≤ cv then continue
      if best.all (·.2 < l - cv) then
        let pf := mkAppN (mkConst ``le_of_le_add) #[mkNatLit l, X, G, c, pX, decl.toExpr]
        best := some (← mkExpectedTypeHint pf (← mkLE (mkNatLit (l - cv)) G), l - cv)
    return best

/-- `gasBoundN` through at most six summaries. -/
def gasBound (G : Expr) : MetaM (Option (Expr × Nat)) := gasBoundN 7 G

/-- Close `c ≤ gas` or `c < gas` for a bounded cost `c` and a gas field `G - a₁ - … - aₖ`
with bounded `aᵢ`, from a hypothesis `L ≤ G`. -/
def gasFact? (norm : Expr → MetaM (Option (Expr × Option Expr))) (t gas : Expr) :
    MetaM (Option Expr) := do
  let (isLt, c) ← match_expr t with
    | LE.le _ _ c _ => pure (false, c)
    | LT.lt _ _ c _ => pure (true, c)
    | _ => return none
  let some (bc, hc) ← costBound norm 4096 c | return none
  let some (G, subs, bs, hb) ← gasChain norm gas | return none
  let some (hL, L) ← gasBound G | return none
  let some bcv ← closedNat? bc | return none
  let mut total := bcv
  for b in bs do
    let some v ← closedNat? b | return none
    total := total + v
  let need := if isLt then total + 1 else total
  unless need ≤ L do return none
  let hble := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let l ← mkListLit (mkConst ``Nat) subs.toList
  let lb ← mkListLit (mkConst ``Nat) bs.toList
  let pf := mkAppN (mkConst (if isLt then ``lt_sub_chain else ``le_sub_chain))
    #[mkNatLit L, G, c, bc, l, lb, hb, hL, hc, hble]
  return some (← mkExpectedTypeHint pf t)

/-! ## Machines as literals -/

/-- The fields of a machine literal `Machine.mk …` and of its frame `Frame.mk …`. -/
def literalFields? (m : Expr) : Option (Array Expr × Array Expr) := do
  let m := m.consumeMData
  guard (m.isAppOfArity ``Machine.mk 8)
  let ms := m.getAppArgs
  let f := (ms.getD 6 default).consumeMData
  guard (f.isAppOfArity ``Frame.mk 11)
  return (ms, f.getAppArgs)

/-- The `k`-th element of a list literal. -/
def listNth? : Nat → Expr → Option Expr
  | 0, l => do
    let some (_, h, _) := l.consumeMData.app3? ``List.cons | none
    some h
  | k + 1, l => do
    let some (_, _, t) := l.consumeMData.app3? ``List.cons | none
    listNth? k t

/-- `f a₁ … aₙ = f b₁ … bₙ` from per-argument equations (`none`: syntactically equal). -/
def congrApp (f : Expr) (olds : Array Expr) (pfs : Array (Option Expr)) :
    MetaM (Option Expr) := do
  let mut acc : Option Expr := none
  for i in [0:olds.size] do
    match acc, (pfs.getD i default) with
    | none, none => pure ()
    | none, some p => acc := some (← mkCongrArg (mkAppN f (olds.extract 0 i)) p)
    | some q, none => acc := some (← mkCongrFun q (olds.getD i default))
    | some q, some p => acc := some (← mkCongr q p)
  return acc

/-- Reduce a projection applied to a structure literal: `Machine.ctx (Machine.mk c …) ↦ c`
(through `have`s and nested projections). `none` if `e` is not such a projection. -/
def projOfN : Nat → Expr → MetaM (Option Expr)
  | 0, _ => return none
  | fuel + 1, e => do
    let e := e.consumeMData
    match e with
    | .proj _ i s =>
      let s ← whnfCore ((← projOfN fuel s).getD s)
      unless s.isApp && s.getAppFn.isConst do return none
      let some (.ctorInfo ci) := (← getEnv).find? s.getAppFn.constName | return none
      return s.getAppArgs[ci.numParams + i]?
    | .app f a =>
      let .const n _ := f | return none
      let some info := (← getEnv).getProjectionFnInfo? n | return none
      let a ← whnfCore ((← projOfN fuel a).getD a)
      unless a.isAppOf info.ctorName do return none
      return a.getAppArgs[info.numParams + info.i]?
    | _ => return none

/-- `projOfN` with enough fuel for the nesting of machine, frame and message fields. -/
def projOf? (e : Expr) : MetaM (Option Expr) := projOfN 8 e

/-- Split the right side of a step lemma into the new fields: `(machine fields, frame fields)`,
each either unchanged (taken from `m`) or a raw new value. -/
def splitRhs (rhs : Expr) (ms fs : Array Expr) :
    MetaM (Option (Array (Expr × Bool) × Array (Expr × Bool))) := do
  let rhs ← whnfCore rhs.consumeMData
  unless rhs.isAppOfArity ``Machine.mk 8 do return none
  let ra := rhs.getAppArgs
  let mut mOut : Array (Expr × Bool) := #[]
  for i in [0:8] do
    if i == 6 then
      mOut := mOut.push ((ra.getD i default), true)
      continue
    match ← projOf? (ra.getD i default) with
    | some r => if r == (ms.getD i default) then mOut := mOut.push ((ms.getD i default), false)
                else mOut := mOut.push ((ra.getD i default), true)
    | none => mOut := mOut.push ((ra.getD i default), (ra.getD i default) != (ms.getD i default))
  -- the frame: `have __src := m.frame; Frame.mk …` or `Frame.mk …`
  let fr ← whnfCore (ra.getD 6 default).consumeMData
  unless fr.isAppOfArity ``Frame.mk 11 do return none
  let fa := fr.getAppArgs
  let mut fOut : Array (Expr × Bool) := #[]
  for i in [0:11] do
    match ← projOf? (fa.getD i default) with
    | some r => if r == (fs.getD i default) then fOut := fOut.push ((fs.getD i default), false)
                else fOut := fOut.push ((fa.getD i default), true)
    | none => fOut := fOut.push ((fa.getD i default), (fa.getD i default) != (fs.getD i default))
  return some (mOut, fOut)

/-! ## The step -/

/-- Reduce the projections of the machine literal `m` in `e` (definitionally), without
descending into `m` itself. -/
def reduceProjs (m e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun x => do
    if x == m then return .done x
    match ← projOf? x with
    | some r => return .visit r
    | none => return .continue)

/-- The elements and tail of a list built from a stack literal by `List.cons` and `List.set`
with numeral indices (`swap`'s `x :: rest.set n y`). -/
def evalList : Nat → Expr → MetaM (Option (Array Expr × Expr))
  | 0, _ => return none
  | fuel + 1, e => do
    let e := e.consumeMData
    if let some (_, h, t) := e.app3? ``List.cons then
      let some (xs, tl) ← evalList fuel t | return none
      return some (#[h] ++ xs, tl)
    match_expr e with
    | List.set _ l i x =>
      let some i ← (evalNat i).run | return none
      let some (xs, tl) ← evalList fuel l | return none
      unless i < xs.size do return none
      return some (xs.set! i x, tl)
    | _ => return some (#[], e)

/-- Normalize a changed field: `(value, proof raw = value)`. -/
def normField (cfg : Cfg) (m e : Expr) : MetaM (Expr × Option Expr) := do
  let e' ← reduceProjs m e
  let (r, _) ← Meta.simp e' cfg.simpCtx cfg.simprocs
  return (r.expr, r.proof?)

/-- `of_decide_eq_true rfl` for a closed proposition whose `decide` evaluates to `true` in the
elaborator (small facts only: numerals, `Word` comparisons); the kernel re-checks it. -/
def closedDecide? (ty : Expr) : MetaM (Option Expr) := do
  if ty.approxDepth > 24 then return none
  if ty.getUsedConstants.any (· == ``isValidJumpDest) then return none
  try
    let inst ← synthInstance (mkApp (mkConst ``Decidable) ty)
    let d ← withTransparency .default <| whnf (mkApp2 (mkConst ``Decidable.decide) ty inst)
    unless d.isConstOf ``Bool.true do return none
    let rflTrue := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    return some (mkApp3 (mkConst ``of_decide_eq_true) ty inst (mkExpectedPropHint rflTrue
      (← mkEq (mkApp2 (mkConst ``Decidable.decide) ty inst) (mkConst ``Bool.true))))
  catch _ => return none

/-- `c ≤ gas` / `c < gas` for a closed cost `c`, by `evm_gas` on the gas field itself in a
context cut down to the small linear facts over `Nat` (large hypotheses make it slow). -/
def gasOmega? (ty gas : Expr) : TacticM (Option Expr) := do
  let (isLt, c) ← match_expr ty with
    | LE.le _ _ c _ => pure (false, c)
    | LT.lt _ _ c _ => pure (true, c)
    | _ => return none
  let some cv ← closedNat? c | return none
  let goal ← if isLt then mkLT (mkNatLit cv) gas else mkLE (mkNatLit cv) gas
  let g ← mkFreshExprSyntheticOpaqueMVar goal
  -- only small linear facts over `Nat` (large hypotheses make `omega` slow)
  let mut drop : Array FVarId := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let t ← instantiateMVars decl.type
    let isNatEq := match t.eq? with
      | some (ty, _, _) => ty.isConstOf ``Nat
      | none => false
    let small := t.approxDepth ≤ 32 && (t.isAppOf ``LE.le || t.isAppOf ``LT.lt || isNatEq)
    unless small do drop := drop.push decl.fvarId
  let g' ← g.mvarId!.tryClearMany drop
  let saved ← getGoals
  setGoals [g']
  let st ← saveState
  let ok ← tryCatchRuntimeEx (do
      withTheReader Core.Context (fun c => { c with maxHeartbeats := 200000000 })
        (withoutRecover (evalTactic (← `(tactic| evm_gas))))
      return true)
    (fun e => do
      trace[EvmLean.wp] "gas omega failed: {e.toMessageData}"
      st.restore
      return false)
  setGoals saved
  unless ok do return none
  return some (← mkExpectedTypeHint (← instantiateMVars g) ty)

/-- Discharge the hypotheses of an instantiated step lemma. `false` if one fails. -/
def dischHyps (cfg : Cfg) (m code : Expr) (pc : Nat) (b : UInt8) (stack gas : Expr)
    (xs : Array Expr) : TacticM Bool := do
  -- costs normalized alone (memory expansion over a literal memory size)
  let norm : Expr → MetaM (Option (Expr × Option Expr)) := fun e => do
    let e1 ← if e.isAppOf ``memoryCost then
        pure ((← withTransparency .default <| unfoldDefinition? e).getD e)
      else pure e
    let (v, p) ← normField cfg m e1
    return some (v, p)
  -- First the structural ones: code byte, stack shape, stack reads, pushed immediates.
  let mut rest : Array Expr := #[]
  for x in xs do
    let ty ← instantiateMVars (← inferType x)
    unless ← isProp ty do continue
    let some (_, lhs, rhs) := ty.eq? | rest := rest.push x; continue
    if lhs.isAppOf ``GetElem?.getElem? then
      let args := lhs.getAppArgs
      let coll := (args.getD 5 default)
      if coll.isAppOf ``Frame.code then
        x.mvarId!.assign (← cfg.codeFact code pc b)
        continue
      if coll.isAppOf ``Frame.stack then
        let some k ← (evalNat (args.getD 6 default)).run | do trace[EvmLean.wp] "fast step: hyp check 1 failed: {ty}"; return false
        let some v := listNth? k stack | do trace[EvmLean.wp] "fast step: hyp check 2 failed: {ty}"; return false
        let_expr Option.some _ rv := rhs | do trace[EvmLean.wp] "fast step: hyp check 3 failed: {ty}"; return false
        unless ← isDefEq rv v do
          trace[EvmLean.wp] "fast step: get mismatch {ty}"
          return false
        x.mvarId!.assign (← mkExpectedTypeHint (← mkEqRefl (← mkAppM ``Option.some #[v])) ty)
        continue
    if lhs.isAppOf ``Frame.stack then
      unless ← isDefEq rhs stack do
        trace[EvmLean.wp] "fast step: stack {stack} does not match {rhs}"
        return false
      x.mvarId!.assign (← mkExpectedTypeHint (← mkEqRefl stack) ty)
      continue
    -- `Bytes.toWord (readBytes code (pc + 1) n) = ?v`: the pushed immediate
    if lhs.isAppOf ``Bytes.toWord then
      let n ← match_expr lhs with
        | Bytes.toWord rb => match_expr rb with
          | readBytes _ _ n => (evalNat n).run
          | _ => pure none
        | _ => pure none
      let some n := n | do trace[EvmLean.wp] "fast step: hyp check 4 failed: {ty}"; return false
      let some pf ← cfg.pushFact code pc n | do trace[EvmLean.wp] "fast step: hyp check 5 failed: {ty}"; return false
      let some (_, _, v) := (← inferType pf).eq? | do trace[EvmLean.wp] "fast step: hyp check 6 failed: {ty}"; return false
      unless ← isDefEq rhs v do
        trace[EvmLean.wp] "fast step: push mismatch {ty}"
        return false
      x.mvarId!.assign (← mkExpectedTypeHint pf ty)
      continue
    rest := rest.push x
  for x in rest do
    if ← x.mvarId!.isAssigned then continue
    let ty ← instantiateMVars (← inferType x)
    unless ← isProp ty do continue
    if ty.hasExprMVar then
      trace[EvmLean.wp] "fast step: unassigned in {ty}"
      return false
    -- stack bounds: `l.length < 1024` on a list literal
    if let some pf ← stackBound? ty then
      x.mvarId!.assign pf
      continue
    -- small closed facts (`JUMPI` conditions on numerals): evaluate `decide` here
    if !ty.hasFVar && !ty.hasMVar then
      if let some pf ← closedDecide? ty then
        x.mvarId!.assign pf
        continue
    match ← gasFact? norm ty gas with
    | some pf =>
      x.mvarId!.assign pf
      continue
    | none => trace[EvmLean.wp] "gas: gasFact none for {gas}"
    -- a closed cost against symbolic gas: `omega` on `c ≤ gas` (no `simp at *`)
    if let some pf ← gasOmega? ty gas then
      x.mvarId!.assign pf
      continue
    -- fall back to the general discharger
    trace[EvmLean.wp] "fast step: fallback discharger for {ty}"
    let g ← mkFreshExprSyntheticOpaqueMVar ty
    let saved ← getGoals
    setGoals [g.mvarId!]
    let st ← saveState
    let ok ← tryCatchRuntimeEx (do withoutRecover cfg.disch; return true)
      (fun e => do
        trace[EvmLean.wp] "fast step: discharger error {e.toMessageData}"
        st.restore
        return false)
    setGoals saved
    unless ok do
      trace[EvmLean.wp] "fast step: side condition failed: {ty}"
      return false
    x.mvarId!.assign g
  return true
where
  stackBound? (ty : Expr) : MetaM (Option Expr) := do
    let_expr LT.lt _ _ l k := ty | return none
    let some _ ← (evalNat k).run | return none
    if !(l.hasFVar || l.hasMVar) then
      try return some (← mkDecideProof ty) catch _ => return none
    let_expr List.length α L := l | return none
    let L := ((← projOf? L).getD L).consumeMData
    -- the literal prefix and the tail of the list
    let mut pre : Array Expr := #[]
    let mut cur := L
    for _ in [0:2048] do
      match cur.consumeMData.app3? ``List.cons with
      | some (_, h, t) => pre := pre.push h; cur := t
      | none => break
    let tl := cur.consumeMData
    if tl.isAppOf ``List.nil then
      try return some (← mkDecideProof ty) catch _ => return none
    unless tl.isFVar do return none
    -- a hypothesis `tl.length ≤ K`
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let hty ← instantiateMVars decl.type
      let_expr LE.le _ _ lhs K := hty | continue
      let_expr List.length _ t := lhs | continue
      unless t == tl do continue
      let some kv ← (evalNat K).run | continue
      let some kk ← (evalNat k).run | continue
      unless pre.size + kv + 1 ≤ kk do continue
      let preE ← mkListLit α pre.toList
      let hble := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
      let pf := mkAppN (mkConst ``length_lt_of_tail) #[α, preE, tl, K, k, decl.toExpr, hble]
      return some (← mkExpectedTypeHint pf ty)
    return none

/-- The new pc: a numeral (definitionally). -/
def normPc (m v : Expr) : MetaM (Expr × Expr × Option Expr) := do
  let v' ← reduceProjs m v
  if let some n ← (evalNat v').run then return (mkNatLit n, mkNatLit n, none)
  -- `x.toNat` for a literal word `x` (jumps)
  if let some n ← (evalNat (← whnfD v')).run then return (mkNatLit n, mkNatLit n, none)
  return (v', v', none)

/-- The new stack: the list structure evaluated (definitionally), the new elements normalized
one by one; elements of the old stack are already normal. -/
def normStack (cfg : Cfg) (m old v : Expr) : MetaM (Expr × Expr × Option Expr) := do
  let v' ← reduceProjs m v
  let some (xs, tl) ← evalList 2048 v' | do
    let (n, p) ← normField cfg m v
    return (v, n, p)
  let some (oldXs, _) ← evalList 2048 old | do
    let (n, p) ← normField cfg m v
    return (v, n, p)
  let α := mkConst ``EvmLean.Word
  let cons := mkApp (mkConst ``List.cons [0]) α
  -- from the tail outwards: (raw list, new list, proof)
  let mut raw := tl
  let mut new := tl
  let mut pf : Option Expr := none
  for x in xs.reverse do
    let (x', px) ← if oldXs.contains x then pure (x, none) else normField cfg m x
    let rawL := mkApp2 cons x raw
    let p ← congrApp cons #[x, raw] #[px, pf]
    raw := rawL
    new := mkApp2 cons x' new
    pf := p
  return (raw, new, pf)

/-- The new gas `old - k`: the cost `k` normalized alone, then `G - n - k` folded to `G - s`
(`foldGas`) or the chain kept. -/
def normGas (cfg : Cfg) (m old v : Expr) : MetaM (Expr × Expr × Option Expr) := do
  let v' ← reduceProjs m v
  let fallback : MetaM (Expr × Expr × Option Expr) := do
    let (n, p) ← normField cfg m v
    return (v, n, p)
  let_expr HSub.hSub _ _ _ _ g k := v' | fallback
  unless g == old do return ← fallback
  let (k', pk) ← normField cfg m k
  let sub (a b : Expr) := mkApp6 (mkConst ``HSub.hSub [0, 0, 0]) (mkConst ``Nat) (mkConst ``Nat)
    (mkConst ``Nat) (mkApp2 (mkConst ``instHSub [0]) (mkConst ``Nat) (mkConst ``instSubNat)) a b
  let subOld := mkApp5 (mkConst ``HSub.hSub [0, 0, 0]) (mkConst ``Nat) (mkConst ``Nat)
    (mkConst ``Nat) (mkApp2 (mkConst ``instHSub [0]) (mkConst ``Nat) (mkConst ``instSubNat)) old
  -- `old - k = old - k'`
  let p1 ← pk.mapM (mkCongrArg subOld ·)
  if !cfg.foldGas then return (v', sub old k', p1)
  let some kv ← (evalNat k').run | fallback
  let some (G, n) ← gasShape old | do
    -- a chain `G - a₁ - … - aₖ` of closed costs (the `sol_step` normal form): fold it
    if let some (G, subs) ← closedChain? old then
      let mut tot := kv
      for a in subs do
        let some v ← closedNat? a | return ← fallback
        tot := tot + v
      let l ← mkListLit (mkConst ``Nat) subs.toList
      let h ← mkEqRefl (mkNatLit tot)
      let p2 ← mkExpectedTypeHint (mkAppN (mkConst ``chain_sub) #[G, k', mkNatLit tot, l, h])
        (← mkEq (sub old k') (sub G (mkNatLit tot)))
      let pf ← match p1 with
        | some p => mkEqTrans p p2
        | none => pure p2
      return (v', sub G (mkNatLit tot), some pf)
    -- `G - A - k = G - (A + k)` (`Nat.sub_sub`, as `wp_step`'s simp set leaves it)
    let_expr HSub.hSub _ _ _ _ G A := old.consumeMData | fallback
    unless G.isFVar do return ← fallback
    let p2 := mkApp3 (mkConst ``Nat.sub_sub) G A k'
    let pf ← match p1 with
      | some p => mkEqTrans p p2
      | none => pure p2
    return (v', sub G (← mkAdd A k'), some pf)
  if n == 0 then return (v', sub G (mkNatLit kv), p1)
  let s := n + kv
  let h ← mkEqRefl (mkNatLit s)
  let p2 := mkAppN (mkConst ``sub_sub_lit) #[G, mkNatLit n, k', mkNatLit s, h]
  let pf ← match p1 with
    | some p => mkEqTrans p p2
    | none => pure p2
  return (v', sub G (mkNatLit s), some pf)

/-- One instruction of the machine literal `m`: the next machine `m'` (changed fields
normalized) and a proof of `step m = .running m'`. `none` if the instruction is not handled
here (halts, calls, creates, `GAS`) or a side condition fails. -/
def stepCore (cfg : Cfg) (m : Expr) (normAll : Bool := false) :
    TacticM (Option (Expr × Expr)) := do
  unless fastStep.enable.get (← getOptions) do return none
  let some (ms, fs) := literalFields? m | do trace[EvmLean.wp] "fast step: core check 1"; return none
  let code := (fs.getD 1 default)
  let some pc ← (evalNat (fs.getD 3 default)).run | do trace[EvmLean.wp] "fast step: core check 2"; return none
  let some bytes ← cfg.bytes code | do trace[EvmLean.wp] "fast step: core check 3"; return none
  let some b := bytes[pc]? | do trace[EvmLean.wp] "fast step: core check 4"; return none
  let bn := b.toNat
  if bn == 0x00 || bn == 0xf3 || bn == 0xfd || bn == 0xfe || bn == 0xff || bn == 0x5a ||
      (0xf0 ≤ bn && bn ≤ 0xfa) then return none
  let lemmas : List (Expr × Option Nat) ←
    if 0x5f ≤ bn ∧ bn ≤ 0x7f then pure [(mkConst ``step_push_val, some (bn - 0x5f))]
    else pure ((stepLemmasFor bn).1.map fun n => (mkConst n, none))
  let saved ← saveState
  for (lem, pushN) in lemmas do
    let r ← tryCatchRuntimeEx (do
      let (xs, _, concl) ← forallMetaTelescope (← inferType lem)
      let_expr Eq _ lhs rhs := concl | do trace[EvmLean.wp] "fast step: core check 5"; return none
      let_expr step mv := lhs | do trace[EvmLean.wp] "fast step: core check 6"; return none
      unless mv.isMVar do return none
      mv.mvarId!.assign m
      if let some n := pushN then
        -- `step_push_val (n : Nat) (hn : n < 33)`
        let some xn ← xs.findM? (fun x => return (← inferType x).isConstOf ``Nat) | do trace[EvmLean.wp] "fast step: core check 7"; return none
        xn.mvarId!.assign (mkNatLit n)
      unless ← dischHyps cfg m code pc b (fs.getD 4 default) (fs.getD 6 default) xs do return none
      let_expr StepResult.running rhs := rhs | do trace[EvmLean.wp] "fast step: core check 8"; return none
      let rhs ← instantiateMVars rhs
      if rhs.hasExprMVar then
        trace[EvmLean.wp] "fast step: rhs mvars {rhs}"
        return none
      let pfStep := mkAppN lem (← xs.mapM instantiateMVars)
      let some (mOut, fOut) ← splitRhs rhs ms fs | do trace[EvmLean.wp] "fast step: core check 9"; return none
      -- only the fields `SameFrame.of_update` may change
      if [0, 1, 4, 7].any (fun i => ((mOut.getD i default)).2) then
        trace[EvmLean.wp] "fast step: machine fields changed {mOut.map (·.2)}"
        return none
      if [0, 1, 2, 9, 10].any (fun i => ((fOut.getD i default)).2) then
        trace[EvmLean.wp] "fast step: frame fields changed {fOut.map (·.2)}"
        return none
      -- normalize the changed fields
      let mut fNew : Array Expr := #[]
      let mut fRaw : Array Expr := #[]
      let mut fPf : Array (Option Expr) := #[]
      let mut fi := 0
      for (v, changed) in fOut do
        let mutable := [3, 4, 5, 6, 7, 8].contains fi
        let (raw, v', p) ← if normAll && mutable then do
            let (v', p) ← normField cfg m v; pure (v, v', p)
          else if !changed then pure (v, v, none)
          else if fi == 3 then normPc m v
          else if fi == 4 then normStack cfg m (fs.getD 4 default) v
          else if fi == 6 then normGas cfg m (fs.getD 6 default) v
          else do let (v', p) ← normField cfg m v; pure (v, v', p)
        fRaw := fRaw.push raw; fNew := fNew.push v'; fPf := fPf.push p
        fi := fi + 1
      let frRaw := mkAppN (mkConst ``Frame.mk) fRaw
      let frNew := mkAppN (mkConst ``Frame.mk) fNew
      let frPf ← congrApp (mkConst ``Frame.mk) fRaw fPf
      let mut mNew : Array Expr := #[]
      let mut mRaw : Array Expr := #[]
      let mut mPf : Array (Option Expr) := #[]
      for i in [0:8] do
        let (v, changed) := (mOut.getD i default)
        if i == 6 then
          mRaw := mRaw.push frRaw; mNew := mNew.push frNew; mPf := mPf.push frPf
        else if changed || (normAll && [2, 3, 5].contains i) then
          let (v', p) ← normField cfg m v
          mRaw := mRaw.push v; mNew := mNew.push v'; mPf := mPf.push p
        else mRaw := mRaw.push v; mNew := mNew.push v; mPf := mPf.push none
      let m'raw := mkAppN (mkConst ``Machine.mk) mRaw
      let m' := mkAppN (mkConst ``Machine.mk) mNew
      let stepTy (x : Expr) := mkApp3 (mkConst ``Eq [1]) (mkConst ``StepResult)
        (mkApp (mkConst ``step) m) (mkApp (mkConst ``StepResult.running) x)
      let mut hstep ← mkExpectedTypeHint pfStep (stepTy m'raw)
      if fastStep.debugSorry.get (← getOptions) == 1 then hstep ← mkSorry (stepTy m'raw) false
      if let some p ← congrApp (mkConst ``Machine.mk) mRaw mPf then
        if fastStep.debugSorry.get (← getOptions) == 7 then
          hstep ← mkEqTrans hstep (← mkSorry (← mkEq (mkApp (mkConst ``StepResult.running) m'raw) (mkApp (mkConst ``StepResult.running) m')) false)
        else
        hstep ← mkEqTrans hstep (← mkCongrArg (mkConst ``StepResult.running) p)
      if fastStep.check.get (← getOptions) then
        try check pfStep catch e => throwError "fast step: pfStep ill-typed: {e.toMessageData}"
        try check hstep catch e => throwError "fast step: hstep ill-typed: {e.toMessageData}"
        let t ← inferType hstep
        unless ← isDefEq t (stepTy m') do throwError "fast step: hstep type {t}"
      trace[EvmLean.symStep] "fast pc {pc}, byte {b}"
      return some (m', hstep))
      (fun e => do
        trace[EvmLean.wp] "fast step: exception {e.toMessageData}"
        return none)
    if r.isSome then return r
    trace[EvmLean.wp] "fast step: {lem} failed at pc {pc}"
    saved.restore
  return none

/-- One fast step on the main goal `WP m Q H`. `false` (goal unchanged) if the instruction is
not handled here. -/
def fastWpStep (cfg : Cfg) (normAll : Bool := false) : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let_expr WP m Q H := t | return false
  if (literalFields? m).isNone then
    trace[EvmLean.wp] "fast step: not a machine literal: {m}"
  let some (m', hstep) ← stepCore cfg m normAll | return false
  let some (mNew, fNew) := literalFields? m' | return false
  let hsame := mkAppN (mkConst ``SameFrame.of_update)
    #[m, mNew.getD 2 default, mNew.getD 3 default, mNew.getD 5 default, fNew.getD 3 default,
      fNew.getD 4 default, fNew.getD 5 default, fNew.getD 6 default, fNew.getD 7 default,
      fNew.getD 8 default]
  let hsame ← mkExpectedTypeHint hsame (mkApp2 (mkConst ``SameFrame) m m')
  if fastStep.check.get (← getOptions) then
    try check hsame catch e => throwError "fast step: hsame ill-typed: {e.toMessageData}"
  let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``WP) m' Q H) (← g.getTag)
  g.assign (mkAppN (mkConst ``WP.of_step) #[m, m', Q, H, hstep, hsame, g'])
  replaceMainGoal [g'.mvarId!]
  return true

/-- The fuel `k + (n + 1)` (or a numeral `n + 1`) as `(k + n, true)`: one step consumes one unit. -/
def predFuel? (fuel : Expr) : MetaM (Option Expr) := do
  let fuel := fuel.consumeMData
  if let some n ← (evalNat fuel).run then
    if n = 0 then return none
    return some (mkNatLit (n - 1))
  let_expr HAdd.hAdd _ _ _ _ k c := fuel | return none
  let some c ← (evalNat c).run | return none
  if c = 0 then return none
  if c = 1 then return some k
  return some (← mkAdd k (mkNatLit (c - 1)))

/-- The `run fuel m` term of a goal (outside binders). -/
def goalRun? (t : Expr) : Option Expr :=
  match t.find? fun x => x.isAppOfArity ``EvmLean.Interpreter.run 2 with
  | some e => if e.hasLooseBVars then none else some e
  | none => none

/-- One fast step of `run fuel m`: `(run fuel' m', proof of run fuel m = run fuel' m')`. -/
def runStepEq (cfg : Cfg) (runE : Expr) (normAll : Bool := false) :
    TacticM (Option (Expr × Expr)) := do
  let fuel := runE.appFn!.appArg!
  let m := runE.appArg!
  let some fuel' ← predFuel? fuel | return none
  let some (m', hstep) ← stepCore cfg m normAll | return none
  -- `run (fuel' + 1) m = run fuel' m'`, with `fuel' + 1 ≡ fuel`
  let runE' := mkApp2 (mkConst ``EvmLean.Interpreter.run) fuel' m'
  let heq := mkAppN (mkConst ``run_succ_of_running) #[m, m', fuel', hstep]
  return some (runE', ← mkExpectedTypeHint heq (← mkEq runE runE'))

/-- Rewrite the occurrence of `runE` in the main goal to `runE'` by `h : runE = runE'` (one
motive for a whole chain of steps). -/
def rewriteRun (runE runE' h : Expr) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let motive ← withLocalDeclD `x (← inferType runE) fun x => do
    mkLambdaFVars #[x] (t.replace fun e => if e == runE then some x else none)
  let t' := motive.beta #[runE']
  let g' ← mkFreshExprSyntheticOpaqueMVar t' (← g.getTag)
  g.assign (← mkEqMPR (← mkCongrArg motive h) g')
  replaceMainGoal [g'.mvarId!]

/-- Fast steps of the `run` term of the main goal while they apply (at most `limit`), composed
into one equation and rewritten into the goal once. The number of steps taken. -/
def fastRunSteps (cfg : Cfg) (normFirst : Bool) (limit : Nat := 1000000) : TacticM Nat :=
  withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some run0 := goalRun? t | return 0
  let mut cur := run0
  let mut pf : Option Expr := none
  let mut n := 0
  for _ in [0:limit] do
    let some (next, h) ← runStepEq cfg cur (normFirst && n == 0) | break
    pf ← match pf with
      | none => pure (some h)
      | some p => pure (some (← mkEqTrans p h))
    cur := next
    n := n + 1
  if let some p := pf then rewriteRun run0 cur p
  return n

end EvmLogic.Tactic.FastStep
