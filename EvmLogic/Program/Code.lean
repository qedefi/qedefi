import Lean
import EvmLogic.Step.Push
import EvmLogic.Program.JumpDest

/-!
# Facts about concrete code, without unfolding it in the elaborator

Code bytes and `PUSHn` immediates of a real contract cannot be obtained by `rfl` in the
elaborator (its `whnf` on a KB-sized list literal exceeds the recursion limit). Here the bytes
are read once at the meta level (`codeBytes?`) and each fact (`codeFact`, `pushFact`) is
produced as `Eq.refl` with the fact as its type, so only the kernel evaluates it.
-/

namespace EvmLogic.Program
open EvmLean Lean Meta EvmLean.Interpreter

/-- `PUSHn` (`0 ≤ n ≤ 32`) with the pushed value given by a hypothesis (a `pushFact`). -/
theorem step_push_val {m : Machine} {v : Word} (n : Nat) (hn : n < 33)
    (hcode : m.frame.code[m.frame.pc]? = some (0x5f + n).toUInt8)
    (hval : Bytes.toWord (readBytes m.frame.code (m.frame.pc + 1) n) = v)
    (hlen : m.frame.stack.length < 1024)
    (hgas : (if n = 0 then Gas.base else Gas.veryLow) ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := v :: m.frame.stack,
      gasLeft := m.frame.gasLeft - (if n = 0 then Gas.base else Gas.veryLow),
      pc := m.frame.pc + (1 + n) } } := by
  have h := step_push ⟨n, hn⟩ hcode hlen hgas
  simp only at h
  rw [h, hval]

def uint8Lit? (e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  if let some n := e.rawNatLit? then return some n
  match_expr e with
  | OfNat.ofNat _ n _ => return n.consumeMData.rawNatLit?
  | _ =>
    let v ← whnfD (mkApp (mkConst ``UInt8.toNat) e)
    (evalNat v).run

/-- The bytes of a literal code expression (unfolding constants and `have`/`let` chunks). -/
def codeBytes? (code : Expr) : MetaM (Option (Array UInt8)) := do
  let mut e ← instantiateMVars code
  for _ in [0:32] do
    e := e.consumeMData
    if e.isAppOfArity ``ByteArray.mk 1 then break
    match ← unfoldDefinition? e with
    | some e' => e := e'
    | none => return none
  let some arr := e.app1? ``ByteArray.mk | return none
  let mut arr := arr.consumeMData
  unless arr.isAppOfArity ``List.toArray 2 || arr.isAppOfArity ``Array.mk 2 do
    arr ← whnfR arr
    unless arr.isAppOfArity ``List.toArray 2 || arr.isAppOfArity ``Array.mk 2 do return none
  let mut cur := arr.getAppArgs.back?.getD (mkConst ``List.nil [0])
  let mut out : Array UInt8 := #[]
  for _ in [0:(1 <<< 24)] do
    cur := cur.consumeMData
    match cur with
    | .letE _ _ v b _ => cur := b.instantiate1 v
    | _ =>
      if cur.isAppOfArity ``List.nil 1 then return some out
      else if let some (_, h, t) := cur.app3? ``List.cons then
        let some b ← uint8Lit? h | return none
        out := out.push b.toUInt8
        cur := t
      else return none
  return none

/-- `fact` as a proof of `type`, to be checked by the kernel by evaluation. -/
def kernelFact (type lhs : Expr) : MetaM Expr := do
  return mkExpectedPropHint (← mkEqRefl lhs) type

/-- The fact `code[pc]? = some b`. -/
def codeFact (code : Expr) (pc : Nat) (b : UInt8) : MetaM Expr := do
  let lhs ← mkAppOptM ``GetElem?.getElem? #[mkConst ``ByteArray, mkConst ``Nat,
    mkConst ``UInt8, none, none, code, mkNatLit pc]
  let rhs ← mkAppM ``Option.some #[← mkNumeral (mkConst ``UInt8) b.toNat]
  kernelFact (← mkEq lhs rhs) rhs

def immValue (bytes : Array UInt8) (off n : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:n] do
    v := v * 256 + (bytes[off + i]?.getD 0).toNat
  return v

/-- The fact `Bytes.toWord (readBytes code (pc + 1) n) = v` for a `PUSHn` at `pc`. -/
def pushFact (code : Expr) (bytes : Array UInt8) (pc n : Nat) : MetaM Expr := do
  let lhs ← mkAppM ``Bytes.toWord
    #[mkApp3 (mkConst ``readBytes) code (mkNatLit (pc + 1)) (mkNatLit n)]
  let rhs := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 256) (mkNatLit (immValue bytes (pc + 1) n))
  kernelFact (← mkEq lhs rhs) rhs

/-- Evaluate a closed word-valued term that is not yet a literal (e.g. solc's `NOT`/`AND`
masks) to `BitVec.ofNat 256 n`; the kernel re-checks it. -/
dsimproc_decl reduceClosedWord (_) := fun e => do
  unless e.isApp do return .continue
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return .continue
  if e.isAppOfArity ``BitVec.ofNat 2 || e.isAppOfArity ``OfNat.ofNat 3 then return .continue
  let ty ← instantiateMVars (← inferType e)
  let ty ← whnfR ty
  let some width := ty.app1? ``BitVec | return .continue
  let some w ← (evalNat width).run | return .continue
  unless w = 256 do return .continue
  let r ← tryCatchRuntimeEx
    (do
      let v ← withTransparency .default <|
        reduce (mkApp2 (mkConst ``BitVec.toNat) (mkNatLit 256) e)
      (evalNat v).run)
    (fun _ => pure none)
  let some n := r | return .continue
  return .done (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 256) (mkNatLit n))

def jumpDestsOf (bytes : Array UInt8) : Std.HashSet Nat := Id.run do
  let mut s : Std.HashSet Nat := {}
  let mut pc := 0
  for _ in [0:bytes.size + 1] do
    if h : pc < bytes.size then
      let b := bytes[pc]
      if b = 0x5b then
        s := s.insert pc
        pc := pc + 1
      else if 0x60 ≤ b ∧ b ≤ 0x7f then pc := pc + 1 + (b.toNat - 0x5f)
      else pc := pc + 1
  return s

/-- `jd = validJumpDests code`, wrapped so that `subst` leaves it alone (substituting
`validJumpDests code` for a large `code` exceeds the recursion limit). -/
def JumpTable (jd : Array Bool) (code : ByteArray) : Prop := jd = validJumpDests code

theorem isValidJumpDest_of_jumpTable {jd : Array Bool} {code : ByteArray} {d : Nat}
    (hjd : JumpTable jd code) (h : jdCheck code d = true) : isValidJumpDest jd d = true := by
  rw [hjd]; exact isValidJumpDest_of_jdCheck h

/-- Close `isValidJumpDest jd d = true` for literal code and numeral `d`, by a
kernel-evaluated `jdCheck`. -/
elab "jumpdest_disch" : tactic => Elab.Tactic.withMainContext do
  let g ← Elab.Tactic.getMainGoal
  let t ← instantiateMVars (← g.getType)
  let_expr Eq _ lhs _ := t | throwError "jumpdest_disch: not an equation"
  let_expr isValidJumpDest jd d := lhs | throwError "jumpdest_disch: not a jump destination"
  let jd ← whnfR jd
  -- The table is `validJumpDests code`, or a variable with a `JumpTable` hypothesis.
  let mut src : Option (Expr × Option Expr) := none
  if let some code := jd.app1? ``validJumpDests then src := some (code, none)
  else
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      if let some (jd', code) := ty.app2? ``JumpTable then
        if jd' == jd then src := some (code, some decl.toExpr)
  let some (code, hjd) := src | throwError "jumpdest_disch: unknown jump table"
  let some n ← (evalNat (← whnfD d)).run | throwError "jumpdest_disch: symbolic destination"
  let some bytes ← codeBytes? code | throwError "jumpdest_disch: code is not a literal"
  unless (jumpDestsOf bytes).contains n do throwError "jumpdest_disch: {n} is not a JUMPDEST"
  let chk ← mkEq (mkApp2 (mkConst ``jdCheck) code d) (mkConst ``Bool.true)
  let pf ← kernelFact chk (mkConst ``Bool.true)
  match hjd with
  | none => g.assign (mkApp3 (mkConst ``isValidJumpDest_of_jdCheck) code d pf)
  | some h => g.assign (mkApp5 (mkConst ``isValidJumpDest_of_jumpTable) jd code d h pf)
  Elab.Tactic.replaceMainGoal []

end EvmLogic.Program
