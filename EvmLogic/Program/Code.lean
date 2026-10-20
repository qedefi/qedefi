import Lean
import EvmLogic.Step.Push
import EvmLogic.Program.JumpDest
import EvmLogic.Program.CodeTable

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

/-! ## Code tables -/

/-- The trie as an expression, with byte literals as `mkNumeral` builds them. -/
def byteTrieExpr : ByteTrie → MetaM Expr
  | .nil => return mkConst ``ByteTrie.nil
  | .leaf b => return mkApp (mkConst ``ByteTrie.leaf) (← mkNumeral (mkConst ``UInt8) b.toNat)
  | .node lo hi => do
    return mkApp2 (mkConst ``ByteTrie.node) (← byteTrieExpr lo) (← byteTrieExpr hi)

/-- The least `d` with `n ≤ 2 ^ d`. -/
def trieDepth (n : Nat) : Nat := Id.run do
  let mut d := 0
  for _ in [0:64] do
    if 2 ^ d < n then d := d + 1
  return d

/-- The table of a code constant `c`: the constants `c.codeTable` and `c.codeTable_ok`, and its
depth, if `code_table c` was run. -/
def codeTable? (code : Expr) : MetaM (Option (Expr × Expr × Nat)) := do
  let some c := code.consumeMData.constName? | return none
  let env ← getEnv
  let tn := c ++ `codeTable
  let some (.defnInfo dv) := env.find? tn | return none
  unless env.contains (c ++ `codeTable_ok) do return none
  let some dE := dv.value.getAppArgs[0]? | return none
  let some d := dE.nat? <|> dE.rawNatLit? | return none
  return some (mkConst tn, mkConst (c ++ `codeTable_ok), d)

/-- `code_table c`: build the `CodeTable` of the literal code constant `c` (bytes and jump
destinations as tries) as `c.codeTable`, and check it once in the kernel
(`c.codeTable_ok : CodeTable.Ok c c.codeTable`). Afterwards code facts about `c` cost a
logarithmic number of kernel steps. -/
elab "code_table " id:ident : command => Elab.Command.liftTermElabM do
  let c ← Elab.realizeGlobalConstNoOverloadWithInfo id
  let code := mkConst c
  let some bytes ← codeBytes? code | throwError "code_table: {c} is not a literal code"
  let d := trieDepth bytes.size
  let l := bytes.toList
  let bt := ByteTrie.ofList d l
  let jt := ByteTrie.ofKeys d (Solidity.jumpDestList (bytes.size + 1) l 0)
  let tableE := mkApp3 (mkConst ``CodeTable.mk) (mkNatLit d) (← byteTrieExpr bt)
    (← byteTrieExpr jt)
  let tn := c ++ `codeTable
  let tableTy := mkConst ``CodeTable
  let dv : DefinitionVal :=
    { name := tn, levelParams := [], type := tableTy, value := tableE,
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  addDecl (Declaration.defnDecl dv)
  let t := mkConst tn
  let okTy := mkApp2 (mkConst ``CodeTable.Ok) code t
  let size ← mkEqRefl (mkConst ``Bool.true)
  let bytesPf ← mkEqRefl (mkApp (mkConst ``CodeTable.bytes) t)
  let jdPf ← mkEqRefl (mkApp (mkConst ``CodeTable.jumpDests) t)
  let pf := mkApp5 (mkConst ``CodeTable.Ok.mk) code t size bytesPf jdPf
  let tv : TheoremVal := { name := c ++ `codeTable_ok, levelParams := [], type := okTy, value := pf }
  addDecl (Declaration.thmDecl tv)

/-- `t.bytes.get t.depth pc = some b`, by kernel evaluation. -/
def tableByteFact (t : Expr) (pc : Nat) (rhs : Expr) : MetaM Expr := do
  let lhs := mkApp3 (mkConst ``ByteTrie.get) (mkApp (mkConst ``CodeTable.depth) t)
    (mkApp (mkConst ``CodeTable.bytes) t) (mkNatLit pc)
  kernelFact (← mkEq lhs rhs) rhs

/-- The fact `code[pc]? = some b`. -/
def codeFact (code : Expr) (pc : Nat) (b : UInt8) : MetaM Expr := do
  let lhs ← mkAppOptM ``GetElem?.getElem? #[mkConst ``ByteArray, mkConst ``Nat,
    mkConst ``UInt8, none, none, code, mkNatLit pc]
  let rhs ← mkAppM ``Option.some #[← mkNumeral (mkConst ``UInt8) b.toNat]
  match ← codeTable? code with
  | some (t, ok, _) =>
    let hb ← tableByteFact t pc rhs
    let pf := mkAppN (mkConst ``CodeTable.getElem?_eq) #[code, t, ok, mkNatLit pc,
      ← mkNumeral (mkConst ``UInt8) b.toNat, hb]
    return mkExpectedPropHint pf (← mkEq lhs rhs)
  | none => kernelFact (← mkEq lhs rhs) rhs

/-- `Bytes.toWord (readBytes code off n) = BitVec.ofNat 256 v` from the table `t` (`ok` its
`CodeTable.Ok` proof), by kernel evaluation of `n` lookups. -/
def wordFact (code t ok : Expr) (off n v : Nat) : MetaM Expr := do
  let lhs := mkAppN (mkConst ``ByteTrie.readNat) #[mkApp (mkConst ``CodeTable.depth) t,
    mkApp (mkConst ``CodeTable.bytes) t, mkNatLit off, mkNatLit n, mkNatLit 0]
  let hv ← kernelFact (← mkEq lhs (mkNatLit v)) (mkNatLit v)
  return mkAppN (mkConst ``CodeTable.toWord_readBytes)
    #[code, t, ok, mkNatLit off, mkNatLit n, mkNatLit v, hv]

def immValue (bytes : Array UInt8) (off n : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:n] do
    v := v * 256 + (bytes[off + i]?.getD 0).toNat
  return v

/-- The fact `Bytes.toWord (readBytes code (pc + 1) n) = v` for a `PUSHn` at `pc`. -/
def pushFact (code : Expr) (bytes : Array UInt8) (pc n : Nat) : MetaM Expr := do
  let lhs ← mkAppM ``Bytes.toWord
    #[mkApp3 (mkConst ``readBytes) code (mkNatLit (pc + 1)) (mkNatLit n)]
  let v := immValue bytes (pc + 1) n
  let rhs := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 256) (mkNatLit v)
  match ← codeTable? code with
  | some (t, ok, _) => wordFact code t ok (pc + 1) n v
  | none => kernelFact (← mkEq lhs rhs) rhs

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

theorem isValidJumpDest_of_jumpTable_mem {jd : Array Bool} {code : ByteArray} {d : Nat}
    (hjd : JumpTable jd code) (h : d ∈ Solidity.jumpDestList (code.size + 1) code.data.toList 0) :
    isValidJumpDest jd d = true := by
  rw [hjd]; exact Solidity.isValidJumpDest_of_mem h

/-- A proof of `d ∈ jumpDestList (code.size + 1) code.data.toList 0` by a table lookup, if
`code` has a table (`code_table`). -/
def jumpDestMem? (code d : Expr) : MetaM (Option Expr) := do
  let some (t, ok, _) ← codeTable? code | return none
  let one ← mkNumeral (mkConst ``UInt8) 1
  let rhs ← mkAppM ``Option.some #[one]
  let lhs := mkApp3 (mkConst ``ByteTrie.get) (mkApp (mkConst ``CodeTable.depth) t)
    (mkApp (mkConst ``CodeTable.jumpDests) t) d
  let hd ← kernelFact (← mkEq lhs rhs) rhs
  return some (mkAppN (mkConst ``CodeTable.mem_jumpDestList) #[code, t, ok, d, hd])

/-- Close `isValidJumpDest jd d = true` for literal code and numeral `d`, by a table lookup
(`code_table`) or a kernel-evaluated `jdCheck`. -/
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
  if let some hmem ← jumpDestMem? code (mkNatLit n) then
    let d' := mkNatLit n
    let pf := match hjd with
      | none => mkApp3 (mkConst ``Solidity.isValidJumpDest_of_mem) code d' hmem
      | some h => mkAppN (mkConst ``isValidJumpDest_of_jumpTable_mem) #[jd, code, d', h, hmem]
    g.assign (← mkExpectedTypeHint pf t)
    Elab.Tactic.replaceMainGoal []
    return
  let chk ← mkEq (mkApp2 (mkConst ``jdCheck) code d) (mkConst ``Bool.true)
  let pf ← kernelFact chk (mkConst ``Bool.true)
  match hjd with
  | none => g.assign (mkApp3 (mkConst ``isValidJumpDest_of_jdCheck) code d pf)
  | some h => g.assign (mkApp5 (mkConst ``isValidJumpDest_of_jumpTable) jd code d h pf)
  Elab.Tactic.replaceMainGoal []

end EvmLogic.Program

section

namespace EvmLogic.Program
open EvmLean Lean Meta EvmLean.Interpreter

/-- Close a closed code fact by a table lookup (`code_table`): `code[j]? = some b`,
`d ∈ jumpDestList (code.size + 1) code.data.toList 0`, or
`Bytes.toWord (readBytes code off n) = BitVec.ofNat 256 v`. `false` if the goal has another
shape, the code has no table, or the fact is false. -/
def closeByTable (g : MVarId) : MetaM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let assign (pf : Expr) : MetaM Bool := do
    g.assign (← mkExpectedTypeHint pf t)
    return true
  if let some (_, lhs, rhs) := t.eq? then
    match_expr lhs with
    | GetElem?.getElem? coll _ _ _ _ code jE =>
      unless coll.isConstOf ``ByteArray do return false
      let some j ← (evalNat jE).run | return false
      let some bytes ← codeBytes? code | return false
      let some b := bytes[j]? | return false
      let_expr Option.some _ v := rhs | return false
      let some v ← uint8Lit? v | return false
      unless v = b.toNat do return false
      let some _ ← codeTable? code | return false
      assign (← codeFact code j b)
    | Bytes.toWord rb =>
      let_expr readBytes code offE nE := rb | return false
      let some off ← (evalNat offE).run | return false
      let some n ← (evalNat nE).run | return false
      let some bytes ← codeBytes? code | return false
      let some (tab, ok, _) ← codeTable? code | return false
      let v := immValue bytes off n
      let_expr BitVec.ofNat _ vE := rhs | return false
      let some v' ← (evalNat vE).run | return false
      unless v' = v % 2 ^ 256 ∧ v < 2 ^ 256 do return false
      assign (← wordFact code tab ok off n v)
    | _ => return false
  else
    let_expr Membership.mem _ _ _ l d := t | return false
    let_expr Solidity.jumpDestList _ lst p := l | return false
    let some 0 ← (evalNat p).run | return false
    let_expr Array.toList _ arr := lst | return false
    let_expr ByteArray.data code := arr | return false
    let some dn ← (evalNat d).run | return false
    let some bytes ← codeBytes? code | return false
    unless (jumpDestsOf bytes).contains dn do return false
    let some hmem ← jumpDestMem? code d | return false
    assign hmem

/-- `decide +kernel` for code facts, by a table lookup when the code has one (`code_table`). -/
elab "table_decide" : tactic => Elab.Tactic.withMainContext do
  let g ← Elab.Tactic.getMainGoal
  if ← closeByTable g then Elab.Tactic.replaceMainGoal []
  else Elab.Tactic.evalTactic (← `(tactic| decide +kernel))

end EvmLogic.Program

end
