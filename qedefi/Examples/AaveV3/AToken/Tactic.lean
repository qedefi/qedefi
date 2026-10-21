import EvmLogic.Tactic.Mcopy
import EvmLogic.Program.Call

/-!
# Proof tools missing from `EvmLogic` (generic; candidates to move there)

* `wp_abstract`: replace a field of a `WP` goal's machine by a variable, cheaply;
* `access_bounds`: bound every `Gas.accessCost` in the goal;
* `step_extcodesize`: the step lemma of `EXTCODESIZE` (solc checks the callee's code size
  before a `CALL` that returns nothing).

## `wp_abstract`

`wp_abstract memory M h` (also `gas`, `sub`, `world`) turns the goal `WP m Q H`, whose machine is a
structure literal, into `WP m' Q H` with the field replaced by a fresh variable `M` and
`h : <old value> = M` in context. Unlike `wp_generalize_mem`/`wp_generalize_gas` (which call
`generalize`, i.e. `kabstract` over the whole goal), it rebuilds the machine at the known
argument position and closes the original goal by `rfl`, so its cost does not depend on the
size of the goal: on the AToken's `mint` path, after three `SSTORE`s and four mapping reads,
`generalize` did not finish in minutes.
-/

namespace Examples.AaveV3.AToken
open EvmLean EvmLean.Interpreter EvmLogic.Program Lean Elab Tactic Meta

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
  let (val, mk) ← match fld.getId with
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
  g.assign (mkApp2 ng val (← mkEqRefl val))
  let (_, ng') ← ng.mvarId!.introN 2 [x.getId, h.getId]
  replaceMainGoal [ng']

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

end Examples.AaveV3.AToken

/-! ## `EXTCODESIZE` (no step lemma in `EvmLogic.Step`) -/

namespace Examples.AaveV3.AToken
open EvmLean EvmLean.Interpreter EvmLogic.Program

variable {m : Machine} {x : Word} {rest : List Word}

/-- **`EXTCODESIZE`**: pushes the code size of the address, charging the EIP-2929 access cost
and warming the address. -/
theorem step_extcodesize (hcode : m.frame.code[m.frame.pc]? = some 0x3b)
    (hstk : m.frame.stack = x :: rest) (hlen : rest.length < 1024)
    (hgas : Gas.accessCost (m.frame.sub.accessedAddresses.contains (Word.toAddress x)) ≤
      m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := ofNat (m.world.code (Word.toAddress x)).size :: rest,
      gasLeft := m.frame.gasLeft -
        Gas.accessCost (m.frame.sub.accessedAddresses.contains (Word.toAddress x)),
      sub := m.frame.sub.warmAddr (Word.toAddress x),
      pc := m.frame.pc + 1 } } := by
  have hg := Nat.not_lt.mpr hgas
  have hl : ¬ Gas.stackLimit ≤ rest.length := Nat.not_le.mpr hlen
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x3b = .extcodesize by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popAddress, pop, getFrame, modifyFrame, StateT.run_bind, hstk, StateT.run_get,
    StateT.run_pure, StateT.run_modify, pure_bind]
  rw [run_accessAddress]
  simp only [pure_bind, charge, push, advance, getFrame, modifyFrame, StateT.run_bind,
    StateT.run_get, StateT.run_pure, StateT.run_modify, hg, hl, ite_false]
  rfl

/-- **`RETURNDATACOPY`** of a non-empty window inside the return data. -/
theorem step_returndatacopy (hcode : m.frame.code[m.frame.pc]? = some 0x3e)
    {y z : Word} (hstk : m.frame.stack = x :: y :: z :: rest) (hz : z.toNat ≠ 0)
    (hrd : y.toNat + z.toNat ≤ m.frame.returnData.size)
    (hgas : 3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat ≤ m.frame.gasLeft) :
    step m = .running { m with frame := { m.frame with
      stack := rest,
      memory := (m.frame.memory.expand x.toNat z.toNat).write x.toNat
        (m.frame.returnData.extract y.toNat (y.toNat + z.toNat)),
      gasLeft := m.frame.gasLeft - (3 + 3 * ((z.toNat + 31) / 32) + memoryCost m x z.toNat),
      pc := m.frame.pc + 1 } } := by
  have hc : Gas.veryLow + Gas.copyCost z.toNat = 3 + 3 * ((z.toNat + 31) / 32) := rfl
  have hg := Nat.not_lt.mpr hgas
  rw [← hc] at hg ⊢
  simp only [memoryCost] at hg
  have hr : ¬ y.toNat + z.toNat > m.frame.returnData.size := Nat.not_lt.mpr hrd
  have hs : ¬ (m.frame.returnData.extract y.toNat (y.toNat + z.toNat)).size = 0 := by
    rw [ByteArray.size_extract]; omega
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x3e = .returndatacopy by
    cases m.ctx.fork <;> rfl]
  simp only [exec, popNat, pop, charge, advance, getFrame, modifyFrame,
    StateT.run_bind, hstk, hg, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
    ite_false, memoryExpansion, expandMemory, List.foldl, writeMemory, hs, hr]
  rfl

end Examples.AaveV3.AToken
