import EvmLogic.Program.Call
import EvmLogic.Step.Memory
import EvmLogic.Tactic.Abstract

/-!
# `CREATE` in the frame-local logic

`step_create_ctor`: a `CREATE` whose soft checks pass (balance, nonce, depth) at a deployable address
pushes the child creation frame (`launchCreate`), with the init code read from memory and
all-but-1/64 of the gas left. `WP.create_ctor` is the callee-summary rule: a frame summary of the
child gives the caller's continuation after `resumeAfter` (the child's code deposited, the new
address pushed, on success).
-/

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter

/-- The static charge of `CREATE` of `size` bytes at `off`: base, init-code words, memory. -/
def ctorCreateCharge (m : Machine) (off size : Word) : Nat :=
  Gas.createCost size.toNat + memoryCost m off size.toNat

/-- The gas handed to the creation frame: all but 1/64 of what is left after the charge. -/
def ctorCreateGas (m : Machine) (off size : Word) : Nat :=
  Gas.maxMessageCallGas (m.frame.gasLeft - ctorCreateCharge m off size)

/-- The address `CREATE` deploys to (sender and its nonce). -/
def ctorCreateTarget (m : Machine) : Address :=
  createAddress m.ctx.crypto.keccak256 m.frame.msg.currentTarget
    (m.world.account m.frame.msg.currentTarget).nonce

/-- The child message of a `CREATE`. -/
def ctorCreateMsg (m : Machine) (v off size : Word) : Message where
  caller := m.frame.msg.currentTarget
  target := none
  currentTarget := ctorCreateTarget m
  gas := ctorCreateGas m off size
  value := v
  data := .empty
  codeAddress := none
  code := readBytes (m.frame.memory.expand off.toNat size.toNat).bytes off.toNat size.toNat
  depth := m.frame.msg.depth + 1
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := (m.frame.sub.warmAddr (ctorCreateTarget m)).accessedAddresses
  accessedStorageKeys := m.frame.sub.accessedStorageKeys

/-- The caller suspended by a `CREATE`: the sender's nonce incremented, the operands popped,
memory expanded, the charge and the child's gas taken, the new address warm. -/
def ctorCreateCaller (m : Machine) (off size : Word) (rest : List Word) : Machine :=
  { m with
    world := incrementNonce m.world m.frame.msg.currentTarget
    frame := { m.frame with
      stack := rest
      memory := m.frame.memory.expand off.toNat size.toNat
      gasLeft := m.frame.gasLeft - ctorCreateCharge m off size - ctorCreateGas m off size
      returnData := .empty
      sub := m.frame.sub.warmAddr (ctorCreateTarget m) } }

variable {m : Machine} {v off size : Word} {rest : List Word}

/-- **`CREATE` pushes the child creation frame**, when the soft checks pass and the new address
is deployable. -/
theorem step_create_ctor (hcode : m.frame.code[m.frame.pc]? = some 0xf0)
    (hstk : m.frame.stack = v :: off :: size :: rest)
    (hgas : ctorCreateCharge m off size ≤ m.frame.gasLeft)
    (hsize : size.toNat ≤ Gas.maxInitCodeSize m.ctx.fork)
    (hstatic : m.frame.msg.isStatic = false)
    (hbal : v.toNat ≤ (m.world.account m.frame.msg.currentTarget).balance.toNat)
    (hnonce : (m.world.account m.frame.msg.currentTarget).nonce ≠ Gas.maxNonce)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hdep : accountDeployable m.world (ctorCreateTarget m) = true) :
    step m = .running (launchCreate (ctorCreateCaller m off size rest) (ctorCreateMsg m v off size)) := by
  have hg : ¬ m.frame.gasLeft < ctorCreateCharge m off size := Nat.not_lt.mpr hgas
  have hs : ¬ size.toNat > Gas.maxInitCodeSize m.ctx.fork := Nat.not_lt.mpr hsize
  have hd : ¬ m.frame.msg.depth + 1 > Gas.stackDepthLimit := Nat.not_lt.mpr hdepth
  have hb : ¬ (m.world.account m.frame.msg.currentTarget).balance.toNat < v.toNat :=
    Nat.not_lt.mpr hbal
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0xf0 = .create by
    cases m.ctx.fork <;> rfl]
  simp only [ctorCreateCharge, memoryCost] at hg
  simp only [exec, execCreate, popNat, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
    StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, memoryExpansion, charge,
    Bool.false_eq_true, ↓reduceIte, hg, expandMemory, List.foldl, hs, readMemory,
    requireNonStatic, hstatic, setReturnData, hb, hnonce, hd, decide_false, Bool.or_false]
  rw [run_accessAddress]
  simp only [ctorCreateTarget] at hdep
  simp only [pure_bind, hdep, Bool.not_true, Bool.false_eq_true, ↓reduceIte, modifyWorld,
    StateT.run_bind, StateT.run_modify, StateT.run_get, StateT.run_pure, launchCreate]
  rfl

/-- **The callee-summary rule for `CREATE`**: if the child creation frame halts with `Hc`, the
caller continues from `resumeAfter` of every end `Hc` allows. -/
theorem WP.create_ctor {Q : Machine → Prop} {H Hc : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xf0)
    (hstk : m.frame.stack = v :: off :: size :: rest)
    (hgas : ctorCreateCharge m off size ≤ m.frame.gasLeft)
    (hsize : size.toNat ≤ Gas.maxInitCodeSize m.ctx.fork)
    (hstatic : m.frame.msg.isStatic = false)
    (hbal : v.toNat ≤ (m.world.account m.frame.msg.currentTarget).balance.toNat)
    (hnonce : (m.world.account m.frame.msg.currentTarget).nonce ≠ Gas.maxNonce)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hdep : accountDeployable m.world (ctorCreateTarget m) = true)
    (hcallee : Halts (launchCreate (ctorCreateCaller m off size rest) (ctorCreateMsg m v off size)) Hc)
    (k : ∀ mf o, Hc mf o →
      SameFrame (launchCreate (ctorCreateCaller m off size rest) (ctorCreateMsg m v off size)) mf →
      WP (resumeAfter (ctorCreateCaller m off size rest).frame m.parents mf o) Q H) :
    WP m Q H :=
  WP.call (step_create_ctor hcode hstk hgas hsize hstatic hbal hnonce hdepth hdep) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcallee (fun mf o hs hc => k mf o hc hs)

/-- **Return after a successful creation**: the code deposited at the new address (its deposit
paid from the child's gas), the address pushed, empty return data, the substate merged. -/
theorem resumeAfter_create_success_ctor {p : Frame} {ps : List Frame} {mf : Machine}
    {out : ByteArray} {g : Nat} (hk : mf.frame.kind = .create)
    (hd : depositCode mf.ctx.fork mf.frame.gasLeft out = .ok g) :
    resumeAfter p ps mf (.success out) =
      { mf with
        parents := ps
        world := setCode mf.world mf.frame.msg.currentTarget out
        frame := { p with
          gasLeft := p.gasLeft + g
          sub := mergeSub p.sub mf.frame.sub (setCode mf.world mf.frame.msg.currentTarget out)
            mf.frame.msg.currentTarget
          returnData := .empty
          stack := Word.ofAddress mf.frame.msg.currentTarget :: p.stack
          pc := p.pc + 1 } } := by
  simp only [resumeAfter, frameResult, hk, hd, resume, ChildResult.success, Option.isNone_none,
    Bool.not_false, Bool.and_self, ite_true]
  rfl

end EvmLogic.Program

/-- Replace every access cost `Gas.accessCost b` of the goal by a variable bounded by 2600
(the warm sets after calls are large terms that make gas goals slow or opaque to `omega`). -/
elab "gen_access" : tactic => Lean.Elab.Tactic.withMainContext do
  let t ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
  let found ← IO.mkRef (#[] : Array Lean.Expr)
  Lean.Meta.forEachExpr t fun e => do
    if e.isAppOfArity ``EvmLean.Gas.accessCost 1 then found.modify (·.push e)
  for e in ← found.get do
    let g ← Lean.Elab.Tactic.getMainGoal
    let pf ← Lean.Meta.mkAppM ``EvmLogic.Program.accessCost_le #[e.appArg!]
    let (_, g) ← (← g.assert `hacc (← Lean.Meta.inferType pf) pf).intro1P
    -- generalize the term in the goal and in the new bound
    let (fvs, g) ← g.revert #[(← g.getDecl).lctx.getFVarIds.back!]
    let r ← g.generalize #[{ expr := e, xName? := `acc }]
    let (_, g) ← r.2.introNP fvs.size
    Lean.Elab.Tactic.replaceMainGoal [g]
