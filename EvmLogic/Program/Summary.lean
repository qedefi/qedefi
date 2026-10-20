import EvmLogic.Step.Call
import EvmLogic.Step.Flow
import EvmLogic.Program.Logic

/-!
# Frames, messages and function summaries

* `Fresh code m`: the executing frame of `m` has just started running `code` (it is
  `Frame.init msg kind snapshot` with `msg.code = code`). This is the shape of the frame both
  at the top level (`initMachine`) and after a `CALL*` pushed a child (`launchCall`), so a
  theorem `Fresh code m → … → Halts m H` about a contract serves as its **summary** in both
  roles: as a top-level transaction (`processMessageCall_of_halts`) and as a callee
  (`EvmLeanProofs.Program.Call`).
* `FunctionSummary code`: an external function of a compiled contract, split as solc compiles
  it: the dispatcher (from the frame start to the function's entry pc, `dispatch`) and the
  body (from the entry pc to the end of the frame, `body`). `FunctionSummary.halts` glues them
  into a frame summary, `FunctionSummary.processMessageCall` into a statement about a top-level
  call.
* `frameResult_success_call` etc. compute what a finished frame hands over.
-/

namespace EvmLean.Program

open Interpreter

/-! ## Fresh frames -/

/-- The executing frame of `m` has just started running `code`. -/
def Fresh (code : ByteArray) (m : Machine) : Prop :=
  ∃ msg kind snapshot, m.frame = Frame.init msg kind snapshot ∧ msg.code = code

/-- The fields of a fresh frame. -/
theorem Fresh.frame {code : ByteArray} {m : Machine} (h : Fresh code m) :
    m.frame.code = code ∧ m.frame.jumpDests = validJumpDests code ∧ m.frame.pc = 0 ∧
      m.frame.stack = [] ∧ m.frame.memory = {} ∧ m.frame.gasLeft = m.frame.msg.gas ∧
      m.frame.returnData = .empty := by
  obtain ⟨msg, kind, snap, hf, hc⟩ := h
  subst hc
  simp only [hf, Frame.init, and_self]

/-- `Frame.init` is fresh. -/
theorem fresh_init (m : Machine) (msg : Message) (kind : FrameKind)
    (snapshot : World × TransientStorage) (h : m.frame = Frame.init msg kind snapshot) :
    Fresh msg.code m :=
  ⟨msg, kind, snapshot, h, rfl⟩

/-! ## What a finished frame hands over -/

/-- A frame of a message call that ends successfully hands over its gas, output, substate,
world and transient storage. -/
theorem frameResult_success_call {mf : Machine} {out : ByteArray} {o s : Nat}
    (hk : mf.frame.kind = .call o s) :
    frameResult mf (.success out) =
      ({ gasLeft := mf.frame.gasLeft, error := none, reverted := false, output := out,
         sub := mf.frame.sub, target := mf.frame.msg.currentTarget, kind := mf.frame.kind },
       mf.world, mf.transient) := by
  simp only [frameResult, hk]

/-- A reverting frame hands over its gas and output; world and transient storage are rolled
back to its snapshot. -/
theorem frameResult_revert {mf : Machine} {out : ByteArray} :
    frameResult mf (.revert out) =
      ({ gasLeft := mf.frame.gasLeft, error := none, reverted := true, output := out,
         sub := mf.frame.sub, target := mf.frame.msg.currentTarget, kind := mf.frame.kind },
       mf.frame.snapshot.1, mf.frame.snapshot.2) := rfl

/-- An exceptionally halting frame hands over no gas and no output; world and transient
storage are rolled back. -/
theorem frameResult_halt {mf : Machine} {e : ExceptionalHalt} :
    frameResult mf (.halt e) =
      ({ gasLeft := 0, error := some e, reverted := false, output := .empty,
         sub := mf.frame.sub, target := mf.frame.msg.currentTarget, kind := mf.frame.kind },
       mf.frame.snapshot.1, mf.frame.snapshot.2) := rfl

/-! ## Top level -/

/-- The machine `initMachine` builds for a top-level call to a non-precompile without value. -/
def startMachine (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message) :
    Machine where
  ctx := ctx
  precompiles := PrecompileImpl.standard ctx
  world := w
  transient := tr
  originalWorld := w
  createdAccounts := ∅
  frame := Frame.init msg (.call 0 0) (w, tr)
  parents := []

/-- The start machine is fresh. -/
theorem fresh_startMachine (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message) :
    Fresh msg.code (startMachine ctx w tr msg) :=
  fresh_init _ msg _ _ rfl

/-- **Top-level glue.** A frame summary of the code a top-level call runs gives the result of
`processMessageCall` for all large enough fuel. The call is to the non-precompile `a` holding
`msg.code` (not a delegation designator), at depth zero, without value, before Prague or
without EIP-7702 authorizations. -/
theorem processMessageCall_of_halts {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {a : Address} {H : Machine → Outcome → Prop}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? msg.code = none) (htarget : msg.target = some a)
    (hca : msg.codeAddress = some a) (hpre : Precompile.isPrecompile ctx.fork a = false)
    (hval : msg.value = 0) (hdepth : msg.depth = 0)
    (h : Halts (startMachine ctx w tr msg) H) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ mf o, H mf o ∧ SameFrame (startMachine ctx w tr msg) mf ∧
      processMessageCall fuel ctx w tr msg = .ok (topLevelResult msg.target
        (frameResult mf o).2.1 (frameResult mf o).2.2 (frameResult mf o).1) := by
  obtain ⟨n, mf, o, hH, hs, hrun⟩ := h.run rfl
  refine ⟨n, fun fuel hle => ⟨mf, o, hH, hs, ?_⟩⟩
  rw [processMessageCall_eq_run hdeleg hdel
    (initMachine_call (pre := PrecompileImpl.standard ctx) htarget hca hpre hval hdepth)]
  exact hrun fuel hle

/-- The top-level result of a successful call frame. -/
theorem topLevelResult_success_call {t : Option Address} {mf : Machine} {out : ByteArray}
    {o s : Nat} (hk : mf.frame.kind = .call o s) :
    let r := topLevelResult t (frameResult mf (.success out)).2.1
      (frameResult mf (.success out)).2.2 (frameResult mf (.success out)).1
    r.success = true ∧ r.output = out ∧ r.world = mf.world ∧ r.gasLeft = mf.frame.gasLeft ∧
      r.logs = mf.frame.sub.logs := by
  simp only [frameResult_success_call hk, topLevelResult_success, topLevelResult_output,
    topLevelResult_world, topLevelResult_gasLeft, ChildResult.success, true_and]
  unfold topLevelResult
  simp [ChildResult.success]

/-! ## Function summaries -/

/-- The 4-byte selector of calldata, as solc's dispatcher computes it
(`shr(224, calldataload(0))`). -/
def selectorOf (data : ByteArray) : Word := Word.shr (224#256) (Bytes.toWord (readBytes data 0 32))

/-- A summary of an external function of the contract with runtime code `code`, in the
shape solc compiles it: a dispatcher that reaches the function's `entry` pc, and a body from
there to the end of the frame. Everything is stated for any machine whose frame is fresh, so
for any parents: the same summary serves top-level calls and calls from other contracts.

* `pre m`: the precondition on the start machine (calldata selecting the function, the
  arguments, caller, value, storage, enough gas, …);
* `atEntry m m'`: what the dispatcher leaves at the entry (typically the stack and the free
  memory pointer), relating the start machine `m` to the machine `m'` at `entry`;
* `post m mf o`: the postcondition, relating the start machine to the end of the frame
  (outcome `o`, machine `mf` seen by `finishFrame`): return data, storage, logs, gas left. -/
structure FunctionSummary (code : ByteArray) where
  /-- The pc of the function body after dispatch. -/
  entry : Nat
  /-- Precondition on the start machine. -/
  pre : Machine → Prop
  /-- The machine at `entry`, given the start machine. -/
  atEntry : Machine → Machine → Prop
  /-- Postcondition: start machine, final machine, outcome. -/
  post : Machine → Machine → Outcome → Prop
  /-- The dispatcher reaches `entry` (or ends the frame satisfying `post`). -/
  dispatch : ∀ m, Fresh code m → pre m →
    WP m (fun m' => m'.frame.pc = entry ∧ atEntry m m') (post m)
  /-- The body ends the frame satisfying `post`. -/
  body : ∀ m m', Fresh code m → pre m → SameFrame m m' → m'.frame.pc = entry → atEntry m m' →
    Halts m' (post m)

namespace FunctionSummary

variable {code : ByteArray} (s : FunctionSummary code)

/-- **Dispatcher + body.** A function summary is a frame summary. -/
theorem halts {m : Machine} (hf : Fresh code m) (hpre : s.pre m) : Halts m (s.post m) :=
  WP.halts_of_false <| (s.dispatch m hf hpre).bind fun m' hs ⟨hpc, he⟩ =>
    WP.halts (s.body m m' hf hpre hs hpc he)

/-- **Function summary of a top-level call.** -/
theorem processMessageCall {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {a : Address}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? code = none) (hcode : msg.code = code)
    (htarget : msg.target = some a) (hca : msg.codeAddress = some a)
    (hpre : Precompile.isPrecompile ctx.fork a = false)
    (hval : msg.value = 0) (hdepth : msg.depth = 0)
    (h : s.pre (startMachine ctx w tr msg)) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ mf o, s.post (startMachine ctx w tr msg) mf o ∧
      SameFrame (startMachine ctx w tr msg) mf ∧
      Interpreter.processMessageCall fuel ctx w tr msg = .ok (topLevelResult msg.target
        (frameResult mf o).2.1 (frameResult mf o).2.2 (frameResult mf o).1) := by
  subst hcode
  exact processMessageCall_of_halts hdeleg hdel htarget hca hpre hval hdepth
    (s.halts (fresh_startMachine ctx w tr msg) h)

end FunctionSummary

end EvmLean.Program
