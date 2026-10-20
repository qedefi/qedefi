import EvmLogic.Step.Basic
import EvmLogic.Step.Flow
import EvmLogic.Program.Logic

/-!
# Frames, messages and function summaries

A theorem `Fresh code m → … → Halts m H` serves as a contract's **summary** both at the top
level (`processMessageCall_of_halts`) and as a callee (`WP.call`). `FunctionSummary code`
splits an external function into solc's dispatcher and the body; internal functions are `WP`
summaries composed with `WP.bind_mono`.
-/

section

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter

/-! ## Fresh frames -/

/-- The executing frame of `m` has just started running `code` (top level or after a
`CALL*`). -/
def Fresh (code : ByteArray) (m : Machine) : Prop :=
  ∃ msg kind snapshot, m.frame = Frame.init msg kind snapshot ∧ msg.code = code

theorem Fresh.frame {code : ByteArray} {m : Machine} (h : Fresh code m) :
    m.frame.code = code ∧ m.frame.jumpDests = validJumpDests code ∧ m.frame.pc = 0 ∧
      m.frame.stack = [] ∧ m.frame.memory = {} ∧ m.frame.gasLeft = m.frame.msg.gas ∧
      m.frame.returnData = .empty := by
  obtain ⟨msg, kind, snap, hf, hc⟩ := h
  subst hc
  simp only [hf, Frame.init, and_self]

theorem fresh_init (m : Machine) (msg : Message) (kind : FrameKind)
    (snapshot : World × TransientStorage) (h : m.frame = Frame.init msg kind snapshot) :
    Fresh msg.code m :=
  ⟨msg, kind, snapshot, h, rfl⟩

/-! ## What a finished frame hands over -/

theorem frameResult_success_call {mf : Machine} {out : ByteArray} {o s : Nat}
    (hk : mf.frame.kind = .call o s) :
    frameResult mf (.success out) =
      ({ gasLeft := mf.frame.gasLeft, error := none, reverted := false, output := out,
         sub := mf.frame.sub, target := mf.frame.msg.currentTarget, kind := mf.frame.kind },
       mf.world, mf.transient) := by
  simp only [frameResult, hk]

theorem frameResult_revert {mf : Machine} {out : ByteArray} :
    frameResult mf (.revert out) =
      ({ gasLeft := mf.frame.gasLeft, error := none, reverted := true, output := out,
         sub := mf.frame.sub, target := mf.frame.msg.currentTarget, kind := mf.frame.kind },
       mf.frame.snapshot.1, mf.frame.snapshot.2) := rfl

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

theorem fresh_startMachine (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message) :
    Fresh msg.code (startMachine ctx w tr msg) :=
  fresh_init _ msg _ _ rfl

/-- **Top-level glue.** A frame summary gives the result of `processMessageCall` for all large
enough fuel (call to a non-precompile, non-delegated `a`, depth zero, no value, no EIP-7702
authorizations). -/
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

/-- A summary of an external function of `code` as solc compiles it: a dispatcher reaching
`entry`, then a body to the end of the frame. Stated for any fresh frame, so it serves both
top-level calls and calls from other contracts. -/
structure FunctionSummary (code : ByteArray) where
  entry : Nat
  pre : Machine → Prop
  /-- What the dispatcher leaves at `entry` (typically stack and free memory pointer). -/
  atEntry : Machine → Machine → Prop
  post : Machine → Machine → Outcome → Prop
  dispatch : ∀ m, Fresh code m → pre m →
    WP m (fun m' => m'.frame.pc = entry ∧ atEntry m m') (post m)
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

end EvmLogic.Program

end

section

/-!
## Composing internal-function summaries

An internal function is summarised by a `WP` from its entry pc (return address on the stack)
whose running postcondition is "back at the return address with the results on the stack".
-/

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter

/-- `m` with pc, stack and gas replaced: where a pure internal function returns to. -/
def _root_.EvmLean.Interpreter.Machine.resumeAt (m : Machine) (pc : Nat) (stack : List Word)
    (gas : Nat) : Machine :=
  { m with frame := { m.frame with pc := pc, stack := stack, gasLeft := gas } }

/-- `m` with pc, stack, memory, gas, return data and substate replaced: where an internal
function with memory or call effects returns to. -/
def _root_.EvmLean.Interpreter.Machine.resumeWith (m : Machine) (pc : Nat) (stack : List Word)
    (mem : Memory) (gas : Nat) (rd : ByteArray) (sub : Substate) : Machine :=
  { m with
    frame :=
      { m.frame with
        pc := pc
        stack := stack
        memory := mem
        gasLeft := gas
        returnData := rd
        sub := sub } }

theorem _root_.EvmLean.Interpreter.Machine.resumeAt_eq (m : Machine) (pc : Nat)
    (stack : List Word) (gas : Nat) :
    m.resumeAt pc stack gas =
      m.resumeWith pc stack m.frame.memory gas m.frame.returnData m.frame.sub := rfl

namespace WP

variable {m : Machine} {Q Q₁ : Machine → Prop} {H H₁ : Machine → Outcome → Prop}

/-- **Sequencing with a summary** whose halting postcondition `H₁` implies the caller's `H`. -/
theorem bind_mono (h : WP m Q₁ H₁) (hH : ∀ mf o, SameFrame m mf → H₁ mf o → H mf o)
    (k : ∀ m', SameFrame m m' → Q₁ m' → WP m' Q H) : WP m Q H :=
  (h.mono (fun _ _ h => h) hH).bind k

/-- A fragment that never ends the frame can be used under any halting postcondition. -/
theorem of_false (h : WP m Q (fun _ _ => False)) : WP m Q H :=
  h.mono (fun _ _ h => h) (fun _ _ _ h => h.elim)

end WP

end EvmLogic.Program

end
