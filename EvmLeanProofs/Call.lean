import EvmLeanProofs.StepBasic

/-!
# From `processMessageCall` to `run`

A top-level message call first applies EIP-7702 delegation (Prague), then `initMachine`
sets up the machine (or answers directly, e.g. for a precompile), then `run` executes it.
When delegation does nothing (before Prague, or no authorizations and no delegation
designator in the code), `processMessageCall` is just `run` from the initial machine.
-/

namespace EvmLean.Interpreter

/-- Delegation does nothing before Prague, or without authorizations when the code is not a
delegation designator. -/
theorem applyTopLevelDelegation_eq {ctx : Context} {isPre : Address → Bool} {w : World}
    {msg : Message} (h : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? msg.code = none) :
    applyTopLevelDelegation ctx isPre w msg = (w, msg, 0) := by
  unfold applyTopLevelDelegation
  split
  · rfl
  · rename_i hf
    have hauth : ctx.tx.authorizations = [] := h.resolve_left hf
    split
    · rfl
    · rfl
    · simp only [hauth, List.isEmpty_nil, ite_true, hdel]

/-- `processMessageCall` runs the machine `initMachine` sets up, when delegation does
nothing. -/
theorem processMessageCall_eq_run {ctx : Context} {w : World} {tr : TransientStorage}
    {msg : Message} {m : Machine} (h : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? msg.code = none)
    (hinit : initMachine (PrecompileImpl.standard ctx) ctx w tr msg = .inr m) (fuel : Nat) :
    processMessageCall fuel ctx w tr msg = run fuel m := by
  simp only [processMessageCall, processMessageCallWith, applyTopLevelDelegation_eq h hdel,
    hinit, Int.add_zero]
  cases run fuel m <;> rfl

/-- `initMachine` for a call to a non-precompile, with no value moving, at depth zero. -/
theorem initMachine_call {pre : PrecompileImpl} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {a : Address} (htarget : msg.target = some a)
    (hcode : msg.codeAddress = some a) (hpre : pre.isPrecompile a = false)
    (hvalue : msg.value = 0) (hdepth : msg.depth = 0) :
    initMachine pre ctx w tr msg = .inr
      { ctx, precompiles := pre, world := w, transient := tr, originalWorld := w,
        createdAccounts := ∅, frame := Frame.init msg (.call 0 0) (w, tr), parents := [] } := by
  simp only [initMachine, hdepth, htarget, hvalue, transferValue, precompileOf, hcode, hpre,
    Gas.stackDepthLimit]
  simp
