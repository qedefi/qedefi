import EvmLeanProofs.Program.Call

/-!
# Calls to precompiles

A `CALL*` whose target is a precompile does not push a frame: `launchCall` runs the
precompile to completion within the same `step` (`runPrecompile`) and resumes the caller at
once. This file states that step for `STATICCALL`, for **any** precompile implementation
`m.precompiles` (in particular `PrecompileImpl.standard ctx`, i.e. `Precompile.run ctx.crypto
ctx.fork` for an arbitrary `Crypto`):

* `precompileResult pre a msg kind`: the `ChildResult` the caller sees (the precompile's
  `Precompile.Result`, with the substate of a fresh child; all gas consumed on failure);
* `step_staticcall_precompile`: one `step` from a `STATICCALL` to a precompile charges the
  caller exactly as `step_staticcall` does (`callCost`) and resumes it with
  `precompileResult` (world and transient storage unchanged);
* `resume_precompile_success` / `resume_precompile_failure`: the resumed caller frame, spelled
  out: success flag pushed, unused gas returned, output copied to the output window and kept
  as return data (`returnMemory`), the child's substate merged (`mergeSub`);
* `WP.staticcall_precompile`: the rule for the frame-local logic;
* `isPrecompile_one`, `run_one`: address `0x01` is `ECRECOVER` in every fork.
-/

namespace EvmLean.Program

open Interpreter

variable {m : Machine} {gas toW inOff inSize outOff outSize : Word} {rest : List Word}

/-- What a caller sees after the precompile at `a` ran on `msg` (`runPrecompile`'s child
result): on success its gas left and output, on failure no gas and no output. -/
def precompileResult (pre : PrecompileImpl) (a : Address) (msg : Message) (kind : FrameKind) :
    ChildResult :=
  if (pre.run a msg.data msg.gas).success then
    { gasLeft := (pre.run a msg.data msg.gas).gasLeft, error := none, reverted := false,
      output := (pre.run a msg.data msg.gas).output, sub := Substate.ofMessage msg,
      target := msg.currentTarget, kind }
  else
    { gasLeft := 0, error := some .precompileFailure, reverted := false, output := .empty,
      sub := Substate.ofMessage msg, target := msg.currentTarget, kind }

/-- `runPrecompile` for a call without value: the world and transient storage stay as they
are (the snapshot is the current state). -/
theorem runPrecompile_eq (pre : PrecompileImpl) (a : Address) (msg : Message) (kind : FrameKind)
    (w : World) (t : TransientStorage) :
    runPrecompile pre a msg kind w t (w, t) = (precompileResult pre a msg kind, w, t) := by
  unfold runPrecompile precompileResult
  cases h : (pre.run a msg.data msg.gas).success <;> simp only [h] <;> rfl

/-- **`STATICCALL` to a precompile** runs it within the step and resumes the caller. The
charges are those of `step_staticcall` (`callCost`); the precompile receives the input window
as data and `(callGas …).subCall` gas. -/
theorem step_staticcall_precompile (hcode : m.frame.code[m.frame.pc]? = some 0xfa)
    (hstk : m.frame.stack = gas :: toW :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = true) :
    step m = .running (resume
      { m with frame := callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize
          outOff outSize) (Word.toAddress toW) inOff inSize outOff outSize }
      (precompileResult m.precompiles (Word.toAddress toW)
        (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) 0
          (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall true true
          inOff inSize outOff outSize)
        (.call outOff.toNat outSize.toNat))) := by
  have hg : ¬ m.frame.gasLeft < callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff
      outSize := Nat.not_lt.mpr hgas
  have hd : ¬ m.frame.msg.depth + 1 > Gas.stackDepthLimit := Nat.not_lt.mpr hdepth
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0xfa = .staticcall by
    cases m.ctx.fork <;> rfl]
  simp only [exec, execCall, popNat, popAddress, pop, getFrame, modifyFrame, StateT.run_bind,
    hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, memoryExpansion]
  rw [run_accessAddress]
  simp only [pure_bind]
  rw [run_accessDelegation _ _ ?hd]
  case hd => exact hdel
  simp only [callCost, callGas, callExt, Nat.add_zero] at hg
  simp only [pure_bind, charge, getFrame, StateT.run_bind, StateT.run_get, StateT.run_pure,
    ite_true, Nat.add_zero, hg, ite_false, modifyFrame, StateT.run_modify,
    reduceCtorEq, decide_false, Bool.false_and, Bool.false_eq_true, expandMemory, genericCall,
    setReturnData, hd, List.foldl, readMemory]
  simp only [pure, Except.pure, launchCall, precompileOf, transferValue, hpre,
    Bool.false_eq_true, ite_false, ite_true, ne_eq, not_true_eq_false, decide_false,
    Bool.and_false]
  rw [runPrecompile_eq]
  rfl

/-- The caller resumed after a **successful** precompile call: `1` pushed, unused gas returned,
the output copied into the output window and kept as return data, the child's (fresh)
substate merged, the pc advanced. -/
theorem resume_precompile_success {M : Machine} {pre : PrecompileImpl} {a : Address}
    {msg : Message} {o s : Nat} (h : (pre.run a msg.data msg.gas).success = true) :
    resume M (precompileResult pre a msg (.call o s)) =
      { M with frame := { M.frame with
        gasLeft := M.frame.gasLeft + (pre.run a msg.data msg.gas).gasLeft
        sub := mergeSub M.frame.sub (Substate.ofMessage msg) M.world msg.currentTarget
        returnData := (pre.run a msg.data msg.gas).output
        stack := 1 :: M.frame.stack
        memory := returnMemory M.frame.memory o s (pre.run a msg.data msg.gas).output
        pc := M.frame.pc + 1 } } := by
  simp only [precompileResult, h, ite_true, resume, ChildResult.success, Option.isNone_none,
    Bool.not_false, Bool.and_self]
  rfl

/-- The caller resumed after a **failed** precompile call (out of gas or invalid input with
exceptional failure): `0` pushed, no gas returned, empty return data, memory unchanged. -/
theorem resume_precompile_failure {M : Machine} {pre : PrecompileImpl} {a : Address}
    {msg : Message} {o s : Nat} (h : (pre.run a msg.data msg.gas).success = false) :
    resume M (precompileResult pre a msg (.call o s)) =
      { M with frame := { M.frame with
        sub := failSub M.frame.sub (Substate.ofMessage msg) M.world msg.currentTarget
        returnData := .empty
        stack := 0 :: M.frame.stack
        pc := M.frame.pc + 1 } } := by
  simp only [precompileResult, h, Bool.false_eq_true, ite_false, resume, ChildResult.success,
    Option.isNone_some, Bool.false_and, failSub, Nat.add_zero]
  have : (ByteArray.empty.extract 0 (min s ByteArray.empty.size)).size = 0 := by simp
  simp only [this, ite_true]

/-- **Precompile-call rule** for the frame-local logic: a `STATICCALL` to a precompile is one
step in the same frame, to the caller resumed with `precompileResult`. -/
theorem WP.staticcall_precompile {Q : Machine → Prop} {H : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xfa)
    (hstk : m.frame.stack = gas :: toW :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = true)
    (k : WP (resume
      { m with frame := callerFrame m rest (callCost m gas 0 (Word.toAddress toW) 0 0 inOff inSize
          outOff outSize) (Word.toAddress toW) inOff inSize outOff outSize }
      (precompileResult m.precompiles (Word.toAddress toW)
        (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) 0
          (callGas m gas 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall true true
          inOff inSize outOff outSize)
        (.call outOff.toNat outSize.toNat))) Q H) :
    WP m Q H :=
  WP.of_step (step_staticcall_precompile hcode hstk hdel hgas hdepth hpre)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ k

/-! ## `ECRECOVER` at `0x01` -/

/-- Address `0x01` is a precompile in every fork. -/
theorem isPrecompile_one (fork : Fork) : Precompile.isPrecompile fork 1 = true := by
  cases fork <;> rfl

/-- Address `0x01` runs `ECRECOVER` in every fork. -/
theorem run_one (crypto : Crypto) (fork : Fork) (input : ByteArray) (gas : Nat) :
    Precompile.run crypto fork 1 input gas = Precompile.ecrecover crypto input gas := by
  cases fork <;> rfl

/-- `ECRECOVER` with enough gas always succeeds (an invalid signature gives empty output) and
costs exactly 3000 gas. -/
theorem ecrecover_success (crypto : Crypto) (input : ByteArray) {gas : Nat} (h : 3000 ≤ gas) :
    (Precompile.ecrecover crypto input gas).success = true ∧
      (Precompile.ecrecover crypto input gas).gasLeft = gas - 3000 := by
  unfold Precompile.ecrecover
  simp only [Nat.not_lt.mpr h, ite_false]
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩

end EvmLean.Program
