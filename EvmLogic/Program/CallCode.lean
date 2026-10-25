import EvmLogic.Program.Call

/-!
# `CALLCODE`

`CALLCODE` runs the code of the target **at the caller's own address** (its storage and balance),
with `CALLER` the caller and `CALLVALUE` the given value, which "moves" from the caller to itself
(a no-op on balances, but it must be affordable and costs 9000). Unlike `CALL` it creates no
account and is allowed in a static frame (the child inherits staticness). `step_callcode` pushes
the child frame; `WP.callcode` is the callee-summary rule (`WP.call`).
-/

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter

variable {m : Machine} {gas toW value inOff inSize outOff outSize : Word} {rest : List Word}

/-- The child machine of a `CALLCODE`: the code of `toW` runs at the caller's address. -/
abbrev callcodeChild (m : Machine) (gas toW value inOff inSize outOff outSize : Word)
    (rest : List Word) : Machine :=
  { m with
    world := transferValue m.world
      (childMsg m m.frame.msg.currentTarget m.frame.msg.currentTarget (Word.toAddress toW) value
        (callGas m gas value (Word.toAddress toW) 0 (transferCost value) inOff inSize outOff
          outSize).subCall true false inOff inSize outOff outSize)
    frame := Frame.init
      (childMsg m m.frame.msg.currentTarget m.frame.msg.currentTarget (Word.toAddress toW) value
        (callGas m gas value (Word.toAddress toW) 0 (transferCost value) inOff inSize outOff
          outSize).subCall true false inOff inSize outOff outSize)
      (.call outOff.toNat outSize.toNat) (m.world, m.transient)
    parents := callerFrame m rest (callCost m gas value (Word.toAddress toW) 0 (transferCost value)
      inOff inSize outOff outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents }

/-- The suspended caller frame of a `CALLCODE`. -/
abbrev callcodeCaller (m : Machine) (gas toW value inOff inSize outOff outSize : Word)
    (rest : List Word) : Frame :=
  callerFrame m rest (callCost m gas value (Word.toAddress toW) 0 (transferCost value) inOff
    inSize outOff outSize) (Word.toAddress toW) inOff inSize outOff outSize

/-- **`CALLCODE` to a non-precompile pushes the child frame** running the code of `toW` at the
caller's address, when the charge is affordable, the caller can pay `value` and the depth limit
is not reached. -/
theorem step_callcode (hcode : m.frame.code[m.frame.pc]? = some 0xf2)
    (hstk : m.frame.stack = gas :: toW :: value :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas value (Word.toAddress toW) 0 (transferCost value) inOff inSize outOff
      outSize ≤ m.frame.gasLeft)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false) :
    step m = .running (callcodeChild m gas toW value inOff inSize outOff outSize rest) := by
  have hg : ¬ m.frame.gasLeft < callCost m gas value (Word.toAddress toW) 0 (transferCost value)
      inOff inSize outOff outSize := Nat.not_lt.mpr hgas
  have hd : ¬ m.frame.msg.depth + 1 > Gas.stackDepthLimit := Nat.not_lt.mpr hdepth
  have hb : ¬ (m.world.balance m.frame.msg.currentTarget).toNat < value.toNat :=
    Nat.not_lt.mpr hbal
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0xf2 = .callcode by
    cases m.ctx.fork <;> rfl]
  simp only [exec, execCall, popNat, popAddress, pop, getFrame, modifyFrame, StateT.run_bind,
    hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, memoryExpansion]
  rw [run_accessAddress]
  simp only [pure_bind]
  rw [run_accessDelegation _ _ ?hd]
  case hd => exact hdel
  simp only [callCost, callGas, callExt, transferCost, Nat.add_zero] at hg
  simp only [pure_bind, charge, getFrame, StateT.run_bind, StateT.run_get, StateT.run_pure,
    Nat.add_zero, hg, ite_false, modifyFrame, StateT.run_modify, reduceCtorEq, decide_false,
    Bool.false_and, Bool.false_eq_true, expandMemory, genericCall, setReturnData, hd,
    List.foldl, readMemory, hb]
  simp only [pure, Except.pure, launchCall, precompileOf, transferValue, hpre, Bool.false_eq_true,
    ite_false]
  rfl

/-- **Callee-summary rule for `CALLCODE`** (`step_callcode` + `WP.call`): if the child frame
(`callcodeChild`: the target's code at the caller's address) `Halts` with `Hc`, the caller
continues from `resumeAfter` of every end `Hc` allows (`resumeAfter_success`/`_revert`/`_halt`). -/
theorem WP.callcode {Q : Machine → Prop} {H Hc : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xf2)
    (hstk : m.frame.stack = gas :: toW :: value :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m gas value (Word.toAddress toW) 0 (transferCost value) inOff inSize outOff
      outSize ≤ m.frame.gasLeft)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (hcallee : Halts (callcodeChild m gas toW value inOff inSize outOff outSize rest) Hc)
    (k : ∀ mf o, Hc mf o → SameFrame (callcodeChild m gas toW value inOff inSize outOff outSize rest)
      mf →
      WP (resumeAfter (callcodeCaller m gas toW value inOff inSize outOff outSize rest) m.parents
        mf o) Q H) :
    WP m Q H :=
  WP.call (step_callcode hcode hstk hdel hgas hbal hdepth hpre) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcallee
    (fun mf o hs hc => k mf o hc hs)

end EvmLogic.Program
