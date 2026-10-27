import Verified.WeirdERC20.AMPL.Spec.MalformedInit
import EvmLogic.Program.PrecompileCall

/-!
# Any-gas rules for AMPL's `permit`: `TIMESTAMP`, `CHAINID` and the call to `ecrecover`

Rules of the any-gas calculus (`Verified.Solady.Spec.AnyGas`) that `permit` needs and the
calculus lacks, stated in AMPL's namespace:

* `wp_timestamp`, `wp_chainid`: push the block's timestamp or chain id;
* `wp_staticcall_one`: solc's `STATICCALL(g, 0x01, inOff, 128, outOff, 32)` to the standard
  `ecrecover` precompile, at any gas and depth. If the call's charge exceeds the gas, the frame
  fails. At the call-depth limit, or when the forwarded gas is below `3000`, the caller
  continues with `0` pushed (memory, gas, access lists and return data then left unknown).
  Otherwise it continues with `1` pushed and the signer's word written at `outOff` (gas and
  access lists left unknown).
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Verified.Solady.Spec.AnyGas

variable {H : Machine → Outcome → Prop} {Q : Machine → Prop} {m : Machine}

/-- `TIMESTAMP` (`pwp_pushValue`). -/
theorem wp_timestamp (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x42)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := (ofNat m.ctx.block.timestamp) :: m.frame.stack,
        gasLeft := m.frame.gasLeft - Gas.base, pc := m.frame.pc + 1 } } Q H) :
    WP m Q H :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `CHAINID` (`pwp_pushValue`). -/
theorem wp_chainid (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x46)
    (hrec : m.frame.stack.length < 1024 → Gas.base ≤ m.frame.gasLeft →
      WP { m with frame := { m.frame with
        stack := (ofNat m.ctx.block.chainId) :: m.frame.stack,
        gasLeft := m.frame.gasLeft - Gas.base, pc := m.frame.pc + 1 } } Q H) :
    WP m Q H :=
  pwp_pushValue hsnap (fun fk => by cases fk <;> rfl) hcode hrec

/-- `ECRECOVER` with less than `3000` gas fails. -/
theorem ecrecover_fail (crypto : Crypto) (input : ByteArray) {gas : Nat} (h : gas < 3000) :
    (Precompile.ecrecover crypto input gas).success = false := by
  unfold Precompile.ecrecover
  simp only [h, ite_true]
  rfl

variable {g toW inOff inSize outOff outSize : Word} {rest : List Word}

/-- **`STATICCALL` at the depth limit** pushes `0` and continues, the forwarded gas refunded. -/
theorem step_staticcall_limit (hcode : m.frame.code[m.frame.pc]? = some 0xfa)
    (hstk : m.frame.stack = g :: toW :: inOff :: inSize :: outOff :: outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : callCost m g 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hdepth : Gas.stackDepthLimit < m.frame.msg.depth + 1) (hlen : rest.length < 1024) :
    step m = .running { m with frame := { callerFrame m rest (callCost m g 0 (Word.toAddress toW)
        0 0 inOff inSize outOff outSize) (Word.toAddress toW) inOff inSize outOff outSize with
      gasLeft := m.frame.gasLeft - callCost m g 0 (Word.toAddress toW) 0 0 inOff inSize outOff
          outSize + (callGas m g 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize).subCall
      stack := 0 :: rest
      pc := m.frame.pc + 1 } } := by
  have hg : ¬ m.frame.gasLeft < callCost m g 0 (Word.toAddress toW) 0 0 inOff inSize outOff
      outSize := Nat.not_lt.mpr hgas
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
    setReturnData, hdepth, List.foldl, readMemory, refundGas, push, advance]
  have hl : ¬ rest.length ≥ Gas.stackLimit := by simp only [Gas.stackLimit]; omega
  simp only [hl, ite_false, StateT.run_modify, pure_bind]
  rfl

/-- `STATICCALL` whose charge exceeds the gas fails. -/
theorem exec_staticcall_oog (hstk : m.frame.stack = g :: toW :: inOff :: inSize :: outOff ::
      outSize :: rest)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none)
    (hgas : m.frame.gasLeft < callCost m g 0 (Word.toAddress toW) 0 0 inOff inSize outOff outSize) :
    (exec (Opcode.decode m.ctx.fork 0xfa)).run m = .error .outOfGas := by
  rw [show Opcode.decode m.ctx.fork 0xfa = .staticcall by cases m.ctx.fork <;> rfl]
  simp only [exec, execCall, popNat, popAddress, pop, getFrame, modifyFrame, StateT.run_bind,
    hstk, StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind, memoryExpansion]
  rw [run_accessAddress]
  simp only [pure_bind]
  rw [run_accessDelegation _ _ ?hd]
  case hd => exact hdel
  simp only [callCost, callGas, callExt, Nat.add_zero] at hgas
  simp only [pure_bind, charge, getFrame, StateT.run_bind, StateT.run_get, StateT.run_pure,
    Nat.add_zero, hgas, ite_true]
  rfl

/-- **solc's call to `ecrecover`, at any gas and depth.** -/
theorem wp_staticcall_one {hash v r s : Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0xfa)
    (hstk : m.frame.stack = g :: 1#256 :: inOff :: 128#256 :: outOff :: 32#256 :: rest)
    (hlen : rest.length < 1024)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hin : m.frame.memory.read inOff.toNat 128 =
      Bytes.ofWord hash ++ (Bytes.ofWord v ++ (Bytes.ofWord r ++ Bytes.ofWord s)))
    (kfail : ∀ (mem : Memory) (gl : Nat) (sb : Substate) (rd : ByteArray),
      WP { m with frame := { m.frame with
        stack := 0 :: rest
        memory := mem
        gasLeft := gl
        sub := sb
        returnData := rd
        pc := m.frame.pc + 1 } } Q H)
    (kok : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit → ∀ (gl : Nat) (sb : Substate),
      sb.logs = m.frame.sub.logs → WP { m with frame := { m.frame with
        stack := 1 :: rest
        memory := returnMemory (callMemory m inOff 128#256 outOff 32#256) outOff.toNat 32
          (ecrecoverOutput m.ctx.crypto hash v r s)
        gasLeft := gl
        sub := sb
        returnData := ecrecoverOutput m.ctx.crypto hash v r s
        pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  have hto : Word.toAddress (1#256) = 1 := by decide
  have hdel' : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress 1#256)) =
      none := by rw [hto]; exact hdel
  by_cases hgas : callCost m g 0 (Word.toAddress 1#256) 0 0 inOff 128#256 outOff 32#256 ≤
      m.frame.gasLeft
  swap
  · exact wp_fail_of_error hsnap hcode (exec_staticcall_oog hstk hdel' (Nat.lt_of_not_le hgas))
  by_cases hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit
  swap
  · exact WP.of_step (step_staticcall_limit hcode hstk hdel' hgas (Nat.lt_of_not_le hdepth) hlen)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (kfail _ _ _ _)
  have hpre : m.precompiles.isPrecompile (Word.toAddress 1#256) = true := by
    rw [hstd, hto]; exact isPrecompile_one _
  refine WP.staticcall_precompile hcode hstk hdel' hgas hdepth hpre ?_
  have hrun : ∀ msg : Message,
      msg.data = Bytes.ofWord hash ++ (Bytes.ofWord v ++ (Bytes.ofWord r ++ Bytes.ofWord s)) →
      3000 ≤ msg.gas → m.precompiles.run 1 msg.data msg.gas =
        { success := true, gasLeft := msg.gas - 3000,
          output := ecrecoverOutput m.ctx.crypto hash v r s } := by
    intro msg hd hg
    rw [hstd, hd]
    exact (run_one _ _ _ _).trans (ecrecover_words _ _ _ _ _ hg)
  have hfl : ∀ msg : Message, msg.gas < 3000 →
      (m.precompiles.run 1 msg.data msg.gas).success = false := by
    intro msg hg
    rw [hstd]
    exact (congrArg Precompile.Result.success (run_one _ _ _ _)).trans (ecrecover_fail _ _ hg)
  rw [hto]
  have hd := childMsg_data m m.frame.msg.currentTarget 1 1 0
    (callGas m g 0 1 0 0 inOff 128#256 outOff 32#256).subCall true true inOff 128#256 outOff
    32#256
  rw [BitVec.toNat_ofNat, show 128 % 2 ^ 256 = 128 by decide, hin] at hd
  rw [hto] at hgas
  by_cases hsub : 3000 ≤ (callGas m g 0 1 0 0 inOff 128#256 outOff 32#256).subCall
  · have hr := hrun _ hd hsub
    rw [resume_precompile_success (by rw [hr])]
    rw [hr]
    exact kok hdepth _ _ (by
      simp [mergeSub, Substate.warmAddr, Substate.ofMessage, callerFrame])
  · rw [resume_precompile_failure (hfl _ (Nat.lt_of_not_le hsub))]
    exact kfail _ _ _ _

end Verified.WeirdERC20.AMPL.Spec.Malformed
