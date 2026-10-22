import EvmLogic.Program.Call
import EvmLogic.Solidity.Call

/-!
# `CALL` to an account without code

A plain ETH payment (`Address.sendValue`, `payable(a).transfer`) to an account with empty code:
the value moves before the child starts (`transferValue`), the child frame halts at once with
success and empty output (`halts_of_code_size_zero`: `step_of_pc_ge`), and the caller resumes
with `1` pushed and all of the child's gas back. `WP.call_codeless` packages this as a single
rule: no callee summary is needed, and the value may be zero or not.
-/

namespace EvmLogic.Program
open EvmLean EvmLean.Interpreter EvmLogic.Solidity

/-- A frame whose code is empty halts at once, with success and empty output. -/
theorem halts_of_code_size_zero {m : Machine} (h : m.frame.code.size = 0) :
    Halts m (fun mf o => mf = m ∧ o = .success .empty) :=
  ⟨1, m, .success .empty, by rw [stepN_one, step_of_pc_ge (by omega)], .refl m, rfl, rfl⟩

/-- The gas charged for a call fits when the gas left covers the access, creation and
transfer charges and the memory expansion (the all-but-1/64 rule caps the rest). -/
theorem callCost_le {m : Machine} {gas value : Word} {to : Address} {create transfer : Nat}
    {inOff inSize outOff outSize : Word}
    (h : Gas.accessCost (m.frame.sub.accessedAddresses.contains to) + create + transfer +
      (callExt m inOff inSize outOff outSize).cost ≤ m.frame.gasLeft) :
    callCost m gas value to create transfer inOff inSize outOff outSize ≤ m.frame.gasLeft := by
  unfold callCost callGas Gas.messageCallGas
  have hlt : ¬ m.frame.gasLeft < Gas.accessCost (m.frame.sub.accessedAddresses.contains to) +
      0 + create + transfer + (callExt m inOff inSize outOff outSize).cost := by omega
  simp only [hlt, ite_false]
  have : Gas.maxMessageCallGas (m.frame.gasLeft - (callExt m inOff inSize outOff outSize).cost -
      (Gas.accessCost (m.frame.sub.accessedAddresses.contains to) + 0 + create + transfer)) ≤
      m.frame.gasLeft - (callExt m inOff inSize outOff outSize).cost -
      (Gas.accessCost (m.frame.sub.accessedAddresses.contains to) + 0 + create + transfer) := by
    unfold Gas.maxMessageCallGas; omega
  have := Nat.min_le_right gas.toNat (Gas.maxMessageCallGas (m.frame.gasLeft -
    (callExt m inOff inSize outOff outSize).cost -
      (Gas.accessCost (m.frame.sub.accessedAddresses.contains to) + 0 + create + transfer)))
  omega

/-- What the caller has after a call whose child returns all its gas: at least the gas left
minus the access, creation and transfer charges and the memory expansion. -/
theorem le_gas_after_call {m : Machine} {gas value : Word} {to : Address} {create transfer : Nat}
    {inOff inSize outOff outSize : Word}
    (h : Gas.accessCost (m.frame.sub.accessedAddresses.contains to) + create + transfer +
      (callExt m inOff inSize outOff outSize).cost ≤ m.frame.gasLeft) :
    m.frame.gasLeft - (Gas.accessCost (m.frame.sub.accessedAddresses.contains to) + create +
        transfer + (callExt m inOff inSize outOff outSize).cost) ≤
      m.frame.gasLeft - callCost m gas value to create transfer inOff inSize outOff outSize +
        (callGas m gas value to create transfer inOff inSize outOff outSize).subCall := by
  have hc := callCost_le (gas := gas) (value := value) h
  unfold callCost callGas Gas.messageCallGas at *
  have hlt : ¬ m.frame.gasLeft < Gas.accessCost (m.frame.sub.accessedAddresses.contains to) +
      0 + create + transfer + (callExt m inOff inSize outOff outSize).cost := by omega
  simp only [hlt, ite_false] at hc ⊢
  omega

/-- `le_gas_after_call` in the shape the caller's gas takes after `resumeAfter_success`. -/
theorem le_gas_after_call' {m : Machine} {gas value : Word} {to : Address} {create transfer : Nat}
    {inOff inSize outOff outSize : Word} {rest : List Word} {msg : Message} {kind : FrameKind}
    {snap : World × TransientStorage} {g : Nat}
    (h : Gas.accessCost (m.frame.sub.accessedAddresses.contains to) + create + transfer +
      (callExt m inOff inSize outOff outSize).cost ≤ m.frame.gasLeft)
    (hmsg : msg.gas = (callGas m gas value to create transfer inOff inSize outOff outSize).subCall)
    (he : (callerFrame m rest (callCost m gas value to create transfer inOff inSize outOff outSize)
      to inOff inSize outOff outSize).gasLeft + (Frame.init msg kind snap).gasLeft = g) :
    m.frame.gasLeft - (Gas.accessCost (m.frame.sub.accessedAddresses.contains to) + create +
        transfer + (callExt m inOff inSize outOff outSize).cost) ≤ g := by
  rw [← he]
  simp only [callerFrame, Frame.init, hmsg]
  exact le_gas_after_call h

variable {m : Machine} {gas toW value inOff inSize outOff outSize : Word} {rest : List Word}

/-- **`CALL` to an account with empty code** (not a precompile). The value moves to the
callee, the child returns at once with success, and the caller continues with `1` on the
stack, the charged gas minus what the child returns, and the child's (unchanged) substate
merged. -/
theorem WP.call_codeless {Q : Machine → Prop} {H : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0xf1)
    (hstk : m.frame.stack = gas :: toW :: value :: inOff :: inSize :: outOff :: outSize :: rest)
    (hempty : (m.world.code (Word.toAddress toW)).size = 0)
    (hgas : callCost m gas value (Word.toAddress toW) (createCost m.world value (Word.toAddress toW))
      (transferCost value) inOff inSize outOff outSize ≤ m.frame.gasLeft)
    (hstatic : m.frame.msg.isStatic = false ∨ value = 0)
    (hbal : value.toNat ≤ (m.world.balance m.frame.msg.currentTarget).toNat)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hpre : m.precompiles.isPrecompile (Word.toAddress toW) = false)
    (k : WP (resumeAfter
      (callerFrame m rest (callCost m gas value (Word.toAddress toW)
        (createCost m.world value (Word.toAddress toW)) (transferCost value) inOff inSize outOff
        outSize) (Word.toAddress toW) inOff inSize outOff outSize) m.parents
      { m with
        world := transferValue m.world
          (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) value
            (callGas m gas value (Word.toAddress toW) (createCost m.world value (Word.toAddress toW))
              (transferCost value) inOff inSize outOff outSize).subCall true false
            inOff inSize outOff outSize)
        frame := Frame.init
          (childMsg m m.frame.msg.currentTarget (Word.toAddress toW) (Word.toAddress toW) value
            (callGas m gas value (Word.toAddress toW) (createCost m.world value (Word.toAddress toW))
              (transferCost value) inOff inSize outOff outSize).subCall true false
            inOff inSize outOff outSize)
          (.call outOff.toNat outSize.toNat) (m.world, m.transient)
        parents := callerFrame m rest (callCost m gas value (Word.toAddress toW)
          (createCost m.world value (Word.toAddress toW)) (transferCost value) inOff inSize outOff
          outSize) (Word.toAddress toW) inOff inSize outOff outSize :: m.parents }
      (.success .empty)) Q H) :
    WP m Q H := by
  have hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress toW)) = none :=
    .inr (delegatedAddress?_of_size (by omega))
  refine WP.call (step_call hcode hstk hdel hgas hstatic hbal hdepth hpre) rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (halts_of_code_size_zero (by simp only [Frame.init, childMsg]; exact hempty)) ?_
  rintro mf o - ⟨rfl, rfl⟩
  exact k

end EvmLogic.Program
