import Verified.WETH9.Spec.ViewsLow
import QEDefi.ERC4626.Logs

/-!
# WETH9's `approve` on the bytecode, for every gas

`approve_low`: `approve(sp, wad)` from a fresh frame, as a `LowOK` judgement: with value it
reverts; in a static frame its `SSTORE` fails; otherwise it writes `allowance[caller][sp] := wad`
(`mappingSlot2 … 4`), logs `Approval(caller, sp, wad)` and returns `true`.
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.Solidity Verified.WETH9.Contracts QEDefi.ERC4626

variable {ctx : Context} {pre : PrecompileImpl} {w : World} {tr : TransientStorage}
  {ow : World} {cr : AddressSet} {msg : Message} {sub : Substate}
  {snap : World × TransientStorage} {k : FrameKind} {ps : List Frame} {gas : Nat}
  {Hf : Machine → Outcome → Prop}

set_option maxHeartbeats 8000000 in
/-- **`approve(sp, wad)`, every gas.** -/
theorem approve_low (sp : Address) (wad : Word)
    (hsel : Abi.selectorOf msg.data = 0x095ea7b3) (hsize : 68 ≤ msg.data.size)
    (hsize' : msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes msg.data 4 32) = Word.ofAddress sp)
    (harg1 : Bytes.toWord (readBytes msg.data 36 32) = wad) (hg : 50000 ≤ gas)
    (hrev : msg.value ≠ 0 → ∀ mf out, Hf mf (.revert out))
    (hstat : msg.value = 0 → msg.isStatic = true → ∀ mf e, Hf mf (.halt e))
    (hok : msg.value = 0 → msg.isStatic = false → ∀ mf out, out = Bytes.ofWord 1 →
      mf.world = w.sstore msg.currentTarget
        (mappingSlot2 ctx.crypto (Word.ofAddress msg.caller) (Word.ofAddress sp) 4) wad →
      mf.transient = tr → mf.createdAccounts = cr →
      mf.frame.sub.logs = sub.logs.push (approvalLog msg.currentTarget msg.caller sp wad) →
      Hf mf (.success out)) :
    LowOK Hf (wethM ctx pre w tr ow cr msg sub snap k ps gas) := by
  have hsel' := div_selector msg.data
  rw [hsel] at hsel'
  have hlt := Dispatch.lt_calldatasize_four (n := msg.data.size) (by omega) (by omega)
  by_cases hv : msg.value = 0
  · cases hst : msg.isStatic
    · low_steps [hsel', hlt, hv, harg0, harg1]
      low_step
      refine hok hv hst _ _ ?_ rfl rfl rfl ?_
      · simp only [outputData, readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat,
          Nat.reduceMod, Nat.reducePow, Memory.read_storeWord]
        rfl
      · simp only [outputMachine, warmKey_logs, addRefund_logs, approvalLog, eventLog,
          encodeArgs_one, logEntry, readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat,
          Nat.reduceMod, Nat.reducePow, Memory.read_storeWord]
        rfl
    · low_steps [hsel', hlt, hv, harg0, harg1]
      low_static hst
      exact hstat hv hst _
  · low_steps [hsel', hlt, iszero_of_ne hv, harg0, harg1]
    low_step
    exact hrev hv _ _

end Verified.WETH9.Spec
