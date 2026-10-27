import Verified.WETH9.Spec.LowStep
import Verified.WETH9.Solvency
import EvmLogic.Solidity.Dispatch

/-!
# WETH9's views on the bytecode, for every gas

`balanceOf_low`, `allowance_low`, `totalSupply_low`: the three views of the deployed code from
a fresh frame, as `LowOK` judgements (every lower-gas version fails or ends the same way): with
no value they return the storage word (`balanceOf[a]`, `allowance[o][sp]`) or the contract's
balance and change nothing; with value they revert (solc 0.4.19 checks `CALLVALUE` in every
non-payable function).
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.Solidity Verified.WETH9.Contracts

variable {ctx : Context} {pre : PrecompileImpl} {w : World} {tr : TransientStorage}
  {ow : World} {cr : AddressSet} {msg : Message} {sub : Substate}
  {snap : World × TransientStorage} {k : FrameKind} {ps : List Frame} {gas : Nat}
  {Hf : Machine → Outcome → Prop}

/-- A fresh frame of the deployed WETH9 code with gas `gas`. -/
abbrev wethM (ctx : Context) (pre : PrecompileImpl) (w : World) (tr : TransientStorage)
    (ow : World) (cr : AddressSet) (msg : Message) (sub : Substate)
    (snap : World × TransientStorage) (k : FrameKind) (ps : List Frame) (gas : Nat) : Machine :=
  Machine.mk ctx pre w tr ow cr
    (Frame.mk msg WETH9.runtimeCode (validJumpDests WETH9.runtimeCode) 0 [] {} gas .empty sub
      snap k) ps

set_option maxHeartbeats 4000000 in
/-- **`balanceOf(a)`, every gas.** -/
theorem balanceOf_low (a : Address)
    (hsel : Abi.selectorOf msg.data = 0x70a08231) (hsize : 36 ≤ msg.data.size)
    (hsize' : msg.data.size < 2 ^ 64)
    (harg : Bytes.toWord (readBytes msg.data 4 32) = Word.ofAddress a) (hg : 5000 ≤ gas)
    (hrev : msg.value ≠ 0 → ∀ mf out, Hf mf (.revert out))
    (hok : msg.value = 0 → ∀ mf out, out = Bytes.ofWord (w.sload msg.currentTarget
        (mappingSlot ctx.crypto (Word.ofAddress a) 3)) → mf.world = w → mf.transient = tr →
      mf.createdAccounts = cr → mf.frame.sub.logs = sub.logs → Hf mf (.success out)) :
    LowOK Hf (wethM ctx pre w tr ow cr msg sub snap k ps gas) := by
  have hsel' := div_selector msg.data
  rw [hsel] at hsel'
  have hlt := Dispatch.lt_calldatasize_four (n := msg.data.size) (by omega) (by omega)
  by_cases hv : msg.value = 0
  · low_steps [hsel', hlt, hv, harg]
    low_step
    refine hok hv _ _ ?_ rfl rfl rfl rfl
    simp only [outputData, readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat,
      Nat.reduceMod, Nat.reducePow, Memory.read_storeWord]
    rfl
  · low_steps [hsel', hlt, iszero_of_ne hv, harg]
    low_step
    exact hrev hv _ _

set_option maxHeartbeats 4000000 in
/-- **`allowance(o, sp)`, every gas.** -/
theorem allowance_low (o sp : Address)
    (hsel : Abi.selectorOf msg.data = 0xdd62ed3e) (hsize : 68 ≤ msg.data.size)
    (hsize' : msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes msg.data 4 32) = Word.ofAddress o)
    (harg1 : Bytes.toWord (readBytes msg.data 36 32) = Word.ofAddress sp) (hg : 5000 ≤ gas)
    (hrev : msg.value ≠ 0 → ∀ mf out, Hf mf (.revert out))
    (hok : msg.value = 0 → ∀ mf out, out = Bytes.ofWord (w.sload msg.currentTarget
        (mappingSlot2 ctx.crypto (Word.ofAddress o) (Word.ofAddress sp) 4)) → mf.world = w →
      mf.transient = tr → mf.createdAccounts = cr → mf.frame.sub.logs = sub.logs →
      Hf mf (.success out)) :
    LowOK Hf (wethM ctx pre w tr ow cr msg sub snap k ps gas) := by
  have hsel' := div_selector msg.data
  rw [hsel] at hsel'
  have hlt := Dispatch.lt_calldatasize_four (n := msg.data.size) (by omega) (by omega)
  by_cases hv : msg.value = 0
  · low_steps [hsel', hlt, hv, harg0, harg1]
    low_step
    refine hok hv _ _ ?_ rfl rfl rfl rfl
    simp only [outputData, readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat,
      Nat.reduceMod, Nat.reducePow, Memory.read_storeWord]
    rfl
  · low_steps [hsel', hlt, iszero_of_ne hv, harg0, harg1]
    low_step
    exact hrev hv _ _

set_option maxHeartbeats 4000000 in
/-- **`totalSupply()`, every gas**: the contract's balance. -/
theorem totalSupply_low
    (hsel : Abi.selectorOf msg.data = 0x18160ddd) (hsize : 4 ≤ msg.data.size)
    (hsize' : msg.data.size < 2 ^ 64) (hg : 5000 ≤ gas)
    (hrev : msg.value ≠ 0 → ∀ mf out, Hf mf (.revert out))
    (hok : msg.value = 0 → ∀ mf out, out = Bytes.ofWord (w.balance msg.currentTarget) →
      mf.world = w → mf.transient = tr → mf.createdAccounts = cr →
      mf.frame.sub.logs = sub.logs → Hf mf (.success out)) :
    LowOK Hf (wethM ctx pre w tr ow cr msg sub snap k ps gas) := by
  have hsel' := div_selector msg.data
  rw [hsel] at hsel'
  have hlt := Dispatch.lt_calldatasize_four (n := msg.data.size) (by omega) (by omega)
  by_cases hv : msg.value = 0
  · cases hw : sub.accessedAddresses.contains msg.currentTarget
    all_goals
      low_steps [hsel', hlt, hv, hw, Word.toAddress_ofAddress, Gas.accessCost,
        Bool.false_eq_true, ↓reduceIte, Gas.warmAccess, Gas.coldAccountAccess]
      low_step
      refine hok hv _ _ ?_ rfl rfl rfl rfl
      simp only [outputData, readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat,
        Nat.reduceMod, Nat.reducePow, Memory.read_storeWord]
  · low_steps [hsel', hlt, iszero_of_ne hv]
    low_step
    exact hrev hv _ _

end Verified.WETH9.Spec
