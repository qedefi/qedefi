import Verified.WETH9.Spec.DepositLow
import Verified.WETH9.Spec.TransferLow
import Verified.WETH9.Spec.Frame
import Verified.WETH9.Spec.TransferFromLow
import Verified.WETH9.Spec.Abs

/-!
# WETH9's fallback on the bytecode, for every gas

`fallback_short_low` (calldata shorter than a selector, a plain ether transfer) and
`fallback_unknown_low` (a selector the dispatcher does not know): WETH9 runs `deposit()`, which
credits the value to the caller and logs `Deposit(caller, value)`; in a static frame its
`SSTORE` fails.
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.GasMono EvmLogic.Solidity Verified.WETH9.Contracts QEDefi.ERC4626
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.WETH9

variable {ctx : Context} {pre : PrecompileImpl} {w : World} {tr : TransientStorage}
  {ow : World} {cr : AddressSet} {msg : Message} {sub : Substate}
  {snap : World × TransientStorage} {k : FrameKind} {ps : List Frame} {gas : Nat}
  {Hf : Machine → Outcome → Prop}

theorem lt_calldatasize_short {n : Nat} (h : n < 4) :
    Word.lt (BitVec.ofNat 256 n) (BitVec.ofNat 256 4) = 1#256 :=
  lt_one_of_lt (by simp only [BitVec.toNat_ofNat]; omega)

set_option maxHeartbeats 8000000 in
/-- **The fallback with calldata shorter than a selector, every gas**: `deposit()`. -/
theorem fallback_short_low (hsize : msg.data.size < 4) (hg : 50000 ≤ gas)
    (hstat : msg.isStatic = true → ∀ mf e, Hf mf (.halt e))
    (hok : msg.isStatic = false → ∀ mf,
      mf.world = w.sstore msg.currentTarget (mappingSlot ctx.crypto (Word.ofAddress msg.caller) 3)
        (w.sload msg.currentTarget (mappingSlot ctx.crypto (Word.ofAddress msg.caller) 3) +
          msg.value) →
      mf.transient = tr → mf.createdAccounts = cr →
      mf.frame.sub.logs = sub.logs.push (depositLog9 msg.currentTarget msg.caller msg.value) →
      Hf mf (.success .empty)) :
    LowOK Hf (wethM ctx pre w tr ow cr msg sub snap k ps gas) := by
  have hlt := lt_calldatasize_short hsize
  cases hst : msg.isStatic
  · low_steps [hlt]
    low_step
    refine hok hst _ rfl rfl rfl ?_
    simp only [warmKey_logs, addRefund_logs, depositLog9, EvmLogic.Solidity.eventLog,
      encodeArgs_one, logEntry,
      readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      Memory.read_storeWord]
    rfl
  · low_steps [hlt]
    low_static hst
    exact hstat hst _

theorem selectorOf_lt (data : ByteArray) : Abi.selectorOf data < 2 ^ 32 := by
  have := Bytes.toNat_lt (readBytes data 0 4)
  rw [size_readBytes] at this
  unfold Abi.selectorOf; simpa using this

theorem eq_sel_ne {s c : Nat} (hs : s < 2 ^ 32) (hc : c < 2 ^ 32) (h : s ≠ c) :
    Word.eq (BitVec.ofNat 256 c) (BitVec.ofNat 256 s) = 0#256 ∧
      Word.eq (BitVec.ofNat 256 s) (BitVec.ofNat 256 c) = 0#256 := by
  have hne : BitVec.ofNat 256 s ≠ BitVec.ofNat 256 c := by
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact h this
  exact ⟨eq_ne_zero (Ne.symm hne), eq_ne_zero hne⟩

set_option maxHeartbeats 8000000 in
/-- **The fallback for a selector the dispatcher does not know, every gas**: `deposit()`. -/
theorem fallback_unknown_low (hsize : 4 ≤ msg.data.size) (hsize' : msg.data.size < 2 ^ 64)
    (hsel : Abi.selectorOf msg.data ∉ weth9Sel) (hg : 50000 ≤ gas)
    (hstat : msg.isStatic = true → ∀ mf e, Hf mf (.halt e))
    (hok : msg.isStatic = false → ∀ mf,
      mf.world = w.sstore msg.currentTarget (mappingSlot ctx.crypto (Word.ofAddress msg.caller) 3)
        (w.sload msg.currentTarget (mappingSlot ctx.crypto (Word.ofAddress msg.caller) 3) +
          msg.value) →
      mf.transient = tr → mf.createdAccounts = cr →
      mf.frame.sub.logs = sub.logs.push (depositLog9 msg.currentTarget msg.caller msg.value) →
      Hf mf (.success .empty)) :
    LowOK Hf (wethM ctx pre w tr ow cr msg sub snap k ps gas) := by
  have hsel' := div_selector msg.data
  have hlt := Dispatch.lt_calldatasize_four (n := msg.data.size) (by omega) (by omega)
  have hs := selectorOf_lt msg.data
  have h0 := eq_sel_ne hs (c := 0x06fdde03) (by decide) (by simp_all [weth9Sel, WETH9.selectors])
  have h1 := eq_sel_ne hs (c := 0x095ea7b3) (by decide) (by simp_all [weth9Sel, WETH9.selectors])
  have h2 := eq_sel_ne hs (c := 0x18160ddd) (by decide) (by simp_all [weth9Sel, WETH9.selectors])
  have h3 := eq_sel_ne hs (c := 0x23b872dd) (by decide) (by simp_all [weth9Sel, WETH9.selectors])
  have h4 := eq_sel_ne hs (c := 0x2e1a7d4d) (by decide) (by simp_all [weth9Sel, WETH9.selectors])
  have h5 := eq_sel_ne hs (c := 0x313ce567) (by decide) (by simp_all [weth9Sel, WETH9.selectors])
  have h6 := eq_sel_ne hs (c := 0x70a08231) (by decide) (by simp_all [weth9Sel, WETH9.selectors])
  have h7 := eq_sel_ne hs (c := 0x95d89b41) (by decide) (by simp_all [weth9Sel, WETH9.selectors])
  have h8 := eq_sel_ne hs (c := 0xa9059cbb) (by decide) (by simp_all [weth9Sel, WETH9.selectors])
  have h9 := eq_sel_ne hs (c := 0xd0e30db0) (by decide) (by simp_all [weth9Sel, WETH9.selectors])
  have h10 := eq_sel_ne hs (c := 0xdd62ed3e) (by decide) (by simp_all [weth9Sel, WETH9.selectors])
  cases hst : msg.isStatic
  · low_steps [hsel', hlt, h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2, h7.1, h7.2, h8.1, h8.2, h9.1, h9.2, h10.1, h10.2]
    low_step
    refine hok hst _ rfl rfl rfl ?_
    simp only [warmKey_logs, addRefund_logs, depositLog9, EvmLogic.Solidity.eventLog,
      encodeArgs_one, logEntry, readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat,
      Nat.reduceMod, Nat.reducePow, Memory.read_storeWord]
    rfl
  · low_steps [hsel', hlt, h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2, h7.1, h7.2, h8.1, h8.2, h9.1, h9.2, h10.1, h10.2]
    low_static hst
    exact hstat hst _

end Verified.WETH9.Spec
