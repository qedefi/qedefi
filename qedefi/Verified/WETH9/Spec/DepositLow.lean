import Verified.WETH9.Spec.ApproveLow

/-!
# WETH9's `deposit()` on the bytecode, for every gas

`deposit_low`: `deposit()` (payable) from a fresh frame, as a `LowOK` judgement: in a static
frame its `SSTORE` fails; otherwise it adds the frame's value to `balanceOf[caller]` (unchecked,
solc 0.4), logs `Deposit(caller, value)` (`depositLog9`, not an ERC-20 event) and stops with
empty return data.

This is what the spec's `OpSpec` (for `Op.deposit`) and `FallbackSpec` (the fallback runs the same
body) are about; see `Verified.WETH9.Spec.Spec` for why neither holds as stated.
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.Solidity Verified.WETH9.Contracts QEDefi.ERC4626

variable {ctx : Context} {pre : PrecompileImpl} {w : World} {tr : TransientStorage}
  {ow : World} {cr : AddressSet} {msg : Message} {sub : Substate}
  {snap : World × TransientStorage} {k : FrameKind} {ps : List Frame} {gas : Nat}
  {Hf : Machine → Outcome → Prop}

/-- `keccak256("Deposit(address,uint256)")`, WETH9's `Deposit` topic. -/
def depositTopic9 : Word :=
  0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c#256

/-- `Deposit(dst, wad)` emitted by WETH9 at `token`. -/
def depositLog9 (token dst : Address) (wad : Word) : Log :=
  eventLog token [depositTopic9, Word.ofAddress dst] [wad]

set_option maxHeartbeats 8000000 in
/-- **`deposit()`, every gas.** -/
theorem deposit_low (hsel : Abi.selectorOf msg.data = 0xd0e30db0) (hsize : 4 ≤ msg.data.size)
    (hsize' : msg.data.size < 2 ^ 64) (hg : 50000 ≤ gas)
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
  rw [hsel] at hsel'
  have hlt := Dispatch.lt_calldatasize_four (n := msg.data.size) (by omega) (by omega)
  cases hst : msg.isStatic
  · low_steps [hsel', hlt]
    low_step
    refine hok hst _ rfl rfl rfl ?_
    simp only [warmKey_logs, addRefund_logs, depositLog9, eventLog, encodeArgs_one, logEntry,
      readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      Memory.read_storeWord]
    rfl
  · low_steps [hsel', hlt]
    low_static hst
    exact hstat hst _

end Verified.WETH9.Spec
