import Verified.WETH9.Spec.ApproveLow

/-!
# WETH9's `transfer` on the bytecode, for every gas

`transfer_low`: `transfer(dst, wad)` from a fresh frame, as a `LowOK` judgement. WETH9's
`transfer` is `transferFrom(msg.sender, dst, wad)` (an internal jump), so the allowance is
skipped: with value it reverts; if `balanceOf[caller] < wad` it reverts; in a static frame the
first `SSTORE` fails; otherwise it writes `balanceOf[caller] -= wad`, then
`balanceOf[dst] += wad` (reading `dst`'s row after the first write, unchecked: solc 0.4), logs
`Transfer(caller, dst, wad)` and returns `true`.
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.Solidity Verified.WETH9.Contracts QEDefi.ERC4626

variable {ctx : Context} {pre : PrecompileImpl} {w : World} {tr : TransientStorage}
  {ow : World} {cr : AddressSet} {msg : Message} {sub : Substate}
  {snap : World × TransientStorage} {k : FrameKind} {ps : List Frame} {gas : Nat}
  {Hf : Machine → Outcome → Prop}

theorem eq_ofAddress_ne {a b : Address} (h : a ≠ b) :
    Word.eq (Word.ofAddress a) (Word.ofAddress b) = 0#256 := by
  have : (Word.ofAddress a == Word.ofAddress b) = false := by
    simpa using fun e => h (Word.ofAddress_injective e)
  simp [Word.eq, Word.ofBool, this]

theorem lt_zero_of_le {x y : Word} (h : y.toNat ≤ x.toNat) : Word.lt x y = 0#256 :=
  (Word.lt_eq_zero_iff x y).2 h

theorem lt_one_of_lt {x y : Word} (h : x.toNat < y.toNat) : Word.lt x y = 1#256 :=
  (Word.lt_eq_one_iff x y).2 h

set_option maxHeartbeats 20000000 in
/-- **`transfer(dst, wad)`, every gas.** -/
theorem transfer_low (dst : Address) (wad bal : Word)
    (hsel : Abi.selectorOf msg.data = 0xa9059cbb) (hsize : 68 ≤ msg.data.size)
    (hsize' : msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes msg.data 4 32) = Word.ofAddress dst)
    (harg1 : Bytes.toWord (readBytes msg.data 36 32) = wad) (hg : 100000 ≤ gas)
    (hbal : w.sload msg.currentTarget (mappingSlot ctx.crypto (Word.ofAddress msg.caller) 3) = bal)
    (hrev : (msg.value ≠ 0 ∨ bal.toNat < wad.toNat) → ∀ mf out, Hf mf (.revert out))
    (hstat : msg.value = 0 → msg.isStatic = true → ∀ mf e, Hf mf (.halt e))
    (hok : msg.value = 0 → msg.isStatic = false → wad.toNat ≤ bal.toNat → ∀ mf out,
      out = Bytes.ofWord 1 →
      mf.world =
        (w.sstore msg.currentTarget (mappingSlot ctx.crypto (Word.ofAddress msg.caller) 3)
          (bal - wad)).sstore msg.currentTarget (mappingSlot ctx.crypto (Word.ofAddress dst) 3)
          ((w.sstore msg.currentTarget (mappingSlot ctx.crypto (Word.ofAddress msg.caller) 3)
            (bal - wad)).sload msg.currentTarget
              (mappingSlot ctx.crypto (Word.ofAddress dst) 3) + wad) →
      mf.transient = tr → mf.createdAccounts = cr →
      mf.frame.sub.logs = sub.logs.push (transferLog msg.currentTarget msg.caller dst wad) →
      Hf mf (.success out)) :
    LowOK Hf (wethM ctx pre w tr ow cr msg sub snap k ps gas) := by
  have hsel' := div_selector msg.data
  rw [hsel] at hsel'
  have hlt := Dispatch.lt_calldatasize_four (n := msg.data.size) (by omega) (by omega)
  have hbal' : w.sload msg.currentTarget (ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress msg.caller) ++ Bytes.ofWord (BitVec.ofNat 256 3))) = bal := hbal
  by_cases hv : msg.value = 0
  · by_cases hb : wad.toNat ≤ bal.toNat
    · cases hst : msg.isStatic
      · low_steps [hsel', hlt, hv, harg0, harg1, hbal', lt_zero_of_le hb]
        low_step
        refine hok hv hst hb _ _ ?_ rfl rfl rfl ?_
        · simp only [outputData, readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat,
            Nat.reduceMod, Nat.reducePow, Memory.read_storeWord]
          rfl
        · simp only [outputMachine, warmKey_logs, addRefund_logs, transferLog, eventLog,
            encodeArgs_one, logEntry, readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat,
            Nat.reduceMod, Nat.reducePow, Memory.read_storeWord]
          rfl
      · low_steps [hsel', hlt, hv, harg0, harg1, hbal', lt_zero_of_le hb]
        low_static hst
        exact hstat hv hst _
    · low_steps [hsel', hlt, hv, harg0, harg1, hbal', lt_one_of_lt (Nat.lt_of_not_le hb)]
      low_step
      exact hrev (.inr (Nat.lt_of_not_le hb)) _ _
  · low_steps [hsel', hlt, iszero_of_ne hv, harg0, harg1]
    low_step
    exact hrev (.inl hv) _ _

end Verified.WETH9.Spec
