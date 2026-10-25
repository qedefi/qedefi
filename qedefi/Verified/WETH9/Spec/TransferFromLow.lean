import Verified.WETH9.Spec.TransferLow

/-!
# WETH9's `transferFrom` on the bytecode, for every gas

`transferFrom_low`: `transferFrom(src, dst, wad)` from a fresh frame, as a `LowOK` judgement.
With value it reverts; `balanceOf[src] < wad` reverts; when `src` is the caller, or the
allowance `allowance[src][caller]` is `2²⁵⁶ − 1`, the allowance is skipped (`hokA`); otherwise
an allowance below `wad` reverts and a sufficient one is debited first (`hokB`). Then
`balanceOf[src] -= wad`, `balanceOf[dst] += wad` (read after the debit), `Transfer(src, dst,
wad)`, `true`. In a static frame the first `SSTORE` fails.
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.Solidity Verified.WETH9.Contracts QEDefi.ERC4626

variable {ctx : Context} {pre : PrecompileImpl} {w : World} {tr : TransientStorage}
  {ow : World} {cr : AddressSet} {msg : Message} {sub : Substate}
  {snap : World × TransientStorage} {k : FrameKind} {ps : List Frame} {gas : Nat}
  {Hf : Machine → Outcome → Prop}

/-- `2²⁵⁶ − 1`, the allowance `transferFrom` does not spend. -/
abbrev maxWord : Word := BitVec.ofNat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935

theorem eq_ne_zero {x y : Word} (h : x ≠ y) : Word.eq x y = 0#256 := by
  have : (x == y) = false := by simpa using h
  simp [Word.eq, Word.ofBool, this]

/-- The world after a move of `wad` from `src` to `dst` (the debit, then the credit read after
it), on WETH9's `balanceOf` rows. -/
def moveWorld (crypto : Crypto) (token src dst : Address) (wad : Word) (w : World) : World :=
  (w.sstore token (mappingSlot crypto (Word.ofAddress src) 3)
      (w.sload token (mappingSlot crypto (Word.ofAddress src) 3) - wad)).sstore token
    (mappingSlot crypto (Word.ofAddress dst) 3)
    ((w.sstore token (mappingSlot crypto (Word.ofAddress src) 3)
      (w.sload token (mappingSlot crypto (Word.ofAddress src) 3) - wad)).sload token
        (mappingSlot crypto (Word.ofAddress dst) 3) + wad)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
/-- **`transferFrom(src, dst, wad)`, every gas.** -/
theorem transferFrom_low (src dst : Address) (wad bal al : Word)
    (hsel : Abi.selectorOf msg.data = 0x23b872dd) (hsize : 100 ≤ msg.data.size)
    (hsize' : msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes msg.data 4 32) = Word.ofAddress src)
    (harg1 : Bytes.toWord (readBytes msg.data 36 32) = Word.ofAddress dst)
    (harg2 : Bytes.toWord (readBytes msg.data 68 32) = wad) (hg : 100000 ≤ gas)
    (hbal : w.sload msg.currentTarget (mappingSlot ctx.crypto (Word.ofAddress src) 3) = bal)
    (hal : w.sload msg.currentTarget
      (mappingSlot2 ctx.crypto (Word.ofAddress src) (Word.ofAddress msg.caller) 4) = al)
    (hrev : (msg.value ≠ 0 ∨ bal.toNat < wad.toNat ∨
        (src ≠ msg.caller ∧ al ≠ maxWord ∧ al.toNat < wad.toNat)) →
      ∀ mf out, Hf mf (.revert out))
    (hstat : msg.value = 0 → msg.isStatic = true → ∀ mf e, Hf mf (.halt e))
    (hokA : msg.value = 0 → msg.isStatic = false → wad.toNat ≤ bal.toNat →
      (src = msg.caller ∨ al = maxWord) → ∀ mf out, out = Bytes.ofWord 1 →
      mf.world = moveWorld ctx.crypto msg.currentTarget src dst wad w →
      mf.transient = tr → mf.createdAccounts = cr →
      mf.frame.sub.logs = sub.logs.push (transferLog msg.currentTarget src dst wad) →
      Hf mf (.success out))
    (hokB : msg.value = 0 → msg.isStatic = false → wad.toNat ≤ bal.toNat → src ≠ msg.caller →
      al ≠ maxWord → wad.toNat ≤ al.toNat → ∀ mf out, out = Bytes.ofWord 1 →
      mf.world = moveWorld ctx.crypto msg.currentTarget src dst wad
        (w.sstore msg.currentTarget
          (mappingSlot2 ctx.crypto (Word.ofAddress src) (Word.ofAddress msg.caller) 4)
          (al - wad)) →
      mf.transient = tr → mf.createdAccounts = cr →
      mf.frame.sub.logs = sub.logs.push (transferLog msg.currentTarget src dst wad) →
      Hf mf (.success out)) :
    LowOK Hf (wethM ctx pre w tr ow cr msg sub snap k ps gas) := by
  have hsel' := div_selector msg.data
  rw [hsel] at hsel'
  have hlt := Dispatch.lt_calldatasize_four (n := msg.data.size) (by omega) (by omega)
  have hbal' : w.sload msg.currentTarget (ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord (BitVec.ofNat 256 3))) = bal := hbal
  have hal' : w.sload msg.currentTarget (ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress msg.caller) ++ Bytes.ofWord (ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord (BitVec.ofNat 256 4))))) = al := hal
  by_cases hv : msg.value = 0
  · by_cases hb : wad.toNat ≤ bal.toNat
    · by_cases hsc : src = msg.caller
      · subst hsc
        cases hst : msg.isStatic
        · low_steps [hsel', hlt, hv, harg0, harg1, harg2, hbal', lt_zero_of_le hb]
          low_step
          refine hokA hv hst hb (.inl rfl) _ _ ?_ ?_ rfl rfl ?_
          · simp only [outputData, readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat,
              Nat.reduceMod, Nat.reducePow, Memory.read_storeWord]
            rfl
          · rw [moveWorld, hbal]; rfl
          · simp only [outputMachine, warmKey_logs, addRefund_logs, transferLog, eventLog,
              encodeArgs_one, logEntry, readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat,
              Nat.reduceMod, Nat.reducePow, Memory.read_storeWord]
            rfl
        · low_steps [hsel', hlt, hv, harg0, harg1, harg2, hbal', lt_zero_of_le hb]
          low_static hst
          exact hstat hv hst _
      · have heq := eq_ofAddress_ne hsc
        by_cases hm : al = maxWord
        · cases hst : msg.isStatic
          · low_steps [hsel', hlt, hv, harg0, harg1, harg2, hbal', hal', hm, heq,
              lt_zero_of_le hb]
            low_step
            refine hokA hv hst hb (.inr hm) _ _ ?_ ?_ rfl rfl ?_
            · simp only [outputData, readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat,
                Nat.reduceMod, Nat.reducePow, Memory.read_storeWord]
              rfl
            · rw [moveWorld, hbal]; rfl
            · simp only [outputMachine, warmKey_logs, addRefund_logs, transferLog, eventLog,
                encodeArgs_one, logEntry, readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat,
                Nat.reduceMod, Nat.reducePow, Memory.read_storeWord]
              rfl
          · low_steps [hsel', hlt, hv, harg0, harg1, harg2, hbal', hal', hm, heq,
              lt_zero_of_le hb]
            low_static hst
            exact hstat hv hst _
        · by_cases ha : wad.toNat ≤ al.toNat
          · cases hst : msg.isStatic
            · low_steps [hsel', hlt, hv, harg0, harg1, harg2, hbal', hal', heq,
                eq_ne_zero hm, eq_ne_zero (Ne.symm hm), lt_zero_of_le hb, lt_zero_of_le ha]
              low_step
              refine hokB hv hst hb hsc hm ha _ _ ?_ ?_ rfl rfl ?_
              · simp only [outputData, readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat,
                  Nat.reduceMod, Nat.reducePow, Memory.read_storeWord]
                rfl
              · rw [moveWorld]; rfl
              · simp only [outputMachine, warmKey_logs, addRefund_logs, transferLog, eventLog,
                  encodeArgs_one, logEntry, readBytes_bytes, Memory.read_expand, BitVec.toNat_ofNat,
                  Nat.reduceMod, Nat.reducePow, Memory.read_storeWord]
                rfl
            · low_steps [hsel', hlt, hv, harg0, harg1, harg2, hbal', hal', heq,
                eq_ne_zero hm, eq_ne_zero (Ne.symm hm), lt_zero_of_le hb, lt_zero_of_le ha]
              low_static hst
              exact hstat hv hst _
          · low_steps [hsel', hlt, hv, harg0, harg1, harg2, hbal', hal', heq,
              eq_ne_zero hm, eq_ne_zero (Ne.symm hm), lt_zero_of_le hb,
              lt_one_of_lt (Nat.lt_of_not_le ha)]
            low_step
            exact hrev (.inr (.inr ⟨hsc, hm, Nat.lt_of_not_le ha⟩)) _ _
    · low_steps [hsel', hlt, hv, harg0, harg1, harg2, hbal',
        lt_one_of_lt (Nat.lt_of_not_le hb)]
      low_step
      exact hrev (.inr (.inl (Nat.lt_of_not_le hb))) _ _
  · low_steps [hsel', hlt, iszero_of_ne hv, harg0, harg1, harg2]
    low_step
    exact hrev (.inl hv) _ _

end Verified.WETH9.Spec
