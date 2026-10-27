import Verified.WeirdERC20.USDT.Spec.TransferRun

/-!
# USDT `transfer(dst, v)` on the lift: the symbolic run

`transfer_high`: the lift of a `transfer` frame reaches, along every branch of the code, an
exit described by `TransferOut`.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.WeirdERC20.USDT.Contracts EvmLogic.Program.Nested EvmLogic.GasMono
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math QEDefi.ERC4626

set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
/-- **`transfer(dst, v)`** on the lift. -/
theorem transfer_high (m : Machine) (hf : Fresh USDT.runtimeCode m) (d : Nat) (dst : Address)
    (v : Word) (hg : g₀ ≤ m.frame.gasLeft + d)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb)
    (hsize : 68 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress dst)
    (harg1 : Bytes.toWord (readBytes m.frame.msg.data 36 32) = v)
    (hdep : m.frame.msg.value = 0 →
      deprecatedField.get (m.world.sload m.frame.msg.currentTarget 10#256) = 0) :
    WP (lift patchedCode d m) (fun mh' => mh'.frame.pc ∉ patchPcs ∧
      ExitsWith (TransferOut dst v m) mh') (fun _ _ => False) := by
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have h68 := lt_size_le (k := 68) hsize (by omega)
  simp only [deprecatedField_get] at hdep
  simp only [g₀] at hg
  by_cases hval : m.frame.msg.value = 0
  swap
  · have hz := iszero_value hval
    lift_intro
    usdt_run [hz, hsel', hlt, Memory.read_64, div_selector]
    usdt_revert
    exact .inl ⟨hval, trivial⟩
  have hdep := hdep hval
  lift_intro
  usdt_run [hval, hsel', hlt, Memory.read_64, div_selector, expCost_20, expCost_0, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, h68]
  -- `whenNotPaused`
  by_cases hp : pausedW m_world m_msg.currentTarget = 0#256
  swap
  · simp only [iszero_of_ne hp, Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    usdt_revert
    exact .inr (.inr ⟨hval, .inl ⟨hp, _, rfl⟩⟩)
  simp only [hp, Solidity.iszero_zero, Solidity.iszero_one]
  xrun
  -- `require(!isBlackListed[msg.sender])`
  by_cases hb : blackW m_ctx.crypto m_world m_msg.currentTarget m_msg.caller = 0#256
  swap
  · simp only [iszero_of_ne hb, Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    usdt_revert
    exact .inr (.inr ⟨hval, .inr (.inl ⟨hp, hb, _, rfl⟩)⟩)
  simp only [hb, Solidity.iszero_zero, Solidity.iszero_one]
  xrun
  simp only [hdep]
  usdt_gas 185000
  xrun [h68]
  by_cases hv0 : v = 0#256
  · have heq : Word.eq v 0#256 = 1#256 := by rw [hv0]; exact Solidity.eq_self _
    simp only [heq, Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    simp only [gt_zero (x := 0#256) (Nat.zero_le _), Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    have hfee : xferFee m_world m_msg.currentTarget v = 0#256 := by rw [hv0]; exact xferFee_zero _ _
    usdt_gas 175000
    simp only [gt_zero (x := 0#256) (y := v) (Nat.zero_le _), Solidity.iszero_zero,
      Solidity.iszero_one]
    xrun
    have hbal : v.toNat ≤ (m_world.sload m_msg.currentTarget
        (balKey m_ctx.crypto m_msg.caller)).toNat := by rw [hv0]; exact Nat.zero_le _
    simp only [gt_zero hbal, Solidity.iszero_zero, Solidity.iszero_one]
    usdt_gas 170000
    xrun
    by_cases hst : m_msg.isStatic = true
    · usdt_static
      exact .inr (.inl ⟨hst, trivial⟩)
    have hst' : m_msg.isStatic = false := by simpa using hst
    xrun
    generalize hW1 : m_world.sstore m_msg.currentTarget (balKey m_ctx.crypto m_msg.caller)
      (m_world.sload m_msg.currentTarget (balKey m_ctx.crypto m_msg.caller) - v) = W1
    generalize hA : W1.sload m_msg.currentTarget (balKey m_ctx.crypto dst) = A
    have hadd : A.toNat + (v - 0#256).toNat < 2 ^ 256 := by
      rw [hv0]; have := A.isLt; simp only [BitVec.sub_zero, BitVec.toNat_ofNat]; omega
    simp only [lt_add_zero hadd, Solidity.iszero_zero, Solidity.iszero_one]
    usdt_gas 140000
    xrun
    usdt_stop
    subst hA hW1
    refine .inr (.inr ⟨hval, .inr (.inr (.inr ⟨hp, hb, ?_, rfl, ?_, rfl, rfl, ?_⟩))⟩)
    · intro h
      unfold xferArithFail at h
      dsimp only at h
      rw [hfee] at h
      simp only [xferW1, xferW2] at h
      rcases h with h | h | h | h | ⟨h, -⟩
      · rw [hv0] at h; simp at h
      · simp at h
      · omega
      · omega
      · exact h rfl
    · dsimp only
      rw [hfee]
      simp only [xferW3, ↓reduceIte]
    · dsimp only
      rw [hfee]
      simp only [xferLogs, ↓reduceIte]
      event_log [v - 0#256]
  simp only [eq_of_ne hv0, Solidity.iszero_zero, Solidity.iszero_one]
  xrun
  simp only [iszero_of_ne hv0, Solidity.iszero_zero, Solidity.iszero_one]
  xrun
  by_cases hno : v.toNat * (m_world.sload m_msg.currentTarget 3#256).toNat < 2 ^ 256
  swap
  · simp only [mul_div_eq_zero (Nat.le_of_not_lt hno), Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    usdt_invalid
    exact .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb, .inl (Nat.le_of_not_lt hno), _, rfl⟩))⟩)
  simp only [mul_div_eq_one hv0 hno, Solidity.iszero_zero, Solidity.iszero_one]
  xrun
  by_cases hfm : (m_world.sload m_msg.currentTarget 4#256).toNat <
      (fee0W m_world m_msg.currentTarget v).toNat
  · simp only [gt_one hfm, Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    have hfee : xferFee m_world m_msg.currentTarget v = m_world.sload m_msg.currentTarget 4#256 := by
      simp only [xferFee, hfm, ↓reduceIte]
    usdt_gas 175000
    by_cases hfv : (m_world.sload m_msg.currentTarget 4#256).toNat ≤ v.toNat
    swap
    · simp only [gt_one (Nat.lt_of_not_le hfv), Solidity.iszero_zero, Solidity.iszero_one]
      xrun
      usdt_invalid
      exact .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb,
        .inr (.inl (by rw [hfee]; exact Nat.lt_of_not_le hfv)), _, rfl⟩))⟩)
    simp only [gt_zero hfv, Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    by_cases hbal : v.toNat ≤ (m_world.sload m_msg.currentTarget
        (balKey m_ctx.crypto m_msg.caller)).toNat
    swap
    · simp only [gt_one (Nat.lt_of_not_le hbal), Solidity.iszero_zero, Solidity.iszero_one]
      xrun
      usdt_invalid
      exact .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb,
        .inr (.inr (.inl (Nat.lt_of_not_le hbal))), _, rfl⟩))⟩)
    simp only [gt_zero hbal, Solidity.iszero_zero, Solidity.iszero_one]
    usdt_gas 170000
    xrun
    by_cases hst : m_msg.isStatic = true
    · usdt_static
      exact .inr (.inl ⟨hst, trivial⟩)
    have hst' : m_msg.isStatic = false := by simpa using hst
    xrun
    generalize hW1 : m_world.sstore m_msg.currentTarget (balKey m_ctx.crypto m_msg.caller)
      (m_world.sload m_msg.currentTarget (balKey m_ctx.crypto m_msg.caller) - v) = W1
    generalize hA : W1.sload m_msg.currentTarget (balKey m_ctx.crypto dst) = A
    by_cases hadd : A.toNat + (v - m_world.sload m_msg.currentTarget 4#256).toNat < 2 ^ 256
    swap
    · simp only [lt_add_one (Nat.le_of_not_lt hadd), Solidity.iszero_zero, Solidity.iszero_one]
      xrun
      usdt_invalid
      subst hA hW1
      exact .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb,
        .inr (.inr (.inr (.inl (by rw [hfee]; exact Nat.le_of_not_lt hadd)))), _, rfl⟩))⟩)
    simp only [lt_add_zero hadd, Solidity.iszero_zero, Solidity.iszero_one]
    usdt_gas 140000
    xrun
    by_cases hf0 : m_world.sload m_msg.currentTarget 4#256 = 0#256
    · simp only [hf0, gt_zero (x := 0#256) (y := 0#256) (Nat.le_refl _), Solidity.iszero_zero,
        Solidity.iszero_one]
      xrun
      usdt_stop
      subst hA hW1
      refine .inr (.inr ⟨hval, .inr (.inr (.inr ⟨hp, hb, ?_, rfl, ?_, rfl, rfl, ?_⟩))⟩)
      · intro h
        unfold xferArithFail at h
        dsimp only at h
        rw [hfee] at h
        simp only [xferW1, xferW2] at h
        rcases h with h | h | h | h | ⟨h, -⟩
        · omega
        · omega
        · omega
        · omega
        · exact h hf0
      · dsimp only
        rw [hfee, hf0]
        simp only [xferW3, ↓reduceIte]
      · dsimp only
        rw [hfee, hf0]
        simp only [xferLogs, ↓reduceIte]
        event_log [v - 0#256]
    have hpos : (0#256).toNat < (m_world.sload m_msg.currentTarget 4#256).toNat := by
      rcases Nat.eq_zero_or_pos (m_world.sload m_msg.currentTarget 4#256).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hf0
      · simpa using h
    simp only [gt_one hpos, Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    generalize hW2 : W1.sstore m_msg.currentTarget (balKey m_ctx.crypto dst) (A + (v - m_world.sload m_msg.currentTarget 4#256)) = W2
    generalize hB : W2.sload m_msg.currentTarget (ownerKey m_ctx.crypto W2 m_msg.currentTarget) = B
    by_cases hadd2 : B.toNat + (m_world.sload m_msg.currentTarget 4#256).toNat < 2 ^ 256
    swap
    · simp only [lt_add_one (Nat.le_of_not_lt hadd2), Solidity.iszero_zero, Solidity.iszero_one]
      xrun
      usdt_invalid
      subst hB hW2 hA hW1
      refine .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb, ?_, _, rfl⟩))⟩)
      unfold xferArithFail
      dsimp only
      rw [hfee]
      exact .inr (.inr (.inr (.inr ⟨hf0, Nat.le_of_not_lt hadd2⟩)))
    simp only [lt_add_zero hadd2, Solidity.iszero_zero, Solidity.iszero_one]
    usdt_gas 100000
    xrun
    usdt_stop
    subst hB hW2 hA hW1
    refine .inr (.inr ⟨hval, .inr (.inr (.inr ⟨hp, hb, ?_, rfl, ?_, rfl, rfl, ?_⟩))⟩)
    · intro h
      unfold xferArithFail at h
      dsimp only at h
      rw [hfee] at h
      simp only [xferW1, xferW2] at h
      rcases h with h | h | h | h | ⟨-, h⟩
      · omega
      · omega
      · omega
      · omega
      · omega
    · dsimp only
      rw [hfee]
      simp only [xferW3, hf0, ↓reduceIte]
    · dsimp only
      rw [hfee]
      simp only [xferLogs, xferW3, hf0, ↓reduceIte]
      rw [logEntry_eq_eventLog (data := [m_world.sload m_msg.currentTarget 4#256]), logEntry_eq_eventLog (data := [v - m_world.sload m_msg.currentTarget 4#256])]
      · logs_simp []
        simp only [transferLog, transferTopic, ownerKey]
      · event_data
      · event_data
  · simp only [gt_zero (Nat.le_of_not_lt hfm), Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    have hfee : xferFee m_world m_msg.currentTarget v = fee0W m_world m_msg.currentTarget v := by
      simp only [xferFee, hfm, ↓reduceIte]
    usdt_gas 175000
    by_cases hfv : (fee0W m_world m_msg.currentTarget v).toNat ≤ v.toNat
    swap
    · simp only [gt_one (Nat.lt_of_not_le hfv), Solidity.iszero_zero, Solidity.iszero_one]
      xrun
      usdt_invalid
      exact .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb,
        .inr (.inl (by rw [hfee]; exact Nat.lt_of_not_le hfv)), _, rfl⟩))⟩)
    simp only [gt_zero hfv, Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    by_cases hbal : v.toNat ≤ (m_world.sload m_msg.currentTarget
        (balKey m_ctx.crypto m_msg.caller)).toNat
    swap
    · simp only [gt_one (Nat.lt_of_not_le hbal), Solidity.iszero_zero, Solidity.iszero_one]
      xrun
      usdt_invalid
      exact .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb,
        .inr (.inr (.inl (Nat.lt_of_not_le hbal))), _, rfl⟩))⟩)
    simp only [gt_zero hbal, Solidity.iszero_zero, Solidity.iszero_one]
    usdt_gas 170000
    xrun
    by_cases hst : m_msg.isStatic = true
    · usdt_static
      exact .inr (.inl ⟨hst, trivial⟩)
    have hst' : m_msg.isStatic = false := by simpa using hst
    xrun
    generalize hW1 : m_world.sstore m_msg.currentTarget (balKey m_ctx.crypto m_msg.caller)
      (m_world.sload m_msg.currentTarget (balKey m_ctx.crypto m_msg.caller) - v) = W1
    generalize hA : W1.sload m_msg.currentTarget (balKey m_ctx.crypto dst) = A
    by_cases hadd : A.toNat + (v - fee0W m_world m_msg.currentTarget v).toNat < 2 ^ 256
    swap
    · simp only [lt_add_one (Nat.le_of_not_lt hadd), Solidity.iszero_zero, Solidity.iszero_one]
      xrun
      usdt_invalid
      subst hA hW1
      exact .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb,
        .inr (.inr (.inr (.inl (by rw [hfee]; exact Nat.le_of_not_lt hadd)))), _, rfl⟩))⟩)
    simp only [lt_add_zero hadd, Solidity.iszero_zero, Solidity.iszero_one]
    usdt_gas 140000
    xrun
    by_cases hf0 : fee0W m_world m_msg.currentTarget v = 0#256
    · simp only [hf0, gt_zero (x := 0#256) (y := 0#256) (Nat.le_refl _), Solidity.iszero_zero,
        Solidity.iszero_one]
      xrun
      usdt_stop
      subst hA hW1
      refine .inr (.inr ⟨hval, .inr (.inr (.inr ⟨hp, hb, ?_, rfl, ?_, rfl, rfl, ?_⟩))⟩)
      · intro h
        unfold xferArithFail at h
        dsimp only at h
        rw [hfee] at h
        simp only [xferW1, xferW2] at h
        rcases h with h | h | h | h | ⟨h, -⟩
        · omega
        · omega
        · omega
        · omega
        · exact h hf0
      · dsimp only
        rw [hfee, hf0]
        simp only [xferW3, ↓reduceIte]
      · dsimp only
        rw [hfee, hf0]
        simp only [xferLogs, ↓reduceIte]
        event_log [v - 0#256]
    have hpos : (0#256).toNat < (fee0W m_world m_msg.currentTarget v).toNat := by
      rcases Nat.eq_zero_or_pos (fee0W m_world m_msg.currentTarget v).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hf0
      · simpa using h
    simp only [gt_one hpos, Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    generalize hW2 : W1.sstore m_msg.currentTarget (balKey m_ctx.crypto dst) (A + (v - fee0W m_world m_msg.currentTarget v)) = W2
    generalize hB : W2.sload m_msg.currentTarget (ownerKey m_ctx.crypto W2 m_msg.currentTarget) = B
    by_cases hadd2 : B.toNat + (fee0W m_world m_msg.currentTarget v).toNat < 2 ^ 256
    swap
    · simp only [lt_add_one (Nat.le_of_not_lt hadd2), Solidity.iszero_zero, Solidity.iszero_one]
      xrun
      usdt_invalid
      subst hB hW2 hA hW1
      refine .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb, ?_, _, rfl⟩))⟩)
      unfold xferArithFail
      dsimp only
      rw [hfee]
      exact .inr (.inr (.inr (.inr ⟨hf0, Nat.le_of_not_lt hadd2⟩)))
    simp only [lt_add_zero hadd2, Solidity.iszero_zero, Solidity.iszero_one]
    usdt_gas 100000
    xrun
    usdt_stop
    subst hB hW2 hA hW1
    refine .inr (.inr ⟨hval, .inr (.inr (.inr ⟨hp, hb, ?_, rfl, ?_, rfl, rfl, ?_⟩))⟩)
    · intro h
      unfold xferArithFail at h
      dsimp only at h
      rw [hfee] at h
      simp only [xferW1, xferW2] at h
      rcases h with h | h | h | h | ⟨-, h⟩
      · omega
      · omega
      · omega
      · omega
      · omega
    · dsimp only
      rw [hfee]
      simp only [xferW3, hf0, ↓reduceIte]
    · dsimp only
      rw [hfee]
      simp only [xferLogs, xferW3, hf0, ↓reduceIte]
      rw [logEntry_eq_eventLog (data := [fee0W m_world m_msg.currentTarget v]), logEntry_eq_eventLog (data := [v - fee0W m_world m_msg.currentTarget v])]
      · logs_simp []
        simp only [transferLog, transferTopic, ownerKey]
      · event_data
      · event_data

end Verified.WeirdERC20.USDT.Spec
