import Verified.WeirdERC20.USDT.Spec.TransferFromRun

/-!
# USDT `transferFrom(src, dst, v)` on the lift: the symbolic run

`transferFrom_high`: the lift of a `transferFrom` frame reaches, along every branch of the code,
an exit described by `TransferFromOut`.

The three ways to the fee (`v = 0`, the fee capped at `maximumFee`, the fee `v · bps / 10000`)
join before the allowance step, and the two allowance steps (spent, or `MAX_UINT`) join before
the balance moves; `tf_allow` and `tf_tail` run those shared stretches once the fee (and the world
after the allowance step) is a single term.
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.WeirdERC20.USDT.Contracts EvmLogic.Program.Nested EvmLogic.GasMono
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math QEDefi.ERC4626

set_option hygiene false in
/-- The balance moves of `transferFrom` (from `value.sub(fee)` on), with `W` the world after the
allowance step (`hW0 : tfW0 … = W`), `F` the fee (`hfee : xferFee … = F`), and `hok`, `hnomul`
ruling out the allowance's and the `mul`'s failures. -/
macro "tf_tail " W:term:max F:term:max : tactic => `(tactic| (
  usdt_gas 140000
  by_cases hfv : ($F).toNat ≤ v.toNat
  swap
  · simp only [gt_one (Nat.lt_of_not_le hfv), Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    usdt_invalid
    refine .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb, ?_, _, rfl⟩))⟩)
    unfold tfArithFail
    dsimp only
    rw [hW0, hfee]
    exact .inr (.inr (.inl (Nat.lt_of_not_le hfv)))
  simp only [gt_zero hfv, Solidity.iszero_zero, Solidity.iszero_one]
  xrun
  by_cases hbal : v.toNat ≤ (($W).sload m_msg.currentTarget (balKey m_ctx.crypto src)).toNat
  swap
  · simp only [gt_one (Nat.lt_of_not_le hbal), Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    usdt_invalid
    refine .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb, ?_, _, rfl⟩))⟩)
    unfold tfArithFail
    dsimp only
    rw [hW0, hfee]
    exact .inr (.inr (.inr (.inl (Nat.lt_of_not_le hbal))))
  simp only [gt_zero hbal, Solidity.iszero_zero, Solidity.iszero_one]
  usdt_gas 135000
  xrun
  by_cases hst : m_msg.isStatic = true
  · usdt_static
    exact .inr (.inl ⟨hst, trivial⟩)
  have hst' : m_msg.isStatic = false := by simpa using hst
  xrun
  generalize hW1 : ($W).sstore m_msg.currentTarget (balKey m_ctx.crypto src)
    (($W).sload m_msg.currentTarget (balKey m_ctx.crypto src) - v) = W1
  generalize hA : W1.sload m_msg.currentTarget (balKey m_ctx.crypto dst) = A
  by_cases hadd : A.toNat + (v - $F).toNat < 2 ^ 256
  swap
  · simp only [lt_add_one (Nat.le_of_not_lt hadd), Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    usdt_invalid
    subst hA hW1
    refine .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb, ?_, _, rfl⟩))⟩)
    unfold tfArithFail
    dsimp only
    rw [hW0, hfee]
    exact .inr (.inr (.inr (.inr (.inl (Nat.le_of_not_lt hadd)))))
  simp only [lt_add_zero hadd, Solidity.iszero_zero, Solidity.iszero_one]
  usdt_gas 105000
  xrun
  by_cases hf0 : $F = 0#256
  · -- with a literal zero fee the stepper has already decided `fee > 0`
    try simp only [hf0, gt_zero (x := 0#256) (y := 0#256) (Nat.le_refl _), Solidity.iszero_zero,
      Solidity.iszero_one]
    try xrun
    usdt_stop
    subst hA hW1
    refine .inr (.inr ⟨hval, .inr (.inr (.inr ⟨hp, hb, ?_, rfl, ?_, rfl, rfl, ?_⟩))⟩)
    · intro h
      unfold tfArithFail at h
      dsimp only at h
      rw [hW0, hfee, hAl] at h
      simp only [xferW1, xferW2] at h
      rcases h with h | h | h | h | h | ⟨h, -⟩
      · omega
      · exact hok h
      · omega
      · omega
      · omega
      · exact h hf0
    · dsimp only
      rw [hW0, hfee]
      try rw [hf0]
      simp only [xferW3, ↓reduceIte]
    · dsimp only
      rw [hW0, hfee]
      try rw [hf0]
      simp only [xferLogs, ↓reduceIte]
      event_log [v - 0#256]
  first
  | exact absurd rfl hf0
  | (
      have hpos : (0#256).toNat < ($F).toNat := by
        rcases Nat.eq_zero_or_pos ($F).toNat with h | h
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hf0
        · simpa using h
      simp only [gt_one hpos, Solidity.iszero_zero, Solidity.iszero_one]
      xrun
      generalize hW2 : W1.sstore m_msg.currentTarget (balKey m_ctx.crypto dst) (A + (v - $F)) = W2
      generalize hB : W2.sload m_msg.currentTarget (ownerKey m_ctx.crypto W2 m_msg.currentTarget) = B
      by_cases hadd2 : B.toNat + ($F).toNat < 2 ^ 256
      swap
      · simp only [lt_add_one (Nat.le_of_not_lt hadd2), Solidity.iszero_zero, Solidity.iszero_one]
        xrun
        usdt_invalid
        subst hB hW2 hA hW1
        refine .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb, ?_, _, rfl⟩))⟩)
        unfold tfArithFail
        dsimp only
        rw [hW0, hfee]
        exact .inr (.inr (.inr (.inr (.inr ⟨hf0, Nat.le_of_not_lt hadd2⟩))))
      simp only [lt_add_zero hadd2, Solidity.iszero_zero, Solidity.iszero_one]
      usdt_gas 65000
      xrun
      usdt_stop
      subst hB hW2 hA hW1
      refine .inr (.inr ⟨hval, .inr (.inr (.inr ⟨hp, hb, ?_, rfl, ?_, rfl, rfl, ?_⟩))⟩)
      · intro h
        unfold tfArithFail at h
        dsimp only at h
        rw [hW0, hfee, hAl] at h
        simp only [xferW1, xferW2] at h
        rcases h with h | h | h | h | h | ⟨-, h⟩
        · omega
        · exact hok h
        · omega
        · omega
        · omega
        · omega
      · dsimp only
        rw [hW0, hfee]
        simp only [xferW3, hf0, ↓reduceIte]
      · dsimp only
        rw [hW0, hfee]
        simp only [xferLogs, xferW3, hf0, ↓reduceIte]
        rw [logEntry_eq_eventLog (data := [$F]), logEntry_eq_eventLog (data := [v - $F])]
        · logs_simp []
          simp only [transferLog, transferTopic, ownerKey]
        · event_data
        · event_data)))

set_option hygiene false in
/-- The allowance step of `transferFrom` (`if (_allowance < MAX_UINT) allowed[src][sender] =
_allowance.sub(v)`), then `tf_tail`, with `F` the fee (`hfee : xferFee … = F`) and `hnomul` the
`mul` fitting. -/
macro "tf_allow " F:term:max : tactic => `(tactic| (
  usdt_gas 170000
  generalize hAl : m_world.sload m_msg.currentTarget (allowKey m_ctx.crypto src m_msg.caller) = Al
  have hmx : (115792089237316195423570985008687907853269984665640564039457584007913129639935#256 :
      Word).toNat = 2 ^ 256 - 1 := rfl
  by_cases hal : Al.toNat < 2 ^ 256 - 1
  · simp only [lt_one (x := Al)
      (y := 115792089237316195423570985008687907853269984665640564039457584007913129639935#256)
      (by rw [hmx]; exact hal), Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    by_cases hav : v.toNat ≤ Al.toNat
    swap
    · simp only [gt_one (Nat.lt_of_not_le hav), Solidity.iszero_zero, Solidity.iszero_one]
      xrun
      usdt_invalid
      refine .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb, ?_, _, rfl⟩))⟩)
      unfold tfArithFail
      dsimp only
      rw [hAl]
      exact .inr (.inl ⟨hal, Nat.lt_of_not_le hav⟩)
    simp only [gt_zero hav, Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    by_cases hst : m_msg.isStatic = true
    · usdt_static
      exact .inr (.inl ⟨hst, trivial⟩)
    have hst' : m_msg.isStatic = false := by simpa using hst
    xrun
    clear hst hst'
    have hok : ¬ (Al.toNat < 2 ^ 256 - 1 ∧ Al.toNat < v.toNat) := fun h => by omega
    have hW0 : tfW0 m_ctx.crypto m_world m_msg.currentTarget src m_msg.caller v =
        m_world.sstore m_msg.currentTarget (allowKey m_ctx.crypto src m_msg.caller) (Al - v) := by
      unfold tfW0; rw [hAl]; simp only [hal, ↓reduceIte]
    generalize hW0' : m_world.sstore m_msg.currentTarget (allowKey m_ctx.crypto src m_msg.caller)
      (Al - v) = W0 at hW0 ⊢
    tf_tail W0 $F
  · simp only [lt_zero (x := Al)
      (y := 115792089237316195423570985008687907853269984665640564039457584007913129639935#256)
      (by rw [hmx]; have := Al.isLt; omega), Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    have hok : ¬ (Al.toNat < 2 ^ 256 - 1 ∧ Al.toNat < v.toNat) := fun h => hal h.1
    have hW0 : tfW0 m_ctx.crypto m_world m_msg.currentTarget src m_msg.caller v = m_world := by
      unfold tfW0; rw [hAl]; simp only [hal, ↓reduceIte]
    tf_tail m_world $F))

set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
/-- **`transferFrom(src, dst, v)`** on the lift. -/
theorem transferFrom_high (m : Machine) (hf : Fresh USDT.runtimeCode m) (d : Nat)
    (src dst : Address) (v : Word) (hg : g₀ ≤ m.frame.gasLeft + d)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd)
    (hsize : 100 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress src)
    (harg1 : Bytes.toWord (readBytes m.frame.msg.data 36 32) = Word.ofAddress dst)
    (harg2 : Bytes.toWord (readBytes m.frame.msg.data 68 32) = v)
    (hdep : m.frame.msg.value = 0 →
      deprecatedField.get (m.world.sload m.frame.msg.currentTarget 10#256) = 0) :
    WP (lift patchedCode d m) (fun mh' => mh'.frame.pc ∉ patchPcs ∧
      ExitsWith (TransferFromOut src dst v m) mh') (fun _ _ => False) := by
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have h100 := lt_size_le (k := 100) hsize (by omega)
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
    harg2, ofAddress_and_addressMask, addressMask_and_ofAddress, h100]
  -- `whenNotPaused`
  by_cases hp : pausedW m_world m_msg.currentTarget = 0#256
  swap
  · simp only [iszero_of_ne hp, Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    usdt_revert
    exact .inr (.inr ⟨hval, .inl ⟨hp, _, rfl⟩⟩)
  simp only [hp, Solidity.iszero_zero, Solidity.iszero_one]
  xrun
  -- `require(!isBlackListed[_from])`
  by_cases hb : blackW m_ctx.crypto m_world m_msg.currentTarget src = 0#256
  swap
  · simp only [iszero_of_ne hb, Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    usdt_revert
    exact .inr (.inr ⟨hval, .inr (.inl ⟨hp, hb, _, rfl⟩)⟩)
  simp only [hb, Solidity.iszero_zero, Solidity.iszero_one]
  xrun
  simp only [hdep]
  usdt_gas 185000
  xrun [h100]
  by_cases hv0 : v = 0#256
  · have heq : Word.eq v 0#256 = 1#256 := by rw [hv0]; exact Solidity.eq_self _
    simp only [heq, Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    simp only [gt_zero (x := 0#256) (Nat.zero_le _), Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    have hfee : xferFee m_world m_msg.currentTarget v = 0#256 := by
      rw [hv0]; exact xferFee_zero _ _
    have hnomul : v.toNat * (m_world.sload m_msg.currentTarget 3#256).toNat < 2 ^ 256 := by
      rw [hv0]; simp
    tf_allow (0#256)
  simp only [eq_of_ne hv0, Solidity.iszero_zero, Solidity.iszero_one]
  xrun
  simp only [iszero_of_ne hv0, Solidity.iszero_zero, Solidity.iszero_one]
  xrun
  by_cases hnomul : v.toNat * (m_world.sload m_msg.currentTarget 3#256).toNat < 2 ^ 256
  swap
  · simp only [mul_div_eq_zero (Nat.le_of_not_lt hnomul), Solidity.iszero_zero,
      Solidity.iszero_one]
    xrun
    usdt_invalid
    exact .inr (.inr ⟨hval, .inr (.inr (.inl ⟨hp, hb, .inl (Nat.le_of_not_lt hnomul), _, rfl⟩))⟩)
  simp only [mul_div_eq_one hv0 hnomul, Solidity.iszero_zero, Solidity.iszero_one]
  xrun
  by_cases hfm : (m_world.sload m_msg.currentTarget 4#256).toNat <
      (fee0W m_world m_msg.currentTarget v).toNat
  · simp only [gt_one hfm, Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    have hfee : xferFee m_world m_msg.currentTarget v = m_world.sload m_msg.currentTarget 4#256 := by
      simp only [xferFee, hfm, ↓reduceIte]
    generalize hF : m_world.sload m_msg.currentTarget 4#256 = F at hfee ⊢
    tf_allow F
  · simp only [gt_zero (Nat.le_of_not_lt hfm), Solidity.iszero_zero, Solidity.iszero_one]
    xrun
    have hfee : xferFee m_world m_msg.currentTarget v =
        (v * m_world.sload m_msg.currentTarget 3#256).div 10000#256 := by
      simp only [xferFee, hfm, ↓reduceIte]
    generalize hF : (v * m_world.sload m_msg.currentTarget 3#256).div 10000#256 = F at hfee ⊢
    tf_allow F

end Verified.WeirdERC20.USDT.Spec
