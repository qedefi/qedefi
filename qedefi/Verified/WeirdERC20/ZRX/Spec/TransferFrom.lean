import Verified.WeirdERC20.ZRX.Spec.TransferCall

/-!
# ZRX under the spec: `transferFrom`, the runs

`transferFrom(src, dst, v)` of ZRX (solc 0.4.11, `UnlimitedAllowanceToken`): the allowance
`a = allowed[src][caller]` is read first; if `balances[src] >= v && a >= v &&
balances[dst] + v >= balances[dst]` the credit, then the debit (read after the credit), then,
when `a < 2²⁵⁶ − 1`, `allowed[src][caller] -= v`; `Transfer`, `true`. Otherwise `false`,
nothing changed.
-/

namespace Verified.WeirdERC20.ZRX.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.ZRX.Contracts
open Verified.Solady.Spec (LowHalts halts_split eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-- The word `2²⁵⁶ − 1`. -/
abbrev maxWord : Word := 115792089237316195423570985008687907853269984665640564039457584007913129639935#256

theorem zrx_lt_max_of {a : Word} (h : (a.lt maxWord).iszero = 0) : a.toNat < 2 ^ 256 - 1 := by
  by_contra hge
  have hu : BitVec.ult a maxWord = false := by simp [BitVec.ult]; omega
  simp [Word.iszero, Word.lt, Word.ofBool, hu] at h

theorem zrx_eq_max_of {a : Word} (h : (a.lt maxWord).iszero ≠ 0) : a.toNat = 2 ^ 256 - 1 := by
  have hlt : ¬ a.toNat < 2 ^ 256 - 1 := by
    intro hlt
    have hu : BitVec.ult a maxWord = true := by simp [BitVec.ult]; omega
    simp [Word.iszero, Word.lt, Word.ofBool, hu] at h
  have := a.isLt
  omega

theorem zrx_lt_max_iszero {a : Word} (h : a.toNat < 2 ^ 256 - 1) : (a.lt maxWord).iszero = 0 := by
  have hu : BitVec.ult a maxWord = true := by simp [BitVec.ult]; omega
  simp [Word.iszero, Word.lt, Word.ofBool, hu]

theorem zrx_eq_max_iszero {a : Word} (h : a.toNat = 2 ^ 256 - 1) : (a.lt maxWord).iszero = 1 := by
  have hu : BitVec.ult a maxWord = false := by simp [BitVec.ult]; omega
  simp [Word.iszero, Word.lt, Word.ofBool, hu]

/-- The world after `transferFrom`'s move: the credit, then the debit read after it. -/
def cdWorld (crypto : Crypto) (w : World) (t src dst : Address) (v : Word) : World :=
  (w.sstore t (balSlot crypto dst) (w.sload t (balSlot crypto dst) + v)).sstore t
    (balSlot crypto src)
    ((w.sstore t (balSlot crypto dst) (w.sload t (balSlot crypto dst) + v)).sload t
      (balSlot crypto src) - v)

/-- The world after `transferFrom` with a finite allowance: the move, then the allowance row
lowered (read after the move). -/
def tfWorld (crypto : Crypto) (w : World) (t c src dst : Address) (v : Word) : World :=
  (cdWorld crypto w t src dst v).sstore t (allowSlot crypto src c)
    ((cdWorld crypto w t src dst v).sload t (allowSlot crypto src c) - v)

/-- `transferFrom(src, dst, v)`'s code-level end: with no value, the move (and the allowance
lowered unless it is `2²⁵⁶ − 1`), `Transfer`, `true`; or (a short balance or allowance, a
wrapping credit) `false` and nothing changed. -/
def TFPost (m : Machine) (src dst : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  m.frame.msg.value = 0 ∧
  (v.toNat ≤ (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat →
    v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat →
    (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat + v.toNat <
      2 ^ 256 →
    m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = (if (m.world.sload m.frame.msg.currentTarget
        (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat < 2 ^ 256 - 1 then
      tfWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src dst v
      else cdWorld m.ctx.crypto m.world m.frame.msg.currentTarget src dst v) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push (transferLog m.frame.msg.currentTarget src dst v)) ∧
  ((m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat < v.toNat ∨
    (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat < v.toNat ∨
    2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat +
      v.toNat →
    o = .success (Bytes.ofWord 0) ∧ mf.world = m.world ∧ mf.transient = m.transient ∧
    mf.createdAccounts = m.createdAccounts ∧ mf.frame.sub.logs = m.frame.sub.logs)

set_option maxHeartbeats 0 in
theorem transferFrom_low (m : Machine) (src dst : Address) (v : Word)
    (hf : Fresh ZRX.runtimeCode m)
    (hd : Args m.frame.msg.data 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (TFPost m src dst v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  have harg2 := harg 2 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1 harg2
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  zrx_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, harg2, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  all_goals have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  · -- the move, a finite allowance
    have hbs := zrx_ge_of (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 0#256)))
      (v := v) (by with_reducible assumption)
    have hal := zrx_ge_of (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 1#256)))))
      (v := v) (by with_reducible assumption)
    have hbd := zrx_nov_of (S := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress dst) ++ Bytes.ofWord 0#256)))
      (v := v) (by with_reducible assumption)
    have hmx := zrx_lt_max_of (a := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 1#256)))))
      (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
      ⟨hv, fun _ _ _ => ⟨‹_›, ?_, ?_, rfl, rfl, ?_⟩, fun h => ?_⟩
    · simp only [outputData]
      apwp_norm []
      rfl
    · have hmx' : (m_world.sload m_msg.currentTarget
          (allowSlot m_ctx.crypto src m_msg.caller)).toNat < 2 ^ 256 - 1 := hmx
      dsimp only
      rw [ite_pos' hmx']
      rfl
    · simp only [outputMachine]
      logs_simp []
      event_log [v]
    · simp only [balSlot, allowSlot, mappingSlot2, mappingSlot] at h
      omega
  · -- the move, the infinite allowance
    have hbs := zrx_ge_of (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 0#256)))
      (v := v) (by with_reducible assumption)
    have hal := zrx_ge_of (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 1#256)))))
      (v := v) (by with_reducible assumption)
    have hbd := zrx_nov_of (S := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress dst) ++ Bytes.ofWord 0#256)))
      (v := v) (by with_reducible assumption)
    have hmx := zrx_eq_max_of (a := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 1#256)))))
      (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
      ⟨hv, fun _ _ _ => ⟨‹_›, ?_, ?_, rfl, rfl, ?_⟩, fun h => ?_⟩
    · simp only [outputData]
      apwp_norm []
      rfl
    · have hmx'' : (m_world.sload m_msg.currentTarget
          (allowSlot m_ctx.crypto src m_msg.caller)).toNat = 2 ^ 256 - 1 := hmx
      have hmx' : ¬ (m_world.sload m_msg.currentTarget
          (allowSlot m_ctx.crypto src m_msg.caller)).toNat < 2 ^ 256 - 1 := by omega
      dsimp only
      rw [ite_neg' hmx']
      rfl
    · simp only [outputMachine]
      logs_simp []
      event_log [v]
    · simp only [balSlot, allowSlot, mappingSlot2, mappingSlot] at h
      omega
  · -- the credit would wrap
    have hbd := zrx_ov_of (S := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress dst) ++ Bytes.ofWord 0#256)))
      (v := v) (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
      ⟨hv, fun _ _ h => ?_, fun _ => ⟨?_, rfl, rfl, rfl, rfl⟩⟩
    · simp only [balSlot, mappingSlot] at h
      omega
    · simp only [outputData]
      apwp_norm []
      rfl
  · -- infeasible: the allowance test seen both ways
    exact absurd (zrx_ge_of (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 1#256)))))
      (v := v) (by with_reducible assumption)) (Nat.not_le.2 (zrx_lt_of (b := m_world.sload
        m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++
          Bytes.ofWord (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++
            Bytes.ofWord 1#256))))) (v := v) (by with_reducible assumption)))
  · -- infeasible: the allowance test seen both ways
    exact absurd (zrx_ge_of (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 1#256)))))
      (v := v) (by with_reducible assumption)) (Nat.not_le.2 (zrx_lt_of (b := m_world.sload
        m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++
          Bytes.ofWord (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++
            Bytes.ofWord 1#256))))) (v := v) (by with_reducible assumption)))
  · -- the allowance is short
    have hal := zrx_lt_of (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 1#256)))))
      (v := v) (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
      ⟨hv, fun _ h _ => ?_, fun _ => ⟨?_, rfl, rfl, rfl, rfl⟩⟩
    · simp only [allowSlot, mappingSlot2, mappingSlot] at h
      omega
    · simp only [outputData]
      apwp_norm []
      rfl
  · -- the balance is short
    have hbs := zrx_lt_of (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 0#256)))
      (v := v) (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
      ⟨hv, fun h _ _ => ?_, fun _ => ⟨?_, rfl, rfl, rfl, rfl⟩⟩
    · simp only [balSlot, mappingSlot] at h
      omega
    · simp only [outputData]
      apwp_norm []
      rfl

set_option maxHeartbeats 0 in
theorem transferFrom_high (m : Machine) (src dst : Address) (v : Word)
    (hf : Fresh ZRX.runtimeCode m)
    (hd : Args m.frame.msg.data 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (TFPost m src dst v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  have harg2 := harg 2 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1 harg2
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  zrx_fresh_intro
  by_cases hbs : v.toNat ≤ (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto src)).toNat
  swap
  · have h3 := zrx_lt_iszero_zero (Nat.lt_of_not_le hbs)
    simp only [balSlot, mappingSlot] at h3
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, h3, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨hval, fun h _ _ => absurd h hbs, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  have h3 := zrx_lt_iszero_one hbs
  simp only [balSlot, mappingSlot] at h3
  by_cases hal : v.toNat ≤
      (m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto src m_msg.caller)).toNat
  swap
  · have h4 := zrx_lt_iszero_zero (Nat.lt_of_not_le hal)
    simp only [allowSlot, mappingSlot2, mappingSlot] at h4
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, h3, h4, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨hval, fun _ h _ => absurd h hal, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  have h4 := zrx_lt_iszero_one hal
  simp only [allowSlot, mappingSlot2, mappingSlot] at h4
  by_cases hbd : (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto dst)).toNat + v.toNat <
      2 ^ 256
  swap
  · have h5 := Verified.Solady.Spec.lt_add_iszero_zero (Nat.le_of_not_lt hbd)
    simp only [balSlot, mappingSlot] at h5
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, h3, h4, h5, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨hval, fun _ _ h => absurd h hbd, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  have h5 := Verified.Solady.Spec.lt_add_iszero_one hbd
  simp only [balSlot, mappingSlot] at h5
  by_cases hmx : (m_world.sload m_msg.currentTarget
      (allowSlot m_ctx.crypto src m_msg.caller)).toNat < 2 ^ 256 - 1
  · have h6 := zrx_lt_max_iszero hmx
    simp only [allowSlot, mappingSlot2, mappingSlot] at h6
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, h3, h4, h5, h6,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine ⟨hval, fun _ _ _ => ⟨hst, rfl, ?_, rfl, rfl, ?_⟩, fun h => ?_⟩
    · rw [ite_pos' hmx]
      rfl
    · simp only [outputMachine]
      logs_simp []
      event_log [v]
    · dsimp only at h
      omega
  · have h6 := zrx_eq_max_iszero (a := m_world.sload m_msg.currentTarget
      (allowSlot m_ctx.crypto src m_msg.caller)) (by have := (m_world.sload m_msg.currentTarget
      (allowSlot m_ctx.crypto src m_msg.caller)).isLt; omega)
    simp only [allowSlot, mappingSlot2, mappingSlot] at h6
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, h3, h4, h5, h6,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine ⟨hval, fun _ _ _ => ⟨hst, rfl, ?_, rfl, rfl, ?_⟩, fun h => ?_⟩
    · rw [ite_neg' hmx]
      rfl
    · simp only [outputMachine]
      logs_simp []
      event_log [v]
    · dsimp only at h
      omega

end Verified.WeirdERC20.ZRX.Spec
