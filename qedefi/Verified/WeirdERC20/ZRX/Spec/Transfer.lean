import Verified.WeirdERC20.ZRX.Spec.Approve
import EvmLogic.Tactic.StepExt

/-!
# ZRX under the spec: `transfer`

`transfer(dst, v)` of ZRX (solc 0.4.11, `StandardToken`):
`if (balances[caller] >= v && balances[dst] + v >= balances[dst])` debit, credit, `Transfer`,
`true`; else `false`, nothing changed. The receiver-overflow test cannot fail in a state the
model admits (`WF`: `2 · supply ≤ MAX` and the actors' balances sum to at most the supply).
-/

namespace Verified.WeirdERC20.ZRX.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.ZRX.Contracts
open Verified.Solady.Spec (LowHalts halts_split eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-! ## Branch conditions -/

/-- `balances[a] >= v` held: the short-circuit's `ISZERO (ISZERO (LT b v))` is `0`. -/
theorem zrx_ge_of {b v : Word} (h : (b.lt v).iszero.iszero = 0) : v.toNat ≤ b.toNat := by
  by_contra hlt
  have hu : BitVec.ult b v = true := by simp [BitVec.ult]; omega
  simp [Word.iszero, Word.lt, Word.ofBool, hu] at h

/-- `balances[a] >= v` failed. -/
theorem zrx_lt_of {b v : Word} (h : (b.lt v).iszero.iszero ≠ 0) : b.toNat < v.toNat := by
  by_contra hge
  have hu : BitVec.ult b v = false := by simp [BitVec.ult]; omega
  simp [Word.iszero, Word.lt, Word.ofBool, hu] at h

/-- `balances[dst] + v >= balances[dst]` held. -/
theorem zrx_nov_of {S v : Word} (h : ((S + v).lt S).iszero.iszero = 0) :
    S.toNat + v.toNat < 2 ^ 256 := by
  apply Verified.Solady.Spec.lt_add_iszero_ne
  intro h0; rw [h0] at h; exact absurd h (by decide)

/-- `balances[dst] + v >= balances[dst]` failed. -/
theorem zrx_ov_of {S v : Word} (h : ((S + v).lt S).iszero.iszero ≠ 0) :
    2 ^ 256 ≤ S.toNat + v.toNat := by
  by_contra hlt
  rw [Verified.Solady.Spec.lt_add_iszero_one (Nat.lt_of_not_le hlt)] at h
  exact h (by decide)

theorem zrx_lt_iszero_one {b v : Word} (h : v.toNat ≤ b.toNat) : (Word.lt b v).iszero = 1 := by
  have hu : BitVec.ult b v = false := by simp [BitVec.ult]; omega
  simp [Word.iszero, Word.lt, Word.ofBool, hu]

theorem zrx_lt_iszero_zero {b v : Word} (h : b.toNat < v.toNat) : (Word.lt b v).iszero = 0 := by
  have hu : BitVec.ult b v = true := by simp [BitVec.ult]; omega
  simp [Word.iszero, Word.lt, Word.ofBool, hu]

/-! ## The run -/

/-- The balance row of `a` (`balances` at slot 0). -/
abbrev balSlot (crypto : Crypto) (a : Address) : Word := mappingSlot crypto (Word.ofAddress a) 0#256

/-- The world after `transfer`'s move of `v` from `src` to `dst`: debit, then credit read after
it. -/
def moveWorld (crypto : Crypto) (w : World) (t src dst : Address) (v : Word) : World :=
  (w.sstore t (balSlot crypto src) (w.sload t (balSlot crypto src) - v)).sstore t
    (balSlot crypto dst)
    ((w.sstore t (balSlot crypto src) (w.sload t (balSlot crypto src) - v)).sload t
      (balSlot crypto dst) + v)

/-- `transfer(dst, v)`'s code-level end: with no value, either the move, `Transfer` and `true`,
or (a short balance, a wrapping credit) `false` and nothing changed. -/
def TransferPost (m : Machine) (dst : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  m.frame.msg.value = 0 ∧
  (v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat →
    (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat + v.toNat <
      2 ^ 256 →
    m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = moveWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller dst v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (transferLog m.frame.msg.currentTarget m.frame.msg.caller dst v)) ∧
  ((m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat < v.toNat ∨
    2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat +
      v.toNat →
    o = .success (Bytes.ofWord 0) ∧ mf.world = m.world ∧ mf.transient = m.transient ∧
    mf.createdAccounts = m.createdAccounts ∧ mf.frame.sub.logs = m.frame.sub.logs)

set_option maxHeartbeats 0 in
theorem transfer_low (m : Machine) (dst : Address) (v : Word) (hf : Fresh ZRX.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa9059cbb [Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (TransferPost m dst v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  zrx_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  · -- the move
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    have hbc := zrx_ge_of (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 0#256)))
      (v := v) (by with_reducible assumption)
    have hbd := zrx_nov_of (S := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress dst) ++ Bytes.ofWord 0#256)))
      (v := v) (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
      ⟨hv, fun _ _ => ⟨‹_›, ?_, rfl, rfl, rfl, ?_⟩, fun h => ?_⟩
    · simp only [outputData]
      apwp_norm []
      rfl
    · simp only [outputMachine]
      logs_simp []
      event_log [v]
    · simp only [balSlot, mappingSlot] at h
      omega
  · -- the credit would wrap
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    have hbd := zrx_ov_of (S := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress dst) ++ Bytes.ofWord 0#256)))
      (v := v) (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
      ⟨hv, fun _ h => ?_, fun _ => ⟨?_, rfl, rfl, rfl, rfl⟩⟩
    · simp only [balSlot, mappingSlot] at h
      omega
    · simp only [outputData]
      apwp_norm []
      rfl
  · -- the balance is short
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    have hbc := zrx_lt_of (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 0#256)))
      (v := v) (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
      ⟨hv, fun h _ => ?_, fun _ => ⟨?_, rfl, rfl, rfl, rfl⟩⟩
    · simp only [balSlot, mappingSlot] at h
      omega
    · simp only [outputData]
      apwp_norm []
      rfl

set_option maxHeartbeats 0 in
theorem transfer_high (m : Machine) (dst : Address) (v : Word) (hf : Fresh ZRX.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa9059cbb [Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (TransferPost m dst v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  zrx_fresh_intro
  by_cases hbc : v.toNat ≤ (m_world.sload m_msg.currentTarget
      (balSlot m_ctx.crypto m_msg.caller)).toNat
  swap
  · have h3 := zrx_lt_iszero_zero (Nat.lt_of_not_le hbc)
    simp only [balSlot, mappingSlot] at h3
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, h3, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨hval, fun h _ => absurd h hbc, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  have h3 := zrx_lt_iszero_one hbc
  simp only [balSlot, mappingSlot] at h3
  by_cases hbd : (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto dst)).toNat + v.toNat <
      2 ^ 256
  swap
  · have h4 := Verified.Solady.Spec.lt_add_iszero_zero (Nat.le_of_not_lt hbd)
    simp only [balSlot, mappingSlot] at h4
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, h3, h4, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨hval, fun _ h => absurd h hbd, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  have h4 := Verified.Solady.Spec.lt_add_iszero_one hbd
  simp only [balSlot, mappingSlot] at h4
  pwp_steps [hval, hst, hsel', hz, harg0, harg1, h3, h4, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64]
  refine ⟨hval, fun _ _ => ⟨hst, rfl, rfl, rfl, rfl, ?_⟩, fun h => ?_⟩
  · simp only [outputMachine]
    logs_simp []
    event_log [v]
  · dsimp only at h
    omega

end Verified.WeirdERC20.ZRX.Spec
