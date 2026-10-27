import Verified.WeirdERC20.LEND.Spec.Approve
import Verified.WeirdERC20.BNB.Spec.Transfer

/-!
# LEND under the spec: `transfer`, the runs

`transfer(dst, v)` of LEND: `require(enableTransfers)`, then `StdToken.transfer`:
`require(balances[caller] >= v)`, `require(balances[dst] + v > balances[dst])` (wrapping: fails
for `v = 0` and on overflow), the debit `safeSub`, the credit `safeAdd` (read after the debit;
its `assert` cannot fail), `Transfer`, `true`.
-/

namespace Verified.WeirdERC20.LEND.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.LEND.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-- The balance row of `a` (`balances` at slot 0). -/
abbrev balSlot (crypto : Crypto) (a : Address) : Word := mappingSlot crypto (Word.ofAddress a) 0#256

/-- The world after `transfer`'s move of `v` from `src` to `dst`: debit, then credit read after
it. -/
def moveWorld (crypto : Crypto) (w : World) (t src dst : Address) (v : Word) : World :=
  (w.sstore t (balSlot crypto src) (w.sload t (balSlot crypto src) - v)).sstore t
    (balSlot crypto dst)
    ((w.sstore t (balSlot crypto src) (w.sload t (balSlot crypto src) - v)).sload t
      (balSlot crypto dst) + v)

/-- `transfer(dst, v)`'s code-level end, with transfers enabled: a short balance, a zero value
or a wrapping credit revert; otherwise the move, `Transfer`, `true`. -/
def TransferPost (m : Machine) (dst : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  ((m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat < v.toNat ∨ v.toNat = 0 ∨
    2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat +
      v.toNat → ∃ out, o = .revert out) ∧
  (v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat → 0 < v.toNat →
    (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat + v.toNat <
      2 ^ 256 →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = moveWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller dst v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (transferLog m.frame.msg.currentTarget m.frame.msg.caller dst v))

set_option maxHeartbeats 0 in
theorem transfer_low (m : Machine) (dst : Address) (v : Word) (hf : Fresh LEND.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa9059cbb [Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (TransferPost m dst v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := BNB.Spec.div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := BNB.Spec.calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  · have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    have hbc := BNB.Spec.le_of_lt_iszero (iszero3_ne (x := (m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++
        Bytes.ofWord 0#256))).lt v) (by with_reducible assumption))
    have hgt := add_gt_of (S := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress dst) ++ Bytes.ofWord 0#256)))
      (v := v) (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun h => ?_, fun _ _ _ =>
      ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩⟩
    · simp only [balSlot, mappingSlot] at h
      omega
    · simp only [outputData]
      apwp_norm []
      rfl
    · simp only [outputMachine]
      logs_simp []
      event_log [v]
  · -- infeasible: the `safeAdd` assert's short-circuit seen both ways
    exact (iszero23' (x := ((m_world.sstore m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 0#256))
      (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 0#256)) - v)).sload
      m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress dst) ++
        Bytes.ofWord 0#256)) + v).lt ((m_world.sstore m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 0#256))
      (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 0#256)) - v)).sload
      m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress dst) ++
        Bytes.ofWord 0#256))))
      (by with_reducible assumption) (by with_reducible assumption)).elim

set_option maxHeartbeats 0 in
theorem transfer_high (m : Machine) (dst : Address) (v : Word) (hf : Fresh LEND.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa9059cbb [Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft)
    (hen : Word.iszero (255#256 &&&
      Word.div (m.world.sload m.frame.msg.currentTarget 3#256) 256#256) = 0) :
    Halts m (TransferPost m dst v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := BNB.Spec.div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := BNB.Spec.calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hbc : v.toNat ≤ (m_world.sload m_msg.currentTarget
      (balSlot m_ctx.crypto m_msg.caller)).toNat
  swap
  · have h3 := BNB.Spec.lt_iszero_zero (Nat.lt_of_not_le hbc)
    simp only [balSlot, mappingSlot] at h3
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, hen, h3, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd h hbc⟩
  have h3 := BNB.Spec.lt_iszero_one hbc
  simp only [balSlot, mappingSlot] at h3
  by_cases hok : 0 < v.toNat ∧
      (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto dst)).toNat + v.toNat < 2 ^ 256
  swap
  · have h4 := add_gt_zero (S := m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto dst))
      (v := v) (by omega)
    simp only [balSlot, mappingSlot] at h4
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, hen, h3, h4, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ h1 h2 => absurd ⟨h1, h2⟩ hok⟩
  obtain ⟨hv0, hbd⟩ := hok
  have h4 := add_gt_one (S := m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto dst))
    hv0 hbd
  simp only [balSlot, mappingSlot] at h4
  have h5 := Verified.Solady.Spec.iszero_gt_of_le hbc
  have hX := BNB.Spec.credit_fits (t := m_msg.currentTarget) hbc hbd
  have h6 := Verified.Solady.Spec.lt_add_iszero_one hX
  have h7 := BNB.Spec.lt_add_iszero_one' hX
  simp only [balSlot, mappingSlot] at h5 h6 h7
  pwp_steps [hval, hst, hsel', hz, harg0, harg1, hen, h3, h4, h5, h6, h7,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine ⟨fun h => ?_, fun _ _ _ => ⟨hval, hst, rfl, rfl, rfl, rfl, ?_⟩⟩
  · dsimp only at h
    omega
  · simp only [outputMachine]
    logs_simp []
    event_log [v]

end Verified.WeirdERC20.LEND.Spec
