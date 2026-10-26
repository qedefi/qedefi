import Verified.WeirdERC20.LEND.Spec.Common

/-!
# LEND under the spec: `approve`

`approve(sp, v)` of LEND: `require(enableTransfers)` (set in the final state), then the USDT
race guard `require(v == 0 || allowed[caller][sp] == 0)`, the allowance row written,
`Approval(caller, sp, v)` logged, `true` returned. Every failure is a `REVERT`.
-/

namespace Verified.WeirdERC20.LEND.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.LEND.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-- The allowance row `allowed[o][sp]` (slot 1). -/
abbrev allowSlot (crypto : Crypto) (o sp : Address) : Word :=
  mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 1#256

/-- `approve(sp, v)`'s code-level end, with transfers enabled: the guard reverts, or the
allowance row written, `Approval` logged, `true`. -/
def ApprovePost (m : Machine) (sp : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (v ≠ 0 → m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp) ≠ 0 → ∃ out, o = .revert out) ∧
  (v = 0 ∨ m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp) = 0 →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp) v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (approvalLog m.frame.msg.currentTarget m.frame.msg.caller sp v))

set_option maxHeartbeats 0 in
theorem approve_low (m : Machine) (sp : Address) (v : Word) (hf : Fresh LEND.runtimeCode m)
    (hd : Args m.frame.msg.data 0x095ea7b3 [Word.ofAddress sp, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ApprovePost m sp v) := by
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
  all_goals have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  · -- `v ≠ 0`, a zero allowance
    have ha := eq0_of_ii (x := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress sp) ++ Bytes.ofWord
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++
          Bytes.ofWord 1#256))))) (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
      ⟨fun _ h => absurd ha h, fun _ => ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩⟩
    · simp only [outputData]
      apwp_norm []
      rfl
    · simp only [outputMachine]
      logs_simp []
      event_log [v]
  · -- `v = 0`
    have h0 := eq0_of_ne (x := v) (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
      ⟨fun h _ => absurd h0 h, fun _ => ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩⟩
    · simp only [outputData]
      apwp_norm []
      rfl
    · simp only [outputMachine]
      logs_simp []
      event_log [v]

set_option maxHeartbeats 0 in
theorem approve_high (m : Machine) (sp : Address) (v : Word) (hf : Fresh LEND.runtimeCode m)
    (hd : Args m.frame.msg.data 0x095ea7b3 [Word.ofAddress sp, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft)
    (hen : Word.iszero (255#256 &&&
      Word.div (m.world.sload m.frame.msg.currentTarget 3#256) 256#256) = 0) :
    Halts m (ApprovePost m sp v) := by
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
  by_cases hv0 : v = 0
  · have h1 := eq0_one hv0
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, hen, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    refine ⟨fun h _ => absurd hv0 h, fun _ => ⟨hval, hst, rfl, rfl, rfl, rfl, ?_⟩⟩
    simp only [outputMachine]
    logs_simp []
    event_log [v]
  have h1 := eq0_zero hv0
  by_cases ha0 : m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto m_msg.caller sp) = 0
  · have h2 := eq0_one ha0
    simp only [allowSlot, mappingSlot2, mappingSlot] at h2
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, hen, h1, h2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    refine ⟨fun _ h => absurd ha0 h, fun _ => ⟨hval, hst, rfl, rfl, rfl, rfl, ?_⟩⟩
    simp only [outputMachine]
    logs_simp []
    event_log [v]
  · have h2 := eq0_zero ha0
    simp only [allowSlot, mappingSlot2, mappingSlot] at h2
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, hen, h1, h2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    refine ⟨fun _ _ => ⟨_, rfl⟩, fun h => ?_⟩
    rcases h with h | h
    · exact absurd h hv0
    · exact absurd h ha0

end Verified.WeirdERC20.LEND.Spec
