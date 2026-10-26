import Verified.WeirdERC20.YAMV2.Spec.Approve

/-!
# YAMv2 under the spec: `transfer`, the bytecode runs

`transfer(to, v)` of YAMv2 (OpenZeppelin-3 `_transfer`, solc 0.6.12): a zero sender (the
caller) or recipient reverts, the debit is `SafeMath.sub` with a reason string (an amount above
the balance reverts), the credit `SafeMath.add` (an overflow reverts), one `Transfer`, `true`.
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.YAMV2.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626
open Verified.WeirdERC20.AMPL.Spec (iszero_lt_size ampl_addr_ne')

/-- The world after the debit of `v` from `src`. -/
def debitWorld (crypto : Crypto) (w : World) (t src : Address) (v : Word) : World :=
  w.sstore t (balSlot crypto src) (w.sload t (balSlot crypto src) - v)

/-- The world after the move of `v` from `src` to `dst`: the debit, then the credit read after
it. -/
def moveWorld (crypto : Crypto) (w : World) (t src dst : Address) (v : Word) : World :=
  (debitWorld crypto w t src v).sstore t (balSlot crypto dst)
    (v + (debitWorld crypto w t src v).sload t (balSlot crypto dst))

/-- `transfer(dst, v)`'s code-level end: a value, a zero sender or recipient, or an amount
above the balance revert; otherwise (when the credit fits) the move, `true`, one `Transfer`. -/
def TransferPost (m : Machine) (dst : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.value ≠ 0 → ∃ out, o = .revert out) ∧
  (m.frame.msg.caller = 0 ∨ dst = 0 ∨
    (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat <
      v.toNat → ∃ out, o = .revert out) ∧
  (m.frame.msg.caller ≠ 0 → dst ≠ 0 →
    v.toNat ≤
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat →
    ((debitWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller v).sload
      m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat + v.toNat < 2 ^ 256 →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = moveWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller dst v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (transferLog m.frame.msg.currentTarget m.frame.msg.caller dst v))

set_option maxHeartbeats 0 in
theorem transfer_low (m : Machine) (dst : Address) (v : Word) (hf : Fresh YAMV2.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa9059cbb [Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (TransferPost m dst v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, loadWord_write_of_disjoint,
    Memory.read_write_of_disjoint, size_readBytes]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  have hc0 := ampl_addr_ne' (by with_reducible assumption : Word.ofAddress m_msg.caller ≠ 0)
  have hd0 := ampl_addr_ne' (by with_reducible assumption : Word.ofAddress dst ≠ 0)
  have hsb := Verified.Solady.Spec.le_of_iszero_gt (by assumption :
    (v.gt (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto m_msg.caller))).iszero ≠ 0)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
    ⟨fun h => absurd hv h, fun h => ?_, fun _ _ _ _ => ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩⟩
  · rcases h with h | h | h
    · exact absurd h hc0
    · exact absurd h hd0
    · exact absurd (Nat.lt_of_lt_of_le h hsb) (Nat.lt_irrefl _)
  · simp only [outputData]
    apwp_norm []
    rfl
  · simp only [outputMachine]
    logs_simp []
    event_log [v]

end Verified.WeirdERC20.YAMV2.Spec
