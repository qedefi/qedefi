import Verified.Solady.Spec.Approve

/-!
# Solady `ERC20` under the spec: `transfer`
-/

namespace Verified.Solady.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open EvmLean.Interpreter EvmLogic.Tactic Verified.Solady.Contracts Verified.Solady.Spec.AnyGas
open QEDefi.ERC4626

/-- The world after Solady's move of `v` from `src` to `dst` (debit, then credit read after the
debit; the credit is unchecked). -/
def moveWorld (crypto : Crypto) (w : World) (t src dst : Address) (v : Word) : World :=
  (w.sstore t (balSlot crypto src) (w.sload t (balSlot crypto src) - v)).sstore t
    (balSlot crypto dst)
    ((w.sstore t (balSlot crypto src) (w.sload t (balSlot crypto src) - v)).sload t
      (balSlot crypto dst) + v)

/-- A move's code-level end from the world `w`: `InsufficientBalance` reverts, or success with
`moveWorld`, the logs `pre` appended and the `Transfer` log. -/
def MovePost (m : Machine) (w : World) (pre : Array Log) (src dst : Address) (v : Word)
    (mf : Machine) (o : Outcome) : Prop :=
  ((w.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat < v.toNat →
    ∃ out, o = .revert out) ∧
  (v.toNat ≤ (w.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = moveWorld m.ctx.crypto w m.frame.msg.currentTarget src dst v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = (m.frame.sub.logs ++ pre).push
      (transferLog m.frame.msg.currentTarget src dst v))

set_option maxHeartbeats 0 in
theorem transfer_low (m : Machine) (dst : Address) (v : Word)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa9059cbb [Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (MovePost m m.world #[] m.frame.msg.caller dst v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0 harg1
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
    Nat.mul_one] at harg0 harg1
  hwp_steps [hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
    ofAddress_and_addressMask, Solidity.eq_self]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  have hle := le_of_iszero_gt (by with_reducible assumption)
  simp (disch := simp (disch := decide) only [Memory.read_expand,
    Memory.read_storeWord_of_disjoint, read_seed_tail]) only [read_balRow] at hle ⊢
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
    ⟨fun h => absurd hle (by simp [balSlot] at h ⊢; omega), fun _ => ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩⟩
  · simp only [outputData]
    apwp_norm []
    rfl
  · simp only [outputMachine]
    logs_simp []
    rw [shr_loadWord_of _ 12 dst]
    · event_log [v]
    · simp (disch := decide) only [Memory.read_expand, Memory.read_storeWord_of_disjoint, read_addr0]

end Verified.Solady.Spec
