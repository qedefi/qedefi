import Verified.Solady.Spec.Approve
import EvmLogic.Tactic.StepExt

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

set_option maxHeartbeats 0 in
theorem transfer_high (m : Machine) (dst : Address) (v : Word)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa9059cbb [Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (MovePost m m.world #[] m.frame.msg.caller dst v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0 harg1
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
    Nat.mul_one] at harg0 harg1
  pwp_steps [hval, hst, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
    hok, ofAddress_and_addressMask, Solidity.eq_self]
  simp (disch := simp (disch := decide) only [Memory.read_expand,
    Memory.read_storeWord_of_disjoint, read_seed_tail]) only [read_balRow]
  by_cases hle : v.toNat ≤ (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto m_msg.caller)).toNat
  · have hc := iszero_gt_of_le hle
    simp only [balSlot] at hc hle
    simp only [hc]
    pwp_xsteps [hval, hst, hc, Memory.read_64, ofAddress_and_addressMask, Solidity.eq_self]
    simp (disch := simp (disch := decide) only [Memory.read_expand,
      Memory.read_storeWord_of_disjoint, read_seed_tail]) only [read_balRow]
    refine ⟨fun h => absurd hle (by simp only [balSlot] at h ⊢; omega),
      fun _ => ⟨hval, hst, rfl, rfl, rfl, rfl, ?_⟩⟩
    simp only [outputMachine]
    logs_simp []
    rw [shr_loadWord_of _ 12 dst]
    · event_log [v]
    · simp (disch := decide) only [Memory.read_expand, Memory.read_storeWord_of_disjoint,
        read_addr0]
  · have hc := iszero_gt_of_lt (Nat.lt_of_not_le hle)
    simp only [balSlot] at hc hle
    simp only [hc]
    pwp_steps [hval, hst, hc, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd h (by simpa [balSlot] using hle)⟩

end Verified.Solady.Spec
