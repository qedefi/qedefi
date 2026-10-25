import Verified.Solady.Spec.Transfer

/-!
# Solady `ERC20` under the spec: `transferFrom`
-/

namespace Verified.Solady.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open EvmLean.Interpreter EvmLogic.Tactic Verified.Solady.Contracts Verified.Solady.Spec.AnyGas
open QEDefi.ERC4626

/-- The allowance `src` gave the caller, as stored. -/
def allowOf (m : Machine) (src : Address) : Word :=
  m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto src m.frame.msg.caller)

/-- The world after `transferFrom`'s allowance step: unchanged for Permit2 or an infinite
allowance, else the allowance decreased by `v`. -/
def allowWorld (m : Machine) (src : Address) (v : Word) : World :=
  if m.frame.msg.caller = PERMIT2 ∨ allowOf m src = ~~~0 then m.world
  else m.world.sstore m.frame.msg.currentTarget (allowSlot m.ctx.crypto src m.frame.msg.caller)
    (allowOf m src - v)

/-- `transferFrom(src, dst, v)`'s code-level end: `InsufficientAllowance` reverts, or the move
from the world after the allowance step. -/
def TFPost (m : Machine) (src dst : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.caller ≠ PERMIT2 → allowOf m src ≠ ~~~0 → (allowOf m src).toNat < v.toNat →
    ∃ out, o = .revert out) ∧
  ((m.frame.msg.caller ≠ PERMIT2 → allowOf m src ≠ ~~~0 → v.toNat ≤ (allowOf m src).toNat) →
    MovePost m (allowWorld m src v) #[] src dst v mf o)

theorem allowWorld_spent {m : Machine} {src : Address} {v : Word}
    (h1 : m.frame.msg.caller ≠ PERMIT2) (h2 : allowOf m src ≠ ~~~0) :
    allowWorld m src v = m.world.sstore m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto src m.frame.msg.caller) (allowOf m src - v) := by
  rw [allowWorld, ite_neg' (by rintro (h | h); exact h1 h; exact h2 h)]

theorem allowWorld_max {m : Machine} {src : Address} {v : Word} (h : allowOf m src = ~~~0) :
    allowWorld m src v = m.world := by
  simp [allowWorld, h]

theorem allowWorld_permit2 {m : Machine} {src : Address} {v : Word}
    (h : m.frame.msg.caller = PERMIT2) : allowWorld m src v = m.world := by
  simp [allowWorld, h]

set_option maxHeartbeats 0 in
theorem transferFrom_low (m : Machine) (src dst : Address) (v : Word)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (TFPost m src dst v) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  have harg2 := harg 2 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0 harg1 harg2
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
    Nat.mul_one] at harg0 harg1 harg2
  hwp_steps [hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1, harg2,
    ofAddress_and_addressMask, Solidity.eq_self]
  all_goals
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    simp only [shl_or_balRow, shl_or_allowRow] at *
    try simp only [read_allow_of, Memory.read_expand, read_addr32] at *
    try simp (disch := simp (disch := decide) only [Memory.read_expand,
      Memory.read_storeWord_of_disjoint, read_seed_tail, rowWord_bal_tail]) only [read_balRow] at *
  · -- a finite allowance, spent
    have hcP := eq_permit2_zero.mp (by with_reducible assumption)
    have hA := iszero_not_eq_zero.mp (by with_reducible assumption)
    have h1 := le_of_iszero_gt (b := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (rowWord src allowSeed) ++
        Bytes.ofAddress m_msg.caller))) (by with_reducible assumption)
    have h2 := le_of_iszero_gt (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun _ _ h =>
      absurd (Nat.lt_of_lt_of_le h h1) (Nat.lt_irrefl _), fun _ => ?_⟩
    rw [allowWorld_spent]
    rotate_left
    · exact hcP
    · exact hA
    refine ⟨fun h => absurd (Nat.lt_of_lt_of_le h h2) (Nat.lt_irrefl _),
      fun _ => ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩⟩
    · simp only [outputData]
      apwp_norm []
      rfl
    · simp only [outputMachine]
      logs_simp []
      rw [shr_shl_addr, shr_loadWord_of _ 12 dst]
      · event_log [v]
      · simp (disch := decide) only [Memory.read_expand, Memory.read_storeWord_of_disjoint,
          read_addr0]
  · -- an infinite allowance
    have hcP := eq_permit2_zero.mp (by with_reducible assumption)
    have hA := iszero_not_ne (by with_reducible assumption)
    have h2 := le_of_iszero_gt (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun _ h => absurd hA
      (by simpa only [allowOf, allowSlot] using h), fun _ => ?_⟩
    rw [allowWorld_max]
    rotate_left
    · exact hA
    refine ⟨fun h => absurd (Nat.lt_of_lt_of_le h h2) (Nat.lt_irrefl _),
      fun _ => ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩⟩
    · simp only [outputData]
      apwp_norm []
      rfl
    · simp only [outputMachine]
      logs_simp []
      rw [shr_shl_addr, shr_loadWord_of _ 12 dst]
      · event_log [v]
      · simp (disch := decide) only [Memory.read_expand, Memory.read_storeWord_of_disjoint,
          read_addr0]
  · -- Permit2
    have hcP := eq_permit2_ne (by with_reducible assumption)
    have h2 := le_of_iszero_gt (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun h => absurd hcP h,
      fun _ => ?_⟩
    rw [allowWorld_permit2]
    rotate_left
    · exact hcP
    refine ⟨fun h => absurd (Nat.lt_of_lt_of_le h h2) (Nat.lt_irrefl _),
      fun _ => ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩⟩
    · simp only [outputData]
      apwp_norm []
      rfl
    · simp only [outputMachine]
      logs_simp []
      rw [shr_shl_addr, shr_loadWord_of _ 12 dst]
      · event_log [v]
      · simp (disch := decide) only [Memory.read_expand, Memory.read_storeWord_of_disjoint,
          read_addr0]

/-- The success end of a `transferFrom` run: rewrite the recipient's row, then the move. -/
macro "tf_close " d:term:max v:term:max : tactic => `(tactic| (
  simp (disch := simp (disch := decide) only [Memory.read_expand,
    Memory.read_storeWord_of_disjoint, read_seed_tail, rowWord_bal_tail]) only [read_balRow]
  refine ⟨fun h => absurd (Nat.lt_of_lt_of_le h ‹_›) (Nat.lt_irrefl _),
    fun _ => ⟨‹_›, ‹_›, rfl, rfl, rfl, rfl, ?_⟩⟩
  simp only [outputMachine]
  logs_simp []
  rw [shr_shl_addr, shr_loadWord_of _ 12 $d (by
    simp (disch := decide) only [Memory.read_expand, Memory.read_storeWord_of_disjoint,
      read_addr0])]
  event_log [$v]))

set_option maxHeartbeats 0 in
theorem transferFrom_high (m : Machine) (src dst : Address) (v : Word)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (TFPost m src dst v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  have harg2 := harg 2 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0 harg1 harg2
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
    Nat.mul_one] at harg0 harg1 harg2
  by_cases hP : m_msg.caller = PERMIT2
  · have hP' := eq_permit2_one hP
    by_cases hB : v.toNat ≤ (m_world.sload m_msg.currentTarget
        (m_ctx.crypto.keccak256 (Bytes.ofWord (rowWord src balSeed)))).toNat
    · have hB' := iszero_gt_of_le hB
      pwp_xsteps [hval, hst, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
        harg2, hok, ofAddress_and_addressMask, Solidity.eq_self, shl_or_balRow, shl_or_allowRow,
        hP', hB']
      refine ⟨fun h => absurd hP h, fun _ => ?_⟩
      rw [allowWorld_permit2]
      rotate_left
      · exact hP
      tf_close dst v
    · have hB' := iszero_gt_of_lt (Nat.lt_of_not_le hB)
      pwp_xsteps [hval, hst, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
        harg2, hok, ofAddress_and_addressMask, Solidity.eq_self, shl_or_balRow, shl_or_allowRow,
        hP', hB']
      refine ⟨fun h => absurd hP h, fun _ => ?_⟩
      rw [allowWorld_permit2]
      rotate_left
      · exact hP
      exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd h hB⟩
  have hP' := eq_permit2_zero' hP
  by_cases hM : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
      (Bytes.ofWord (rowWord src allowSeed) ++ Bytes.ofAddress m_msg.caller)) = ~~~0
  · have hM' := iszero_not_one hM
    by_cases hB : v.toNat ≤ (m_world.sload m_msg.currentTarget
        (m_ctx.crypto.keccak256 (Bytes.ofWord (rowWord src balSeed)))).toNat
    · have hB' := iszero_gt_of_le hB
      pwp_xsteps [hval, hst, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
        harg2, hok, ofAddress_and_addressMask, Solidity.eq_self, shl_or_balRow, shl_or_allowRow,
        read_allow_of, Memory.read_expand, read_addr32, hP', hM', hB']
      refine ⟨fun _ h => absurd hM h, fun _ => ?_⟩
      rw [allowWorld_max]
      rotate_left
      · exact hM
      tf_close dst v
    · have hB' := iszero_gt_of_lt (Nat.lt_of_not_le hB)
      pwp_xsteps [hval, hst, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
        harg2, hok, ofAddress_and_addressMask, Solidity.eq_self, shl_or_balRow, shl_or_allowRow,
        read_allow_of, Memory.read_expand, read_addr32, hP', hM', hB']
      refine ⟨fun _ h => absurd hM h, fun _ => ?_⟩
      rw [allowWorld_max]
      rotate_left
      · exact hM
      exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd h hB⟩
  have hM' := iszero_not_zero' hM
  by_cases hA : v.toNat ≤ (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
      (Bytes.ofWord (rowWord src allowSeed) ++ Bytes.ofAddress m_msg.caller))).toNat
  swap
  · have hA' := iszero_gt_of_lt (Nat.lt_of_not_le hA)
    pwp_xsteps [hval, hst, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
      harg2, hok, ofAddress_and_addressMask, Solidity.eq_self, shl_or_balRow, shl_or_allowRow,
      read_allow_of, Memory.read_expand, read_addr32, hP', hM', hA']
    exact ⟨fun _ _ _ => ⟨_, rfl⟩, fun h => absurd (h hP hM) hA⟩
  have hA' := iszero_gt_of_le hA
  by_cases hB : v.toNat ≤ ((m_world.sstore m_msg.currentTarget (m_ctx.crypto.keccak256
      (Bytes.ofWord (rowWord src allowSeed) ++ Bytes.ofAddress m_msg.caller))
      (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
        (Bytes.ofWord (rowWord src allowSeed) ++ Bytes.ofAddress m_msg.caller)) - v)).sload
      m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (rowWord src balSeed)))).toNat
  · have hB' := iszero_gt_of_le hB
    pwp_xsteps [hval, hst, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
      harg2, hok, ofAddress_and_addressMask, Solidity.eq_self, shl_or_balRow, shl_or_allowRow,
      read_allow_of, Memory.read_expand, read_addr32, hP', hM', hA', hB']
    refine ⟨fun _ _ h => absurd (Nat.lt_of_lt_of_le h hA) (Nat.lt_irrefl _), fun _ => ?_⟩
    rw [allowWorld_spent]
    rotate_left
    · exact hP
    · exact hM
    tf_close dst v
  · have hB' := iszero_gt_of_lt (Nat.lt_of_not_le hB)
    pwp_xsteps [hval, hst, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1,
      harg2, hok, ofAddress_and_addressMask, Solidity.eq_self, shl_or_balRow, shl_or_allowRow,
      read_allow_of, Memory.read_expand, read_addr32, hP', hM', hA', hB']
    refine ⟨fun _ _ h => absurd (Nat.lt_of_lt_of_le h hA) (Nat.lt_irrefl _), fun _ => ?_⟩
    rw [allowWorld_spent]
    rotate_left
    · exact hP
    · exact hM
    exact ⟨fun _ => ⟨_, rfl⟩, fun h => absurd h hB⟩

end Verified.Solady.Spec
