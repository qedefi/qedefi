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

/-! ## The obligation -/

/-- The allowance step of the model. -/
def spent (s : VState Address) (c src : Address) (v : ℕ) : VState Address :=
  if c = PERMIT2 ∨ s.allowance src c = QEDefi.Math.MAX then s
  else s.setAllowance src c (s.allowance src c - v)

theorem solady_call_transferFrom (s : VState Address) (c src dst : Address) (v : ℕ) :
    M.call s c (.transferFrom src dst v) =
      if c ≠ PERMIT2 ∧ s.allowance src c ≠ QEDefi.Math.MAX ∧ s.allowance src c < v then
        .halt .revert
      else if s.bal src < v then .halt .revert
      else .ok { spent s c src v with bal := s.bal - Finsupp.single src v + Finsupp.single dst v }
        (.word true) := by
  simp only [M, Solady.soladyModel, Variant.model_call, Variant.call, Variant.step,
    Variant.transferFrom, Variant.spend, Variant.move, Variant.moveOk, Variant.units,
    Variant.feeOverflow, Variant.feeOf, Variant.credit, Variant.solady, Variant.standard,
    Variant.failKind, Variant.guardOk, Variant.overflows, Variant.failWith, Variant.retData,
    Infinite.test, spent]
  by_cases hP : c = PERMIT2
  · subst hP
    by_cases hb : s.bal src < v <;> simp [hb]
  · have hP' : ¬ some PERMIT2 = some c := fun e => hP (Option.some.inj e).symm
    by_cases hM : s.allowance src c = QEDefi.Math.MAX
    · by_cases hb : s.bal src < v <;> simp [hP, hP', hM, hb]
    · by_cases ha : s.allowance src c < v
      · simp [hP, hP', hM, ha]
      · by_cases hb : s.bal src < v
        · simp [hP, hP', hM, ha, hb, VState.setAllowance]
        · simp [hP, hP', hM, ha, hb, VState.setAllowance]

theorem sload_allowWorld_bal {Act : Finset Address} {m : Machine} {src a : Address} {v : Word}
    (hS : SoladySound m.ctx.crypto Act) (hs : src ∈ Act) (hc : m.frame.msg.caller ∈ Act)
    (ha : a ∈ Act) :
    (allowWorld m src v).sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a) =
      m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a) := by
  unfold allowWorld
  split
  · rfl
  · rw [World.sload_sstore_ne_key _ _ _ (hS.allow_bal src hs _ hc a ha).symm]

/-- **`transferFrom(src, dst, v)`**: `InsufficientAllowance` or `InsufficientBalance` reverts, or
the allowance step (none for Permit2 or an infinite allowance) and the move. -/
theorem call_transferFrom (src dst : Address) (v : ℕ) :
    CallSpec SoladyToken.runtimeCode soladyAbs M g₀ (.transferFrom src dst v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hsA : src ∈ Act := haddr src (by simp [Call.addrs])
  have hdA : dst ∈ Act := haddr dst (by simp [Call.addrs])
  have hcA := hs.caller
  have hS := hs.sound
  refine halts_split' (G := Normal g₀ m)
    (fun hG => transferFrom_high m src dst (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1)
    (transferFrom_low m src dst (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrevA, hmove⟩
  have hwv := toNat_word hv256
  -- the code-level facts, as numbers
  have hmax : allowOf m src = ~~~0 ↔ (allowOf m src).toNat = QEDefi.Math.MAX := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; apply BitVec.eq_of_toNat_eq; rw [h]; rfl
  by_cases hrev : m.frame.msg.caller ≠ PERMIT2 ∧ allowOf m src ≠ ~~~0 ∧ (allowOf m src).toNat < v
  · obtain ⟨out, rfl⟩ := hrevA hrev.1 hrev.2.1 (by rw [hwv]; exact hrev.2.2)
    by_cases hG : Normal g₀ m
    · left
      have hpre := pre_eq hs hG.2.2
      have hal : (pre soladyAbs Act m).allowance src m.frame.msg.caller = (allowOf m src).toNat := by
        rw [hpre]; simp [read, allowances, hsA, hcA, allowOf]
      rw [solady_call_transferFrom, hal, ite_pos' ⟨hrev.1, fun h => hrev.2.1 (hmax.mpr h), hrev.2.2⟩]
      exact ⟨out, rfl⟩
    · exact .inr ⟨trivial, hG⟩
  have hok : m.frame.msg.caller ≠ PERMIT2 → allowOf m src ≠ ~~~0 →
      (word v).toNat ≤ (allowOf m src).toNat := by
    intro h1 h2; rw [hwv]; by_contra h3; exact hrev ⟨h1, h2, Nat.lt_of_not_le h3⟩
  obtain ⟨hrevB, hsucc⟩ := hmove hok
  have hbsrc := sload_allowWorld_bal (v := word v) hS hsA hcA hsA
  by_cases hb : (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat < v
  · obtain ⟨out, rfl⟩ := hrevB (by rw [hbsrc, hwv]; exact hb)
    by_cases hG : Normal g₀ m
    · left
      have hpre := pre_eq hs hG.2.2
      have hal : (pre soladyAbs Act m).allowance src m.frame.msg.caller = (allowOf m src).toNat := by
        rw [hpre]; simp [read, allowances, hsA, hcA, allowOf]
      have hbal : (pre soladyAbs Act m).bal src =
          (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat := by
        rw [hpre]; simp [read, balances, hsA]
      rw [solady_call_transferFrom, hal, ite_neg' (by
        rintro ⟨h1, h2, h3⟩; exact hrev ⟨h1, fun h => h2 (hmax.mp h), h3⟩), hbal, ite_pos' hb]
      exact ⟨out, rfl⟩
    · exact .inr ⟨trivial, hG⟩
  left
  have hle : (word v).toNat ≤ ((allowWorld m src (word v)).sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto src)).toNat := by rw [hbsrc, hwv]; omega
  obtain ⟨hv, -, ho, hw, ht, hcr, hl⟩ := hsucc hle
  have hpre := pre_eq hs hv
  have hal : (pre soladyAbs Act m).allowance src m.frame.msg.caller = (allowOf m src).toNat := by
    rw [hpre]; simp [read, allowances, hsA, hcA, allowOf]
  have hbal : ∀ a ∈ Act, (pre soladyAbs Act m).bal a =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a)).toNat := by
    intro a ha; rw [hpre]; simp [read, balances, ha]
  rw [solady_call_transferFrom, hal, ite_neg' (by
    rintro ⟨h1, h2, h3⟩; exact hrev ⟨h1, fun h => h2 (hmax.mp h), h3⟩), hbal src hsA,
    ite_neg' hb]
  -- the state after the allowance step, through the abstraction
  have hspent : read m.ctx.crypto Act (allowWorld m src (word v)) m.frame.msg.currentTarget =
      spent (pre soladyAbs Act m) m.frame.msg.caller src v := by
    unfold allowWorld spent
    rw [hal]
    by_cases hc : m.frame.msg.caller = PERMIT2 ∨ allowOf m src = ~~~0
    · rw [ite_pos' hc, ite_pos' (hc.imp id hmax.mp), hpre]
    · rw [ite_neg' hc, ite_neg' (fun h => hc (h.imp id hmax.mpr)),
        read_sstore_allow hS hsA hcA, hpre]
      have hkv := hok (fun h => hc (.inl h)) (fun h => hc (.inr h))
      congr 1
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), hwv]
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show read _ _ _ _ = _
    rw [hw, moveWorld, read_moveWorld hS hsA hdA hle, hspent, hwv]
    · simp only [spent]
      split <;> rfl
    · intro hsd
      have h1 := bal_add_lt hs.wf hsd
      rw [hbal src hsA, hbal dst hdA] at h1
      try rw [sload_allowWorld_bal hS hsA hcA hdA]
      rw [hwv]
      omega
  · rw [hw, moveWorld]
    refine FrameKeeps.sstore (bal_mem _ hdA) (FrameKeeps.sstore (bal_mem _ hsA) ?_)
    unfold allowWorld
    split
    · exact frameKeeps_refl
    · exact FrameKeeps.sstore (allow_mem _ _ hsA hcA) frameKeeps_refl
  · rw [hl]
    simp [M, Solady.soladyModel, Solady.soladyEvents, Spec.eventLog]

end Verified.Solady.Spec
