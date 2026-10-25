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

/-! ## The obligation -/

theorem solady_call_transfer (s : VState Address) (c d : Address) (v : ℕ) :
    M.call s c (.transfer d v) =
      if s.bal c < v then .halt .revert
      else .ok { s with bal := s.bal - Finsupp.single c v + Finsupp.single d v } (.word true) := by
  by_cases h : s.bal c < v
  · simp [M, Solady.soladyModel, Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      Variant.move, Variant.units, Variant.solady, Variant.standard, Variant.failKind,
      Variant.guardOk, Variant.overflows, Variant.feeOverflow, Variant.failWith, h]
  · simp [M, Solady.soladyModel, Variant.call, Variant.step, Variant.transfer, Variant.moveOk,
      Variant.move, Variant.units, Variant.solady, Variant.standard, Variant.feeOverflow,
      Variant.feeOf, Variant.credit, Variant.retData, h]

/-- Under the model's invariant, two actors' balances fit a word together. -/
theorem bal_add_lt {s : VState Address} (hw : M.wf s) {c d : Address} (hcd : c ≠ d) :
    s.bal c + s.bal d < 2 ^ 256 := by
  have h := QEDefi.ERC20.add_le_total (f := s.bal) hcd
  simp only [M, Solady.soladyModel, Variant.model_wf, Variant.WF, Variant.solady,
    Variant.standard, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hw
  have : s.supply ≤ QEDefi.Math.MAX := hw.2
  simp only [QEDefi.Math.MAX] at this
  omega

theorem toNat_word {v : ℕ} (hv : v < 2 ^ 256) : (word v).toNat = v := by
  rw [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

/-- **`transfer(dst, v)`**: `InsufficientBalance` reverts, or the move with its `Transfer`. -/
theorem call_transfer (dst : Address) (v : ℕ) :
    CallSpec SoladyToken.runtimeCode soladyAbs M g₀ (.transfer dst v) := by
  intro Act m hs hc haddr
  obtain ⟨hv256, hd⟩ := hc
  have hdA : dst ∈ Act := haddr dst (by simp [Call.addrs])
  have hcA := hs.caller
  refine halts_split' (G := Normal g₀ m)
    (fun hG => transfer_high m dst (word v) hs.fresh hd hs.size hG.2.2 hG.2.1 hG.1)
    (transfer_low m dst (word v) hs.fresh hd hs.size) ?_
  rintro mf o ⟨hrev, hok⟩
  by_cases hlt : (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat < v
  · obtain ⟨out, rfl⟩ := hrev (by rwa [toNat_word hv256])
    by_cases hG : Normal g₀ m
    · left
      have hpre := pre_eq hs hG.2.2
      have hbc : (pre soladyAbs Act m).bal m.frame.msg.caller =
          (m.world.sload m.frame.msg.currentTarget
            (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
        rw [hpre]; simp [read, balances, hcA]
      rw [solady_call_transfer, hbc, ite_pos' hlt]
      exact ⟨out, rfl⟩
    · exact .inr ⟨trivial, hG⟩
  left
  have hle : (word v).toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by rw [toNat_word hv256]; omega
  obtain ⟨hv, -, ho, hw, ht, hcr, hl⟩ := hok hle
  have hpre := pre_eq hs hv
  have hbc : (pre soladyAbs Act m).bal m.frame.msg.caller =
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat := by
    rw [hpre]; simp [read, balances, hcA]
  rw [solady_call_transfer, hbc, ite_neg' hlt]
  refine ⟨by rw [ho]; rfl, ?_, ?_, ht, hcr, ?_⟩
  · show read _ _ _ _ = _
    rw [hw, moveWorld, read_moveWorld hs.sound hcA hdA hle, ← hpre, toNat_word hv256]
    intro hcd
    have h1 := bal_add_lt hs.wf hcd
    have hbd : (pre soladyAbs Act m).bal dst =
        (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat := by
      rw [hpre]; simp [read, balances, hdA]
    rw [toNat_word hv256]; omega
  · rw [hw, moveWorld]
    exact FrameKeeps.sstore (bal_mem _ hdA) (FrameKeeps.sstore (bal_mem _ hcA) frameKeeps_refl)
  · rw [hl]
    simp [M, Solady.soladyModel, Solady.soladyEvents, Spec.eventLog]

end Verified.Solady.Spec
