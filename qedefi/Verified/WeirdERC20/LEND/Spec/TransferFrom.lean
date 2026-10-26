import Verified.WeirdERC20.LEND.Spec.Transfer

/-!
# LEND under the spec: `transferFrom`, the runs

`transferFrom(src, dst, v)` of LEND: `require(enableTransfers)`, then `StdToken.transferFrom`:
`require(balances[src] >= v)`, `require(allowed[src][caller] >= v)`,
`require(balances[dst] + v > balances[dst])`, the credit `safeAdd`, the debit `safeSub` (read
after the credit), the allowance `safeSub` (read after the move), `Transfer`, `true`.
-/

namespace Verified.WeirdERC20.LEND.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.LEND.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-- The world after `transferFrom`'s move: the credit, then the debit read after it. -/
def cdWorld (crypto : Crypto) (w : World) (t src dst : Address) (v : Word) : World :=
  (w.sstore t (balSlot crypto dst) (w.sload t (balSlot crypto dst) + v)).sstore t
    (balSlot crypto src)
    ((w.sstore t (balSlot crypto dst) (w.sload t (balSlot crypto dst) + v)).sload t
      (balSlot crypto src) - v)

/-- The world after `transferFrom`: the move, then the allowance row lowered (read after the
move). -/
def tfWorld (crypto : Crypto) (w : World) (t c src dst : Address) (v : Word) : World :=
  (cdWorld crypto w t src dst v).sstore t (allowSlot crypto src c)
    ((cdWorld crypto w t src dst v).sload t (allowSlot crypto src c) - v)

/-- The debit after the credit is covered: the debited row is the credited one, or another. -/
theorem debit_fits {w : World} {t : Address} {ks kd : Word} {v : Word}
    (hbs : v.toNat ≤ (w.sload t ks).toNat) (hbd : (w.sload t kd).toNat + v.toNat < 2 ^ 256) :
    v.toNat ≤ ((w.sstore t kd (w.sload t kd + v)).sload t ks).toNat := by
  rw [World.sload_sstore]
  split
  · rw [BitVec.toNat_add, Nat.mod_eq_of_lt hbd]; omega
  · exact hbs

/-- `transferFrom(src, dst, v)`'s code-level end, with transfers enabled: a short balance or
allowance, a zero value, a wrapping credit or (read after the move) a short allowance revert;
otherwise the move and the allowance lowered, `Transfer`, `true`. -/
def TFPost (m : Machine) (src dst : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  ((m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat < v.toNat ∨
    (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat < v.toNat ∨ v.toNat = 0 ∨
    2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat +
      v.toNat → ∃ out, o = .revert out) ∧
  (((cdWorld m.ctx.crypto m.world m.frame.msg.currentTarget src dst v).sload
      m.frame.msg.currentTarget (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat <
      v.toNat → (∃ out, o = .revert out) ∨ ∃ e, o = .halt e) ∧
  (v.toNat ≤ (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat →
    v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat → 0 < v.toNat →
    (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto dst)).toNat + v.toNat <
      2 ^ 256 →
    v.toNat ≤ ((cdWorld m.ctx.crypto m.world m.frame.msg.currentTarget src dst v).sload
      m.frame.msg.currentTarget (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = tfWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src dst v ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push (transferLog m.frame.msg.currentTarget src dst v))

set_option maxHeartbeats 0 in
theorem transferFrom_low (m : Machine) (src dst : Address) (v : Word)
    (hf : Fresh LEND.runtimeCode m)
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
  have hsel' := BNB.Spec.div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := BNB.Spec.calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, harg2, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  · have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    have hbs := BNB.Spec.le_of_lt_iszero (iszero3_ne (x := (m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++
        Bytes.ofWord 0#256))).lt v) (by with_reducible assumption))
    have hal := BNB.Spec.le_of_lt_iszero (iszero3_ne (x := (m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
        (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 1#256))))).lt v)
      (by with_reducible assumption))
    have hgt := add_gt_of (S := m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress dst) ++ Bytes.ofWord 0#256)))
      (v := v) (by with_reducible assumption)
    have ha2 := Verified.Solady.Spec.le_of_iszero_gt (iszero3_ne
      ‹(v.gt (World.sload _ m_msg.currentTarget (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ _)))).iszero.iszero.iszero ≠ 0›)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun h => ?_, fun h => ?_,
      fun _ _ _ _ _ => ⟨hv, ‹_›, ?_, rfl, rfl, rfl, ?_⟩⟩
    · simp only [balSlot, allowSlot, mappingSlot2, mappingSlot] at h
      omega
    · simp only [cdWorld, balSlot, allowSlot, mappingSlot2, mappingSlot] at h
      omega
    · simp only [outputData]
      apwp_norm []
      rfl
    · simp only [outputMachine]
      logs_simp []
      event_log [v]
  · -- infeasible: the `safeAdd` assert's short-circuit seen both ways
    exact (iszero23' (x := (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress dst) ++ Bytes.ofWord 0#256)) + v).lt
      (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress dst) ++ Bytes.ofWord 0#256))))
      (by with_reducible assumption) (by with_reducible assumption)).elim

set_option maxHeartbeats 0 in
theorem transferFrom_high (m : Machine) (src dst : Address) (v : Word)
    (hf : Fresh LEND.runtimeCode m)
    (hd : Args m.frame.msg.data 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft)
    (hen : Word.iszero (255#256 &&&
      Word.div (m.world.sload m.frame.msg.currentTarget 3#256) 256#256) = 0) :
    Halts m (TFPost m src dst v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  have harg2 := harg 2 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1 harg2
  have hsel' := BNB.Spec.div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := BNB.Spec.calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hbs : v.toNat ≤ (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto src)).toNat
  swap
  · have h3 := BNB.Spec.lt_iszero_zero (Nat.lt_of_not_le hbs)
    simp only [balSlot, mappingSlot] at h3
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, hen, h3, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ => .inl ⟨_, rfl⟩, fun h => absurd h hbs⟩
  have h3 := BNB.Spec.lt_iszero_one hbs
  simp only [balSlot, mappingSlot] at h3
  by_cases hal : v.toNat ≤
      (m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto src m_msg.caller)).toNat
  swap
  · have h4 := BNB.Spec.lt_iszero_zero (Nat.lt_of_not_le hal)
    simp only [allowSlot, mappingSlot2, mappingSlot] at h4
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, hen, h3, h4,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ => .inl ⟨_, rfl⟩, fun _ h => absurd h hal⟩
  have h4 := BNB.Spec.lt_iszero_one hal
  simp only [allowSlot, mappingSlot2, mappingSlot] at h4
  by_cases hok : 0 < v.toNat ∧
      (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto dst)).toNat + v.toNat < 2 ^ 256
  swap
  · have h5 := add_gt_zero (S := m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto dst))
      (v := v) (by omega)
    simp only [balSlot, mappingSlot] at h5
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, hen, h3, h4, h5,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ => .inl ⟨_, rfl⟩, fun _ _ h1 h2 => absurd ⟨h1, h2⟩ hok⟩
  obtain ⟨hv0, hbd⟩ := hok
  have h5 := add_gt_one (S := m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto dst))
    hv0 hbd
  have h6 := Verified.Solady.Spec.lt_add_iszero_one hbd
  have h7 := BNB.Spec.lt_add_iszero_one' hbd
  have h8 := Verified.Solady.Spec.iszero_gt_of_le
    (debit_fits (t := m_msg.currentTarget) hbs hbd)
  simp only [balSlot, mappingSlot] at h5 h6 h7 h8
  by_cases ha2 : v.toNat ≤ ((cdWorld m_ctx.crypto m_world m_msg.currentTarget src dst v).sload
      m_msg.currentTarget (allowSlot m_ctx.crypto src m_msg.caller)).toNat
  swap
  · have h9 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le ha2)
    simp only [cdWorld, allowSlot, balSlot, mappingSlot2, mappingSlot] at h9
    pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, hen, h3, h4, h5, h6, h7, h8, h9,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    refine WP.halt_of_step (step_invalid (by pcode_fact)) (.refl _) ⟨fun h => ?_,
      fun _ => .inr ⟨_, rfl⟩, fun _ _ _ _ h => absurd h ha2⟩
    dsimp only at h
    omega
  have h9 := Verified.Solady.Spec.iszero_gt_of_le ha2
  simp only [cdWorld, allowSlot, balSlot, mappingSlot2, mappingSlot] at h9
  pwp_steps [hval, hst, hsel', hz, harg0, harg1, harg2, hen, h3, h4, h5, h6, h7, h8, h9,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  refine ⟨fun h => ?_, fun h => ?_, fun _ _ _ _ _ => ⟨hval, hst, rfl, rfl, rfl, rfl, ?_⟩⟩
  · dsimp only at h
    omega
  · dsimp only at h
    omega
  · simp only [outputMachine]
    logs_simp []
    event_log [v]

end Verified.WeirdERC20.LEND.Spec
