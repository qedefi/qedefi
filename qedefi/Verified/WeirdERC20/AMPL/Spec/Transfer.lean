import Verified.WeirdERC20.AMPL.Spec.Approve

/-!
# AMPL under the spec: `transfer`, the bytecode runs

`transfer(to, v)` of `UFragments` (solc 0.7.6): `to ≠ 0`, `to ≠ address(this)`, the gon value
`v · gonsPerFragment` (`SafeMath.mul`), the debit and the credit (`SafeMath.sub`/`add`), one
`Transfer`, `true`. Every failure is a `REVERT`.
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

theorem ampl_add_lt_one {S v : Word} (h : S.toNat + v.toNat < 2 ^ 256) :
    ((S + v).lt v).iszero = 1 := by
  have hm : (S.toNat + v.toNat) % 2 ^ 256 = S.toNat + v.toNat := Nat.mod_eq_of_lt h
  simp only [Word.lt, Word.ofBool, BitVec.ult, BitVec.toNat_add, hm, Word.iszero]
  have : ¬ S.toNat + v.toNat < v.toNat := by omega
  simp [this]

theorem ampl_add_lt_zero {S v : Word} (h : 2 ^ 256 ≤ S.toNat + v.toNat) :
    ((S + v).lt v).iszero = 0 := by
  have hS := S.isLt
  have hm : (S.toNat + v.toNat) % 2 ^ 256 = S.toNat + v.toNat - 2 ^ 256 := by
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  simp only [Word.lt, Word.ofBool, BitVec.ult, BitVec.toNat_add, hm, Word.iszero]
  have : S.toNat + v.toNat - 2 ^ 256 < v.toNat := by omega
  simp only [this, decide_true, ite_true, beq_iff_eq]
  decide

theorem ampl_mul_eq_one {a b : Word} (ha : 0 < a.toNat) (h : b.toNat * a.toNat < 2 ^ 256) :
    Word.eq (Word.div (b * a) a) b = 1 := by
  have : Word.div (b * a) a = b := by
    apply BitVec.eq_of_toNat_eq
    simp only [Word.div, BitVec.toNat_udiv, BitVec.toNat_mul, Nat.mod_eq_of_lt h]
    exact Nat.mul_div_cancel _ ha
  simp [Word.eq, Word.ofBool, this]

theorem ampl_mul_eq_zero {a b : Word} (ha : 0 < a.toNat) (h : 2 ^ 256 ≤ b.toNat * a.toNat) :
    Word.eq (Word.div (b * a) a) b = 0 := by
  have : Word.div (b * a) a ≠ b := by
    intro e
    have := congrArg BitVec.toNat e
    simp only [Word.div, BitVec.toNat_udiv, BitVec.toNat_mul] at this
    have hlt : (b.toNat * a.toNat) % 2 ^ 256 < b.toNat * a.toNat :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) h
    have : (b.toNat * a.toNat) % 2 ^ 256 / a.toNat < b.toNat :=
      (Nat.div_lt_iff_lt_mul ha).2 hlt
    omega
  have h' : (Word.div (b * a) a == b) = false := by simpa using this
  simp [Word.eq, Word.ofBool, h']

theorem ampl_mul_ok {a b : Word} (ha : 0 < a.toNat) (h : Word.eq (Word.div (b * a) a) b ≠ 0) :
    b.toNat * a.toNat < 2 ^ 256 := by
  by_contra hc
  exact h (ampl_mul_eq_zero ha (Nat.le_of_not_lt hc))

theorem ampl_mul_toNat {a b : Word} (h : b.toNat * a.toNat < 2 ^ 256) :
    (b * a).toNat = b.toNat * a.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem ampl_pos_of_ne {v : Word} (h : v ≠ 0) : 0 < v.toNat := by
  rcases Nat.eq_zero_or_pos v.toNat with h0 | h0
  · exact absurd (BitVec.eq_of_toNat_eq (by simp [h0])) h
  · exact h0

theorem ampl_addr_ne {a b : Address} (h : ((Word.ofAddress a).eq (Word.ofAddress b)).iszero ≠ 0) :
    a ≠ b := by
  rintro rfl
  exact h (by simp [Word.eq, Word.ofBool, Word.iszero])

theorem ampl_eq_addr_zero (a : Address) :
    ((Word.ofAddress a).eq (Word.ofAddress a)).iszero = 0 := by
  simp [Word.eq, Word.ofBool, Word.iszero]

theorem ampl_eq_addr_one {a b : Address} (h : a ≠ b) :
    ((Word.ofAddress a).eq (Word.ofAddress b)).iszero = 1 := by
  have : Word.ofAddress a ≠ Word.ofAddress b := fun e => h (by
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e
    have ha : a.toNat < 2 ^ 160 := a.isLt
    have hb : b.toNat < 2 ^ 160 := b.isLt
    simp only [Word.ofAddress, BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this)
  have h' : (Word.ofAddress a == Word.ofAddress b) = false := by simpa using this
  simp [Word.eq, Word.ofBool, Word.iszero, h']

theorem ampl_gt_zero (X : Word) : (Word.gt 0#256 X).iszero = 1 :=
  Verified.Solady.Spec.iszero_gt_of_le (Nat.zero_le _)

theorem ampl_zero_add_lt (X : Word) : (Word.lt (0#256 + X) X).iszero = 1 :=
  ampl_add_lt_one (S := 0#256) (by simp [X.isLt])

theorem ampl_addr_ne' {a : Address} (h : Word.ofAddress a ≠ 0) : a ≠ 0 := by
  rintro rfl; exact h rfl

/-- The `_gonBalances` row of `a` (slot 158). -/
abbrev balSlot (crypto : Crypto) (a : Address) : Word :=
  mappingSlot crypto (Word.ofAddress a) 158#256

/-- The world after the debit of `g` gons from `src`. -/
def debitWorld (crypto : Crypto) (w : World) (t src : Address) (g : Word) : World :=
  w.sstore t (balSlot crypto src) (w.sload t (balSlot crypto src) - g)

/-- The world after the move of `g` gons from `src` to `dst`: the debit, then the credit read
after it. -/
def moveWorld (crypto : Crypto) (w : World) (t src dst : Address) (g : Word) : World :=
  (debitWorld crypto w t src g).sstore t (balSlot crypto dst)
    (g + (debitWorld crypto w t src g).sload t (balSlot crypto dst))

/-- `transfer(dst, v)`'s code-level end: a value, a zero or self recipient, or a gon value
above the balance (wrapping included) revert; otherwise (when the credit fits) the move of
`v · gonsPerFragment` gons, `true`, one `Transfer`. -/
def TransferPost (m : Machine) (dst : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.value ≠ 0 → ∃ out, o = .revert out) ∧
  (dst = 0 ∨ dst = m.frame.msg.currentTarget ∨
    (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat <
      (m.world.sload m.frame.msg.currentTarget 157#256).toNat * v.toNat →
    ∃ out, o = .revert out) ∧
  (dst ≠ 0 → dst ≠ m.frame.msg.currentTarget →
    (m.world.sload m.frame.msg.currentTarget 157#256).toNat * v.toNat ≤
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat →
    ((debitWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller
      (m.world.sload m.frame.msg.currentTarget 157#256 * v)).sload m.frame.msg.currentTarget
        (balSlot m.ctx.crypto dst)).toNat +
      (m.world.sload m.frame.msg.currentTarget 157#256).toNat * v.toNat < 2 ^ 256 →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = moveWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller dst
      (m.world.sload m.frame.msg.currentTarget 157#256 * v) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (transferLog m.frame.msg.currentTarget m.frame.msg.caller dst v))

set_option maxHeartbeats 0 in
theorem transfer_low (m : Machine) (dst : Address) (v : Word) (hf : Fresh AMPL.runtimeCode m)
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
    Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  all_goals
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    have hdw : Word.ofAddress dst ≠ 0 := by with_reducible assumption
    have hd0 := ampl_addr_ne' hdw
    have hdt := ampl_addr_ne (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
      ⟨fun h => absurd hv h, fun h => ?_, fun _ _ _ _ => ⟨hv, ‹_›, ?_, ?_, rfl, rfl, ?_⟩⟩
    on_goal 2 =>
      simp only [outputData]
      apwp_norm []
      rfl
  · have hv0 : v = 0 := by with_reducible assumption
    subst hv0
    rename_i h
    rcases h with h | h | h
    · exact absurd h hd0
    · exact absurd h.symm hdt
    · simp at h
  · have hv0 : v = 0 := by with_reducible assumption
    subst hv0
    simp only [outputMachine, moveWorld, debitWorld]
    rfl
  · have hv0 : v = 0 := by with_reducible assumption
    subst hv0
    simp only [outputMachine]
    logs_simp []
    event_log [(0 : Word)]
  · have hvp := ampl_pos_of_ne (by with_reducible assumption : v ≠ 0)
    have hm := ampl_mul_ok hvp (by with_reducible assumption)
    have hsb := Verified.Solady.Spec.le_of_iszero_gt (v := m_world.sload m_msg.currentTarget 157#256 * v)
      (by with_reducible assumption)
    rw [ampl_mul_toNat hm] at hsb
    rename_i h
    rcases h with h | h | h
    · exact absurd h hd0
    · exact absurd h.symm hdt
    · exact absurd (Nat.lt_of_lt_of_le h hsb) (Nat.lt_irrefl _)
  · simp only [outputMachine]
    rfl
  · simp only [outputMachine]
    logs_simp []
    event_log [v]

set_option maxHeartbeats 0 in
theorem transfer_high (m : Machine) (dst : Address) (v : Word) (hf : Fresh AMPL.runtimeCode m)
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
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hd0 : dst = 0
  · subst hd0
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun h => absurd rfl h⟩
  have hdw : Word.ofAddress dst ≠ 0 := fun e => hd0 (by
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e
    have hs : dst.toNat < 2 ^ 160 := dst.isLt
    simp only [Word.ofAddress, BitVec.toNat_setWidth] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    simpa using this)
  by_cases hdt : dst = m_msg.currentTarget
  · have h2 : ((Word.ofAddress m_msg.currentTarget).eq (Word.ofAddress dst)).iszero = 0 := by
      rw [hdt]; exact ampl_eq_addr_zero _
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ h => absurd hdt h⟩
  have h2 := ampl_eq_addr_one (Ne.symm hdt)
  by_cases hv0 : v = 0
  · subst hv0
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    rw [ampl_gt_zero]
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    rw [ampl_zero_add_lt]
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    refine ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ => ⟨hval, hst, rfl, ?_, rfl, rfl, ?_⟩⟩
    · rcases h with h | h | h
      · exact absurd h hd0
      · exact absurd h hdt
      · simp at h
    · simp only [outputMachine, moveWorld, debitWorld]
      rfl
    · simp only [outputMachine]
      logs_simp []
      event_log [(0 : Word)]
  have hvp := ampl_pos_of_ne hv0
  pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, hv0, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  set G := m_world.sload m_msg.currentTarget 157#256 with hG
  set bS := m_world.sload m_msg.currentTarget
    (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord 158#256))
    with hbS
  by_cases hm : G.toNat * v.toNat < 2 ^ 256
  swap
  · rw [ampl_mul_eq_zero hvp (Nat.le_of_not_lt hm)]
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, hv0, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ h _ =>
      absurd (Nat.lt_of_le_of_lt h (BitVec.isLt _)) (by omega)⟩
  rw [ampl_mul_eq_one hvp hm]
  pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, hv0, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  have hgv := ampl_mul_toNat hm
  by_cases hsb : G.toNat * v.toNat ≤ bS.toNat
  swap
  · rw [Verified.Solady.Spec.iszero_gt_of_lt (v := G * v) (b := bS) (by rw [hgv]; omega)]
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, hv0, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ h => absurd h hsb⟩
  rw [Verified.Solady.Spec.iszero_gt_of_le (v := G * v) (b := bS) (by rw [hgv]; exact hsb)]
  pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, hv0, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  by_cases hfit : ((debitWorld m_ctx.crypto m_world m_msg.currentTarget m_msg.caller
      (G * v)).sload m_msg.currentTarget (balSlot m_ctx.crypto dst)).toNat + G.toNat * v.toNat <
        2 ^ 256
  swap
  · have h3 := ampl_add_lt_zero (S := G * v) (v := (debitWorld m_ctx.crypto m_world
      m_msg.currentTarget m_msg.caller (G * v)).sload m_msg.currentTarget (balSlot m_ctx.crypto dst))
      (by rw [hgv]; omega)
    simp only [debitWorld, balSlot, mappingSlot] at h3
    rw [h3]
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, hv0, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ _ h => absurd h hfit⟩
  have h3 := ampl_add_lt_one (S := G * v) (v := (debitWorld m_ctx.crypto m_world
    m_msg.currentTarget m_msg.caller (G * v)).sload m_msg.currentTarget (balSlot m_ctx.crypto dst))
    (by rw [hgv]; omega)
  simp only [debitWorld, balSlot, mappingSlot] at h3
  rw [h3]
  pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, hv0, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  refine ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ => ⟨hval, hst, rfl, ?_, rfl, rfl, ?_⟩⟩
  · rcases h with h | h | h
    · exact absurd h hd0
    · exact absurd h hdt
    · exact absurd (Nat.lt_of_lt_of_le h hsb) (Nat.lt_irrefl _)
  · simp only [outputMachine]
    rfl
  · simp only [outputMachine]
    logs_simp []
    event_log [v]

end Verified.WeirdERC20.AMPL.Spec
