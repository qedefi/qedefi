import Verified.WeirdERC20.AMPL.Spec.Transfer

/-!
# AMPL under the spec: `transferFrom`, the bytecode runs

`transferFrom(from, to, v)` of `UFragments`: `to ≠ 0`, `to ≠ address(this)`, the allowance
lowered by `v` (`SafeMath.sub`), then (reading `gonsPerFragment` and the balances after that
write) the move of `v · gonsPerFragment` gons, one `Transfer`, `true`. Every failure reverts.
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-- The `_allowedFragments` row of `o` for `sp` (slot 159). -/
abbrev allowSlot (crypto : Crypto) (o sp : Address) : Word :=
  mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 159#256

/-- The world after the allowance of `src` for `c` is lowered by `v`. -/
def allowWorld (crypto : Crypto) (w : World) (t c src : Address) (v : Word) : World :=
  w.sstore t (allowSlot crypto src c) (w.sload t (allowSlot crypto src c) - v)

/-- `transferFrom(src, dst, v)`'s code-level end: a value, a zero or self recipient, an
allowance below `v`, or a gon value (read after the allowance write) above the balance revert;
otherwise (when the credit fits) the allowance lowered and the move, `true`, one `Transfer`. -/
def TFPost (m : Machine) (src dst : Address) (v : Word) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.value ≠ 0 → ∃ out, o = .revert out) ∧
  (dst = 0 ∨ dst = m.frame.msg.currentTarget ∨
    (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat < v.toNat ∨
    ((allowWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src v).sload
      m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat <
      ((allowWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src v).sload
        m.frame.msg.currentTarget 157#256).toNat * v.toNat →
    ∃ out, o = .revert out) ∧
  (dst ≠ 0 → dst ≠ m.frame.msg.currentTarget →
    v.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto src m.frame.msg.caller)).toNat →
    ((allowWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src v).sload
        m.frame.msg.currentTarget 157#256).toNat * v.toNat ≤
      ((allowWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src v).sload
        m.frame.msg.currentTarget (balSlot m.ctx.crypto src)).toNat →
    ((debitWorld m.ctx.crypto
        (allowWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src v)
        m.frame.msg.currentTarget src
        ((allowWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src v).sload
          m.frame.msg.currentTarget 157#256 * v)).sload m.frame.msg.currentTarget
        (balSlot m.ctx.crypto dst)).toNat +
      ((allowWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src v).sload
        m.frame.msg.currentTarget 157#256).toNat * v.toNat < 2 ^ 256 →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ o = .success (Bytes.ofWord 1) ∧
    mf.world = moveWorld m.ctx.crypto
      (allowWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src v)
      m.frame.msg.currentTarget src dst
      ((allowWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller src v).sload
        m.frame.msg.currentTarget 157#256 * v) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push (transferLog m.frame.msg.currentTarget src dst v))

set_option maxHeartbeats 0 in
theorem transferFrom_low (m : Machine) (src dst : Address) (v : Word)
    (hf : Fresh AMPL.runtimeCode m)
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
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, harg2, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  all_goals
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    have hdw : Word.ofAddress dst ≠ 0 := by with_reducible assumption
    have hd0 := ampl_addr_ne' hdw
    have hdt := ampl_addr_ne (by with_reducible assumption)
    have hac := Verified.Solady.Spec.le_of_iszero_gt (b := m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 159#256)))))
      (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
      ⟨fun h => absurd hv h, fun h => ?_, fun _ _ _ _ _ => ⟨hv, ‹_›, ?_, ?_, rfl, rfl, ?_⟩⟩
    on_goal 2 =>
      simp only [outputData]
      apwp_norm []
      rfl
  · have hv0 : v = 0 := by with_reducible assumption
    subst hv0
    rename_i h
    rcases h with h | h | h | h
    · exact absurd h hd0
    · exact absurd h.symm hdt
    · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)
    · simp at h
  · have hv0 : v = 0 := by with_reducible assumption
    subst hv0
    simp only [outputMachine, moveWorld, debitWorld, allowWorld]
    rfl
  · have hv0 : v = 0 := by with_reducible assumption
    subst hv0
    simp only [outputMachine]
    logs_simp []
    event_log [(0 : Word)]
  · have hvp := ampl_pos_of_ne (by with_reducible assumption : v ≠ 0)
    have hm := ampl_mul_ok hvp (by with_reducible assumption)
    have hsb := Verified.Solady.Spec.le_of_iszero_gt (v := (m_world.sstore m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 159#256))))
      (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 159#256)))) - v)).sload m_msg.currentTarget 157#256 * v)
      (by with_reducible assumption)
    rw [ampl_mul_toNat hm] at hsb
    rename_i h
    rcases h with h | h | h | h
    · exact absurd h hd0
    · exact absurd h.symm hdt
    · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)
    · exact absurd (Nat.lt_of_lt_of_le h hsb) (Nat.lt_irrefl _)
  · simp only [outputMachine]
    rfl
  · simp only [outputMachine]
    logs_simp []
    event_log [v]

set_option maxHeartbeats 0 in
theorem transferFrom_high (m : Machine) (src dst : Address) (v : Word)
    (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0x23b872dd [Word.ofAddress src, Word.ofAddress dst, v])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (TFPost m src dst v) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  have harg2 := harg 2 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1 harg2
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 96) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hd0 : dst = 0
  · subst hd0
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, ofAddress_and_addressMask,
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
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hdw, h2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ h => absurd hdt h⟩
  have h2 := ampl_eq_addr_one (Ne.symm hdt)
  by_cases hac : v.toNat ≤
      (m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto src m_msg.caller)).toNat
  swap
  · have ha1 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le hac)
    simp only [allowSlot, mappingSlot2, mappingSlot] at ha1
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hdw, h2, ha1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ h => absurd h hac⟩
  have ha1 := Verified.Solady.Spec.iszero_gt_of_le hac
  simp only [allowSlot, mappingSlot2, mappingSlot] at ha1
  by_cases hv0 : v = 0
  · subst hv0
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hdw, h2, ha1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    rw [ampl_gt_zero]
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hdw, h2, ha1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    rw [ampl_zero_add_lt]
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hdw, h2, ha1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    refine ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ _ => ⟨hval, hst, rfl, ?_, rfl, rfl, ?_⟩⟩
    · rcases h with h | h | h | h
      · exact absurd h hd0
      · exact absurd h hdt
      · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)
      · simp at h
    · simp only [outputMachine, moveWorld, debitWorld, allowWorld]
      rfl
    · simp only [outputMachine]
      logs_simp []
      event_log [(0 : Word)]
  have hvp := ampl_pos_of_ne hv0
  pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hdw, h2, ha1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, hv0]
  set G := (m_world.sstore m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 159#256))))
      (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 159#256)))) - v)).sload m_msg.currentTarget 157#256 with hG
  set bS := (m_world.sstore m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 159#256))))
      (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 159#256)))) - v)).sload m_msg.currentTarget
    (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 158#256)) with hbS
  by_cases hm : G.toNat * v.toNat < 2 ^ 256
  swap
  · rw [ampl_mul_eq_zero hvp (Nat.le_of_not_lt hm)]
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hdw, h2, ha1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, hv0]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ _ h _ => by
      have h' : G.toNat * v.toNat ≤ bS.toNat := h
      have := bS.isLt
      omega⟩
  rw [ampl_mul_eq_one hvp hm]
  pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hdw, h2, ha1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, hv0]
  have hgv := ampl_mul_toNat hm
  by_cases hsb : G.toNat * v.toNat ≤ bS.toNat
  swap
  · rw [Verified.Solady.Spec.iszero_gt_of_lt (v := G * v) (b := bS) (by rw [hgv]; omega)]
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hdw, h2, ha1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, hv0]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ _ h => absurd h hsb⟩
  rw [Verified.Solady.Spec.iszero_gt_of_le (v := G * v) (b := bS) (by rw [hgv]; exact hsb)]
  pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hdw, h2, ha1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, hv0]
  by_cases hfit : ((debitWorld m_ctx.crypto (m_world.sstore m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 159#256))))
      (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 159#256)))) - v)) m_msg.currentTarget src
      (G * v)).sload m_msg.currentTarget (balSlot m_ctx.crypto dst)).toNat + G.toNat * v.toNat <
        2 ^ 256
  swap
  · have h3 := ampl_add_lt_zero (S := G * v) (v := (debitWorld m_ctx.crypto (m_world.sstore m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 159#256))))
      (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 159#256)))) - v))
      m_msg.currentTarget src (G * v)).sload m_msg.currentTarget (balSlot m_ctx.crypto dst))
      (by rw [hgv]; omega)
    simp only [debitWorld, balSlot, mappingSlot] at h3
    rw [h3]
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hdw, h2, ha1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, hv0]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ _ _ h => absurd h hfit⟩
  have h3 := ampl_add_lt_one (S := G * v) (v := (debitWorld m_ctx.crypto (m_world.sstore m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 159#256))))
      (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 159#256)))) - v))
    m_msg.currentTarget src (G * v)).sload m_msg.currentTarget (balSlot m_ctx.crypto dst))
    (by rw [hgv]; omega)
  simp only [debitWorld, balSlot, mappingSlot] at h3
  rw [h3]
  pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, harg2, hdw, h2, ha1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self, hv0]
  refine ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ _ => ⟨hval, hst, rfl, ?_, rfl, rfl, ?_⟩⟩
  · rcases h with h | h | h | h
    · exact absurd h hd0
    · exact absurd h hdt
    · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)
    · exact absurd (Nat.lt_of_lt_of_le h hsb) (Nat.lt_irrefl _)
  · simp only [outputMachine]
    rfl
  · simp only [outputMachine]
    logs_simp []
    event_log [v]

end Verified.WeirdERC20.AMPL.Spec
