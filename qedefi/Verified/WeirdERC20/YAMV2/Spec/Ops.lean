import Verified.WeirdERC20.YAMV2.Spec.Approve

/-!
# YAMv2 under the spec: `mint` and `increaseAllowance`, the bytecode runs

* `mint(dst, x)`: only the minter (`minter`, slot 0), `dst ≠ 0`, `SafeMath.add` on the supply
  and on `dst`'s balance, `Transfer(0, dst, x)`;
* `increaseAllowance(sp, x)`: `SafeMath.add` on `allowance[caller][sp]`, then `_approve`'s
  zero checks.
-/

namespace Verified.WeirdERC20.YAMV2.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.YAMV2.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626
open Verified.WeirdERC20.AMPL.Spec (iszero_lt_size ampl_addr_ne')

/-- solc reads an `address` variable by masking its slot. -/
theorem and_addressMask_eq (w : Word) :
    w &&& 1461501637330902918203684832716283019655932542975#256 =
      Word.ofAddress (Word.toAddress w) := by
  apply BitVec.eq_of_toNat_eq
  have h := w.isLt
  simp only [Word.ofAddress, Word.toAddress, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by decide : 1461501637330902918203684832716283019655932542975 < 2 ^ 256),
    show (1461501637330902918203684832716283019655932542975 : Nat) = 2 ^ 160 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega : w.toNat % 2 ^ 160 < 2 ^ 256)]

theorem addressMask_and_eq (w : Word) :
    1461501637330902918203684832716283019655932542975#256 &&& w =
      Word.ofAddress (Word.toAddress w) := by
  rw [BitVec.and_comm]; exact and_addressMask_eq w

/-- `EQ` of two different addresses. -/
theorem eq_ofAddress_ne {a b : Address} (h : a ≠ b) :
    Word.eq (Word.ofAddress a) (Word.ofAddress b) = 0 := by
  have : Word.ofAddress a ≠ Word.ofAddress b := fun e => h (by
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e
    have ha : a.toNat < 2 ^ 160 := a.isLt
    have hb : b.toNat < 2 ^ 160 := b.isLt
    simp only [Word.ofAddress, BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this)
  have h' : (Word.ofAddress a == Word.ofAddress b) = false := by simpa using this
  simp [Word.eq, Word.ofBool, h']

/-- A `SafeMath.add` check that passed: the sum fits. -/
theorem add_fit_of_iszero {S v : Word} (h : ((S + v).lt v).iszero ≠ 0) :
    S.toNat + v.toNat < 2 ^ 256 := by
  by_contra hc
  exact h (Verified.WeirdERC20.AMPL.Spec.ampl_add_lt_zero (Nat.le_of_not_lt hc))

/-- The world after `mint(dst, x)`: the supply, then `dst`'s balance read after it. -/
def mintWorld (crypto : Crypto) (w : World) (t dst : Address) (x : Word) : World :=
  (w.sstore t 3#256 (x + w.sload t 3#256)).sstore t (balSlot crypto dst)
    (x + (w.sstore t 3#256 (x + w.sload t 3#256)).sload t (balSlot crypto dst))

/-- `mint(dst, x)`'s code-level end. -/
def MintPost (m : Machine) (dst : Address) (x : Word) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.value ≠ 0 → ∃ out, o = .revert out) ∧
  (m.frame.msg.caller ≠ Word.toAddress (m.world.sload m.frame.msg.currentTarget 0#256) ∨
    dst = 0 ∨ 2 ^ 256 ≤ x.toNat + (m.world.sload m.frame.msg.currentTarget 3#256).toNat →
    ∃ out, o = .revert out) ∧
  (m.frame.msg.caller = Word.toAddress (m.world.sload m.frame.msg.currentTarget 0#256) →
    dst ≠ 0 → x.toNat + (m.world.sload m.frame.msg.currentTarget 3#256).toNat < 2 ^ 256 →
    x.toNat + ((m.world.sstore m.frame.msg.currentTarget 3#256
      (x + m.world.sload m.frame.msg.currentTarget 3#256)).sload m.frame.msg.currentTarget
        (balSlot m.ctx.crypto dst)).toNat < 2 ^ 256 →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ (∃ out, o = .success out) ∧
    mf.world = mintWorld m.ctx.crypto m.world m.frame.msg.currentTarget dst x ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem mint_low (m : Machine) (dst : Address) (x : Word) (hf : Fresh YAMV2.runtimeCode m)
    (hd : Args m.frame.msg.data 0x40c10f19 [Word.ofAddress dst, x])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (MintPost m dst x) := by
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
    and_addressMask_eq, addressMask_and_eq, Word.toAddress_ofAddress, Memory.read_64,
    Abi.shr_calldataload_zero, Solidity.eq_self]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  have hd0 := ampl_addr_ne' (by with_reducible assumption : Word.ofAddress dst ≠ 0)
  have hS := add_fit_of_iszero (by with_reducible assumption :
    ((x + m_world.sload m_msg.currentTarget 3#256).lt
      (m_world.sload m_msg.currentTarget 3#256)).iszero ≠ 0)
  have hmin : m_msg.caller = Word.toAddress (m_world.sload m_msg.currentTarget 0#256) := by
    by_contra hne
    have h1 : (Word.ofAddress m_msg.caller).eq
        (Word.ofAddress (m_world.sload m_msg.currentTarget 0#256).toAddress) ≠ 0 := by
      with_reducible assumption
    exact h1 (eq_ofAddress_ne hne)
  refine WP.halt_of_step (step_stop (by pcode_fact)) (by same_frame) (hok _ _
    ⟨fun h => absurd hv h, fun h => ?_, fun _ _ _ _ => ⟨hv, ‹_›, ⟨_, rfl⟩, rfl, rfl, rfl⟩⟩)
  rcases h with h | h | h
  · exact absurd hmin h
  · exact absurd h hd0
  · dsimp only at h; omega

set_option maxHeartbeats 0 in
theorem mint_high (m : Machine) (dst : Address) (x : Word) (hf : Fresh YAMV2.runtimeCode m)
    (hd : Args m.frame.msg.data 0x40c10f19 [Word.ofAddress dst, x])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (MintPost m dst x) := by
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
  by_cases hmin : m_msg.caller = Word.toAddress (m_world.sload m_msg.currentTarget 0#256)
  swap
  · have he := eq_ofAddress_ne hmin
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, he, ofAddress_and_addressMask,
      addressMask_and_ofAddress, and_addressMask_eq, addressMask_and_eq, Word.toAddress_ofAddress,
      Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun h => absurd h hmin⟩
  have he : (Word.ofAddress m_msg.caller).eq
      (Word.ofAddress (m_world.sload m_msg.currentTarget 0#256).toAddress) = 1#256 := by
    rw [← hmin]; exact Solidity.eq_self _
  by_cases hd0 : dst = 0
  · subst hd0
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, he, ofAddress_and_addressMask,
      addressMask_and_ofAddress, and_addressMask_eq, addressMask_and_eq, Word.toAddress_ofAddress,
      Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ h => absurd rfl h⟩
  have hdw := ofAddress_ne_zero hd0
  by_cases hS : x.toNat + (m_world.sload m_msg.currentTarget 3#256).toNat < 2 ^ 256
  swap
  · have h3 := Verified.WeirdERC20.AMPL.Spec.ampl_add_lt_zero (S := x)
      (v := m_world.sload m_msg.currentTarget 3#256) (by omega)
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, he, hdw, h3, ofAddress_and_addressMask,
      addressMask_and_ofAddress, and_addressMask_eq, addressMask_and_eq, Word.toAddress_ofAddress,
      Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ h => absurd h hS⟩
  have h3 := Verified.WeirdERC20.AMPL.Spec.ampl_add_lt_one (S := x)
    (v := m_world.sload m_msg.currentTarget 3#256) hS
  by_cases hB : x.toNat + ((m_world.sstore m_msg.currentTarget 3#256
      (x + m_world.sload m_msg.currentTarget 3#256)).sload m_msg.currentTarget
        (balSlot m_ctx.crypto dst)).toNat < 2 ^ 256
  swap
  · have h4 := Verified.WeirdERC20.AMPL.Spec.ampl_add_lt_zero (S := x)
      (v := (m_world.sstore m_msg.currentTarget 3#256
        (x + m_world.sload m_msg.currentTarget 3#256)).sload m_msg.currentTarget
          (balSlot m_ctx.crypto dst)) (by omega)
    simp only [balSlot, mappingSlot] at h4
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, he, hdw, h3, h4,
      ofAddress_and_addressMask, addressMask_and_ofAddress, and_addressMask_eq,
      addressMask_and_eq, Word.toAddress_ofAddress, Memory.read_64, Abi.shr_calldataload_zero,
      Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ _ h => absurd h hB⟩
  have h4 := Verified.WeirdERC20.AMPL.Spec.ampl_add_lt_one (S := x)
    (v := (m_world.sstore m_msg.currentTarget 3#256
      (x + m_world.sload m_msg.currentTarget 3#256)).sload m_msg.currentTarget
        (balSlot m_ctx.crypto dst)) hB
  simp only [balSlot, mappingSlot] at h4
  pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, he, hdw, h3, h4,
    ofAddress_and_addressMask, addressMask_and_ofAddress, and_addressMask_eq,
    addressMask_and_eq, Word.toAddress_ofAddress, Memory.read_64, Abi.shr_calldataload_zero,
    Solidity.eq_self]
  refine WP.halt_of_step (step_stop (by pcode_fact)) (by same_frame) ?_
  refine ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ _ => ⟨hval, hst, ⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  rcases h with h | h | h
  · exact absurd hmin h
  · exact absurd h hd0
  · dsimp only at h; omega

/-- `increaseAllowance(sp, x)`'s code-level end. -/
def IncreasePost (m : Machine) (sp : Address) (x : Word) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.value ≠ 0 → ∃ out, o = .revert out) ∧
  (m.frame.msg.caller = 0 ∨ sp = 0 ∨ 2 ^ 256 ≤ x.toNat +
    (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat →
    ∃ out, o = .revert out) ∧
  (m.frame.msg.caller ≠ 0 → sp ≠ 0 → x.toNat +
    (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat
      < 2 ^ 256 →
    m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧ (∃ out, o = .success out) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)
      (x + m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp)) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem increase_low (m : Machine) (sp : Address) (x : Word) (hf : Fresh YAMV2.runtimeCode m)
    (hd : Args m.frame.msg.data 0x39509351 [Word.ofAddress sp, x])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (IncreasePost m sp x) := by
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
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  have hc0 := ampl_addr_ne' (by with_reducible assumption : Word.ofAddress m_msg.caller ≠ 0)
  have hs0 := ampl_addr_ne' (by with_reducible assumption : Word.ofAddress sp ≠ 0)
  have hA0 : ((x + m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto m_msg.caller sp)).lt
      (m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto m_msg.caller sp))).iszero ≠ 0 := by
    simp only [allowSlot, mappingSlot2, mappingSlot]; with_reducible assumption
  have hA := add_fit_of_iszero hA0
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
    ⟨fun h => absurd hv h, fun h => ?_, fun _ _ _ => ⟨hv, ‹_›, ⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  rcases h with h | h | h
  · exact absurd h hc0
  · exact absurd h hs0
  · dsimp only at h; omega

set_option maxHeartbeats 0 in
theorem increase_high (m : Machine) (sp : Address) (x : Word) (hf : Fresh YAMV2.runtimeCode m)
    (hd : Args m.frame.msg.data 0x39509351 [Word.ofAddress sp, x])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (IncreasePost m sp x) := by
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
  by_cases hA : x.toNat +
      (m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto m_msg.caller sp)).toNat < 2 ^ 256
  swap
  · have h3 := Verified.WeirdERC20.AMPL.Spec.ampl_add_lt_zero (S := x)
      (v := m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto m_msg.caller sp)) (by omega)
    simp only [allowSlot, mappingSlot2, mappingSlot] at h3
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, h3, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ _ h => absurd h hA⟩
  have h3 := Verified.WeirdERC20.AMPL.Spec.ampl_add_lt_one (S := x)
    (v := m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto m_msg.caller sp)) hA
  simp only [allowSlot, mappingSlot2, mappingSlot] at h3
  by_cases hc0 : m_msg.caller = 0
  · have hcw0 : Word.ofAddress m_msg.caller = 0#256 := by rw [hc0]; rfl
    rw [hcw0] at h3
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, h3, hcw0, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self,
      loadWord_write_of_disjoint, Memory.size_write, size_readBytes]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun h => absurd hc0 h⟩
  have hcw := ofAddress_ne_zero hc0
  by_cases hs0 : sp = 0
  · subst hs0
    rw [show Word.ofAddress (0 : Address) = 0#256 from rfl] at h3
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, h3, hcw, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self,
      loadWord_write_of_disjoint, Memory.size_write, size_readBytes]
    exact ⟨fun h => absurd hval h, fun _ => ⟨_, rfl⟩, fun _ h => absurd rfl h⟩
  have hsw := ofAddress_ne_zero hs0
  pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, h3, hcw, hsw, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  refine ⟨fun h => absurd hval h, fun h => ?_, fun _ _ _ => ⟨hval, hst, ⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  rcases h with h | h | h
  · exact absurd h hc0
  · exact absurd h hs0
  · dsimp only at h; omega

end Verified.WeirdERC20.YAMV2.Spec
