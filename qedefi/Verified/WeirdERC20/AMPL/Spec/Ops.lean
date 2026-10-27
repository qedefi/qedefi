import Verified.WeirdERC20.AMPL.Spec.TransferFromCall
import Verified.WeirdERC20.AMPL.Spec.Fallback

/-!
# AMPL under the spec: `transferAll`, `transferAllFrom`, `increaseAllowance`, `decreaseAllowance`

`transferAll(to)`: `to ≠ 0`, `to ≠ address(this)`, `gonsPerFragment > 0` (`SafeMath.div`), the
caller's row deleted and `to` credited with all of its gons (`SafeMath.add`), `true`.
`transferAllFrom(from, to)`: the same checks, the allowance of `from` for the caller lowered by
the fragment value `gons / gonsPerFragment` (`SafeMath.sub`), then the move of all of `from`'s
gons. `increaseAllowance(sp, x)`: the allowance raised (`SafeMath.add`). `decreaseAllowance(sp,
x)`: the allowance lowered, to zero when `x` covers it. Every failure reverts.
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

theorem ampl_gt_zero_one {x : Word} (h : x ≠ 0) : Word.gt x 0#256 = 1 := by
  have : BitVec.ult 0#256 x = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.zero_mod, decide_eq_true_eq]
    exact ampl_pos_of_ne h
  simp [Word.gt, Word.ofBool, this]

theorem ampl_add_ok {S v : Word} (h : ((S + v).lt v).iszero ≠ 0) :
    S.toNat + v.toNat < 2 ^ 256 := by
  by_contra hc
  exact h (ampl_add_lt_zero (Nat.le_of_not_lt hc))

/-- The world after `transferAll` from `c` to `d`: `c`'s row deleted, then `d` credited with
`g` gons (read after the delete). -/
def allWorld (crypto : Crypto) (w : World) (t c d : Address) (g : Word) : World :=
  (w.sstore t (balSlot crypto c) 0#256).sstore t (balSlot crypto d)
    (g + (w.sstore t (balSlot crypto c) 0#256).sload t (balSlot crypto d))

/-- `transferAll(d)`'s code-level end. -/
def TAPost (m : Machine) (d : Address) (mf : Machine) (o : Outcome) : Prop :=
  (d = 0 ∨ d = m.frame.msg.currentTarget ∨ m.world.sload m.frame.msg.currentTarget 157#256 = 0 →
    Fails o) ∧
  (d ≠ 0 → d ≠ m.frame.msg.currentTarget → m.world.sload m.frame.msg.currentTarget 157#256 ≠ 0 →
    (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)).toNat +
      ((m.world.sstore m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)
        0#256).sload m.frame.msg.currentTarget (balSlot m.ctx.crypto d)).toNat < 2 ^ 256 →
    (∃ out, o = .success out) ∧
    mf.world = allWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller d
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto m.frame.msg.caller)) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem transferAll_low (m : Machine) (d : Address) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa3a7e7f3 [Word.ofAddress d])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (TAPost m d) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
    Nat.mul_zero, Nat.add_zero] at hsize harg0
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  have hd0 := ampl_addr_ne' (by with_reducible assumption)
  have hdt := ampl_addr_ne (by with_reducible assumption)
  have hG : m_world.sload m_msg.currentTarget 157#256 ≠ 0 := by with_reducible assumption
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun h => ?_, fun _ _ _ _ =>
    ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  rcases h with h | h | h
  · exact absurd h hd0
  · exact absurd h.symm hdt
  · exact absurd h hG

set_option maxHeartbeats 0 in
theorem transferAll_high (m : Machine) (d : Address) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa3a7e7f3 [Word.ofAddress d])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (TAPost m d) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
    Nat.mul_zero, Nat.add_zero] at hsize harg0
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 32) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hd0 : d = 0
  · subst hd0
    pwp_steps [hval, hst, hsel', hz, hl, harg0, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun _ => trivial, fun h => absurd rfl h⟩
  have hdw : Word.ofAddress d ≠ 0 := fun e => hd0 (by
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e
    have hs : d.toNat < 2 ^ 160 := d.isLt
    simp only [Word.ofAddress, BitVec.toNat_setWidth] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    simpa using this)
  by_cases hdt : d = m_msg.currentTarget
  · have h2 : ((Word.ofAddress m_msg.currentTarget).eq (Word.ofAddress d)).iszero = 0 := by
      rw [hdt]; exact ampl_eq_addr_zero _
    pwp_steps [hval, hst, hsel', hz, hl, harg0, hdw, h2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun _ => trivial, fun _ h => absurd hdt h⟩
  have h2 := ampl_eq_addr_one (Ne.symm hdt)
  by_cases hG : m_world.sload m_msg.currentTarget 157#256 = 0
  · pwp_steps [hval, hst, hsel', hz, hl, harg0, hdw, h2, hG, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun _ => trivial, fun _ _ h => absurd hG h⟩
  have h3 := ampl_gt_zero_one hG
  by_cases hfit : (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto m_msg.caller)).toNat +
      ((m_world.sstore m_msg.currentTarget (balSlot m_ctx.crypto m_msg.caller) 0#256).sload
        m_msg.currentTarget (balSlot m_ctx.crypto d)).toNat < 2 ^ 256
  swap
  · have h4 := ampl_add_lt_zero (Nat.le_of_not_lt hfit)
    simp only [balSlot, mappingSlot] at h4
    pwp_steps [hval, hst, hsel', hz, hl, harg0, hdw, h2, h3, hG, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    rw [h4]
    pwp_steps [hval, hst, hsel', hz, hl, harg0, hdw, h2, h3, hG, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun _ => trivial, fun _ _ _ h => absurd h hfit⟩
  have h4 := ampl_add_lt_one hfit
  simp only [balSlot, mappingSlot] at h4
  pwp_steps [hval, hst, hsel', hz, hl, harg0, hdw, h2, h3, hG, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  rw [h4]
  pwp_xsteps [hval, hst, hsel', hz, hl, harg0, hdw, h2, h3, hG, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  exact ⟨fun h => by
      rcases h with h | h | h
      · exact absurd h hd0
      · exact absurd h hdt
      · exact absurd h hG,
    fun _ _ _ _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩

/-- The world after `transferAllFrom(a, d)` by `c`: the allowance lowered by the fragment value
`v`, then the move of `g` gons (`a`'s row deleted, `d` credited, both read after the writes). -/
def allFromWorld (crypto : Crypto) (w : World) (t c a d : Address) (g v : Word) : World :=
  allWorld crypto (w.sstore t (allowSlot crypto a c) (w.sload t (allowSlot crypto a c) - v)) t a d g

/-- `transferAllFrom(a, d)`'s code-level end. -/
def TAFPost (m : Machine) (a d : Address) (mf : Machine) (o : Outcome) : Prop :=
  (d = 0 ∨ d = m.frame.msg.currentTarget ∨ m.world.sload m.frame.msg.currentTarget 157#256 = 0 ∨
    (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto a m.frame.msg.caller)).toNat <
      (Word.div (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a))
        (m.world.sload m.frame.msg.currentTarget 157#256)).toNat → Fails o) ∧
  (d ≠ 0 → d ≠ m.frame.msg.currentTarget → m.world.sload m.frame.msg.currentTarget 157#256 ≠ 0 →
    (Word.div (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a))
        (m.world.sload m.frame.msg.currentTarget 157#256)).toNat ≤
      (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto a m.frame.msg.caller)).toNat →
    (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a)).toNat +
      (((m.world.sstore m.frame.msg.currentTarget (allowSlot m.ctx.crypto a m.frame.msg.caller)
        (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto a m.frame.msg.caller) -
          Word.div (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a))
            (m.world.sload m.frame.msg.currentTarget 157#256))).sstore m.frame.msg.currentTarget
        (balSlot m.ctx.crypto a) 0#256).sload m.frame.msg.currentTarget
          (balSlot m.ctx.crypto d)).toNat < 2 ^ 256 →
    (∃ out, o = .success out) ∧
    mf.world = allFromWorld m.ctx.crypto m.world m.frame.msg.currentTarget m.frame.msg.caller a d
      (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a))
      (Word.div (m.world.sload m.frame.msg.currentTarget (balSlot m.ctx.crypto a))
        (m.world.sload m.frame.msg.currentTarget 157#256)) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem transferAllFrom_low (m : Machine) (a d : Address) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0x84d4b410 [Word.ofAddress a, Word.ofAddress d])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (TAFPost m a d) := by
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
  have hd0 := ampl_addr_ne' (by with_reducible assumption)
  have hdt := ampl_addr_ne (by with_reducible assumption)
  have hG : m_world.sload m_msg.currentTarget 157#256 ≠ 0 := by with_reducible assumption
  have hac := Verified.Solady.Spec.le_of_iszero_gt (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun h => ?_, fun _ _ _ _ _ =>
    ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  rcases h with h | h | h | h
  · exact absurd h hd0
  · exact absurd h.symm hdt
  · exact absurd h hG
  · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _)

set_option maxHeartbeats 0 in
theorem transferAllFrom_high (m : Machine) (a d : Address) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0x84d4b410 [Word.ofAddress a, Word.ofAddress d])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (TAFPost m a d) := by
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
  by_cases hd0 : d = 0
  · subst hd0
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun _ => trivial, fun h => absurd rfl h⟩
  have hdw : Word.ofAddress d ≠ 0 := fun e => hd0 (by
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e
    have hs : d.toNat < 2 ^ 160 := d.isLt
    simp only [Word.ofAddress, BitVec.toNat_setWidth] at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    simpa using this)
  by_cases hdt : d = m_msg.currentTarget
  · have h2 : ((Word.ofAddress m_msg.currentTarget).eq (Word.ofAddress d)).iszero = 0 := by
      rw [hdt]; exact ampl_eq_addr_zero _
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun _ => trivial, fun _ h => absurd hdt h⟩
  have h2 := ampl_eq_addr_one (Ne.symm hdt)
  by_cases hG : m_world.sload m_msg.currentTarget 157#256 = 0
  · pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, hG, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun _ => trivial, fun _ _ h => absurd hG h⟩
  have h3 := ampl_gt_zero_one hG
  by_cases hac : (Word.div (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto a))
        (m_world.sload m_msg.currentTarget 157#256)).toNat ≤
      (m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto a m_msg.caller)).toNat
  swap
  · have h4 := Verified.Solady.Spec.iszero_gt_of_lt (Nat.lt_of_not_le hac)
    simp only [allowSlot, balSlot, mappingSlot2, mappingSlot] at h4
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, h3, h4, hG,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
      Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun _ => trivial, fun _ _ _ h => absurd h hac⟩
  have h4 := Verified.Solady.Spec.iszero_gt_of_le hac
  simp only [allowSlot, balSlot, mappingSlot2, mappingSlot] at h4
  by_cases hfit : (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto a)).toNat +
      (((m_world.sstore m_msg.currentTarget (allowSlot m_ctx.crypto a m_msg.caller)
        (m_world.sload m_msg.currentTarget (allowSlot m_ctx.crypto a m_msg.caller) -
          Word.div (m_world.sload m_msg.currentTarget (balSlot m_ctx.crypto a))
            (m_world.sload m_msg.currentTarget 157#256))).sstore m_msg.currentTarget
        (balSlot m_ctx.crypto a) 0#256).sload m_msg.currentTarget
          (balSlot m_ctx.crypto d)).toNat < 2 ^ 256
  swap
  · have h5 := ampl_add_lt_zero (Nat.le_of_not_lt hfit)
    simp only [allowSlot, balSlot, mappingSlot2, mappingSlot] at h5
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, h3, h4, hG,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
      Abi.shr_calldataload_zero, Solidity.eq_self]
    rw [h5]
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, h3, h4, hG,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
      Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun _ => trivial, fun _ _ _ _ h => absurd h hfit⟩
  have h5 := ampl_add_lt_one hfit
  simp only [allowSlot, balSlot, mappingSlot2, mappingSlot] at h5
  pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, h3, h4, hG,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
    Abi.shr_calldataload_zero, Solidity.eq_self]
  rw [h5]
  pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, hdw, h2, h3, h4, hG,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
    Abi.shr_calldataload_zero, Solidity.eq_self]
  exact ⟨fun h => by
      rcases h with h | h | h | h
      · exact absurd h hd0
      · exact absurd h hdt
      · exact absurd h hG
      · exact absurd (Nat.lt_of_lt_of_le h hac) (Nat.lt_irrefl _),
    fun _ _ _ _ _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩

/-- `increaseAllowance(sp, x)`'s code-level end: an overflowing sum fails; otherwise the
allowance raised by `x`, `true`. -/
def IncPost (m : Machine) (sp : Address) (x : Word) (mf : Machine) (o : Outcome) : Prop :=
  (2 ^ 256 ≤ x.toNat + (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat → Fails o) ∧
  (x.toNat + (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat < 2 ^ 256 →
    (∃ out, o = .success out) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp)
      (x + m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp)) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

/-- `decreaseAllowance(sp, x)`'s code-level end: the allowance lowered by `x`, or to zero when
`x` covers it, `true`. -/
def DecPost (m : Machine) (sp : Address) (x : Word) (mf : Machine) (o : Outcome) : Prop :=
  (∃ out, o = .success out) ∧
  (x.toNat < (m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat →
    mf.world = m.world.sstore m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp)
      (m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto m.frame.msg.caller sp) - x)) ∧
  ((m.world.sload m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp)).toNat ≤ x.toNat →
    mf.world = m.world.sstore m.frame.msg.currentTarget
      (allowSlot m.ctx.crypto m.frame.msg.caller sp) 0#256) ∧
  mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts

set_option maxHeartbeats 0 in
theorem inc_low (m : Machine) (sp : Address) (x : Word) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0x39509351 [Word.ofAddress sp, x])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (IncPost m sp x) := by
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
  have hfit := ampl_add_ok (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨fun h => ?_, fun _ =>
    ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  exact absurd h (Nat.not_le.2 hfit)

set_option maxHeartbeats 0 in
theorem inc_high (m : Machine) (sp : Address) (x : Word) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0x39509351 [Word.ofAddress sp, x])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (IncPost m sp x) := by
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
  by_cases hfit : x.toNat + (m_world.sload m_msg.currentTarget
      (allowSlot m_ctx.crypto m_msg.caller sp)).toNat < 2 ^ 256
  swap
  · have h1 := ampl_add_lt_zero (Nat.le_of_not_lt hfit)
    simp only [allowSlot, mappingSlot2, mappingSlot] at h1
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    rw [h1]
    pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun _ => trivial, fun h => absurd h hfit⟩
  have h1 := ampl_add_lt_one hfit
  simp only [allowSlot, mappingSlot2, mappingSlot] at h1
  pwp_steps [hval, hst, hsel', hz, hl, harg0, harg1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  rw [h1]
  pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  exact ⟨fun h => absurd h (Nat.not_le.2 hfit), fun _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩

theorem ampl_lt_iszero_zero {a b : Word} (h : a.toNat < b.toNat) : (Word.lt a b).iszero = 0 := by
  have : BitVec.ult a b = true := by simpa [BitVec.ult] using h
  simp [Word.lt, Word.ofBool, Word.iszero, this]

theorem ampl_lt_iszero_one {a b : Word} (h : b.toNat ≤ a.toNat) : (Word.lt a b).iszero = 1 := by
  have : BitVec.ult a b = false := by simp [BitVec.ult]; omega
  simp [Word.lt, Word.ofBool, Word.iszero, this]

theorem ampl_lt_of_iszero_zero {a b : Word} (h : (Word.lt a b).iszero = 0) :
    a.toNat < b.toNat := by
  by_contra hc
  rw [ampl_lt_iszero_one (Nat.le_of_not_lt hc)] at h
  exact absurd h (by decide)

theorem ampl_le_of_lt_iszero {a b : Word} (h : (Word.lt a b).iszero ≠ 0) :
    b.toNat ≤ a.toNat := by
  by_contra hc
  exact h (ampl_lt_iszero_zero (Nat.lt_of_not_le hc))

set_option maxHeartbeats 0 in
theorem dec_low (m : Machine) (sp : Address) (x : Word) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa457c2d7 [Word.ofAddress sp, x])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (DecPost m sp x) := by
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
  · have hlt := ampl_lt_of_iszero_zero (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨⟨_, rfl⟩, fun _ => rfl,
      fun h => absurd (Nat.lt_of_lt_of_le hlt h) (Nat.lt_irrefl _), rfl, rfl⟩
  · have hle := ampl_le_of_lt_iszero (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨⟨_, rfl⟩,
      fun h => absurd (Nat.lt_of_lt_of_le h hle) (Nat.lt_irrefl _), fun _ => rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem dec_high (m : Machine) (sp : Address) (x : Word) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0xa457c2d7 [Word.ofAddress sp, x])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (DecPost m sp x) := by
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
  by_cases hlt : x.toNat < (m_world.sload m_msg.currentTarget
      (allowSlot m_ctx.crypto m_msg.caller sp)).toNat
  · have h1 := ampl_lt_iszero_zero hlt
    have h2 := Verified.Solady.Spec.iszero_gt_of_le (Nat.le_of_lt hlt)
    simp only [allowSlot, mappingSlot2, mappingSlot] at h1 h2
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, h1, h2, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨⟨_, rfl⟩, fun _ => rfl, fun h => absurd (Nat.lt_of_lt_of_le hlt h) (Nat.lt_irrefl _),
      rfl, rfl⟩
  · have h1 := ampl_lt_iszero_one (Nat.le_of_not_lt hlt)
    simp only [allowSlot, mappingSlot2, mappingSlot] at h1
    pwp_xsteps [hval, hst, hsel', hz, hl, harg0, harg1, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨⟨_, rfl⟩, fun h => absurd h hlt, fun _ => rfl, rfl, rfl⟩

end Verified.WeirdERC20.AMPL.Spec
