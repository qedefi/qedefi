import Verified.WeirdERC20.AMPL.Spec.Ops

/-!
# AMPL under the spec: the owner's entry points, the bytecode runs

`setMonetaryPolicy(p)`, `transferOwnership(o)`, `renounceOwnership()` (`onlyOwner`: the caller
is the address in slot 104): the address part of slot 155 (the monetary policy) or slot 104
(the owner) rewritten, the bits above it kept, no return data. `transferOwnership` also
requires `o ≠ 0`. Every failure reverts.
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.Solady.Spec (LowHalts halts_split' eq_zero_of_iszero_ne ite_pos' ite_neg')
open Verified.Solady.Spec.AnyGas QEDefi.ERC4626

/-- The bits of a word above its address part, `2²⁵⁶ − 2¹⁶⁰`. -/
abbrev hiMask : Word :=
  115792089237316195423570985007226406215939081747436879206741300988257197096960#256

theorem setWidth_hiMask : BitVec.setWidth 160 hiMask = 0 := by decide

theorem toAddress_or_and_hi (a : Address) (x : Word) :
    Word.toAddress (Word.ofAddress a ||| x &&& hiMask) = a := by
  simp only [Word.toAddress, Word.ofAddress, BitVec.setWidth_or, BitVec.setWidth_and,
    setWidth_hiMask]
  simp

theorem toAddress_or_hi_and (a : Address) (x : Word) :
    Word.toAddress (Word.ofAddress a ||| hiMask &&& x) = a := by
  simp only [Word.toAddress, Word.ofAddress, BitVec.setWidth_or, BitVec.setWidth_and,
    setWidth_hiMask]
  simp

theorem toAddress_hi_and (x : Word) : Word.toAddress (hiMask &&& x) = 0 := by
  simp only [Word.toAddress, BitVec.setWidth_and, setWidth_hiMask]
  simp

theorem mask_and (x : Word) :
    1461501637330902918203684832716283019655932542975#256 &&& x = Word.ofAddress x.toAddress := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [Word.ofAddress, Word.toAddress, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  rw [Nat.and_comm,
    Nat.mod_eq_of_lt (by decide : 1461501637330902918203684832716283019655932542975 < 2 ^ 256)]
  rw [show (1461501637330902918203684832716283019655932542975 : Nat) = 2 ^ 160 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  have h1 := Nat.mod_lt x.toNat (by decide : 0 < 2 ^ 160)
  rw [Nat.mod_eq_of_lt (a := BitVec.toNat x % 2 ^ 160) (by omega)]

theorem eq_addr_one {a b : Address} (h : a = b) : (Word.ofAddress a).eq (Word.ofAddress b) = 1 := by
  subst h; simp [Word.eq, Word.ofBool]

theorem eq_addr_zero {a b : Address} (h : a ≠ b) : (Word.ofAddress a).eq (Word.ofAddress b) = 0 := by
  have : Word.ofAddress a ≠ Word.ofAddress b := fun e => h (Word.ofAddress_injective e)
  have h' : (Word.ofAddress a == Word.ofAddress b) = false := by simpa using this
  simp [Word.eq, Word.ofBool, h']

theorem owner_of_eq {c : Address} {x : Word}
    (h : (Word.ofAddress c).eq (1461501637330902918203684832716283019655932542975#256 &&& x) ≠ 0) :
    c = x.toAddress := by
  rw [mask_and] at h
  by_contra hc
  exact h (eq_addr_zero hc)

/-! ## `setMonetaryPolicy(p)` -/

/-- `setMonetaryPolicy(p)`'s code-level end. -/
def SetMPPost (m : Machine) (p : Address) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.caller ≠ (m.world.sload m.frame.msg.currentTarget 104#256).toAddress → Fails o) ∧
  (m.frame.msg.caller = (m.world.sload m.frame.msg.currentTarget 104#256).toAddress →
    (∃ out, o = .success out) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget 155#256
      (Word.ofAddress p ||| m.world.sload m.frame.msg.currentTarget 155#256 &&& hiMask) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem setMP_low (m : Machine) (p : Address) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0x8b5a6a08 [Word.ofAddress p])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (SetMPPost m p) := by
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
  have hown := owner_of_eq (by with_reducible assumption)
  exact pwp_stop (by pcode_fact) (hok _ _ ⟨fun h => absurd hown h, fun _ =>
    ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩)

set_option maxHeartbeats 0 in
theorem setMP_high (m : Machine) (p : Address) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0x8b5a6a08 [Word.ofAddress p])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (SetMPPost m p) := by
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
  by_cases hown : m_msg.caller = (m_world.sload m_msg.currentTarget 104#256).toAddress
  · have h1 := eq_addr_one hown
    pwp_steps [hval, hst, hsel', hz, hl, harg0, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact pwp_stop (by pcode_fact) ⟨fun h => absurd hown h, fun _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  · have h1 := eq_addr_zero hown
    pwp_steps [hval, hst, hsel', hz, hl, harg0, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun _ => trivial, fun h => absurd h hown⟩

/-! ## `transferOwnership(o)` -/

/-- `transferOwnership(o)`'s code-level end. -/
def TOPost (m : Machine) (a : Address) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.caller ≠ (m.world.sload m.frame.msg.currentTarget 104#256).toAddress ∨ a = 0 →
    Fails o) ∧
  (m.frame.msg.caller = (m.world.sload m.frame.msg.currentTarget 104#256).toAddress → a ≠ 0 →
    (∃ out, o = .success out) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget 104#256
      (Word.ofAddress a ||| hiMask &&& m.world.sload m.frame.msg.currentTarget 104#256) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem transferOwnership_low (m : Machine) (a : Address) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0xf2fde38b [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (TOPost m a) := by
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
  have hown := owner_of_eq (by with_reducible assumption)
  have ha0 := ampl_addr_ne' (by with_reducible assumption)
  exact pwp_stop (by pcode_fact) (hok _ _ ⟨fun h => by
    rcases h with h | h
    · exact absurd hown h
    · exact absurd h ha0, fun _ _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩)

set_option maxHeartbeats 0 in
theorem transferOwnership_high (m : Machine) (a : Address) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0xf2fde38b [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (TOPost m a) := by
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
  by_cases hown : m_msg.caller = (m_world.sload m_msg.currentTarget 104#256).toAddress
  swap
  · have h1 := eq_addr_zero hown
    pwp_steps [hval, hst, hsel', hz, hl, harg0, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun _ => trivial, fun h => absurd h hown⟩
  have h1 := eq_addr_one hown
  by_cases ha0 : a = 0
  · subst ha0
    pwp_steps [hval, hst, hsel', hz, hl, harg0, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun _ => trivial, fun _ h => absurd rfl h⟩
  have haw : Word.ofAddress a ≠ 0 := fun e => ha0 (Word.ofAddress_injective (by rw [e]; rfl))
  pwp_steps [hval, hst, hsel', hz, hl, harg0, mask_and, Word.toAddress_ofAddress, h1, haw, ofAddress_and_addressMask,
    addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  exact pwp_stop (by pcode_fact) ⟨fun h => by
      rcases h with h | h
      · exact absurd hown h
      · exact absurd h ha0, fun _ _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩

/-! ## `renounceOwnership()` -/

/-- `renounceOwnership()`'s code-level end. -/
def RenPost (m : Machine) (mf : Machine) (o : Outcome) : Prop :=
  (m.frame.msg.caller ≠ (m.world.sload m.frame.msg.currentTarget 104#256).toAddress → Fails o) ∧
  (m.frame.msg.caller = (m.world.sload m.frame.msg.currentTarget 104#256).toAddress →
    (∃ out, o = .success out) ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget 104#256
      (hiMask &&& m.world.sload m.frame.msg.currentTarget 104#256) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts)

set_option maxHeartbeats 0 in
theorem renounce_low (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x715018a6) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (RenPost m) := by
  intro H hF hok
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  have hown := owner_of_eq (by with_reducible assumption)
  exact pwp_stop (by pcode_fact) (hok _ _ ⟨fun h => absurd hown h, fun _ =>
    ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩)

set_option maxHeartbeats 0 in
theorem renounce_high (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x715018a6) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (RenPost m) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  by_cases hown : m_msg.caller = (m_world.sload m_msg.currentTarget 104#256).toAddress
  · have h1 := eq_addr_one hown
    pwp_steps [hval, hst, hsel', hz, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact pwp_stop (by pcode_fact) ⟨fun h => absurd hown h, fun _ => ⟨⟨_, rfl⟩, rfl, rfl, rfl⟩⟩
  · have h1 := eq_addr_zero hown
    pwp_steps [hval, hst, hsel', hz, mask_and, Word.toAddress_ofAddress, h1, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
    exact ⟨fun _ => trivial, fun h => absurd h hown⟩

end Verified.WeirdERC20.AMPL.Spec
