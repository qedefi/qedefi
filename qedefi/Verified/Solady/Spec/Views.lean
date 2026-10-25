import Verified.Solady.Spec.Common
import Verified.Solady.Spec.Rows

/-!
# Solady `ERC20` under the spec: the views
-/

namespace Verified.Solady.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity QEDefi.ERC20 QEDefi.ERC20.Spec
open EvmLean.Interpreter EvmLogic.Tactic Verified.Solady.Contracts Verified.Solady.Spec.AnyGas

/-- A view's code-level end: success with the word `x`, nothing changed, no value. -/
def ViewPost (m : Machine) (x : Word) (mf : Machine) (o : Outcome) : Prop :=
  m.frame.msg.value = 0 ∧ o = .success (Bytes.ofWord x) ∧ mf.world = m.world ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs

set_option maxHeartbeats 0 in
theorem balanceOf_low (m : Machine) (a : Address)
    (hf : Fresh SoladyToken.runtimeCode m) (hd : Args m.frame.msg.data 0x70a08231 [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto a))) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at harg0
  hwp_steps [hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0,
    ofAddress_and_addressMask, Solidity.eq_self]
  rw [read_row _ a balSeed]
  rotate_left
  · decide
  · simp only [Memory.read_storeWord]
  · rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
      read_storeWord_slice' _ 12 20 12 32 _ (by omega) rfl]
    rfl
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _
    ⟨eq_zero_of_iszero_ne (x := m_msg.value) ‹_›, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm [balSlot]

set_option maxHeartbeats 0 in
theorem allowance_low (m : Machine) (o sp : Address)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0xdd62ed3e [Word.ofAddress o, Word.ofAddress sp])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (if sp = PERMIT2 then BitVec.ofNat 256 QEDefi.Math.MAX else
      m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto o sp))) := by
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
  · have hp := (permit2_test sp).mp ‹_›
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
    simp only [outputData, hp, ↓reduceIte]
    apwp_norm []
    rfl
  · have hp : sp ≠ PERMIT2 := fun h => ‹Word.ofAddress sp + _ ≠ 0› ((permit2_test sp).mpr h)
    rw [read_allowRow _ o sp allowSeed]
    rotate_left
    · decide
    · simp only [Memory.read_storeWord]
    · rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
        read_storeWord_slice' _ 12 20 12 32 _ (by omega) rfl]
      rfl
    · rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
        Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
        read_storeWord_slice' _ 32 12 20 44 _ (by omega) rfl]
    have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
    refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
    simp only [outputData, hp, ↓reduceIte]
    apwp_norm [allowSlot]

set_option maxHeartbeats 0 in
theorem totalSupply_low (m : Machine) (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0x18160ddd []) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (m.world.sload m.frame.msg.currentTarget supplySlot)) := by
  intro H hF hok
  obtain ⟨hsel, hsize, -⟩ := hd
  simp only [List.length_nil] at hsize
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm [supplySlot]
  rfl

set_option maxHeartbeats 0 in
theorem totalSupply_high (m : Machine) (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0x18160ddd []) (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ViewPost m (m.world.sload m.frame.msg.currentTarget supplySlot)) := by
  obtain ⟨hsel, hsize, -⟩ := hd
  simp only [List.length_nil] at hsize
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64]
  refine ⟨hval, ?_, rfl, rfl, rfl, rfl⟩
  rfl

set_option maxHeartbeats 0 in
theorem balanceOf_high (m : Machine) (a : Address)
    (hf : Fresh SoladyToken.runtimeCode m) (hd : Args m.frame.msg.data 0x70a08231 [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ViewPost m (m.world.sload m.frame.msg.currentTarget
      (balSlot m.ctx.crypto a))) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil] at hsize harg0
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at harg0
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, hok,
    ofAddress_and_addressMask, Solidity.eq_self]
  rw [read_row _ a balSeed]
  rotate_left
  · decide
  · simp only [Memory.read_storeWord]
  · rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
      read_storeWord_slice' _ 12 20 12 32 _ (by omega) rfl]
    rfl
  exact ⟨hval, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem allowance_high (m : Machine) (o sp : Address)
    (hf : Fresh SoladyToken.runtimeCode m)
    (hd : Args m.frame.msg.data 0xdd62ed3e [Word.ofAddress o, Word.ofAddress sp])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ViewPost m (if sp = PERMIT2 then BitVec.ofNat 256 QEDefi.Math.MAX else
      m.world.sload m.frame.msg.currentTarget (allowSlot m.ctx.crypto o sp))) := by
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
  by_cases hp : sp = PERMIT2
  · have hp' := (permit2_test sp).mpr hp
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1, hok,
      ofAddress_and_addressMask, Solidity.eq_self, hp']
    refine ⟨hval, ?_, rfl, rfl, rfl, rfl⟩
    simp only [hp, ↓reduceIte]
    rfl
  · have hp' : Word.ofAddress sp +
        115792089237316195423570985008687907853269803818564352520799939062701070251101#256 ≠ 0 :=
      fun h => hp ((permit2_test sp).mp h)
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Memory.read_64, harg0, harg1, hok,
      ofAddress_and_addressMask, Solidity.eq_self, hp']
    rw [read_allowRow _ o sp allowSeed]
    rotate_left
    · decide
    · simp only [Memory.read_storeWord]
    · rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
        read_storeWord_slice' _ 12 20 12 32 _ (by omega) rfl]
      rfl
    · rw [Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
        Memory.read_storeWord_of_disjoint _ _ _ _ _ (by omega), Memory.read_expand,
        read_storeWord_slice' _ 32 12 20 44 _ (by omega) rfl]
    refine ⟨hval, ?_, rfl, rfl, rfl, rfl⟩
    simp only [hp, ↓reduceIte]
    rfl

/-! ## The obligations -/

theorem world_eq_snapshot {Act : Finset Address} {m : Machine}
    (hs : Start SoladyToken.runtimeCode soladyAbs M Act m) (hv : m.frame.msg.value = 0) :
    m.world = m.frame.snapshot.1 := by
  rw [hs.launched, transferValue_zero _ _ hv]

theorem pre_eq {Act : Finset Address} {m : Machine}
    (hs : Start SoladyToken.runtimeCode soladyAbs M Act m) (hv : m.frame.msg.value = 0) :
    pre soladyAbs Act m = read m.ctx.crypto Act m.world m.frame.msg.currentTarget := by
  rw [world_eq_snapshot hs hv]; rfl

/-- **`totalSupply()`** returns the stored supply. -/
theorem view_totalSupply : ViewSpec SoladyToken.runtimeCode soladyAbs M g₀ .totalSupply := by
  intro Act m hs hd _
  refine halts_split (fun hG => totalSupply_high m hs.fresh hd hs.size hG.2 hG.1)
    (totalSupply_low m hs.fresh hd hs.size) ?_
  rintro mf o ⟨hv, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  rw [pre_eq hs hv]
  rfl

/-- **`balanceOf(a)`** returns the actor's balance row. -/
theorem view_balanceOf (a : Address) :
    ViewSpec SoladyToken.runtimeCode soladyAbs M g₀ (.balanceOf a) := by
  intro Act m hs hd ha
  have haA : a ∈ Act := ha a (by simp [View.addrs])
  refine halts_split (fun hG => balanceOf_high m a hs.fresh hd hs.size hG.2 hG.1)
    (balanceOf_low m a hs.fresh hd hs.size) ?_
  rintro mf o ⟨hv, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  rw [pre_eq hs hv]
  simp [View.value, M, Solady.soladyModel, Variant.balanceOf, Variant.solady, Variant.standard, read,
    balances, haA]

/-- **`allowance(o, sp)`** returns the actors' allowance row, or `MAX` for Permit2. -/
theorem view_allowance (o sp : Address) :
    ViewSpec SoladyToken.runtimeCode soladyAbs M g₀ (.allowance o sp) := by
  intro Act m hs hd ha
  have hoA : o ∈ Act := ha o (by simp [View.addrs])
  have hsA : sp ∈ Act := ha sp (by simp [View.addrs])
  refine halts_split (fun hG => allowance_high m o sp hs.fresh hd hs.size hG.2 hG.1)
    (allowance_low m o sp hs.fresh hd hs.size) ?_
  rintro mf o' ⟨hv, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  rw [pre_eq hs hv]
  by_cases hp : sp = PERMIT2
  · subst hp
    simp [View.value, M, Solady.soladyModel, Variant.allowanceOf, Variant.solady, QEDefi.Math.MAX]
  · simp [View.value, M, Solady.soladyModel, Variant.allowanceOf, Variant.solady, Variant.standard,
      read, allowances, hoA, hsA, hp, Ne.symm hp]

/-- **The three views.** -/
theorem views (v : View) : ViewSpec SoladyToken.runtimeCode soladyAbs M g₀ v := by
  cases v with
  | balanceOf a => exact view_balanceOf a
  | allowance o sp => exact view_allowance o sp
  | totalSupply => exact view_totalSupply

end Verified.Solady.Spec