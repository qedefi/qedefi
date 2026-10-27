import Verified.WeirdERC20.LEND.Spec.Common

/-!
# LEND under the spec: the views

`totalSupply()` (slot 2, `supply`), `balanceOf(a)` and `allowance(o, sp)` of the mainnet LEND
code: the exact case by `pwp_steps` (enough gas, no value), any gas, value or static flag by
`hwp_steps` (the frame fails, at the non-payable check's `REVERT` or out of gas, or returns
the same word), combined by `halts_split`.
-/

namespace Verified.WeirdERC20.LEND.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.LEND.Contracts
open Verified.Solady.Spec (LowHalts ViewPost halts_split eq_zero_of_iszero_ne)
open Verified.Solady.Spec.AnyGas

set_option maxHeartbeats 0 in
theorem totalSupply_low (m : Machine) (hf : Fresh LEND.runtimeCode m)
    (hd : Args m.frame.msg.data 0x18160ddd []) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (m.world.sload m.frame.msg.currentTarget 2#256)) := by
  intro H hF hok
  obtain ⟨hsel, hsize, -⟩ := hd
  simp only [List.length_nil] at hsize
  have hsel' := BNB.Spec.div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := BNB.Spec.calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm []

set_option maxHeartbeats 0 in
theorem totalSupply_high (m : Machine) (hf : Fresh LEND.runtimeCode m)
    (hd : Args m.frame.msg.data 0x18160ddd []) (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ViewPost m (m.world.sload m.frame.msg.currentTarget 2#256)) := by
  obtain ⟨hsel, hsize, -⟩ := hd
  simp only [List.length_nil] at hsize
  have hsel' := BNB.Spec.div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := BNB.Spec.calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  pwp_steps [hval, hsel', hz]
  exact ⟨hval, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem balanceOf_low (m : Machine) (a : Address) (hf : Fresh LEND.runtimeCode m)
    (hd : Args m.frame.msg.data 0x70a08231 [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (m.world.sload m.frame.msg.currentTarget
      (mappingSlot m.ctx.crypto (Word.ofAddress a) 0#256))) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, Nat.mul_zero,
    Nat.add_zero] at hsize harg0
  have hsel' := BNB.Spec.div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := BNB.Spec.calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm [mappingSlot]

set_option maxHeartbeats 0 in
theorem balanceOf_high (m : Machine) (a : Address) (hf : Fresh LEND.runtimeCode m)
    (hd : Args m.frame.msg.data 0x70a08231 [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ViewPost m (m.world.sload m.frame.msg.currentTarget
      (mappingSlot m.ctx.crypto (Word.ofAddress a) 0#256))) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, Nat.mul_zero,
    Nat.add_zero] at hsize harg0
  have hsel' := BNB.Spec.div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := BNB.Spec.calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  pwp_steps [hval, hsel', hz, harg0, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  exact ⟨hval, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem allowance_low (m : Machine) (o sp : Address) (hf : Fresh LEND.runtimeCode m)
    (hd : Args m.frame.msg.data 0xdd62ed3e [Word.ofAddress o, Word.ofAddress sp])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (m.world.sload m.frame.msg.currentTarget
      (mappingSlot2 m.ctx.crypto (Word.ofAddress o) (Word.ofAddress sp) 1#256))) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := BNB.Spec.div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := BNB.Spec.calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm [mappingSlot2, mappingSlot]

set_option maxHeartbeats 0 in
theorem allowance_high (m : Machine) (o sp : Address) (hf : Fresh LEND.runtimeCode m)
    (hd : Args m.frame.msg.data 0xdd62ed3e [Word.ofAddress o, Word.ofAddress sp])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ViewPost m (m.world.sload m.frame.msg.currentTarget
      (mappingSlot2 m.ctx.crypto (Word.ofAddress o) (Word.ofAddress sp) 1#256))) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := BNB.Spec.div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := BNB.Spec.calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  pwp_steps [hval, hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  exact ⟨hval, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The obligations -/

/-- **`totalSupply()`** returns `supply`. -/
theorem view_totalSupply : ViewSpec LEND.runtimeCode abs M g₀ .totalSupply := by
  intro Act m hs hd _
  refine halts_split (fun hG => totalSupply_high m hs.fresh hd hs.size hG.2 hG.1)
    (totalSupply_low m hs.fresh hd hs.size) ?_
  rintro mf o ⟨-, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  rw [pre_eq hs]
  rfl

/-- **`balanceOf(a)`** returns the actor's row of `balances`. -/
theorem view_balanceOf (a : Address) : ViewSpec LEND.runtimeCode abs M g₀ (.balanceOf a) := by
  intro Act m hs hd ha
  have haA : a ∈ Act := ha a (by simp [View.addrs])
  refine halts_split (fun hG => balanceOf_high m a hs.fresh hd hs.size hG.2 hG.1)
    (balanceOf_low m a hs.fresh hd hs.size) ?_
  rintro mf o ⟨-, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  rw [pre_eq hs]
  exact (readMap_of_mem haA _ _ _).symm

/-- **`allowance(o, sp)`** returns the actors' row of `allowed`. -/
theorem view_allowance (o sp : Address) :
    ViewSpec LEND.runtimeCode abs M g₀ (.allowance o sp) := by
  intro Act m hs hd ha
  have hoA : o ∈ Act := ha o (by simp [View.addrs])
  have hsA : sp ∈ Act := ha sp (by simp [View.addrs])
  refine halts_split (fun hG => allowance_high m o sp hs.fresh hd hs.size hG.2 hG.1)
    (allowance_low m o sp hs.fresh hd hs.size) ?_
  rintro mf o' ⟨-, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  rw [pre_eq hs]
  simp [View.value, M, QEDefi.ERC20.Spec.LEND.model, read, readMap2, hoA, hsA, allowedSlot]

/-- **The three views of LEND.** -/
theorem views (v : View) : ViewSpec LEND.runtimeCode abs M g₀ v := by
  cases v with
  | balanceOf a => exact view_balanceOf a
  | allowance o sp => exact view_allowance o sp
  | totalSupply => exact view_totalSupply

end Verified.WeirdERC20.LEND.Spec
