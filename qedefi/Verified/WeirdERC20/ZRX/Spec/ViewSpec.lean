import Verified.WeirdERC20.ZRX.Spec.Views
import Verified.WeirdERC20.BNB.Spec.Write
import Verified.Solady.Spec.Views

/-!
# ZRX under the spec: the views at any gas

`ViewSpec` for ZRX's three views: the exact case is `Views.lean` (`totalSupply_halts`,
`balanceOf_halts`, `allowance_halts`, with enough gas and no value); any gas, value or static
flag by `hwp_steps` (the frame fails, at the non-payable check's `INVALID` or out of gas, or
returns the same word), combined by `halts_split` (`Verified.Solady.Spec.Common`).
-/

namespace Verified.WeirdERC20.ZRX.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.ZRX.Contracts
open Verified.Solady.Spec (LowHalts halts_split eq_zero_of_iszero_ne)
open Verified.Solady.Spec.AnyGas

/-- The ZRX model. -/
noncomputable abbrev M : TokenModel (VState Address) Address Empty := QEDefi.ERC20.Spec.ZRX.model

set_option maxHeartbeats 0 in
theorem totalSupply_low (m : Machine) (hf : Fresh ZRX.runtimeCode m)
    (hd : Args m.frame.msg.data 0x18160ddd []) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (Verified.Solady.Spec.ViewPost m (m.world.sload m.frame.msg.currentTarget 3#256)) := by
  intro H hF hok
  obtain ⟨hsel, hsize, -⟩ := hd
  simp only [List.length_nil] at hsize
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  zrx_fresh_intro
  hwp_steps [hsel', hz]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm []

set_option maxHeartbeats 0 in
theorem balanceOf_low (m : Machine) (a : Address) (hf : Fresh ZRX.runtimeCode m)
    (hd : Args m.frame.msg.data 0x70a08231 [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (Verified.Solady.Spec.ViewPost m (m.world.sload m.frame.msg.currentTarget
      (mappingSlot m.ctx.crypto (Word.ofAddress a) 0#256))) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, Nat.mul_zero,
    Nat.add_zero] at hsize harg0
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  zrx_fresh_intro
  hwp_steps [hsel', hz, harg0, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm [mappingSlot]

set_option maxHeartbeats 0 in
theorem allowance_low (m : Machine) (o sp : Address) (hf : Fresh ZRX.runtimeCode m)
    (hd : Args m.frame.msg.data 0xdd62ed3e [Word.ofAddress o, Word.ofAddress sp])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (Verified.Solady.Spec.ViewPost m (m.world.sload m.frame.msg.currentTarget
      (mappingSlot2 m.ctx.crypto (Word.ofAddress o) (Word.ofAddress sp) 1#256))) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  zrx_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm [mappingSlot2, mappingSlot]

/-! ## The obligations -/

/-- With no value, the model state at the start of the frame is read from the frame's world. -/
theorem pre_eq {Act : Finset Address} {m : Machine} (hs : Start ZRX.runtimeCode abs M Act m)
    (hv : m.frame.msg.value = 0) :
    pre abs Act m = read m.ctx.crypto Act m.world m.frame.msg.currentTarget := by
  rw [hs.launched, transferValue_zero _ _ hv]; rfl

/-- The high-gas run with the value recorded (`ViewPost` of `Verified.Solady.Spec`). -/
theorem high_of {m : Machine} {x : Word} (hv : m.frame.msg.value = 0)
    (h : Halts m (Verified.WeirdERC20.ZRX.Spec.ViewPost x m)) :
    Halts m (Verified.Solady.Spec.ViewPost m x) :=
  h.mono fun _ _ _ ⟨ho, h1, h2, h3, h4⟩ => ⟨hv, ho, h1, h2, h3, h4⟩

theorem g₀_ge {m : Machine} (hg : g₀ ≤ m.frame.gasLeft) : 5000 ≤ m.frame.gasLeft :=
  le_trans (by decide) hg

/-- **`totalSupply()`** returns slot 3. -/
theorem view_totalSupply : ViewSpec ZRX.runtimeCode abs M g₀ .totalSupply := by
  intro Act m hs hd _
  refine halts_split (fun hG => high_of hG.2 (totalSupply_halts m hs.fresh hG.2 hd.selector
      (by simpa using hd.size) hs.size (g₀_ge hG.1)))
    (totalSupply_low m hs.fresh hd hs.size) ?_
  rintro mf o ⟨hv, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  rw [pre_eq hs hv]
  simp [View.value, M, QEDefi.ERC20.Spec.ZRX.model, Variant.model, Variant.totalSupply,
    QEDefi.ERC20.Spec.ZRX.variant, Variant.standard, VState.ofToken, read, readSlot, supplySlot]

/-- **`balanceOf(a)`** returns the actor's row of `balances`. -/
theorem view_balanceOf (a : Address) : ViewSpec ZRX.runtimeCode abs M g₀ (.balanceOf a) := by
  intro Act m hs hd ha
  have haA : a ∈ Act := ha a (by simp [View.addrs])
  refine halts_split (fun hG => high_of hG.2 (balanceOf_halts m hs.fresh a hG.2 hd.selector
      (by simpa using hd.size) hs.size (hd.arg 0 (by simp)) (g₀_ge hG.1)))
    (balanceOf_low m a hs.fresh hd hs.size) ?_
  rintro mf o ⟨hv, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  rw [pre_eq hs hv]
  simp [View.value, M, QEDefi.ERC20.Spec.ZRX.model, Variant.model, Variant.balanceOf,
    QEDefi.ERC20.Spec.ZRX.variant, Variant.standard, VState.ofToken, read, haA, balancesSlot]

/-- **`allowance(o, sp)`** returns the actors' row of `allowed`. -/
theorem view_allowance (o sp : Address) : ViewSpec ZRX.runtimeCode abs M g₀ (.allowance o sp) := by
  intro Act m hs hd ha
  have hoA : o ∈ Act := ha o (by simp [View.addrs])
  have hsA : sp ∈ Act := ha sp (by simp [View.addrs])
  refine halts_split (fun hG => high_of hG.2 (allowance_halts m hs.fresh o sp hG.2 hd.selector
      (by simpa using hd.size) hs.size (hd.arg 0 (by simp)) (hd.arg 1 (by simp)) (g₀_ge hG.1)))
    (allowance_low m o sp hs.fresh hd hs.size) ?_
  rintro mf o' ⟨hv, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  rw [pre_eq hs hv]
  simp [View.value, M, QEDefi.ERC20.Spec.ZRX.model, Variant.model, Variant.allowanceOf,
    QEDefi.ERC20.Spec.ZRX.variant, Variant.standard, VState.ofToken, read, readMap2, hoA, hsA,
    allowedSlot]

/-- **The three views of ZRX**, at any gas. -/
theorem views (v : View) : ViewSpec ZRX.runtimeCode abs M g₀ v := by
  cases v with
  | balanceOf a => exact view_balanceOf a
  | allowance o sp => exact view_allowance o sp
  | totalSupply => exact view_totalSupply

end Verified.WeirdERC20.ZRX.Spec
