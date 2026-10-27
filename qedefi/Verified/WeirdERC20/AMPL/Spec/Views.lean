import Verified.WeirdERC20.AMPL.Spec.Abs
import Verified.Solady.Spec.Views

/-!
# AMPL under the spec: the views

`totalSupply()`, `balanceOf(a)` and `allowance(o, sp)` of the `UFragments` implementation code (solc 0.7.6), in any frame (at the proxy by `DELEGATECALL`):
the exact case by `pwp_steps` (enough gas, no value), any gas, value or static flag by
`hwp_steps` (the frame fails or returns the same word), combined by `halts_split`
(`Verified.Solady.Spec.Common`).
-/

namespace Verified.WeirdERC20.AMPL.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.Solady.Spec (LowHalts ViewPost halts_split eq_zero_of_iszero_ne)
open Verified.Solady.Spec.AnyGas
open QEDefi.ERC20.Spec.AMPL (AState AState.setAllowance liftR AmplOp amplOp rebaseOp rebaseSupply)

code_table AMPL.runtimeCode

/-- solc's ABI length check `calldatasize - 4 < k` fails on long enough calldata. -/
theorem iszero_lt_size {n k : Nat} (h1 : 4 + k ≤ n) (h2 : n < 2 ^ 64) :
    Word.iszero (Word.lt (ofNat n - 4#256) (BitVec.ofNat 256 k)) = 1 := by
  rw [Word.iszero_eq_one_iff]
  have hx : (ofNat n - 4#256 : Word).toNat = n - 4 := by
    rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def, ofNat]; omega)]
    simp [ofNat]; omega
  have : ¬ BitVec.ult (ofNat n - 4#256) (BitVec.ofNat 256 k) := by
    simp only [BitVec.ult, hx, BitVec.toNat_ofNat, decide_eq_true_eq]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp [Word.lt, Word.ofBool, this]

set_option maxHeartbeats 0 in
theorem totalSupply_low (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0x18160ddd []) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (m.world.sload m.frame.msg.currentTarget 156#256)) := by
  intro H hF hok
  obtain ⟨hsel, hsize, -⟩ := hd
  simp only [List.length_nil] at hsize
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, Abi.shr_calldataload_zero, Memory.read_64]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm []

set_option maxHeartbeats 0 in
theorem totalSupply_high (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0x18160ddd []) (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ViewPost m (m.world.sload m.frame.msg.currentTarget 156#256)) := by
  obtain ⟨hsel, hsize, -⟩ := hd
  simp only [List.length_nil] at hsize
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  pwp_steps [hval, hsel', hz, Abi.shr_calldataload_zero, Memory.read_64]
  exact ⟨hval, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem balanceOf_low (m : Machine) (a : Address) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0x70a08231 [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (Word.div (m.world.sload m.frame.msg.currentTarget
      (mappingSlot m.ctx.crypto (Word.ofAddress a) 158#256))
        (m.world.sload m.frame.msg.currentTarget 157#256))) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, Nat.mul_zero,
    Nat.add_zero] at hsize harg0
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
    Abi.shr_calldataload_zero, Solidity.eq_self]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm [mappingSlot]

set_option maxHeartbeats 0 in
theorem balanceOf_high (m : Machine) (a : Address) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0x70a08231 [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hg : g₀ ≤ m.frame.gasLeft)
    (hsc : (m.world.sload m.frame.msg.currentTarget 157#256).toNat ≠ 0) :
    Halts m (ViewPost m (Word.div (m.world.sload m.frame.msg.currentTarget
      (mappingSlot m.ctx.crypto (Word.ofAddress a) 158#256))
        (m.world.sload m.frame.msg.currentTarget 157#256))) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, Nat.mul_zero,
    Nat.add_zero] at hsize harg0
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hok := iszero_lt_size (n := m.frame.msg.data.size) (k := 32) (by omega) hsz
  have hgt : Word.gt (m.world.sload m.frame.msg.currentTarget 157#256) 0#256 = 1 := by
    have : BitVec.ult 0#256 (m.world.sload m.frame.msg.currentTarget 157#256) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat]; simpa [Nat.pos_iff_ne_zero] using hsc
    simp [Word.gt, Word.ofBool, this]
  have hS0 : m.world.sload m.frame.msg.currentTarget 157#256 ≠ 0 := fun h => hsc (by rw [h]; rfl)
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  pwp_steps [hval, hsel', hz, hok, hgt, hS0, harg0, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Memory.read_64, Abi.shr_calldataload_zero, Solidity.eq_self]
  exact ⟨hval, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem allowance_low (m : Machine) (o sp : Address) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0xdd62ed3e [Word.ofAddress o, Word.ofAddress sp])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (m.world.sload m.frame.msg.currentTarget
      (mappingSlot2 m.ctx.crypto (Word.ofAddress o) (Word.ofAddress sp) 159#256))) := by
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
  hwp_steps [hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
    Abi.shr_calldataload_zero, Solidity.eq_self]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm [mappingSlot2, mappingSlot]

set_option maxHeartbeats 0 in
theorem allowance_high (m : Machine) (o sp : Address) (hf : Fresh AMPL.runtimeCode m)
    (hd : Args m.frame.msg.data 0xdd62ed3e [Word.ofAddress o, Word.ofAddress sp])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ViewPost m (m.world.sload m.frame.msg.currentTarget
      (mappingSlot2 m.ctx.crypto (Word.ofAddress o) (Word.ofAddress sp) 159#256))) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hok := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  pwp_steps [hval, hsel', hz, hok, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64,
    Abi.shr_calldataload_zero, Solidity.eq_self]
  exact ⟨hval, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The obligations -/

theorem pre_eq {Act : Finset Address} {m : Machine}
    (hs : Start AMPL.runtimeCode amplAbs M Act m) (hv : m.frame.msg.value = 0) :
    pre amplAbs Act m = amplRead m.ctx.crypto Act m.world m.frame.msg.currentTarget := by
  rw [hs.launched, transferValue_zero _ _ hv]; rfl

/-- Under the model's invariant `_gonsPerFragment` is positive. -/
theorem scale_ne {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address}
    (hwf : M.wf (amplRead crypto Act w t)) : (w.sload t 157#256).toNat ≠ 0 := by
  simp only [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.WF, Variant.ampl,
    Variant.standard, ↓reduceIte] at hwf
  obtain ⟨-, h0, hle, hsc⟩ := hwf
  simp only [amplRead, readSlot] at h0 hle hsc
  rw [hsc]
  apply Nat.pos_iff_ne_zero.mp
  apply Nat.div_pos _ h0
  calc _ ≤ 2 ^ 128 - 1 := hle
    _ ≤ Variant.amplTotalGons := by simp only [Variant.amplTotalGons, QEDefi.Math.MAX]; omega

/-- Under the model's invariant the instance is initialized (supply `0` is not well formed). -/
theorem live_of_wf {crypto : Crypto} {Act : Finset Address} {w : World} {t : Address}
    (hwf : M.wf (amplRead crypto Act w t)) : Live w t := by
  simp only [M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.WF, Variant.ampl,
    Variant.standard, ↓reduceIte] at hwf
  obtain ⟨-, h0, -⟩ := hwf
  by_contra hL
  simp [amplRead, hL] at h0

/-- **`totalSupply()`** returns slot 156. -/
theorem view_totalSupply : ViewSpec AMPL.runtimeCode amplAbs M g₀ .totalSupply := by
  intro Act m hs hd _
  refine halts_split (fun hG => totalSupply_high m hs.fresh hd hs.size hG.2 hG.1)
    (totalSupply_low m hs.fresh hd hs.size) ?_
  rintro mf o ⟨hv, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  have hL := live_of_wf (by have := hs.wf; rwa [pre_eq hs hv] at this)
  rw [pre_eq hs hv]
  simp [View.value, M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.totalSupply, Variant.ampl,
    Variant.standard, amplRead, hL, readSlot]

/-- **`balanceOf(a)`** returns the actor's gons divided by `_gonsPerFragment`. -/
theorem view_balanceOf (a : Address) : ViewSpec AMPL.runtimeCode amplAbs M g₀ (.balanceOf a) := by
  intro Act m hs hd ha
  have haA : a ∈ Act := ha a (by simp [View.addrs])
  refine halts_split (fun hG => balanceOf_high m a hs.fresh hd hs.size hG.2 hG.1
    (scale_ne (by have := hs.wf; rwa [pre_eq hs hG.2] at this)))
    (balanceOf_low m a hs.fresh hd hs.size) ?_
  rintro mf o ⟨hv, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  rw [pre_eq hs hv]
  simp [View.value, M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.balanceOf, Variant.ampl,
    Variant.standard, amplRead, haA]
  simp only [Word.div, readSlot, BitVec.toNat_udiv]

/-- **`allowance(o, sp)`** returns the actors' row of `_allowedFragments`. -/
theorem view_allowance (o sp : Address) :
    ViewSpec AMPL.runtimeCode amplAbs M g₀ (.allowance o sp) := by
  intro Act m hs hd ha
  have hoA : o ∈ Act := ha o (by simp [View.addrs])
  have hsA : sp ∈ Act := ha sp (by simp [View.addrs])
  refine halts_split (fun hG => allowance_high m o sp hs.fresh hd hs.size hG.2 hG.1)
    (allowance_low m o sp hs.fresh hd hs.size) ?_
  rintro mf o' ⟨hv, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  rw [pre_eq hs hv]
  simp [View.value, M, QEDefi.ERC20.Spec.AMPL.amplModel, Variant.allowanceOf, Variant.ampl,
    Variant.standard, amplRead, readMap2, hoA, hsA]

/-- **The three views of AMPL.** -/
theorem views (v : View) : ViewSpec AMPL.runtimeCode amplAbs M g₀ v := by
  cases v with
  | balanceOf a => exact view_balanceOf a
  | allowance o sp => exact view_allowance o sp
  | totalSupply => exact view_totalSupply

end Verified.WeirdERC20.AMPL.Spec
