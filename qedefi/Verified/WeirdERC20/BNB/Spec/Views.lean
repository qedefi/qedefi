import Verified.WeirdERC20.BNB.Spec.Abs
import Verified.Solady.Spec.Views

/-!
# BNB under the spec: the views

`totalSupply()`, `balanceOf(a)` and `allowance(o, sp)` of the mainnet BNB code (solc 0.4.12):
the exact case by `pwp_steps` (enough gas, no value), any gas, value or static flag by
`hwp_steps` (the frame fails or returns the same word), combined by `halts_split`
(`Verified.Solady.Spec.Common`).
-/

namespace Verified.WeirdERC20.BNB.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.BNB.Contracts
open Verified.Solady.Spec (LowHalts ViewPost halts_split eq_zero_of_iszero_ne)
open Verified.Solady.Spec.AnyGas

code_table BNB.runtimeCode

/-- solc 0.4's selector extraction (`CALLDATALOAD 0 / 2²²⁴ & 0xffffffff`). -/
theorem div_selector (data : ByteArray) :
    (4294967295#256 &&& Word.div (Bytes.toWord (readBytes data 0 32))
      26959946667150639794667015087019630673637144422540572481103610249216#256) =
      BitVec.ofNat 256 (Abi.selectorOf data) := by
  have hs := Abi.shr_calldataload_zero data
  have hsel : Abi.selectorOf data < 2 ^ 32 := by
    have := Bytes.toNat_lt (readBytes data 0 4)
    rw [size_readBytes] at this
    unfold Abi.selectorOf; simpa using this
  have hdiv : Word.div (Bytes.toWord (readBytes data 0 32))
      26959946667150639794667015087019630673637144422540572481103610249216#256 =
      Word.shr (BitVec.ofNat 256 224) (Bytes.toWord (readBytes data 0 32)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [Word.div, Word.shr, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight,
      BitVec.toNat_udiv, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow]
  rw [hdiv, hs]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : Abi.selectorOf data < 2 ^ 256),
    show (4294967295 : Nat) % 2 ^ 256 = 2 ^ 32 - 1 by decide, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hsel]

theorem calldatasize_ne {n : ℕ} (h4 : 4 ≤ n) (h : n < 2 ^ 64) : Word.iszero (ofNat n) = 0 := by
  apply iszero_of_ne
  intro h0
  have := congrArg BitVec.toNat h0
  simp [ofNat] at this
  omega

set_option maxHeartbeats 0 in
theorem totalSupply_low (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hd : Args m.frame.msg.data 0x18160ddd []) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (m.world.sload m.frame.msg.currentTarget 3#256)) := by
  intro H hF hok
  obtain ⟨hsel, hsize, -⟩ := hd
  simp only [List.length_nil] at hsize
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm []

set_option maxHeartbeats 0 in
theorem totalSupply_high (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hd : Args m.frame.msg.data 0x18160ddd []) (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ViewPost m (m.world.sload m.frame.msg.currentTarget 3#256)) := by
  obtain ⟨hsel, hsize, -⟩ := hd
  simp only [List.length_nil] at hsize
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  pwp_steps [hval, hsel', hz]
  exact ⟨hval, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem balanceOf_low (m : Machine) (a : Address) (hf : Fresh BNB.runtimeCode m)
    (hd : Args m.frame.msg.data 0x70a08231 [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (m.world.sload m.frame.msg.currentTarget
      (mappingSlot m.ctx.crypto (Word.ofAddress a) 5#256))) := by
  intro H hF hok
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, Nat.mul_zero,
    Nat.add_zero] at hsize harg0
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm [mappingSlot]

set_option maxHeartbeats 0 in
theorem balanceOf_high (m : Machine) (a : Address) (hf : Fresh BNB.runtimeCode m)
    (hd : Args m.frame.msg.data 0x70a08231 [Word.ofAddress a])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ViewPost m (m.world.sload m.frame.msg.currentTarget
      (mappingSlot m.ctx.crypto (Word.ofAddress a) 5#256))) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, Nat.mul_zero,
    Nat.add_zero] at hsize harg0
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  pwp_steps [hval, hsel', hz, harg0, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  exact ⟨hval, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem allowance_low (m : Machine) (o sp : Address) (hf : Fresh BNB.runtimeCode m)
    (hd : Args m.frame.msg.data 0xdd62ed3e [Word.ofAddress o, Word.ofAddress sp])
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    LowHalts m (ViewPost m (m.world.sload m.frame.msg.currentTarget
      (mappingSlot2 m.ctx.crypto (Word.ofAddress o) (Word.ofAddress sp) 7#256))) := by
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
  solady_fresh_intro
  hwp_steps [hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  have hv : m_msg.value = 0 := eq_zero_of_iszero_ne (by with_reducible assumption)
  refine pwp_return hF (by pcode_fact) rfl fun _ => hok _ _ ⟨hv, ?_, rfl, rfl, rfl, rfl⟩
  simp only [outputData]
  apwp_norm [mappingSlot2, mappingSlot]

set_option maxHeartbeats 0 in
theorem allowance_high (m : Machine) (o sp : Address) (hf : Fresh BNB.runtimeCode m)
    (hd : Args m.frame.msg.data 0xdd62ed3e [Word.ofAddress o, Word.ofAddress sp])
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hval : m.frame.msg.value = 0) (hg : g₀ ≤ m.frame.gasLeft) :
    Halts m (ViewPost m (m.world.sload m.frame.msg.currentTarget
      (mappingSlot2 m.ctx.crypto (Word.ofAddress o) (Word.ofAddress sp) 7#256))) := by
  obtain ⟨hsel, hsize, harg⟩ := hd
  have harg0 := harg 0 (by simp)
  have harg1 := harg 1 (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hsize harg0 harg1
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  simp only [g₀] at hg
  apply WP.halts_of_false
  solady_fresh_intro
  pwp_steps [hval, hsel', hz, harg0, harg1, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  exact ⟨hval, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The obligations -/

theorem pre_eq {Act : Finset Address} {m : Machine}
    (hs : Start BNB.runtimeCode bnbAbs M Act m) (hv : m.frame.msg.value = 0) :
    pre bnbAbs Act m = bnbRead m.ctx.crypto Act m.world m.frame.msg.currentTarget := by
  rw [hs.launched, transferValue_zero _ _ hv]; rfl

/-- **`totalSupply()`** returns slot 3. -/
theorem view_totalSupply : ViewSpec BNB.runtimeCode bnbAbs M g₀ .totalSupply := by
  intro Act m hs hd _
  refine halts_split (fun hG => totalSupply_high m hs.fresh hd hs.size hG.2 hG.1)
    (totalSupply_low m hs.fresh hd hs.size) ?_
  rintro mf o ⟨hv, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  rw [pre_eq hs hv]
  rfl

/-- **`balanceOf(a)`** returns the actor's row of `balanceOf`. -/
theorem view_balanceOf (a : Address) : ViewSpec BNB.runtimeCode bnbAbs M g₀ (.balanceOf a) := by
  intro Act m hs hd ha
  have haA : a ∈ Act := ha a (by simp [View.addrs])
  refine halts_split (fun hG => balanceOf_high m a hs.fresh hd hs.size hG.2 hG.1)
    (balanceOf_low m a hs.fresh hd hs.size) ?_
  rintro mf o ⟨hv, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  rw [pre_eq hs hv]
  simp [View.value, M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.balanceOf, Variant.bnb,
    Variant.standard, bnbRead, haA]

/-- **`allowance(o, sp)`** returns the actors' row of `allowance`. -/
theorem view_allowance (o sp : Address) :
    ViewSpec BNB.runtimeCode bnbAbs M g₀ (.allowance o sp) := by
  intro Act m hs hd ha
  have hoA : o ∈ Act := ha o (by simp [View.addrs])
  have hsA : sp ∈ Act := ha sp (by simp [View.addrs])
  refine halts_split (fun hG => allowance_high m o sp hs.fresh hd hs.size hG.2 hG.1)
    (allowance_low m o sp hs.fresh hd hs.size) ?_
  rintro mf o' ⟨hv, ho, hw, ht, hc, hl⟩
  refine ⟨_, ho, ?_, hw, ht, hc, hl⟩
  rw [pre_eq hs hv]
  simp [View.value, M, QEDefi.ERC20.Spec.BNB.bnbModel, Variant.allowanceOf, Variant.bnb,
    Variant.standard, bnbRead, readMap2, hoA, hsA]

/-- **The three views of BNB.** -/
theorem views (v : View) : ViewSpec BNB.runtimeCode bnbAbs M g₀ v := by
  cases v with
  | balanceOf a => exact view_balanceOf a
  | allowance o sp => exact view_allowance o sp
  | totalSupply => exact view_totalSupply

end Verified.WeirdERC20.BNB.Spec
