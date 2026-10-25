import Verified.OpenZeppelin.ERC20.Callee
import EvmLogic.Tactic.Patched

/-!
# `OzAsset`'s dispatcher: value, unknown selectors, the other two views

Callee summaries (any fresh frame) of the paths of the deployed `ERC20Mock` not covered by
`Callee*.lean`: no function is payable, so a frame with value reverts before the dispatcher
(`value_halts`); calldata shorter than a selector, or with a selector the dispatcher does not
know, reverts (`short_halts`, `unknown_halts`); `allowance(o, sp)` and `totalSupply()` return
their storage word and change nothing.
-/

namespace Verified.OpenZeppelin.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Solidity.ERC20
open EvmLean.Interpreter EvmLogic.Tactic QEDefi.ERC4626 Verified.OpenZeppelin.Contracts
open Verified.Solmate.ERC20 (lt_size_four)

set_option maxHeartbeats 0 in
/-- **A frame with value reverts**, whatever its calldata (no function is payable). -/
theorem value_halts (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value ≠ 0) (hg : 100 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hz : Word.iszero m.frame.msg.value = 0#256 := by
    simpa [Word.iszero, Word.ofBool] using hval
  fresh_intro
  pwp_steps [hz]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- **Calldata shorter than a selector reverts** (no fallback function). -/
theorem short_halts (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsize : m.frame.msg.data.size < 4)
    (hg : 100 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt : Word.lt (ofNat m.frame.msg.data.size) (BitVec.ofNat 256 4) = 1 :=
    (Word.lt_eq_one_iff _ _).2 (by simp only [ofNat, BitVec.toNat_ofNat]; omega)
  fresh_intro
  pwp_steps [hval, hlt]
  exact ⟨_, rfl⟩

theorem word_eq_ofNat_ne {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (h : a ≠ b) :
    Word.eq (BitVec.ofNat 256 a) (BitVec.ofNat 256 b) = 0#256 := by
  unfold Word.eq Word.ofBool
  have : BitVec.ofNat 256 a ≠ BitVec.ofNat 256 b := by
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact h this
  simp [this]

theorem word_gt_ofNat_one {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (h : b < a) :
    Word.gt (BitVec.ofNat 256 a) (BitVec.ofNat 256 b) = 1#256 :=
  (Word.gt_eq_one_iff _ _).2 (by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]; exact h)

theorem word_gt_ofNat_zero {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (h : a ≤ b) :
    Word.gt (BitVec.ofNat 256 a) (BitVec.ofNat 256 b) = 0#256 := by
  unfold Word.gt Word.ofBool
  have : ¬ BitVec.ult (BitVec.ofNat 256 b) (BitVec.ofNat 256 a) := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      decide_eq_true_eq]
    omega
  simp [this]

theorem selectorOf_lt (data : ByteArray) : Abi.selectorOf data < 2 ^ 32 := by
  have := Bytes.toNat_lt (readBytes data 0 4)
  rw [size_readBytes] at this
  exact this

set_option maxHeartbeats 0 in
/-- **A selector the dispatcher does not know reverts** (no fallback function). -/
theorem unknown_halts (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hsize : 4 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hg : 1000 ≤ m.frame.gasLeft)
    (hsel : Abi.selectorOf m.frame.msg.data ∉
      [0xdd62ed3e, 0x095ea7b3, 0x70a08231, 0x9dc29fac, 0x313ce567, 0x40c10f19, 0x06fdde03,
        0x95d89b41, 0x18160ddd, 0xa9059cbb, 0x23b872dd]) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hs := selectorOf_lt m.frame.msg.data
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hsel
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hsel
  have e1 := word_eq_ofNat_ne (by omega) (by omega) (Ne.symm h1)
  have e2 := word_eq_ofNat_ne (by omega) (by omega) (Ne.symm h2)
  have e3 := word_eq_ofNat_ne (by omega) (by omega) (Ne.symm h3)
  have e4 := word_eq_ofNat_ne (by omega) (by omega) (Ne.symm h4)
  have e5 := word_eq_ofNat_ne (by omega) (by omega) (Ne.symm h5)
  have e6 := word_eq_ofNat_ne (by omega) (by omega) (Ne.symm h6)
  have e7 := word_eq_ofNat_ne (by omega) (by omega) (Ne.symm h7)
  have e8 := word_eq_ofNat_ne (by omega) (by omega) (Ne.symm h8)
  have e9 := word_eq_ofNat_ne (by omega) (by omega) (Ne.symm h9)
  have e10 := word_eq_ofNat_ne (by omega) (by omega) (Ne.symm h10)
  have e11 := word_eq_ofNat_ne (by omega) (by omega) (Ne.symm h11)
  rcases Nat.lt_or_ge (Abi.selectorOf m.frame.msg.data) 0x40c10f19 with hl | hl
  · have hgt := word_gt_ofNat_one (a := 0x40c10f19) (by omega) (by omega) hl
    fresh_intro
    pwp_steps [hval, hlt, Abi.shr_calldataload_zero, hgt, e1, e2, e3, e4, e5, e6, e7, e8, e9,
      e10, e11]
    exact ⟨_, rfl⟩
  · have hgt := word_gt_ofNat_zero (a := 0x40c10f19) (by omega) (by omega) hl
    fresh_intro
    pwp_steps [hval, hlt, Abi.shr_calldataload_zero, hgt, e1, e2, e3, e4, e5, e6, e7, e8, e9,
      e10, e11]
    exact ⟨_, rfl⟩

/-- A view returned the word `x` and changed nothing. -/
def ViewPost (x : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (Bytes.ofWord x) ∧ mf.world = m.world ∧ mf.transient = m.transient ∧
    mf.createdAccounts = m.createdAccounts ∧ mf.frame.sub.logs = m.frame.sub.logs

set_option maxHeartbeats 0 in
/-- **`allowance(o, sp)`**, in any frame: the word in the allowance slot. -/
theorem allowance_halts (m : Machine) (hf : Fresh OzAsset.runtimeCode m) (o sp : Address)
    (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xdd62ed3e)
    (hsize : 68 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg0 : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress o)
    (harg1 : Bytes.toWord (readBytes m.frame.msg.data 36 32) = Word.ofAddress sp)
    (hg : 5000 ≤ m.frame.gasLeft) :
    Halts m (fun mf out => ViewPost (m.world.sload m.frame.msg.currentTarget
      (allowanceSlot m.ctx.crypto Layout.oz o sp)) m mf out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  simp only [allowanceSlot_oz]

set_option maxHeartbeats 0 in
/-- **`totalSupply()`**, in any frame: the word in slot 2. -/
theorem totalSupply_halts (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x18160ddd)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 5000 ≤ m.frame.gasLeft) :
    Halts m (fun mf out => ViewPost (m.world.sload m.frame.msg.currentTarget Layout.oz.totalSupply)
      m mf out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Verified.OpenZeppelin.ERC20.Spec
