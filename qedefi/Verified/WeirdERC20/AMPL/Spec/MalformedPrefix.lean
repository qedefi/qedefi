import Verified.WeirdERC20.AMPL.Spec.MalformedCert
import Verified.WeirdERC20.Common.DataExec

/-!
# AMPL's dispatcher with any calldata

`UFragments` is compiled by solc 0.7.6 with ABI coder v1: the dispatcher checks that there is
no value (once, for every entry point) and that the calldata holds every argument word, and
masks each `address` word to its low 160 bits without checking the high bits. For each entry
point that takes an `address` (`transfer`, `approve`, `transferFrom`, `increaseAllowance`,
`decreaseAllowance`, `transferAll`, `transferAllFrom`, `setMonetaryPolicy`,
`transferOwnership`), two symbolic runs of the dispatcher up to the function body:

* `X_dirty`, at any gas, with any value and any calldata of the selector: the frame fails (no
  value is accepted, too few argument words revert, or the gas runs out), or it reaches the
  body entry (`entryG`) with the argument words decoded, the `address` words masked, with no
  more gas than it started with;
* `X_clean`, with at least `10000` gas, no value and enough argument words: the frame reaches
  the body entry exactly (`entry`: `c` gas spent).

Also: `getter_dispatch` (a getter's dispatch target, nothing written), `value_low` (value
fails), and `rebase_dirty`, `renounce_dirty`, `permit_dirty` (fail, or no value and enough
argument words).
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.WeirdERC20.AMPL.Spec Verified.WeirdERC20.Common Verified.Solady.Spec.AnyGas
open Verified.Common.Malformed (Unchanged)
open EvmLogic.AbsInt

/-- The memory after solc's prologue (`mstore(0x40, 0x80)`). -/
def mem0 : Memory := (({} : Memory).expand 64 32).storeWord 64 128#256

/-- The machine `m` at a function body's entry: pc `pc`, stack `st`, the free memory pointer
written, gas `g`. -/
def entryG (m : Machine) (pc : Nat) (st : List Word) (g : Nat) : Machine :=
  { m with frame := { m.frame with pc := pc, stack := st, memory := mem0, gasLeft := g } }

/-- The body entry after spending `c` gas. -/
def entry (m : Machine) (pc : Nat) (st : List Word) (c : Nat) : Machine :=
  entryG m pc st (m.frame.gasLeft - c)

/-- A masked `address` argument word. -/
abbrev maddr (d : ByteArray) (i : Nat) : Word := Word.ofAddress (Word.toAddress (argWord d i))

/-- The stack at the entry of a body taking an `address` and a word. -/
def st2 (d : ByteArray) (ret sel : Word) : List Word := [argWord d 1, maddr d 0, ret, sel]

/-- The stack at the entry of a body taking an `address`. -/
def st1 (d : ByteArray) (ret sel : Word) : List Word := [maddr d 0, ret, sel]

/-- The stack at the entry of `transferAllFrom`'s body. -/
def stAA (d : ByteArray) : List Word := [maddr d 1, maddr d 0, 648#256, 2228532240#256]

/-- The stack at the entry of `transferFrom`'s body. -/
def st3 (d : ByteArray) : List Word :=
  [argWord d 2, maddr d 1, maddr d 0, 648#256, 599290589#256]

/-- solc's address mask (`2¹⁶⁰ − 1`) keeps the address. -/
theorem and_mask_lit (x : Word) :
    x &&& 1461501637330902918203684832716283019655932542975#256 =
      Word.ofAddress (Word.toAddress x) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Word.ofAddress, Word.toAddress,
    BitVec.toNat_setWidth]
  rw [show (1461501637330902918203684832716283019655932542975 : Nat) % 2 ^ 256 = 2 ^ 160 - 1 by
    norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega : x.toNat % 2 ^ 160 < 2 ^ 256)]

theorem mask_lit_and (x : Word) :
    1461501637330902918203684832716283019655932542975#256 &&& x =
      Word.ofAddress (Word.toAddress x) := by
  rw [BitVec.and_comm]; exact and_mask_lit x

/-- solc's ABI length check `calldatasize - 4 < k` passed: the calldata holds `k` bytes of
arguments. -/
theorem size_of_iszero_lt {n k : Nat} (h4 : 4 ≤ n) (hn : n < 2 ^ 64) (hk : k < 2 ^ 64)
    (h : Word.iszero (Word.lt (ofNat n - 4#256) (BitVec.ofNat 256 k)) ≠ 0) : 4 + k ≤ n := by
  by_contra hc
  apply h
  have hx : (ofNat n - 4#256 : Word).toNat = n - 4 := by
    rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def, ofNat]; omega)]
    simp [ofNat]; omega
  have : BitVec.ult (ofNat n - 4#256) (BitVec.ofNat 256 k) := by
    simp only [BitVec.ult, hx, BitVec.toNat_ofNat, decide_eq_true_eq]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp [Word.lt, Word.ofBool, this, Word.iszero]

set_option maxHeartbeats 0 in
/-- `transfer`'s dispatcher and decoder, exactly. -/
theorem transfer_clean (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 4291 (st2 m.frame.msg.data 648#256 2835717307#256) 276)
      (fun _ _ => False) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 4291 [hval, hsel', hz, hl, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st1, stAA, st3, maddr]

set_option maxHeartbeats 0 in
/-- `transfer`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem transfer_dirty (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 4291 (st2 m.frame.msg.data 648#256 2835717307#256)
        s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      68 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [4291] [hsel', hz, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st1, stAA, st3, maddr], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 64) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `approve`'s dispatcher and decoder, exactly. -/
theorem approve_clean (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 1950 (st2 m.frame.msg.data 648#256 157198259#256) 278)
      (fun _ _ => False) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 1950 [hval, hsel', hz, hl, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st1, stAA, st3, maddr]

set_option maxHeartbeats 0 in
/-- `approve`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem approve_dirty (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 1950 (st2 m.frame.msg.data 648#256 157198259#256)
        s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      68 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [1950] [hsel', hz, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st1, stAA, st3, maddr], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 64) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `increaseAllowance`'s dispatcher and decoder, exactly. -/
theorem increaseAllowance_clean (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x39509351) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 2819 (st2 m.frame.msg.data 648#256 961581905#256) 299)
      (fun _ _ => False) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 2819 [hval, hsel', hz, hl, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st1, stAA, st3, maddr]

set_option maxHeartbeats 0 in
/-- `increaseAllowance`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem increaseAllowance_dirty (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x39509351) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 2819 (st2 m.frame.msg.data 648#256 961581905#256)
        s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      68 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [2819] [hsel', hz, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st1, stAA, st3, maddr], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 64) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `decreaseAllowance`'s dispatcher and decoder, exactly. -/
theorem decreaseAllowance_clean (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa457c2d7) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 4145 (st2 m.frame.msg.data 648#256 2757214935#256) 254)
      (fun _ _ => False) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 4145 [hval, hsel', hz, hl, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st1, stAA, st3, maddr]

set_option maxHeartbeats 0 in
/-- `decreaseAllowance`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem decreaseAllowance_dirty (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa457c2d7) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 4145 (st2 m.frame.msg.data 648#256 2757214935#256)
        s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      68 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [4145] [hsel', hz, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st1, stAA, st3, maddr], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 64) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `transferAll`'s dispatcher and decoder, exactly. -/
theorem transferAll_clean (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa3a7e7f3) (hsize : 36 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 3943 (st1 m.frame.msg.data 648#256 2745690099#256) 305)
      (fun _ _ => False) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 32) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 3943 [hval, hsel', hz, hl, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st1, stAA, st3, maddr]

set_option maxHeartbeats 0 in
/-- `transferAll`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem transferAll_dirty (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa3a7e7f3) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 3943 (st1 m.frame.msg.data 648#256 2745690099#256)
        s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      36 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [3943] [hsel', hz, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st1, stAA, st3, maddr], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 32) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `setMonetaryPolicy`'s dispatcher and decoder, exactly. -/
theorem setMonetaryPolicy_clean (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x8b5a6a08) (hsize : 36 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 3698 (st1 m.frame.msg.data 974#256 2337958408#256) 262)
      (fun _ _ => False) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 32) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 3698 [hval, hsel', hz, hl, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st1, stAA, st3, maddr]

set_option maxHeartbeats 0 in
/-- `setMonetaryPolicy`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem setMonetaryPolicy_dirty (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x8b5a6a08) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 3698 (st1 m.frame.msg.data 974#256 2337958408#256)
        s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      36 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [3698] [hsel', hz, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st1, stAA, st3, maddr], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 32) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `transferOwnership`'s dispatcher and decoder, exactly. -/
theorem transferOwnership_clean (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xf2fde38b) (hsize : 36 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 5423 (st1 m.frame.msg.data 974#256 4076725131#256) 304)
      (fun _ _ => False) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 32) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 5423 [hval, hsel', hz, hl, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st1, stAA, st3, maddr]

set_option maxHeartbeats 0 in
/-- `transferOwnership`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem transferOwnership_dirty (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xf2fde38b) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 5423 (st1 m.frame.msg.data 974#256 4076725131#256)
        s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      36 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [5423] [hsel', hz, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st1, stAA, st3, maddr], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 32) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `transferAllFrom`'s dispatcher and decoder, exactly. -/
theorem transferAllFrom_clean (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x84d4b410) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 3411 (stAA m.frame.msg.data) 261)
      (fun _ _ => False) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 3411 [hval, hsel', hz, hl, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st1, stAA, st3, maddr]

set_option maxHeartbeats 0 in
/-- `transferAllFrom`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem transferAllFrom_dirty (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x84d4b410) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 3411 (stAA m.frame.msg.data)
        s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      68 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [3411] [hsel', hz, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st1, stAA, st3, maddr], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 64) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `transferFrom`'s dispatcher and decoder, exactly. -/
theorem transferFrom_clean (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (hsize : 100 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 2291 (st3 m.frame.msg.data) 326)
      (fun _ _ => False) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 96) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 2291 [hval, hsel', hz, hl, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st1, stAA, st3, maddr]

set_option maxHeartbeats 0 in
/-- `transferFrom`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem transferFrom_dirty (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 2291 (st3 m.frame.msg.data)
        s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      100 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [2291] [hsel', hz, and_mask_lit, mask_lit_and, Abi.shr_calldataload_zero]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st1, stAA, st3, maddr], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 96) h4 hsz (by norm_num) ‹_›⟩

/-! ## Getters, value, and the entry points without an `address` -/

/-- The dispatcher's run to a getter's dispatch target leaves the world, the transient storage
and the logs, with the selector as the only word on the stack. -/
def AtGetter (m : Machine) (q : Nat) (sel : Nat) (s : Machine) : Prop :=
  s.frame.pc = q ∧ s.frame.stack = [BitVec.ofNat 256 sel] ∧ s.frame.code = AMPL.runtimeCode ∧
    Unchanged m s

set_option maxHeartbeats 0 in
/-- The dispatcher to a getter, at any gas. -/
theorem getter_dispatch {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (m : Machine)
    (hf : Fresh AMPL.runtimeCode m) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (AtGetter m q sel) (fun _ o => Fails o) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  simp only [getterEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hge
  rcases hge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    solady_fresh_intro
    hwp_steps stop_at [479, 976, 1002, 1094, 1102, 1132, 1184, 1230, 1273, 1395, 1431, 1439,
      1447, 1581, 1708, 1754] [hsel', hz, Abi.shr_calldataload_zero]
    exact WP.ret ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **A getter fails or changes nothing**, with any value, arguments and gas. -/
theorem getter_halts {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (m : Machine)
    (hf : Fresh AMPL.runtimeCode m) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    Halts m (fun mf o => Fails o ∨ Unchanged m mf) := by
  have hin : InT amplGetters q [.top] :=
    amplGetters_seed (List.mem_map.2 ⟨(sel, q), hge, rfl⟩)
  rcases getter_dispatch hge m hf hsel h4 hsz with ⟨s, hst, hpc, hs, hcode, h1, h2, h3⟩ | h
  · refine Halts.of_steps hst ((Verified.Common.Malformed.halts_pure amplGetters_cert
      amplGetters_pure s hcode (Verified.Common.Malformed.inCert_top hin hpc hs)).mono
      fun mf _ _ ⟨g1, g2, g3⟩ => .inr ?_)
    exact ⟨g1.trans h1, g2.trans h2, g3.trans h3⟩
  · exact h.mono fun _ _ _ h => .inl h

set_option maxHeartbeats 0 in
/-- **A frame with value fails** (the dispatcher's first check: no function is payable), at
any gas. -/
theorem value_low (m : Machine) (hf : Fresh AMPL.runtimeCode m) (hval : m.frame.msg.value ≠ 0) :
    Halts m (fun _ o => Fails o) := by
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hz := EvmLogic.Solidity.iszero_of_ne hval
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hz]

set_option maxHeartbeats 0 in
/-- `rebase(uint256,int256)`'s dispatcher at any gas: it fails, or there is no value and the
calldata holds both argument words. -/
theorem rebase_dirty (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x7a43e23f) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun _ => m.frame.msg.value = 0 ∧ 68 ≤ m.frame.msg.data.size)
      (fun _ o => Fails o) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  solady_fresh_intro
  hwp_steps stop_at [1260] [hsel', hz, Abi.shr_calldataload_zero]
  exact WP.ret ⟨Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 64) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `permit`'s dispatcher at any gas: it fails, or there is no value and the calldata holds the
seven argument words. -/
theorem permit_dirty (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun _ => m.frame.msg.value = 0 ∧ 228 ≤ m.frame.msg.data.size)
      (fun _ o => Fails o) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  solady_fresh_intro
  hwp_steps stop_at [1649] [hsel', hz, Abi.shr_calldataload_zero]
  exact WP.ret ⟨Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 224) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- The dispatcher's value check at any gas: the frame fails, or there is no value. -/
theorem value_dirty (m : Machine) (hf : Fresh AMPL.runtimeCode m) :
    WP m (fun _ => m.frame.msg.value = 0) (fun _ o => Fails o) := by
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  solady_fresh_intro
  hwp_steps stop_at [16] []
  exact WP.ret (Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›)

end Verified.WeirdERC20.AMPL.Spec.Malformed
