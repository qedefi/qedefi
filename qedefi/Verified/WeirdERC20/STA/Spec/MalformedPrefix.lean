import Verified.WeirdERC20.STA.Spec.Views
import Verified.WeirdERC20.Common.DataExec

/-!
# Statera's dispatcher with any calldata

For each entry point of the mainnet Statera code (solc 0.5.0) that takes an `address`
(`transfer`, `approve`, `transferFrom`, `destroyFrom`, `upAllowance`, `downAllowance`), two
symbolic runs of the dispatcher and the argument decoder up to the function body:

* `X_dirty`, at any gas, with any value and any calldata of the selector: the frame fails (no
  value is accepted, too few argument words revert, or the gas runs out), or it reaches the
  body entry (`entryG`) with the argument words decoded — the `address` words masked to their
  low 160 bits — with no more gas than it started with;
* `X_clean`, with at least `10000` gas, no value and enough argument words: the frame reaches
  the body entry exactly (`entry`: `c` gas spent).

The `address` mask is solc's `2 ** 160 - 1` (`and_mask_lit`).
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.STA.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.STA.Contracts
open Verified.WeirdERC20.STA.Spec Verified.WeirdERC20.Common Verified.Solady.Spec.AnyGas

/-- The memory after solc's prologue (`mstore(0x40, 0x80)`). -/
def mem0 : Memory := (({} : Memory).expand 64 32).storeWord 64 128#256

/-- The machine `m` at a function body's entry: pc `pc`, stack `st`, the free memory pointer
written, gas `g`. -/
def entryG (m : Machine) (pc : Nat) (st : List Word) (g : Nat) : Machine :=
  { m with frame := { m.frame with pc := pc, stack := st, memory := mem0, gasLeft := g } }

/-- The body entry after spending `c` gas. -/
def entry (m : Machine) (pc : Nat) (st : List Word) (c : Nat) : Machine :=
  entryG m pc st (m.frame.gasLeft - c)

/-- The stack at the entry of a body taking an `address` and a word: the decoded arguments,
the return label `ret`, the selector. -/
def st2 (d : ByteArray) (ret sel : Word) : List Word :=
  [argWord d 1, Word.ofAddress (Word.toAddress (argWord d 0)), ret, sel]

/-- The stack at the entry of `transferFrom`'s body. -/
def st3 (d : ByteArray) : List Word :=
  [argWord d 2, Word.ofAddress (Word.toAddress (argWord d 1)),
    Word.ofAddress (Word.toAddress (argWord d 0)), 478#256, 599290589#256]

/-- solc's address mask (`2¹⁶⁰ − 1`, computed as `2 ** 160 - 1`) keeps the address. -/
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

/-- solc 0.5's ABI length check `calldatasize - 4 < k` passed: the calldata holds `k` bytes of
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
theorem transfer_clean (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 0x088f (st2 m.frame.msg.data 478#256 2835717307#256) 472) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 0x088f [hval, hsel', hz, hl, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st3]

set_option maxHeartbeats 0 in
/-- `transfer`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem transfer_dirty (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 0x088f (st2 m.frame.msg.data 478#256 2835717307#256) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      68 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x088f] [hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 64) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `approve`'s dispatcher and decoder, exactly. -/
theorem approve_clean (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 0x04fe (st2 m.frame.msg.data 478#256 157198259#256) 296) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 0x04fe [hval, hsel', hz, hl, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st3]

set_option maxHeartbeats 0 in
/-- `approve`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem approve_dirty (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 0x04fe (st2 m.frame.msg.data 478#256 157198259#256) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      68 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x04fe] [hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 64) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `upAllowance`'s dispatcher and decoder, exactly. -/
theorem upAllowance_clean (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xe5981a42) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 0x0aa3 (st2 m.frame.msg.data 478#256 3851950658#256) 560) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 0x0aa3 [hval, hsel', hz, hl, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st3]

set_option maxHeartbeats 0 in
/-- `upAllowance`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem upAllowance_dirty (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xe5981a42) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 0x0aa3 (st2 m.frame.msg.data 478#256 3851950658#256) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      68 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x0aa3] [hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 64) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `downAllowance`'s dispatcher and decoder, exactly. -/
theorem downAllowance_clean (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xdf401a96) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 0x09f3 (st2 m.frame.msg.data 478#256 3745520278#256) 538) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 0x09f3 [hval, hsel', hz, hl, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st3]

set_option maxHeartbeats 0 in
/-- `downAllowance`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem downAllowance_dirty (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xdf401a96) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 0x09f3 (st2 m.frame.msg.data 478#256 3745520278#256) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      68 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x09f3] [hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 64) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `destroyFrom`'s dispatcher and decoder, exactly. -/
theorem destroyFrom_clean (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x33393efa) (hsize : 68 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 0x0771 (st2 m.frame.msg.data 686#256 859389690#256) 384) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 64) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 0x0771 [hval, hsel', hz, hl, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st3]

set_option maxHeartbeats 0 in
/-- `destroyFrom`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem destroyFrom_dirty (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x33393efa) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 0x0771 (st2 m.frame.msg.data 686#256 859389690#256) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      68 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x0771] [hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 64) h4 hsz (by norm_num) ‹_›⟩

set_option maxHeartbeats 0 in
/-- `transferFrom`'s dispatcher and decoder, exactly. -/
theorem transferFrom_clean (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (hsize : 100 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry m 0x0583 (st3 m.frame.msg.data) 367) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hl := iszero_lt_size (n := m.frame.msg.data.size) (k := 96) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 0x0583 [hval, hsel', hz, hl, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem0, argWord, st2, st3]

set_option maxHeartbeats 0 in
/-- `transferFrom`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem transferFrom_dirty (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG m 0x0583 (st3 m.frame.msg.data) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0 ∧
      100 ≤ m.frame.msg.data.size) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x0583] [hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ⟨by simp only [entryG, mem0, argWord, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 96) h4 hsz (by norm_num) ‹_›⟩

end Verified.WeirdERC20.STA.Spec.Malformed
