import Verified.WETH9.Spec.Abs
import Verified.WETH9.Solvency
import Verified.WeirdERC20.BNB.Spec.Views
import Verified.WeirdERC20.STA.Spec.MalformedPrefix
import Verified.WeirdERC20.Common.Entry

/-!
# WETH9's dispatcher with any calldata

For each entry point of the mainnet WETH9 code (solc 0.4.19) that takes arguments and is not
excluded (`transfer`, `approve`, `transferFrom`), two symbolic
runs of the dispatcher and the argument decoder up to the function body:

* `X_dirty`, at any gas, with any value and any calldata of the selector: the frame fails (no
  value is accepted, or the gas runs out), or it reaches the body entry (`entryG`) with the
  argument words decoded — zero-padded past the calldata (solc 0.4 checks no length), the
  `address` words masked to their low 160 bits — with no more gas than it started with;
* `X_clean`, with at least `10000` gas and no value: the frame reaches the body entry exactly
  (`entry`: `c` gas spent).
-/

set_option linter.unusedSimpArgs false

namespace Verified.WETH9.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WETH9.Contracts
open Verified.WETH9.Spec Verified.WeirdERC20.Common
open Verified.WeirdERC20.BNB.Spec (div_selector argWord)
open Verified.Solady.Spec.AnyGas
open Verified.WeirdERC20.STA.Spec.Malformed (and_mask_lit mask_lit_and)

/-- The memory after solc 0.4's prologue (`mstore(0x40, 0x60)`). -/
def mem60 : Memory := (({} : Memory).expand 64 32).storeWord 64 96#256

/-- The stack at the entry of a body taking one word. -/
def st1 (d : ByteArray) (ret sel : Word) : List Word := [argWord d 0, ret, sel]

/-- The stack at the entry of a body taking an `address` and a word. -/
def st2 (d : ByteArray) (ret sel : Word) : List Word :=
  [argWord d 1, Word.ofAddress (Word.toAddress (argWord d 0)), ret, sel]

/-- The stack at the entry of a body taking two `address`es and a word. -/
def st3 (d : ByteArray) (ret sel : Word) : List Word :=
  [argWord d 2, Word.ofAddress (Word.toAddress (argWord d 1)),
    Word.ofAddress (Word.toAddress (argWord d 0)), ret, sel]

set_option maxHeartbeats 0 in
/-- `approve`'s dispatcher and decoder, exactly. -/
theorem approve_clean (m : Machine) (hf : Fresh WETH9.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry mem60 m 0x057b (st2 m.frame.msg.data 391#256 157198259#256) 204) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  solady_fresh_intro
  pwp_run_to 0x057b [hval, hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem60, argWord, st1, st2, st3]

set_option maxHeartbeats 0 in
/-- `approve`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem approve_dirty (m : Machine) (hf : Fresh WETH9.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG mem60 m 0x057b (st2 m.frame.msg.data 391#256 157198259#256) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x057b] [hsel', hz, and_mask_lit, mask_lit_and]
  exact WP.ret ⟨by simp only [entryG, mem60, argWord, st1, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›⟩

set_option maxHeartbeats 0 in
/-- `transferFrom`'s dispatcher and decoder, exactly. -/
theorem transferFrom_clean (m : Machine) (hf : Fresh WETH9.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry mem60 m 0x068c (st3 m.frame.msg.data 553#256 599290589#256) 278) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  solady_fresh_intro
  pwp_run_to 0x068c [hval, hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem60, argWord, st1, st2, st3]

set_option maxHeartbeats 0 in
/-- `transferFrom`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem transferFrom_dirty (m : Machine) (hf : Fresh WETH9.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG mem60 m 0x068c (st3 m.frame.msg.data 553#256 599290589#256) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x068c] [hsel', hz, and_mask_lit, mask_lit_and]
  exact WP.ret ⟨by simp only [entryG, mem60, argWord, st1, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›⟩

set_option maxHeartbeats 0 in
/-- `transfer`'s dispatcher and decoder, exactly. -/
theorem transfer_clean (m : Machine) (hf : Fresh WETH9.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry mem60 m 0x0bce (st2 m.frame.msg.data 944#256 2835717307#256) 358) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  solady_fresh_intro
  pwp_run_to 0x0bce [hval, hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem60, argWord, st1, st2, st3]

set_option maxHeartbeats 0 in
/-- `transfer`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem transfer_dirty (m : Machine) (hf : Fresh WETH9.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG mem60 m 0x0bce (st2 m.frame.msg.data 944#256 2835717307#256) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x0bce] [hsel', hz, and_mask_lit, mask_lit_and]
  exact WP.ret ⟨by simp only [entryG, mem60, argWord, st1, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›⟩

/-- An argument word past the end of the calldata reads zero. -/
theorem word_past {d : ByteArray} {off : Nat} (h : d.size ≤ off) :
    Bytes.toWord (readBytes d off 32) = 0 := by
  simp only [readBytes, h, ↓reduceIte]
  decide

theorem ofAddress_toAddress_zero : Word.ofAddress (Word.toAddress 0) = 0 := by decide

end Verified.WETH9.Spec.Malformed
