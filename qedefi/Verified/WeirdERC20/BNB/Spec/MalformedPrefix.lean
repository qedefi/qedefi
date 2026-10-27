import Verified.WeirdERC20.BNB.Spec.Views
import Verified.WeirdERC20.STA.Spec.MalformedPrefix
import Verified.WeirdERC20.Common.Entry

/-!
# BNB's dispatcher with any calldata

For each entry point of the mainnet BNB code (solc 0.4.12) that takes arguments and is not
excluded (`transfer`, `approve`, `transferFrom`, `burn`, `freeze`, `unfreeze`), two symbolic
runs of the dispatcher and the argument decoder up to the function body:

* `X_dirty`, at any gas, with any value and any calldata of the selector: the frame fails (no
  value is accepted, or the gas runs out), or it reaches the body entry (`entryG`) with the
  argument words decoded — zero-padded past the calldata (solc 0.4 checks no length), the
  `address` words masked to their low 160 bits — with no more gas than it started with;
* `X_clean`, with at least `10000` gas and no value: the frame reaches the body entry exactly
  (`entry`: `c` gas spent).
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.BNB.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.BNB.Contracts
open Verified.WeirdERC20.BNB.Spec Verified.WeirdERC20.Common Verified.Solady.Spec.AnyGas
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
theorem approve_clean (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry mem60 m 0x063a (st2 m.frame.msg.data 433#256 157198259#256) 201) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 0x063a [hval, hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem60, argWord, st1, st2, st3]

set_option maxHeartbeats 0 in
/-- `approve`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem approve_dirty (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG mem60 m 0x063a (st2 m.frame.msg.data 433#256 157198259#256) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x063a] [hsel', hz, and_mask_lit, mask_lit_and]
  exact WP.ret ⟨by simp only [entryG, mem60, argWord, st1, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›⟩

set_option maxHeartbeats 0 in
/-- `transferFrom`'s dispatcher and decoder, exactly. -/
theorem transferFrom_clean (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry mem60 m 0x06dc (st3 m.frame.msg.data 595#256 599290589#256) 275) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 0x06dc [hval, hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem60, argWord, st1, st2, st3]

set_option maxHeartbeats 0 in
/-- `transferFrom`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem transferFrom_dirty (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG mem60 m 0x06dc (st3 m.frame.msg.data 595#256 599290589#256) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x06dc] [hsel', hz, and_mask_lit, mask_lit_and]
  exact WP.ret ⟨by simp only [entryG, mem60, argWord, st1, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›⟩

set_option maxHeartbeats 0 in
/-- `burn`'s dispatcher and decoder, exactly. -/
theorem burn_clean (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x42966c68) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry mem60 m 0x0bd6 (st1 m.frame.msg.data 736#256 1117154408#256) 281) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 0x0bd6 [hval, hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem60, argWord, st1, st2, st3]

set_option maxHeartbeats 0 in
/-- `burn`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem burn_dirty (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x42966c68) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG mem60 m 0x0bd6 (st1 m.frame.msg.data 736#256 1117154408#256) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x0bd6] [hsel', hz, and_mask_lit, mask_lit_and]
  exact WP.ret ⟨by simp only [entryG, mem60, argWord, st1, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›⟩

set_option maxHeartbeats 0 in
/-- `unfreeze`'s dispatcher and decoder, exactly. -/
theorem unfreeze_clean (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x6623fc46) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry mem60 m 0x0d29 (st1 m.frame.msg.data 795#256 1713634374#256) 303) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 0x0d29 [hval, hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem60, argWord, st1, st2, st3]

set_option maxHeartbeats 0 in
/-- `unfreeze`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem unfreeze_dirty (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x6623fc46) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG mem60 m 0x0d29 (st1 m.frame.msg.data 795#256 1713634374#256) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x0d29] [hsel', hz, and_mask_lit, mask_lit_and]
  exact WP.ret ⟨by simp only [entryG, mem60, argWord, st1, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›⟩

set_option maxHeartbeats 0 in
/-- `transfer`'s dispatcher and decoder, exactly. -/
theorem transfer_clean (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry mem60 m 0x0fd2 (st2 m.frame.msg.data 1190#256 2835717307#256) 421) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 0x0fd2 [hval, hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem60, argWord, st1, st2, st3]

set_option maxHeartbeats 0 in
/-- `transfer`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem transfer_dirty (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG mem60 m 0x0fd2 (st2 m.frame.msg.data 1190#256 2835717307#256) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x0fd2] [hsel', hz, and_mask_lit, mask_lit_and]
  exact WP.ret ⟨by simp only [entryG, mem60, argWord, st1, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›⟩

set_option maxHeartbeats 0 in
/-- `freeze`'s dispatcher and decoder, exactly. -/
theorem freeze_clean (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd7a78db8) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hval : m.frame.msg.value = 0)
    (hg : 10000 ≤ m.frame.gasLeft) :
    WP m (fun s => s = entry mem60 m 0x1278 (st1 m.frame.msg.data 1302#256 3618082232#256) 435) (fun _ _ => False) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  solady_fresh_intro
  pwp_run_to 0x1278 [hval, hsel', hz, and_mask_lit, mask_lit_and]
  refine WP.ret ?_
  simp only [entry, entryG, mem60, argWord, st1, st2, st3]

set_option maxHeartbeats 0 in
/-- `freeze`'s dispatcher and decoder at any gas, with any value and calldata. -/
theorem freeze_dirty (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd7a78db8) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun s => s = entryG mem60 m 0x1278 (st1 m.frame.msg.data 1302#256 3618082232#256) s.frame.gasLeft ∧
      s.frame.gasLeft ≤ m.frame.gasLeft ∧ m.frame.msg.value = 0) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  have hgb : m.frame.gasLeft ≤ m.frame.gasLeft := Nat.le_refl _
  solady_fresh_intro
  hwp_steps stop_at [0x1278] [hsel', hz, and_mask_lit, mask_lit_and]
  exact WP.ret ⟨by simp only [entryG, mem60, argWord, st1, st2, st3], by assumption,
    Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›⟩

/-- An argument word past the end of the calldata reads zero. -/
theorem word_past {d : ByteArray} {off : Nat} (h : d.size ≤ off) :
    Bytes.toWord (readBytes d off 32) = 0 := by
  simp only [readBytes, h, ↓reduceIte]
  decide

theorem ofAddress_toAddress_zero : Word.ofAddress (Word.toAddress 0) = 0 := by decide

set_option maxHeartbeats 0 in
/-- `transfer` with at most 4 calldata bytes fails (recipient `0`). -/
theorem transfer_short (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xa9059cbb) (h4 : 4 ≤ m.frame.msg.data.size)
    (hs : m.frame.msg.data.size ≤ 4) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun _ => False) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  have hw4 := word_past (d := m.frame.msg.data) (off := 4) (by omega)
  have hw36 := word_past (d := m.frame.msg.data) (off := 36) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  solady_fresh_intro
  hwp_steps [hsel', hz, hw4, hw36, and_mask_lit, mask_lit_and, ofAddress_toAddress_zero]

set_option maxHeartbeats 0 in
/-- `approve` with at most 36 calldata bytes fails (value `0`). -/
theorem approve_short (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x095ea7b3) (h4 : 4 ≤ m.frame.msg.data.size)
    (hs : m.frame.msg.data.size ≤ 36) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun _ => False) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  have hw36 := word_past (d := m.frame.msg.data) (off := 36) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  solady_fresh_intro
  hwp_steps [hsel', hz, hw36, and_mask_lit, mask_lit_and, ofAddress_toAddress_zero]

set_option maxHeartbeats 0 in
/-- `transferFrom` with at most 36 calldata bytes fails (recipient `0`). -/
theorem transferFrom_short (m : Machine) (hf : Fresh BNB.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd) (h4 : 4 ≤ m.frame.msg.data.size)
    (hs : m.frame.msg.data.size ≤ 36) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun _ => False) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := calldatasize_ne (n := m.frame.msg.data.size) (by omega) hsz
  have hw36 := word_past (d := m.frame.msg.data) (off := 36) (by omega)
  have hw68 := word_past (d := m.frame.msg.data) (off := 68) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  solady_fresh_intro
  hwp_steps [hsel', hz, hw36, hw68, and_mask_lit, mask_lit_and, ofAddress_toAddress_zero]

end Verified.WeirdERC20.BNB.Spec.Malformed
