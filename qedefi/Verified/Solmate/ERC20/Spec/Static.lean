import Verified.Solmate.ERC20.Spec.Normal
import EvmLogic.Program.Nested.Gas

/-!
# Solmate's `ERC20` in static frames

`transfer`, `transferFrom`, `approve`, `mint` and `burn` write storage on every successful
path, so in a static frame they fail: they revert where the model fails, and otherwise the
first `SSTORE` halts (`step_sstore_static`). The views are the same in static frames
(`view_normal` has no static hypothesis).
-/

namespace Verified.Solmate.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Program.Nested EvmLogic.Tactic EvmLogic.Solidity.ERC20
open Verified.Solmate.Contracts Verified.Solmate.ERC20 QEDefi.ERC20.Spec

theorem exec_sstore_static (m : Machine) (hstatic : m.frame.msg.isStatic = true) :
    Wp (exec .sstore) (fun _ _ => False) m := by
  simp [exec, execSstore, requireNonStatic, accessStorageKey, hstatic]

/-- **`SSTORE` in a static frame halts.** -/
theorem step_sstore_static {m : Machine} (hcode : m.frame.code[m.frame.pc]? = some 0x55)
    (hstatic : m.frame.msg.isStatic = true) : ∃ e, step m = finishFrame m (.halt e) := by
  rw [step_eq_of_code hcode, show Opcode.decode m.ctx.fork 0x55 = .sstore by
    cases m.ctx.fork <;> rfl]
  cases h : (exec .sstore).run m with
  | error e => exact ⟨e, rfl⟩
  | ok p => exact ((exec_sstore_static m hstatic).of_run h).elim

/-- A frame at `SSTORE` in a static frame ends with an exceptional halt. -/
theorem wp_sstore_static {m : Machine} {Q : Machine → Prop} {H : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0x55) (hstatic : m.frame.msg.isStatic = true)
    (hH : ∀ e, H m (.halt e)) : WP m Q H := by
  obtain ⟨e, he⟩ := step_sstore_static hcode hstatic
  exact WP.halt_of_step he (.refl _) (hH e)

variable {ia : SolmateAsset.Immutables}

set_option maxHeartbeats 0 in
/-- `transfer` in a static frame fails. -/
theorem transfer_static (m : Machine) (hf : Fresh (code ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = true) {dst : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => Fails o) := by
  by_cases hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)).toNat
  · apply WP.halts_of_false
    obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
    have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
    have hsel' := Dispatch.selector_eq hsel
    have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
        (BitVec.ofNat 256 64)) = 1 := iszero_slt_calldatasize hsize (by omega)
    simp only [balanceSlot_solmate] at hbal
    have hagree := assetJumpDestsAgree ia
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [gt_sub_self_of_le hbal, iszero_zero]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    apply wp_sstore_static
    · pcode_fact
    · exact hstatic
    · intro e; trivial
  · exact (transfer_halts_revert m hf hval hd hsz (by omega) (by omega)).mono
      fun _ o _ h => by obtain ⟨⟨out, rfl⟩, -⟩ := h; trivial

set_option maxHeartbeats 0 in
/-- `approve` in a static frame fails. -/
theorem approve_static (m : Machine) (hf : Fresh (code ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = true) {spender : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x095ea7b3 (Word.ofAddress spender) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 40000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => Fails o) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 64))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  apply wp_sstore_static
  · pcode_fact
  · exact hstatic
  · intro e; trivial

set_option maxHeartbeats 0 in
/-- `mint` in a static frame fails. -/
theorem mint_static (m : Machine) (hf : Fresh (code ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = true) {dst : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x40c10f19 (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => Fails o) := by
  by_cases hov : (m.world.sload m.frame.msg.currentTarget 2#256).toNat + amount.toNat < 2 ^ 256
  · apply WP.halts_of_false
    obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
    have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
    have hsel' := Dispatch.selector_eq hsel
    have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
        (BitVec.ofNat 256 64)) = 1 := iszero_slt_calldatasize hsize (by omega)
    have hagree := assetJumpDestsAgree ia
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [gt_add_self_of_lt hov, iszero_zero]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    apply wp_sstore_static
    · pcode_fact
    · exact hstatic
    · intro e; trivial
  · exact (mint_halts_revert m hf hval hd hsz (by omega) (by omega)).mono
      fun _ o _ h => by obtain ⟨⟨out, rfl⟩, -⟩ := h; trivial

set_option maxHeartbeats 0 in
/-- `burn` in a static frame fails. -/
theorem burn_static (m : Machine) (hf : Fresh (code ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = true) {src : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => Fails o) := by
  by_cases hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
      (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat
  · apply WP.halts_of_false
    obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
    have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
    have hsel' := Dispatch.selector_eq hsel
    have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256)
        (BitVec.ofNat 256 64)) = 1 := iszero_slt_calldatasize hsize (by omega)
    simp only [balanceSlot_solmate] at hbal
    have hagree := assetJumpDestsAgree ia
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [gt_sub_self_of_le hbal, iszero_zero]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    apply wp_sstore_static
    · pcode_fact
    · exact hstatic
    · intro e; trivial
  · exact (burn_halts_revert m hf hval hd hsz (by omega) (by omega)).mono
      fun _ o _ h => by obtain ⟨⟨out, rfl⟩, -⟩ := h; trivial

set_option maxHeartbeats 0 in
/-- `transferFrom` in a static frame fails. -/
theorem transferFrom_static (m : Machine) (hf : Fresh (code ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = true) {src dst : Address}
    {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => Fails o) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 96))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
    ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  by_cases hmax : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 4#256)))) = MAXW
  · simp only [hmax, Solidity.eq_self]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    by_cases hbal : amount.toNat ≤ (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 3#256))).toNat
    · simp only [gt_sub_self_of_le hbal, iszero_zero]
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      apply wp_sstore_static
      · pcode_fact
      · exact hstatic
      · intro e; trivial
    · simp only [gt_sub_self_of_lt (Nat.lt_of_not_le hbal), iszero_one]
      pwp_steps
      trivial
  · simp only [eq_of_ne hmax]
    by_cases hle : amount.toNat ≤ (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
          (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 4#256))))).toNat
    · pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      simp only [gt_sub_self_of_le hle, iszero_zero]
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      apply wp_sstore_static
      · pcode_fact
      · exact hstatic
      · intro e; trivial
    · rw [Nat.not_le] at hle
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      simp only [gt_sub_self_of_lt hle, iszero_one]
      pwp_steps
      trivial

end Verified.Solmate.ERC20.Spec
