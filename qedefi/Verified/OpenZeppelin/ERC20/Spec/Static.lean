import Verified.OpenZeppelin.ERC20.CalleeTransferFrom
import Verified.OpenZeppelin.ERC20.CalleeMintBurn
import EvmLogic.Tactic.Patched
import EvmLogic.Program.Nested.Wp
import QEDefi.ERC20.Spec.Bytecode

/-!
# `OzAsset` in a static frame

Every state-changing function of the deployed `ERC20Mock` fails in a static frame (a
`STATICCALL`): its paths either revert or reach an `SSTORE`, which fails there
(`step_sstore_static`). Each proof follows the branches of the corresponding callee summary.
-/

namespace Verified.OpenZeppelin.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Solidity.ERC20
open EvmLean.Interpreter EvmLogic.Tactic QEDefi.ERC4626 Verified.OpenZeppelin.Contracts
open EvmLogic.Program.Nested (Wp)
open Verified.Solmate.ERC20 (TwoWordCall ThreeWordCall lt_size_four)

/-- **`SSTORE` in a static frame** fails (out of gas or `writeInStaticContext`). -/
theorem step_sstore_static {m : Machine} {x y : Word} {rest : List Word}
    (hcode : m.frame.code[m.frame.pc]? = some 0x55) (hstk : m.frame.stack = x :: y :: rest)
    (hstatic : m.frame.msg.isStatic = true) :
    ∃ e, step m = finishFrame m (.halt e) := by
  have hdec : Opcode.decode m.ctx.fork 0x55 = .sstore := by cases m.ctx.fork <;> rfl
  have hw : Wp (exec (Opcode.decode m.ctx.fork 0x55)) (fun _ _ => False) m := by
    rw [hdec]
    simp [exec, execSstore, requireNonStatic, accessStorageKey, hstk, hstatic]
  cases hrun : (exec (Opcode.decode m.ctx.fork 0x55)).run m with
  | error e => exact ⟨e, step_of_exec_error hcode hrun⟩
  | ok p => exact (hw.of_run hrun).elim

theorem halts_sstore_static {m : Machine} {H : Machine → Outcome → Prop}
    (hcode : m.frame.code[m.frame.pc]? = some 0x55)
    (hstk : 2 ≤ m.frame.stack.length) (hstatic : m.frame.msg.isStatic = true)
    (hH : ∀ e, H m (.halt e)) : Halts m H := by
  obtain ⟨x, y, rest, hs⟩ : ∃ x y rest, m.frame.stack = x :: y :: rest := by
    match h : m.frame.stack, hstk with
    | x :: y :: rest, _ => exact ⟨x, y, rest, rfl⟩
  obtain ⟨e, he⟩ := step_sstore_static hcode hs hstatic
  exact Halts.of_step he (.refl _) (hH e)

/-- Close a `WP` goal stopped at an `SSTORE` of a static frame, the postcondition a failure. -/
macro "sstore_static" : tactic => `(tactic| (
  refine WP.halts (halts_sstore_static ?_ ?_ ?_ (fun _ => trivial))
  · code_fact
  · simp
  · assumption))

open QEDefi.ERC20.Spec (Fails)

set_option hygiene false in
/-- The common prefix: the selector, the calldata size check. -/
macro "oz_pre" n:num : tactic => `(tactic| (
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 $n))
      = 1 := iszero_slt_calldatasize hsize (by omega)))

set_option maxHeartbeats 0 in
/-- **`transfer(dst, amount)` fails in a static frame.** -/
theorem transfer_static (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = true) {dst : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => Fails o) := by
  oz_pre 64
  by_cases hc : m.frame.msg.caller = 0
  · have hc' : Word.ofAddress m.frame.msg.caller = 0#256 := by rw [hc]; rfl
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, hc',
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    exact trivial
  have hc' := ofAddress_ne_zero hc
  by_cases hdst : dst = 0
  · subst hdst
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, ofAddress_zero,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    exact trivial
  have hd' := ofAddress_ne_zero hdst
  rcases Nat.lt_or_ge (m.world.sload m.frame.msg.currentTarget
      (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress m.frame.msg.caller) ++
        Bytes.ofWord 0#256))).toNat amount.toNat with hbal | hbal
  · fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [(Word.lt_eq_one_iff _ _).2 hbal]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    exact trivial
  · fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [(Word.lt_eq_zero_iff _ _).2 hbal]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    sstore_static

set_option maxHeartbeats 0 in
/-- **`approve(spender, amount)` fails in a static frame.** -/
theorem approve_static (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = true) {spender : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x095ea7b3 (Word.ofAddress spender) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 40000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => Fails o) := by
  oz_pre 64
  by_cases hc : m.frame.msg.caller = 0
  · have hc' : Word.ofAddress m.frame.msg.caller = 0#256 := by rw [hc]; rfl
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64, hc']
    exact trivial
  have hc' := ofAddress_ne_zero hc
  by_cases hs : spender = 0
  · subst hs
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64, ofAddress_zero]
    exact trivial
  have hs' := ofAddress_ne_zero hs
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  sstore_static

set_option maxHeartbeats 0 in
/-- **`mint(dst, amount)` fails in a static frame.** -/
theorem mint_static (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = true) {dst : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x40c10f19 (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => Fails o) := by
  oz_pre 64
  by_cases hdst : dst = 0
  · subst hdst
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64, ofAddress_zero]
    exact trivial
  have hd' := ofAddress_ne_zero hdst
  rcases Nat.lt_or_ge ((m.world.sload m.frame.msg.currentTarget 2#256).toNat + amount.toNat)
      (2 ^ 256) with hov | hov
  · fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [gt_add_self_eq_zero hov]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    sstore_static
  · fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [gt_add_self_eq_one hov]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    exact trivial

set_option maxHeartbeats 0 in
/-- **`burn(src, amount)` fails in a static frame.** -/
theorem burn_static (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = true) {src : Address}
    {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => Fails o) := by
  oz_pre 64
  by_cases hsrc : src = 0
  · subst hsrc
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64, ofAddress_zero]
    exact trivial
  have hs' := ofAddress_ne_zero hsrc
  rcases Nat.lt_or_ge (m.world.sload m.frame.msg.currentTarget
      (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 0#256))).toNat
      amount.toNat with hbal | hbal
  · fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [(Word.lt_eq_one_iff _ _).2 hbal]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    exact trivial
  · fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [(Word.lt_eq_zero_iff _ _).2 hbal]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    sstore_static

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- **`transferFrom(src, dst, amount)` fails in a static frame.** -/
theorem transferFrom_static (m : Machine) (hf : Fresh OzAsset.runtimeCode m)
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
  by_cases hmax : m.world.sload m.frame.msg.currentTarget (m.ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress m.frame.msg.caller) ++ Bytes.ofWord (m.ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 1#256)))) = maxWord
  · by_cases hs : src = 0
    · subst hs
      simp only [ofAddress_zero] at hmax
      fresh_intro
      pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64, ofAddress_zero]
      simp only [lt_maxLit_of_eq hmax]
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64, ofAddress_zero]
      exact trivial
    have hs' := ofAddress_ne_zero hs
    by_cases hdst : dst = 0
    · subst hdst
      fresh_intro
      pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64, ofAddress_zero]
      simp only [lt_maxLit_of_eq hmax]
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64, ofAddress_zero]
      exact trivial
    have hd' := ofAddress_ne_zero hdst
    rcases Nat.lt_or_ge (m.world.sload m.frame.msg.currentTarget
        (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++
          Bytes.ofWord 0#256))).toNat amount.toNat with hbal | hbal
    · fresh_intro
      pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
      simp only [lt_maxLit_of_eq hmax]
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      simp only [(Word.lt_eq_one_iff _ _).2 hbal]
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      exact trivial
    · fresh_intro
      pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
      simp only [lt_maxLit_of_eq hmax]
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      simp only [(Word.lt_eq_zero_iff _ _).2 hbal]
      pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      sstore_static
  rcases Nat.lt_or_ge (m.world.sload m.frame.msg.currentTarget (m.ctx.crypto.keccak256
      (Bytes.ofWord (Word.ofAddress m.frame.msg.caller) ++ Bytes.ofWord (m.ctx.crypto.keccak256
        (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 1#256))))).toNat amount.toNat with
    hlt' | hle
  · fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
    simp only [lt_maxLit_of_ne hmax]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    simp only [(Word.lt_eq_one_iff _ _).2 hlt']
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
    exact trivial
  by_cases hs : src = 0
  · subst hs
    simp only [ofAddress_zero] at hmax hle
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64, ofAddress_zero]
    simp only [lt_maxLit_of_ne hmax]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64, ofAddress_zero]
    simp only [(Word.lt_eq_zero_iff _ _).2 hle]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64, ofAddress_zero]
    exact trivial
  have hs' := ofAddress_ne_zero hs
  by_cases hc : m.frame.msg.caller = 0
  · have hc' : Word.ofAddress m.frame.msg.caller = 0#256 := by rw [hc]; rfl
    simp only [hc'] at hmax hle
    fresh_intro
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64, hc']
    simp only [lt_maxLit_of_ne hmax]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64, hc']
    simp only [(Word.lt_eq_zero_iff _ _).2 hle]
    pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64, hc']
    exact trivial
  have hc' := ofAddress_ne_zero hc
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2,
      ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self, Memory.read_64]
  simp only [lt_maxLit_of_ne hmax]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  simp only [(Word.lt_eq_zero_iff _ _).2 hle]
  pwp_steps [ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
  sstore_static

end Verified.OpenZeppelin.ERC20.Spec
