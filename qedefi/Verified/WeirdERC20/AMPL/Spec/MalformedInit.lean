import Verified.WeirdERC20.AMPL.Spec.MalformedPrefix

/-!
# AMPL's initializers revert on an initialized instance

`initialize(address)` and `initialize(string,string,uint8)` carry OpenZeppelin's (zos)
`initializer` modifier: `require(initializing || isConstructor() || !initialized)`, with
`isConstructor()` the check `extcodesize(address()) == 0`. On an instance in the scope of the
abstraction (`Live`: `initialized` set, `initializing` clear) whose executing account holds code
of a size below `2²⁵⁶` (`EXTCODESIZE` pushes the size modulo `2²⁵⁶`), the modifier reverts:
`init_addr_low`, `init_strings_low`, at any gas, with any value and calldata.

The `EXTCODESIZE` and `CALLDATACOPY` rules of the any-gas calculus (`wp_extcodesize`,
`wp_calldatacopy`) leave the gas, the access lists and (for the copy) the memory unknown: the
modifier reads neither.
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open EvmLogic.Program.Nested
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.AMPL.Contracts
open Verified.WeirdERC20.AMPL.Spec Verified.Solady.Spec.AnyGas

variable {H : Machine → Outcome → Prop} {Q : Machine → Prop} {m : Machine}

/-- `EXTCODESIZE` at any gas, with the size of the code at the address; the gas and the access
lists after it are left unknown. -/
theorem wp_extcodesize {x : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x3b)
    (hstk : m.frame.stack = x :: rest)
    (hrec : ∀ (g : Nat) (sub : Substate), WP { m with frame := { m.frame with
        stack := ofNat (m.world.code (Word.toAddress x)).size :: rest,
        gasLeft := g, sub := sub, pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  have hdec : Opcode.decode m.ctx.fork 0x3b = .extcodesize := by cases m.ctx.fork <;> rfl
  by_cases hl : rest.length < 1024
  · by_cases hg : Gas.accessCost (m.frame.sub.accessedAddresses.contains (Word.toAddress x)) ≤
        m.frame.gasLeft
    · exact WP.of_step (step_extcodesize hcode hstk hl hg) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
        (hrec _ _)
    · have hg' := Nat.lt_of_not_le hg
      refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
      rw [hdec]
      simp only [exec, popAddress, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
        StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind]
      rw [run_accessAddress]
      simp only [pure_bind, charge, getFrame, StateT.run_bind, StateT.run_get, StateT.run_pure,
        hg', ite_true]
      rfl
  · have hl' : Gas.stackLimit ≤ rest.length := Nat.le_of_not_lt hl
    by_cases hg : Gas.accessCost (m.frame.sub.accessedAddresses.contains (Word.toAddress x)) ≤
        m.frame.gasLeft
    · have hg' := Nat.not_lt.mpr hg
      refine wp_fail_of_error (e := .stackOverflow) hsnap hcode ?_
      rw [hdec]
      simp only [exec, popAddress, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
        StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind]
      rw [run_accessAddress]
      simp only [pure_bind, charge, push, getFrame, modifyFrame, StateT.run_bind, StateT.run_get,
        StateT.run_pure, StateT.run_modify, hg', hl', ite_true, ite_false]
      rfl
    · have hg' := Nat.lt_of_not_le hg
      refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
      rw [hdec]
      simp only [exec, popAddress, pop, getFrame, modifyFrame, StateT.run_bind, hstk,
        StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind]
      rw [run_accessAddress]
      simp only [pure_bind, charge, getFrame, StateT.run_bind, StateT.run_get, StateT.run_pure,
        hg', ite_true]
      rfl

/-- `CALLDATACOPY` at any gas: the memory and gas after it are left unknown. -/
theorem wp_calldatacopy {x y z : Word} {rest : List Word}
    (hsnap : FailH H) (hcode : m.frame.code[m.frame.pc]? = some 0x37)
    (hstk : m.frame.stack = x :: y :: z :: rest)
    (hrec : ∀ (mem : Memory) (g : Nat), WP { m with frame := { m.frame with
      stack := rest, memory := mem, gasLeft := g, pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  have hdec : Opcode.decode m.ctx.fork 0x37 = .calldatacopy := by cases m.ctx.fork <;> rfl
  by_cases hg : Gas.veryLow + Gas.copyCost z.toNat + (Gas.extendMemory m.frame.memory.size
      [(x.toNat, z.toNat)]).cost ≤ m.frame.gasLeft
  · have hg' := Nat.not_lt.mpr hg
    have : ∃ mem, step m = .running { m with frame := { m.frame with
        stack := rest, memory := mem, gasLeft := m.frame.gasLeft - (Gas.veryLow +
        Gas.copyCost z.toNat + (Gas.extendMemory m.frame.memory.size [(x.toNat, z.toNat)]).cost),
        pc := m.frame.pc + 1 } } := by
      by_cases hs : z.toNat = 0
      · refine ⟨m.frame.memory.expand x.toNat z.toNat, ?_⟩
        rw [step_eq_of_code hcode, hdec]
        simp only [exec, copyToMemory, popNat, pop, charge, advance, getFrame, modifyFrame,
          StateT.run_bind, hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify,
          pure_bind, ite_false, ite_true, memoryExpansion, expandMemory, List.foldl, writeMemory,
          size_readBytes]
        rw [ite_eq_left hs]
        rfl
      · refine ⟨(m.frame.memory.expand x.toNat z.toNat).write x.toNat
          (readBytes m.frame.msg.data y.toNat z.toNat), ?_⟩
        rw [step_eq_of_code hcode, hdec]
        simp only [exec, copyToMemory, popNat, pop, charge, advance, getFrame, modifyFrame,
          StateT.run_bind, hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify,
          pure_bind, ite_false, ite_true, memoryExpansion, expandMemory, List.foldl, writeMemory,
          size_readBytes, hs]
        rfl
    obtain ⟨mem, h⟩ := this
    exact WP.of_step h ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ (hrec _ _)
  · have hg' := Nat.lt_of_not_le hg
    refine wp_fail_of_error (e := .outOfGas) hsnap hcode ?_
    rw [hdec]
    simp only [exec, copyToMemory, popNat, pop, charge, advance, getFrame, modifyFrame,
      StateT.run_bind, hstk, hg', StateT.run_get, StateT.run_pure, StateT.run_modify, pure_bind,
      ite_true, memoryExpansion, expandMemory, List.foldl, writeMemory]
    rfl

/-- `Live`: the `initialized` byte is `1` and the `initializing` byte `0`. -/
theorem live_bytes {x : Word} (h : x &&& 65535#256 = 1#256) :
    x &&& 255#256 = 1#256 ∧ Word.div x 256#256 &&& 255#256 = 0#256 := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at h'
  rw [show (65535 : Nat) % 2 ^ 256 = 2 ^ 16 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h'
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [show (255 : Nat) % 2 ^ 256 = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    norm_num at h' ⊢
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [Word.div, BitVec.toNat_and, BitVec.toNat_udiv, BitVec.toNat_ofNat]
    rw [show (255 : Nat) % 2 ^ 256 = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    norm_num at h' ⊢
    omega

theorem iszero_size {n : Nat} (h0 : n ≠ 0) (h1 : n < 2 ^ 256) : Word.iszero (ofNat n) = 0 := by
  apply EvmLogic.Solidity.iszero_of_ne
  intro h
  have := congrArg BitVec.toNat h
  simp only [ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1] at this
  exact h0 (by simpa using this)

set_option maxHeartbeats 0 in
/-- **`initialize(address)` reverts on an initialized instance with code**, at any gas. -/
theorem init_addr_low (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xc4d66de8) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hL : Live m.world m.frame.msg.currentTarget)
    (hc0 : (m.world.code m.frame.msg.currentTarget).size ≠ 0)
    (hc1 : (m.world.code m.frame.msg.currentTarget).size < 2 ^ 256) :
    Halts m (fun _ o => Fails o) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  obtain ⟨hB1, hB0⟩ := live_bytes hL
  rw [BitVec.and_comm] at hB1 hB0
  have hcz := iszero_size hc0 hc1
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps stop_at [5454] [hsel', hz, Abi.shr_calldataload_zero, and_mask_lit, mask_lit_and,
    hB0, hB1]
  refine wp_extcodesize hF (by pcode_fact) rfl fun _ _ => ?_
  dsimp only
  hwp_steps [hsel', hz, Abi.shr_calldataload_zero, and_mask_lit, mask_lit_and, hB0, hB1,
    Word.toAddress_ofAddress, hcz]

set_option maxHeartbeats 0 in
/-- **`initialize(string,string,uint8)` reverts on an initialized instance with code**, at any
gas: whatever the decoder copies into memory, the modifier reverts. -/
theorem init_strings_low (m : Machine) (hf : Fresh AMPL.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x1624f6c6) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hL : Live m.world m.frame.msg.currentTarget)
    (hc0 : (m.world.code m.frame.msg.currentTarget).size ≠ 0)
    (hc1 : (m.world.code m.frame.msg.currentTarget).size < 2 ^ 256) :
    Halts m (fun _ o => Fails o) := by
  have hsel' := Dispatch.selector_eq hsel
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  obtain ⟨hB1, hB0⟩ := live_bytes hL
  rw [BitVec.and_comm] at hB1 hB0
  have hcz := iszero_size hc0 hc1
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps stop_at [811] [hsel', hz, Abi.shr_calldataload_zero, hB0, hB1]
  all_goals refine wp_calldatacopy hF (by pcode_fact) rfl fun _ _ => ?_
  all_goals dsimp only
  all_goals hwp_steps stop_at [946] [hsel', hz, Abi.shr_calldataload_zero, hB0, hB1]
  all_goals refine wp_calldatacopy hF (by pcode_fact) rfl fun _ _ => ?_
  all_goals dsimp only
  all_goals hwp_steps stop_at [5454] [hsel', hz, Abi.shr_calldataload_zero, hB0, hB1]
  all_goals refine wp_extcodesize hF (by pcode_fact) rfl fun _ _ => ?_
  all_goals dsimp only
  all_goals hwp_steps [hsel', hz, Abi.shr_calldataload_zero, hB0, hB1,
    Word.toAddress_ofAddress, hcz]

end Verified.WeirdERC20.AMPL.Spec.Malformed
