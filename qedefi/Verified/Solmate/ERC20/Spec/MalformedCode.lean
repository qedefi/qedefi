import Verified.Solmate.ERC20.Spec.MalformedLow
import Verified.Solmate.ERC20.Malformed
import Verified.Common.Malformed.Post

/-!
# Solmate's asset: the code-level facts `MalformedSpec` needs

In any fresh frame without value and with at least 2000 gas:

* `getter_wp`: a getter's selector reaches the getter's entry with the selector as the only
  stack word and nothing changed; from there the getter changes nothing (`getter_halts`, the
  read-only region `solGetters`);
* `permit_reaches_short`, `permit_reaches_dirty0`, `permit_reaches_dirty1`: malformed `permit`
  calldata reaches its decoder's `REVERT` (2430 short, 2273 dirty `address`);
  `permit_dirtyV_halts` / `permit_reaches_dirtyV`: a `v` word of 256 or more reverts at 2488.
-/

namespace Verified.Solmate.ERC20.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity EvmLogic.Tactic
open EvmLogic.AbsInt Verified.Solmate.Contracts Verified.Solmate.ERC20 Verified.Solmate.ERC4626
open Verified.Solmate.ERC20.Spec Verified.Common.Malformed

variable {ia : SolmateAsset.Immutables}

/-- The machine `m'` is at the getter entry `q`, described by the getters' region, with the
world, transient storage and logs of `m`. -/
def AtGetter (ia : SolmateAsset.Immutables) (m : Machine) (q : Nat) (m' : Machine) : Prop :=
  m'.frame.pc = q ∧ m'.frame.code = code ia ∧ InCert (fun _ => 0) solGetters m' ∧
    Unchanged m m'

set_option maxHeartbeats 0 in
/-- **A getter's selector reaches the getter's entry**, changing nothing. -/
theorem getter_wp {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (m : Machine)
    (hf : Fresh (code ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = sel) (hsize : 4 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hg : 1000 ≤ m.frame.gasLeft) :
    WP m (AtGetter ia m q) (fun _ _ => False) := by
  have hin : InT solGetters q [.top] :=
    solGetters_seed (List.mem_map.2 ⟨(sel, q), hge, rfl⟩)
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := assetJumpDestsAgree ia
  simp only [getterEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hge
  rcases hge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    fresh_intro
    pwp_run_to 233, 488, 340, 397, 457, 426, 553, 298 [hval, hsel', hlt,
      Abi.shr_calldataload_zero]
    exact WP.ret ⟨rfl, rfl, inCert_top hin rfl rfl, rfl, rfl, rfl⟩

/-- **A getter changes nothing**, whatever its arguments. -/
theorem getter_halts {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (m : Machine)
    (hf : Fresh (code ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = sel) (hsize : 4 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hg : 1000 ≤ m.frame.gasLeft) :
    Halts m (fun mf _ => Unchanged m mf) := by
  rcases getter_wp hge m hf hval hsel hsize hsize' hg with ⟨m', hst, _, hcode, hin, h1, h2, h3⟩ | h
  · refine Halts.of_steps hst ((halts_pure solGetters_cert solGetters_pure m' hcode hin).mono
      fun _ _ _ h => ⟨h.1.trans h1, h.2.1.trans h2, h.2.2.trans h3⟩)
  · exact h.mono fun _ _ _ h => h.elim

/-- **A getter's selector reaches a target.** -/
theorem getter_reaches {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (m : Machine)
    (hf : Fresh (code ia) m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = sel) (hsize : 4 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hg : 1000 ≤ m.frame.gasLeft) :
    ∃ mT, Steps m mT ∧ mT.frame.pc = q := by
  rcases getter_wp hge m hf hval hsel hsize hsize' hg with ⟨m', hst, hpc, -⟩ | h
  · exact ⟨m', hst, hpc⟩
  · obtain ⟨_, _, _, _, _, h⟩ := h; exact h.elim

/-- The `REVERT` of a decoder is reached. -/
theorem reached {m : Machine} {q : Nat} (h : WP m (fun m' => m'.frame.pc = q) (fun _ _ => False)) :
    ∃ mT, Steps m mT ∧ mT.frame.pc = q := by
  rcases h with ⟨mT, hs, hq⟩ | ⟨_, _, _, _, _, h⟩
  · exact ⟨mT, hs, hq⟩
  · exact h.elim

set_option maxHeartbeats 0 in
theorem permit_reaches_short (m : Machine) (hf : Fresh (code ia) m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf)
    (hsize : 4 ≤ m.frame.msg.data.size) (hshort : m.frame.msg.data.size < 228)
    (hg : 2000 ≤ m.frame.gasLeft) :
    ∃ mT, Steps m mT ∧ mT.frame.pc = 2430 := by
  apply reached
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 0 := iszero_slt_short hsize (by omega) (by decide)
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_run_to 2430 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok]
  exact WP.ret rfl

set_option maxHeartbeats 0 in
theorem permit_reaches_dirty0 (m : Machine) (hf : Fresh (code ia) m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf)
    (hsize : 228 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 0) (hg : 2000 ≤ m.frame.gasLeft) :
    ∃ mT, Steps m mT ∧ mT.frame.pc = 2273 := by
  apply reached
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_run_to 2273 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]
  exact WP.ret rfl

set_option maxHeartbeats 0 in
theorem permit_reaches_dirty1 (m : Machine) (hf : Fresh (code ia) m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf)
    (hsize : 228 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc0 : CleanAddr m.frame.msg.data 0) (hd : ¬ CleanAddr m.frame.msg.data 1)
    (hg : 2000 ≤ m.frame.gasLeft) :
    ∃ mT, Steps m mT ∧ mT.frame.pc = 2273 := by
  apply reached
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [argWord] at hd'
  have hc0' := cleanAddr_lit hc0
  simp only [argWord] at hc0'
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_run_to 2273 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', hc0', Solidity.eq_self]
  exact WP.ret rfl

set_option maxHeartbeats 0 in
theorem permit_reaches_dirtyV (m : Machine) (hf : Fresh (code ia) m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf)
    (hsize : 228 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc0 : CleanAddr m.frame.msg.data 0) (hc1 : CleanAddr m.frame.msg.data 1)
    (hd : ¬ CleanU8 m.frame.msg.data) (hg : 2000 ≤ m.frame.gasLeft) :
    ∃ mT, Steps m mT ∧ mT.frame.pc = 2488 := by
  apply reached
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_255_zero hd
  simp only [argWord] at hd'
  have hc0' := cleanAddr_lit hc0
  simp only [argWord] at hc0'
  have hc1' := cleanAddr_lit hc1
  simp only [argWord] at hc1'
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_run_to 2488 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', hc0', hc1',
    Solidity.eq_self]
  exact WP.ret rfl


set_option maxHeartbeats 0 in
theorem permit_dirtyV_halts (m : Machine) (hf : Fresh (code ia) m)
    (hval : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf)
    (hsize : 228 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hc0 : CleanAddr m.frame.msg.data 0) (hc1 : CleanAddr m.frame.msg.data 1)
    (hd : ¬ CleanU8 m.frame.msg.data) (hg : 2000 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_255_zero hd
  simp only [argWord] at hd'
  have hc0' := cleanAddr_lit hc0
  simp only [argWord] at hc0'
  have hc1' := cleanAddr_lit hc1
  simp only [argWord] at hc1'
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, hd', hc0', hc1',
    Solidity.eq_self]
  exact ⟨_, rfl⟩

end Verified.Solmate.ERC20.Spec.Malformed
