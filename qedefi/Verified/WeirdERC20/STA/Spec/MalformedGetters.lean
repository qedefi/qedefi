import Verified.WeirdERC20.STA.Spec.MalformedCert
import Verified.WeirdERC20.STA.Spec.MalformedPrefix

/-!
# Statera's getters and `destroy` with any calldata, at any gas

* `getter_halts`: a frame dispatched to one of the eight getters (`name`, `cut`,
  `totalSupply`, `decimals`, `balanceOf`, `symbol`, `basePercent`, `allowance`) fails or
  changes nothing, with any value, any arguments and any gas: the dispatcher reaches the
  getter's dispatch target without writing anything (or runs out of gas), and from there the
  read-only region `staGetters` ends with nothing changed (`halts_pure`).
* `destroy_dirty`: `destroy(uint256)` fails, or the frame has no value and a whole argument
  word (then its calldata is what `staOps` decodes).
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.STA.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open QEDefi.ERC20 QEDefi.ERC20.Spec Verified.WeirdERC20.STA.Contracts
open Verified.WeirdERC20.STA.Spec Verified.WeirdERC20.Common Verified.Solady.Spec.AnyGas
open Verified.Common.Malformed EvmLogic.AbsInt

/-- The dispatcher's run to a getter's dispatch target leaves the world, the transient storage
and the logs, with the selector as the only word on the stack. -/
def AtGetter (m : Machine) (q : Nat) (sel : Nat) (s : Machine) : Prop :=
  s.frame.pc = q ∧ s.frame.stack = [BitVec.ofNat 256 sel] ∧ s.frame.code = STA.runtimeCode ∧
    Unchanged m s

set_option maxHeartbeats 0 in
/-- The dispatcher to a getter, at any gas. -/
theorem getter_dispatch {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (m : Machine)
    (hf : Fresh STA.runtimeCode m) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (AtGetter m q sel) (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  simp only [getterEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hge
  rcases hge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    solady_fresh_intro
    hwp_steps stop_at [0x00df, 0x0169, 0x01f2, 0x024a, 0x02b0, 0x02e3, 0x035b, 0x0370] [hsel', hz]
    exact WP.ret ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **A getter fails or changes nothing**, with any value, arguments and gas. -/
theorem getter_halts {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (m : Machine)
    (hf : Fresh STA.runtimeCode m) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (h4 : 4 ≤ m.frame.msg.data.size) (hsz : m.frame.msg.data.size < 2 ^ 64) :
    Halts m (fun mf o => Fails o ∨ Unchanged m mf) := by
  have hin : InT staGetters q [.top] :=
    staGetters_seed (List.mem_map.2 ⟨(sel, q), hge, rfl⟩)
  rcases getter_dispatch hge m hf hsel h4 hsz with ⟨s, hst, hpc, hs, hcode, h1, h2, h3⟩ | h
  · refine Halts.of_steps hst ((halts_pure staGetters_cert staGetters_pure s hcode
      (inCert_top hin hpc hs)).mono fun mf _ _ ⟨g1, g2, g3⟩ => .inr ?_)
    exact ⟨g1.trans h1, g2.trans h2, g3.trans h3⟩
  · exact h.mono fun _ _ _ h => .inl h

set_option maxHeartbeats 0 in
/-- `destroy(uint256)` fails, or has no value and a whole argument word. -/
theorem destroy_dirty (m : Machine) (hf : Fresh STA.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x9d118770) (h4 : 4 ≤ m.frame.msg.data.size)
    (hsz : m.frame.msg.data.size < 2 ^ 64) :
    WP m (fun _ => m.frame.msg.value = 0 ∧ 36 ≤ m.frame.msg.data.size)
      (fun _ o => Fails o) := by
  have hsel' := div_selector m.frame.msg.data
  rw [hsel] at hsel'
  have hz := Verified.Solady.Spec.lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hF : FailH (fun (_ : Machine) (o : Outcome) => Fails o) :=
    ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  solady_fresh_intro
  hwp_steps stop_at [0x0882] [hsel', hz]
  exact WP.ret ⟨Verified.Solady.Spec.eq_zero_of_iszero_ne ‹_›,
    size_of_iszero_lt (k := 32) h4 hsz (by norm_num) ‹_›⟩

end Verified.WeirdERC20.STA.Spec.Malformed
