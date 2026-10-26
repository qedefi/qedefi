import Verified.OpenZeppelin.ERC20.Spec.Dispatch
import Verified.Common.Malformed.Region
import EvmLogic.Tactic.KernelRfl

/-!
# `ERC20Mock`'s getters change nothing, with any calldata and any gas

The six getters of the deployed `ERC20Mock` (`name()`, `symbol()`, `decimals()`,
`balanceOf(a)`, `allowance(o, sp)`, `totalSupply()`) form a read-only region of the code from
their entries (`ozGetters`, explored by the kernel, `ozGetters_pure`): their argument decoders,
the storage string copy of `name`/`symbol` and the return encoders only read. So a frame
dispatched to a getter ends with its world, transient storage and logs unchanged, whatever
its arguments (`getter_halts`).
-/

namespace Verified.OpenZeppelin.ERC20.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open EvmLogic.AbsInt Verified.OpenZeppelin.Contracts Verified.Common.Malformed
open Verified.Solmate.ERC20 (lt_size_four)
open Verified.Solmate.ERC20.Spec (recorded)

/-- The getters' selectors and entry pcs (the selector is the only word on the stack). -/
def getterEntries : List (Nat × Nat) :=
  [(0x06fdde03, 170), (0x95d89b41, 348), (0x313ce567, 272), (0x70a08231, 308),
    (0xdd62ed3e, 394), (0x18160ddd, 235)]

/-- The exploration seeds: each getter entry with a one-word stack. -/
def getterSeeds : List (Nat × AStack) := getterEntries.map fun p => (p.2, [.top])

/-- The read-only region of the getters. -/
def ozGetters : Tree := (regionCert OzAsset.runtimeCode getterSeeds 100000).getD .leaf

theorem ozGetters_some : (regionCert OzAsset.runtimeCode getterSeeds 100000).isSome = true := by
  kernel_decide

theorem ozGetters_eq : regionCert OzAsset.runtimeCode getterSeeds 100000 = some ozGetters := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 ozGetters_some
  rw [ozGetters, ht]; rfl

/-- The byte of the code at `q`, through its kernel table. -/
noncomputable def tbyte (q : Nat) : UInt8 :=
  (OzAsset.runtimeCode.codeTable.bytes.get OzAsset.runtimeCode.codeTable.depth q).getD 0

theorem tbyte_eq (q : Nat) : tbyte q = Bytes.getD OzAsset.runtimeCode q :=
  (EvmLogic.Program.CodeTable.getD_eq OzAsset.runtimeCode.codeTable_ok q).symm

set_option maxRecDepth 100000 in
theorem ozGetters_check : (recorded ozGetters).all (fun q => pureByte (tbyte q)) = true := by
  kernel_decide

/-- **Every instruction of the getters' region is pure.** -/
theorem ozGetters_pure : ∀ q ∈ recorded ozGetters, pureByte (Bytes.getD OzAsset.runtimeCode q) = true :=
  fun q hq => by
    have := List.all_eq_true.1 ozGetters_check q hq
    rwa [tbyte_eq] at this

theorem ozGetters_cert : Verified.Solmate.ERC20.Spec.CertT (fun _ => 0) (fun _ => true)
    OzAsset.runtimeCode ozGetters :=
  (regionCert_sound ozGetters_eq).1

theorem ozGetters_seed {q : Nat} (h : (q, [AVal.top]) ∈ getterSeeds) : InT ozGetters q [.top] :=
  (regionCert_sound (ρ := fun _ => 0) (t := ozGetters) ozGetters_eq).2 (q, [.top]) h

set_option maxHeartbeats 0 in
/-- **A getter changes nothing**, with any arguments, in any fresh frame without value and
with at least 1000 gas. -/
theorem getter_halts {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (m : Machine)
    (hf : Fresh OzAsset.runtimeCode m) (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = sel) (hsize : 4 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hg : 1000 ≤ m.frame.gasLeft) :
    Halts m (fun mf _ => Unchanged m mf) := by
  apply WP.halts_of_false
  have hin : InT ozGetters q [.top] :=
    ozGetters_seed (List.mem_map.2 ⟨(sel, q), hge, rfl⟩)
  have hlt := lt_size_four (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  simp only [getterEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hge
  rcases hge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    fresh_intro
    pwp_run_to 170, 348, 272, 308, 394, 235 [hval, hsel', hlt, Abi.shr_calldataload_zero]
    exact WP.halts ((halts_pure ozGetters_cert ozGetters_pure _ rfl
      (inCert_top hin rfl rfl)).mono fun _ _ _ h => h)

end Verified.OpenZeppelin.ERC20.Spec.Malformed
