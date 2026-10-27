import Verified.WeirdERC20.STA.Spec.Views
import Verified.WeirdERC20.Common.DataLockstep
import Verified.Common.Malformed.Region
import EvmLogic.Tactic.KernelRfl

/-!
# Statera's code: two regions explored by the kernel

* **The getters** (`staGetters`): from the dispatch targets of `name()`, `cut(uint256)`,
  `totalSupply()`, `decimals()`, `balanceOf(address)`, `symbol()`, `basePercent()` and
  `allowance(address,address)` (the selector the only word on the stack), every reachable
  instruction is pure (`staGetters_pure`): the value check, the argument decoder, the storage
  string copy and the return encoders only read.
* **The bodies** (`staBodies`): from the body entries of `transfer`, `approve`,
  `transferFrom`, `destroyFrom`, `upAllowance` and `downAllowance` (after the dispatcher has
  decoded and masked the arguments), no reachable instruction reads the calldata or the gas,
  or starts a child (`staBodies_safe`).
-/

namespace Verified.WeirdERC20.STA.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open EvmLogic.AbsInt Verified.WeirdERC20.STA.Contracts Verified.Common.Malformed
open Verified.WeirdERC20.Common
open Verified.Solmate.ERC20.Spec (recorded CertT)

/-- The byte of the code at `q`, through its kernel table. -/
noncomputable def tbyte (q : Nat) : UInt8 :=
  (STA.runtimeCode.codeTable.bytes.get STA.runtimeCode.codeTable.depth q).getD 0

theorem tbyte_eq (q : Nat) : tbyte q = Bytes.getD STA.runtimeCode q :=
  (EvmLogic.Program.CodeTable.getD_eq STA.runtimeCode.codeTable_ok q).symm

/-! ## The getters -/

/-- The getters' selectors and dispatch targets. -/
def getterEntries : List (Nat × Nat) :=
  [(0x06fdde03, 0x00df), (0x09260db7, 0x0169), (0x18160ddd, 0x01f2), (0x313ce567, 0x024a),
    (0x70a08231, 0x02b0), (0x95d89b41, 0x02e3), (0xc5ac0ded, 0x035b), (0xdd62ed3e, 0x0370)]

/-- The exploration seeds: each getter's dispatch target with a one-word stack. -/
def getterSeeds : List (Nat × AStack) := getterEntries.map fun p => (p.2, [.top])

/-- The read-only region of the getters. -/
def staGetters : Tree := (regionCert STA.runtimeCode getterSeeds 100000).getD .leaf

theorem staGetters_some : (regionCert STA.runtimeCode getterSeeds 100000).isSome = true := by
  kernel_decide

theorem staGetters_eq : regionCert STA.runtimeCode getterSeeds 100000 = some staGetters := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 staGetters_some
  rw [staGetters, ht]; rfl

set_option maxRecDepth 100000 in
theorem staGetters_check : (recorded staGetters).all (fun q => pureByte (tbyte q)) = true := by
  kernel_decide

/-- **Every instruction of the getters' region is pure.** -/
theorem staGetters_pure :
    ∀ q ∈ recorded staGetters, pureByte (Bytes.getD STA.runtimeCode q) = true :=
  fun q hq => by
    have := List.all_eq_true.1 staGetters_check q hq
    rwa [tbyte_eq] at this

theorem staGetters_cert : CertT (fun _ => 0) (fun _ => true) STA.runtimeCode staGetters :=
  (regionCert_sound staGetters_eq).1

theorem staGetters_seed {q : Nat} (h : (q, [AVal.top]) ∈ getterSeeds) :
    InT staGetters q [.top] :=
  (regionCert_sound (ρ := fun _ => 0) (t := staGetters) staGetters_eq).2 (q, [.top]) h

/-! ## The bodies -/

/-- The body entries with their abstract stacks (the decoded arguments, the return label, the
selector). -/
def bodySeeds : List (Nat × AStack) :=
  [(0x088f, [.top, .top, .const 478, .top]), (0x04fe, [.top, .top, .const 478, .top]),
    (0x0aa3, [.top, .top, .const 478, .top]), (0x09f3, [.top, .top, .const 478, .top]),
    (0x0771, [.top, .top, .const 686, .top]), (0x0583, [.top, .top, .top, .const 478, .top])]

/-- The region of the bodies. -/
def staBodies : Tree := (regionCert STA.runtimeCode bodySeeds 100000).getD .leaf

theorem staBodies_some : (regionCert STA.runtimeCode bodySeeds 100000).isSome = true := by
  kernel_decide

theorem staBodies_eq : regionCert STA.runtimeCode bodySeeds 100000 = some staBodies := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 staBodies_some
  rw [staBodies, ht]; rfl

set_option maxRecDepth 100000 in
theorem staBodies_check : (recorded staBodies).all (fun q => dataSafeB (tbyte q)) = true := by
  kernel_decide

/-- **No instruction of the bodies' region reads the calldata or the gas, or starts a
child.** -/
theorem staBodies_safe :
    ∀ q ∈ recorded staBodies, dataSafeB (Bytes.getD STA.runtimeCode q) = true :=
  fun q hq => by
    have := List.all_eq_true.1 staBodies_check q hq
    rwa [tbyte_eq] at this

theorem staBodies_cert : CertT (fun _ => 0) (fun _ => true) STA.runtimeCode staBodies :=
  (regionCert_sound staBodies_eq).1

theorem staBodies_seed {q : Nat} {s : AStack} (h : (q, s) ∈ bodySeeds) : InT staBodies q s :=
  (regionCert_sound (ρ := fun _ => 0) (t := staBodies) staBodies_eq).2 (q, s) h

end Verified.WeirdERC20.STA.Spec.Malformed
