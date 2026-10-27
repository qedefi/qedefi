import Verified.WETH9.Solvency
import Verified.WeirdERC20.Common.DataLockstep
import Verified.Common.Malformed.Region
import EvmLogic.Tactic.KernelRfl

/-!
# WETH9's code: two regions explored by the kernel

* **The getters** (`wethGetters`): from the dispatch targets of `name()`, `totalSupply()`,
  `decimals()`, `balanceOf(address)`, `symbol()` and `allowance(address,address)` (the selector
  the only word on the stack), every reachable instruction is pure (`wethGetters_pure`).
* **The bodies** (`wethBodies`): from the body entries of `approve`, `transferFrom` and
  `transfer` (after the dispatcher has decoded the arguments), no reachable instruction reads
  the calldata or the gas, or starts a child (`wethBodies_safe`).
-/

namespace Verified.WETH9.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open EvmLogic.AbsInt Verified.WETH9.Contracts Verified.Common.Malformed
open Verified.WeirdERC20.Common
open Verified.Solmate.ERC20.Spec (recorded CertT)

/-- The byte of the code at `q`, through its kernel table. -/
noncomputable def tbyte (q : Nat) : UInt8 :=
  (WETH9.runtimeCode.codeTable.bytes.get WETH9.runtimeCode.codeTable.depth q).getD 0

theorem tbyte_eq (q : Nat) : tbyte q = Bytes.getD WETH9.runtimeCode q :=
  (EvmLogic.Program.CodeTable.getD_eq WETH9.runtimeCode.codeTable_ok q).symm

/-! ## The getters -/

/-- The getters' selectors and dispatch targets. -/
def getterEntries : List (Nat × Nat) :=
  [(0x06fdde03, 0x00b9), (0x18160ddd, 0x01a1), (0x313ce567, 0x0266), (0x70a08231, 0x0295),
    (0x95d89b41, 0x02e2), (0xdd62ed3e, 0x03d4)]

/-- The exploration seeds: each getter's dispatch target with a one-word stack. -/
def getterSeeds : List (Nat × AStack) := getterEntries.map fun p => (p.2, [.top])

/-- The read-only region of the getters. -/
def wethGetters : Tree := (regionCert WETH9.runtimeCode getterSeeds 100000).getD .leaf

theorem wethGetters_some : (regionCert WETH9.runtimeCode getterSeeds 100000).isSome = true := by
  kernel_decide

theorem wethGetters_eq : regionCert WETH9.runtimeCode getterSeeds 100000 = some wethGetters := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 wethGetters_some
  rw [wethGetters, ht]; rfl

set_option maxRecDepth 100000 in
theorem wethGetters_check : (recorded wethGetters).all (fun q => pureByte (tbyte q)) = true := by
  kernel_decide

/-- **Every instruction of the getters' region is pure.** -/
theorem wethGetters_pure :
    ∀ q ∈ recorded wethGetters, pureByte (Bytes.getD WETH9.runtimeCode q) = true :=
  fun q hq => by
    have := List.all_eq_true.1 wethGetters_check q hq
    rwa [tbyte_eq] at this

theorem wethGetters_cert : CertT (fun _ => 0) (fun _ => true) WETH9.runtimeCode wethGetters :=
  (regionCert_sound wethGetters_eq).1

theorem wethGetters_seed {q : Nat} (h : (q, [AVal.top]) ∈ getterSeeds) :
    InT wethGetters q [.top] :=
  (regionCert_sound (ρ := fun _ => 0) (t := wethGetters) wethGetters_eq).2 (q, [.top]) h

/-! ## The bodies -/

/-- The body entries with their abstract stacks (the decoded arguments, the return label, the
selector). -/
def bodySeeds : List (Nat × AStack) :=
  [(0x057b, [.top, .top, .const 391, .top]), (0x068c, [.top, .top, .top, .const 553, .top]),
    (0x0bce, [.top, .top, .const 944, .top])]

/-- The region of the bodies. -/
def wethBodies : Tree := (regionCert WETH9.runtimeCode bodySeeds 100000).getD .leaf

theorem wethBodies_some : (regionCert WETH9.runtimeCode bodySeeds 100000).isSome = true := by
  kernel_decide

theorem wethBodies_eq : regionCert WETH9.runtimeCode bodySeeds 100000 = some wethBodies := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 wethBodies_some
  rw [wethBodies, ht]; rfl

set_option maxRecDepth 100000 in
theorem wethBodies_check : (recorded wethBodies).all (fun q => dataSafeB (tbyte q)) = true := by
  kernel_decide

/-- **No instruction of the bodies' region reads the calldata or the gas, or starts a
child.** -/
theorem wethBodies_safe :
    ∀ q ∈ recorded wethBodies, dataSafeB (Bytes.getD WETH9.runtimeCode q) = true :=
  fun q hq => by
    have := List.all_eq_true.1 wethBodies_check q hq
    rwa [tbyte_eq] at this

theorem wethBodies_cert : CertT (fun _ => 0) (fun _ => true) WETH9.runtimeCode wethBodies :=
  (regionCert_sound wethBodies_eq).1

theorem wethBodies_seed {q : Nat} {s : AStack} (h : (q, s) ∈ bodySeeds) : InT wethBodies q s :=
  (regionCert_sound (ρ := fun _ => 0) (t := wethBodies) wethBodies_eq).2 (q, s) h

end Verified.WETH9.Spec.Malformed
