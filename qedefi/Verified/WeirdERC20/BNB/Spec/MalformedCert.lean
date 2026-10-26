import Verified.WeirdERC20.BNB.Spec.Views
import Verified.WeirdERC20.Common.DataLockstep
import Verified.Common.Malformed.Region
import EvmLogic.Tactic.KernelRfl

/-!
# BNB's code: two regions explored by the kernel

* **The getters** (`bnbGetters`): from the dispatch targets of `name()`, `totalSupply()`,
  `decimals()`, `balanceOf(address)`, `owner()`, `symbol()`, `freezeOf(address)` and
  `allowance(address,address)` (the selector the only word on the stack), every reachable
  instruction is pure (`bnbGetters_pure`).
* **The bodies** (`bnbBodies`): from the body entries of `approve`, `transferFrom`, `burn`,
  `unfreeze`, `transfer` and `freeze` (after the dispatcher has decoded the arguments), no
  reachable instruction reads the calldata or the gas, or starts a child (`bnbBodies_safe`).
-/

namespace Verified.WeirdERC20.BNB.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open EvmLogic.AbsInt Verified.WeirdERC20.BNB.Contracts Verified.Common.Malformed
open Verified.WeirdERC20.Common
open Verified.Solmate.ERC20.Spec (recorded CertT)

/-- The byte of the code at `q`, through its kernel table. -/
noncomputable def tbyte (q : Nat) : UInt8 :=
  (BNB.runtimeCode.codeTable.bytes.get BNB.runtimeCode.codeTable.depth q).getD 0

theorem tbyte_eq (q : Nat) : tbyte q = Bytes.getD BNB.runtimeCode q :=
  (EvmLogic.Program.CodeTable.getD_eq BNB.runtimeCode.codeTable_ok q).symm

/-! ## The getters -/

/-- The getters' selectors and dispatch targets. -/
def getterEntries : List (Nat × Nat) :=
  [(0x06fdde03, 0x00e2), (0x18160ddd, 0x01cb), (0x313ce567, 0x026d), (0x70a08231, 0x0335),
    (0x8da5cb5b, 0x0382), (0x95d89b41, 0x03d7), (0xcd4217c1, 0x04a8), (0xdd62ed3e, 0x0530)]

/-- The exploration seeds: each getter's dispatch target with a one-word stack. -/
def getterSeeds : List (Nat × AStack) := getterEntries.map fun p => (p.2, [.top])

/-- The read-only region of the getters. -/
def bnbGetters : Tree := (regionCert BNB.runtimeCode getterSeeds 100000).getD .leaf

theorem bnbGetters_some : (regionCert BNB.runtimeCode getterSeeds 100000).isSome = true := by
  kernel_decide

theorem bnbGetters_eq : regionCert BNB.runtimeCode getterSeeds 100000 = some bnbGetters := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 bnbGetters_some
  rw [bnbGetters, ht]; rfl

set_option maxRecDepth 100000 in
theorem bnbGetters_check : (recorded bnbGetters).all (fun q => pureByte (tbyte q)) = true := by
  kernel_decide

/-- **Every instruction of the getters' region is pure.** -/
theorem bnbGetters_pure :
    ∀ q ∈ recorded bnbGetters, pureByte (Bytes.getD BNB.runtimeCode q) = true :=
  fun q hq => by
    have := List.all_eq_true.1 bnbGetters_check q hq
    rwa [tbyte_eq] at this

theorem bnbGetters_cert : CertT (fun _ => 0) (fun _ => true) BNB.runtimeCode bnbGetters :=
  (regionCert_sound bnbGetters_eq).1

theorem bnbGetters_seed {q : Nat} (h : (q, [AVal.top]) ∈ getterSeeds) :
    InT bnbGetters q [.top] :=
  (regionCert_sound (ρ := fun _ => 0) (t := bnbGetters) bnbGetters_eq).2 (q, [.top]) h

/-! ## The bodies -/

/-- The body entries with their abstract stacks (the decoded arguments, the return label, the
selector). -/
def bodySeeds : List (Nat × AStack) :=
  [(0x063a, [.top, .top, .const 433, .top]), (0x06dc, [.top, .top, .top, .const 595, .top]),
    (0x0bd6, [.top, .const 736, .top]), (0x0d29, [.top, .const 795, .top]),
    (0x0fd2, [.top, .top, .const 1190, .top]), (0x1278, [.top, .const 1302, .top])]

/-- The region of the bodies. -/
def bnbBodies : Tree := (regionCert BNB.runtimeCode bodySeeds 100000).getD .leaf

theorem bnbBodies_some : (regionCert BNB.runtimeCode bodySeeds 100000).isSome = true := by
  kernel_decide

theorem bnbBodies_eq : regionCert BNB.runtimeCode bodySeeds 100000 = some bnbBodies := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 bnbBodies_some
  rw [bnbBodies, ht]; rfl

set_option maxRecDepth 100000 in
theorem bnbBodies_check : (recorded bnbBodies).all (fun q => dataSafeB (tbyte q)) = true := by
  kernel_decide

/-- **No instruction of the bodies' region reads the calldata or the gas, or starts a
child.** -/
theorem bnbBodies_safe :
    ∀ q ∈ recorded bnbBodies, dataSafeB (Bytes.getD BNB.runtimeCode q) = true :=
  fun q hq => by
    have := List.all_eq_true.1 bnbBodies_check q hq
    rwa [tbyte_eq] at this

theorem bnbBodies_cert : CertT (fun _ => 0) (fun _ => true) BNB.runtimeCode bnbBodies :=
  (regionCert_sound bnbBodies_eq).1

theorem bnbBodies_seed {q : Nat} {s : AStack} (h : (q, s) ∈ bodySeeds) : InT bnbBodies q s :=
  (regionCert_sound (ρ := fun _ => 0) (t := bnbBodies) bnbBodies_eq).2 (q, s) h

end Verified.WeirdERC20.BNB.Spec.Malformed
