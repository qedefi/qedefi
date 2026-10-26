import Verified.WeirdERC20.AMPL.Spec.Views
import Verified.WeirdERC20.Common.DataLockstep
import Verified.Common.Malformed.Region
import EvmLogic.Tactic.KernelRfl

/-!
# AMPL's code: two regions explored by the kernel

* **The getters** (`amplGetters`): from the dispatch targets of the sixteen getters (`name`,
  `symbol`, `decimals`, `totalSupply`, `scaledTotalSupply`, `balanceOf`, `scaledBalanceOf`,
  `allowance`, `nonces`, `owner`, `isOwner`, `monetaryPolicy`, `DOMAIN_SEPARATOR`,
  `EIP712_DOMAIN`, `EIP712_REVISION`, `PERMIT_TYPEHASH`), with the selector the only word on the
  stack, every reachable instruction is pure (`amplGetters_pure`).
* **The bodies** (`amplBodies`): from the body entries of the entry points taking an `address`
  (`transfer`, `approve`, `transferFrom`, `increaseAllowance`, `decreaseAllowance`,
  `transferAll`, `transferAllFrom`, `setMonetaryPolicy`, `transferOwnership`), after the
  dispatcher has decoded and masked the arguments, no reachable instruction reads the calldata
  or the gas, or starts a child (`amplBodies_safe`).
-/

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open EvmLogic.AbsInt Verified.WeirdERC20.AMPL.Contracts Verified.Common.Malformed
open Verified.WeirdERC20.Common
open Verified.Solmate.ERC20.Spec (recorded CertT)

/-- The byte of the code at `q`, through its kernel table. -/
noncomputable def tbyte (q : Nat) : UInt8 :=
  (AMPL.runtimeCode.codeTable.bytes.get AMPL.runtimeCode.codeTable.depth q).getD 0

theorem tbyte_eq (q : Nat) : tbyte q = Bytes.getD AMPL.runtimeCode q :=
  (EvmLogic.Program.CodeTable.getD_eq AMPL.runtimeCode.codeTable_ok q).symm

/-! ## The getters -/

/-- The getters' selectors and dispatch targets. -/
def getterEntries : List (Nat × Nat) :=
  [(0x06fdde03, 479), (0x18160ddd, 976), (0x1da24f3e, 1002), (0x30adf81f, 1094),
    (0x313ce567, 1102), (0x3644e515, 1132), (0x70a08231, 1184), (0x78160376, 1230),
    (0x7ecebe00, 1273), (0x8da5cb5b, 1395), (0x8e27d7d7, 1431), (0x8f32d59b, 1439),
    (0x95d89b41, 1447), (0xb1bf962d, 1581), (0xdd62ed3e, 1708), (0xe1b11da4, 1754)]

/-- The exploration seeds: each getter's dispatch target with a one-word stack. -/
def getterSeeds : List (Nat × AStack) := getterEntries.map fun p => (p.2, [.top])

/-- The read-only region of the getters. -/
def amplGetters : Tree := (regionCert AMPL.runtimeCode getterSeeds 100000).getD .leaf

theorem amplGetters_some : (regionCert AMPL.runtimeCode getterSeeds 100000).isSome = true := by
  kernel_decide

theorem amplGetters_eq : regionCert AMPL.runtimeCode getterSeeds 100000 = some amplGetters := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 amplGetters_some
  rw [amplGetters, ht]; rfl

set_option maxRecDepth 100000 in
theorem amplGetters_check : (recorded amplGetters).all (fun q => pureByte (tbyte q)) = true := by
  kernel_decide

/-- **Every instruction of the getters' region is pure.** -/
theorem amplGetters_pure :
    ∀ q ∈ recorded amplGetters, pureByte (Bytes.getD AMPL.runtimeCode q) = true :=
  fun q hq => by
    have := List.all_eq_true.1 amplGetters_check q hq
    rwa [tbyte_eq] at this

theorem amplGetters_cert : CertT (fun _ => 0) (fun _ => true) AMPL.runtimeCode amplGetters :=
  (regionCert_sound amplGetters_eq).1

theorem amplGetters_seed {q : Nat} (h : (q, [AVal.top]) ∈ getterSeeds) :
    InT amplGetters q [.top] :=
  (regionCert_sound (ρ := fun _ => 0) (t := amplGetters) amplGetters_eq).2 (q, [.top]) h

/-! ## The bodies -/

/-- The body entries with their abstract stacks (the decoded arguments, the return label, the
selector). -/
def bodySeeds : List (Nat × AStack) :=
  [(4291, [.top, .top, .const 648, .top]), (1950, [.top, .top, .const 648, .top]),
    (2819, [.top, .top, .const 648, .top]), (4145, [.top, .top, .const 648, .top]),
    (3411, [.top, .top, .const 648, .top]), (2291, [.top, .top, .top, .const 648, .top]),
    (3943, [.top, .const 648, .top]), (3698, [.top, .const 974, .top]),
    (5423, [.top, .const 974, .top])]

/-- The region of the bodies. -/
def amplBodies : Tree := (regionCert AMPL.runtimeCode bodySeeds 100000).getD .leaf

theorem amplBodies_some : (regionCert AMPL.runtimeCode bodySeeds 100000).isSome = true := by
  kernel_decide

theorem amplBodies_eq : regionCert AMPL.runtimeCode bodySeeds 100000 = some amplBodies := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 amplBodies_some
  rw [amplBodies, ht]; rfl

set_option maxRecDepth 100000 in
theorem amplBodies_check : (recorded amplBodies).all (fun q => dataSafeB (tbyte q)) = true := by
  kernel_decide

/-- **No instruction of the bodies' region reads the calldata or the gas, or starts a
child.** -/
theorem amplBodies_safe :
    ∀ q ∈ recorded amplBodies, dataSafeB (Bytes.getD AMPL.runtimeCode q) = true :=
  fun q hq => by
    have := List.all_eq_true.1 amplBodies_check q hq
    rwa [tbyte_eq] at this

theorem amplBodies_cert : CertT (fun _ => 0) (fun _ => true) AMPL.runtimeCode amplBodies :=
  (regionCert_sound amplBodies_eq).1

theorem amplBodies_seed {q : Nat} {s : AStack} (h : (q, s) ∈ bodySeeds) : InT amplBodies q s :=
  (regionCert_sound (ρ := fun _ => 0) (t := amplBodies) amplBodies_eq).2 (q, s) h

end Verified.WeirdERC20.AMPL.Spec.Malformed
