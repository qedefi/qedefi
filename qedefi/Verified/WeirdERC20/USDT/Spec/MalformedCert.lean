import Verified.WeirdERC20.USDT.Spec.MalformedCode
import Verified.WeirdERC20.Common.DataLockstep
import Verified.Common.Malformed.Region
import EvmLogic.Tactic.KernelRfl

/-!
# USDT's code: two regions explored by the kernel

* **The getters and views** (`usdtGetters`): from the dispatch targets of the sixteen getters
  (the selector the only word on the stack), and from the bodies of `totalSupply()`,
  `balanceOf(address)` and `allowance(address,address)` past their deprecation branch (the
  token not deprecated), every reachable instruction is pure (`usdtGetters_pure`): the
  forwarding to the upgraded token is not reached.
* **The bodies** (`usdtBodies`): from the bodies of `transfer`, `approve` and `transferFrom`
  past their modifiers, the deprecation branch and the `onlyPayloadSize` checks (the last
  calldata read), no reachable instruction reads the calldata or the gas, or starts a child
  (`usdtBodies_safe`).
-/

namespace Verified.WeirdERC20.USDT.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open EvmLogic.AbsInt Verified.WeirdERC20.USDT.Contracts Verified.Common.Malformed
open Verified.WeirdERC20.Common
open Verified.Solmate.ERC20.Spec (recorded CertT)

/-- The byte of the code at `q`, through its kernel table. -/
noncomputable def tbyte (q : Nat) : UInt8 :=
  (USDT.runtimeCode.codeTable.bytes.get USDT.runtimeCode.codeTable.depth q).getD 0

theorem tbyte_eq (q : Nat) : tbyte q = Bytes.getD USDT.runtimeCode q :=
  (EvmLogic.Program.CodeTable.getD_eq USDT.runtimeCode.codeTable_ok q).symm

/-! ## The getters -/

/-- The getters' selectors and dispatch targets. -/
def getterEntries : List (Nat × Nat) :=
  [(0x06fdde03, 0x019b), (0x0e136b19, 0x02a4), (0x26976e3f, 0x0394), (0x27e235e3, 0x03e9),
    (0x313ce567, 0x0436), (0x35390714, 0x045f), (0x3eaaf86b, 0x0488), (0x59bf1abe, 0x04c6),
    (0x5c658165, 0x0517), (0x5c975abb, 0x0583), (0x893d20e8, 0x0612), (0x8da5cb5b, 0x0667),
    (0x95d89b41, 0x06bc), (0xdd644f72, 0x086a), (0xe47d6060, 0x0893), (0xe5b5019a, 0x091d)]

/-- The views' bodies past the deprecation branch (not deprecated), with their abstract
stacks: `totalSupply`, `balanceOf`, `allowance`. -/
def viewSeeds : List (Nat × AStack) :=
  [(0x0eb4, [.top, .const 797, .top]), (0x1337, [.top, .top, .const 1511, .top]),
    (0x1c3f, [.top, .top, .top, .const 2132, .top])]

/-- The exploration seeds: each getter's dispatch target with a one-word stack. -/
def getterSeeds : List (Nat × AStack) := getterEntries.map (fun p => (p.2, [.top])) ++ viewSeeds

/-- The read-only region of the getters. -/
def usdtGetters : Tree := (regionCert USDT.runtimeCode getterSeeds 100000).getD .leaf

theorem usdtGetters_some : (regionCert USDT.runtimeCode getterSeeds 100000).isSome = true := by
  kernel_decide

theorem usdtGetters_eq : regionCert USDT.runtimeCode getterSeeds 100000 = some usdtGetters := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 usdtGetters_some
  rw [usdtGetters, ht]; rfl

set_option maxRecDepth 100000 in
theorem usdtGetters_check : (recorded usdtGetters).all (fun q => pureByte (tbyte q)) = true := by
  kernel_decide

/-- **Every instruction of the getters' region is pure.** -/
theorem usdtGetters_pure :
    ∀ q ∈ recorded usdtGetters, pureByte (Bytes.getD USDT.runtimeCode q) = true :=
  fun q hq => by
    have := List.all_eq_true.1 usdtGetters_check q hq
    rwa [tbyte_eq] at this

theorem usdtGetters_cert : CertT (fun _ => 0) (fun _ => true) USDT.runtimeCode usdtGetters :=
  (regionCert_sound usdtGetters_eq).1

theorem usdtGetters_seed {q : Nat} {s : AStack} (h : (q, s) ∈ getterSeeds) :
    InT usdtGetters q s :=
  (regionCert_sound (ρ := fun _ => 0) (t := usdtGetters) usdtGetters_eq).2 (q, s) h

/-! ## The bodies -/

/-- The body entries with their abstract stacks (the decoded arguments, the return label, the
selector). -/
def bodySeeds : List (Nat × AStack) :=
  [(0x26b6, [.top, .top, .top, .top, .top, .const 5785, .top, .top, .const 1930, .top]),
    (0x2026, [.top, .top, .top, .const 3259, .top, .top, .top, .const 674, .top]),
    (0x21c8, [.top, .top, .top, .top, .top, .top, .top, .const 4247, .top, .top, .top,
      .const 914, .top])]

/-- The region of the bodies. -/
def usdtBodies : Tree := (regionCert USDT.runtimeCode bodySeeds 100000).getD .leaf

theorem usdtBodies_some : (regionCert USDT.runtimeCode bodySeeds 100000).isSome = true := by
  kernel_decide

theorem usdtBodies_eq : regionCert USDT.runtimeCode bodySeeds 100000 = some usdtBodies := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 usdtBodies_some
  rw [usdtBodies, ht]; rfl

set_option maxRecDepth 100000 in
theorem usdtBodies_check : (recorded usdtBodies).all (fun q => dataSafeB (tbyte q)) = true := by
  kernel_decide

/-- **No instruction of the bodies' region reads the calldata or the gas, or starts a
child.** -/
theorem usdtBodies_safe :
    ∀ q ∈ recorded usdtBodies, dataSafeB (Bytes.getD USDT.runtimeCode q) = true :=
  fun q hq => by
    have := List.all_eq_true.1 usdtBodies_check q hq
    rwa [tbyte_eq] at this

theorem usdtBodies_cert : CertT (fun _ => 0) (fun _ => true) USDT.runtimeCode usdtBodies :=
  (regionCert_sound usdtBodies_eq).1

theorem usdtBodies_seed {q : Nat} {s : AStack} (h : (q, s) ∈ bodySeeds) : InT usdtBodies q s :=
  (regionCert_sound (ρ := fun _ => 0) (t := usdtBodies) usdtBodies_eq).2 (q, s) h

end Verified.WeirdERC20.USDT.Spec.Malformed
