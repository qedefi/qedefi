import Verified.Solady.Spec.Common
import Verified.Common.Malformed.Region
import Verified.Common.Malformed.Post
import Verified.Solmate.ERC4626.UnknownSelectors
import EvmLogic.Tactic.KernelRfl

/-!
# `SoladyToken` at any gas: the code-level facts `MalformedSpec` needs

Solady's `ERC20` functions are `public` Solidity functions: their arguments go through solc's
ABI decoder, which reverts on short calldata and on a dirty `address` (or `uint8`) word before
Solady's assembly body runs (pcs 1930–1996 and 2087–2195 of the compiled `SoladyToken`). So
malformed calldata is rejected exactly as in a token written in Solidity.

All runs here are at **any gas** (`hwp_steps`): a frame fails or ends as stated.

* `getter_low`: a getter (`name`, `symbol`, `decimals`, `DOMAIN_SEPARATOR`, `nonces`,
  `balanceOf`, `allowance`, `totalSupply`) changes nothing, whatever its arguments (the
  read-only region `sdyGetters` from its entry);
* `short_low`, `dirty0_low`, `dirty1_low`, `dirtyV_low`: malformed calldata of a writing entry
  point (`transfer`, `approve`, `transferFrom`, `mint`, `burn`, `permit`) fails;
* `value_low`: a frame with value fails (no function is payable).
-/

namespace Verified.Solady.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open EvmLogic.AbsInt Verified.Solady.Contracts Verified.Solady.Spec Verified.Solady.Spec.AnyGas
open Verified.Common.Malformed
open Verified.Solmate.ERC20.Spec (recorded)
open Verified.Solmate.ERC4626 (CleanAddr cleanAddr_lit eq_and_mask_zero iszero_slt_short)

/-- The frame failed. -/
theorem failH_fails : FailH fun (_ : Machine) (o : Outcome) => QEDefi.ERC20.Spec.Fails o :=
  ⟨fun _ _ => trivial, fun _ _ => trivial⟩

/-! ## The getters' region -/

/-- The getters' selectors and entry pcs. -/
def getterEntries : List (Nat × Nat) :=
  [(0x06fdde03, 233), (0x18160ddd, 298), (0x313ce567, 343), (0x3644e515, 358),
    (0x70a08231, 387), (0x7ecebe00, 424), (0x95d89b41, 461), (0xdd62ed3e, 550)]

/-- The exploration seeds: each getter entry with a one-word stack. -/
def getterSeeds : List (Nat × AStack) := getterEntries.map fun p => (p.2, [.top])

/-- The read-only region of the getters. -/
def sdyGetters : Tree := (regionCert SoladyToken.runtimeCode getterSeeds 100000).getD .leaf

theorem sdyGetters_some :
    (regionCert SoladyToken.runtimeCode getterSeeds 100000).isSome = true := by
  kernel_decide

theorem sdyGetters_eq :
    regionCert SoladyToken.runtimeCode getterSeeds 100000 = some sdyGetters := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 sdyGetters_some
  rw [sdyGetters, ht]; rfl

/-- The byte of the code at `q`, through its kernel table. -/
noncomputable def tbyte (q : Nat) : UInt8 :=
  (SoladyToken.runtimeCode.codeTable.bytes.get SoladyToken.runtimeCode.codeTable.depth q).getD 0

theorem tbyte_eq (q : Nat) : tbyte q = Bytes.getD SoladyToken.runtimeCode q :=
  (EvmLogic.Program.CodeTable.getD_eq SoladyToken.runtimeCode.codeTable_ok q).symm

set_option maxRecDepth 100000 in
theorem sdyGetters_check : (recorded sdyGetters).all (fun q => pureByte (tbyte q)) = true := by
  kernel_decide

/-- **Every instruction of the getters' region is pure.** -/
theorem sdyGetters_pure :
    ∀ q ∈ recorded sdyGetters, pureByte (Bytes.getD SoladyToken.runtimeCode q) = true :=
  fun q hq => by
    have := List.all_eq_true.1 sdyGetters_check q hq
    rwa [tbyte_eq] at this

theorem sdyGetters_cert : Verified.Solmate.ERC20.Spec.CertT (fun _ => 0) (fun _ => true)
    SoladyToken.runtimeCode sdyGetters :=
  (regionCert_sound sdyGetters_eq).1

theorem sdyGetters_seed {q : Nat} (h : (q, [AVal.top]) ∈ getterSeeds) :
    InT sdyGetters q [.top] :=
  (regionCert_sound (ρ := fun _ => 0) (t := sdyGetters) sdyGetters_eq).2 (q, [.top]) h

set_option maxHeartbeats 0 in
/-- **A getter fails or changes nothing**, at any gas, with any arguments and value. -/
theorem getter_low {sel q : Nat} (hge : (sel, q) ∈ getterEntries) (m : Machine)
    (hf : Fresh SoladyToken.runtimeCode m) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64) :
    Halts m (fun mf o => QEDefi.ERC20.Spec.Fails o ∨ Unchanged m mf) := by
  have hF : FailH fun (mf : Machine) (o : Outcome) => QEDefi.ERC20.Spec.Fails o ∨ Unchanged m mf :=
    ⟨fun _ _ => .inl trivial, fun _ _ => .inl trivial⟩
  have hin : InT sdyGetters q [.top] :=
    sdyGetters_seed (List.mem_map.2 ⟨(sel, q), hge, rfl⟩)
  have hlt := lt_size_four' (n := m.frame.msg.data.size) hsize (by omega)
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  simp only [getterEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hge
  rcases hge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    solady_fresh_intro
    hwp_steps stop_at [233, 298, 343, 358, 387, 424, 461, 550] [hlt, hsel',
      Abi.shr_calldataload_zero]
    exact WP.halts ((halts_pure sdyGetters_cert sdyGetters_pure _ rfl
      (inCert_top hin rfl rfl)).mono fun _ _ _ h => .inr h)

/-! ## Malformed arguments fail -/

/-- The writing entry points with their argument sizes (bytes after the selector). -/
def writeShapes : List (Nat × Nat) :=
  [(0xa9059cbb, 64), (0x095ea7b3, 64), (0x40c10f19, 64), (0x9dc29fac, 64), (0x23b872dd, 96),
    (0xd505accf, 224)]

set_option maxHeartbeats 0 in
/-- **A frame with value fails** (no function is payable), at any gas. -/
theorem value_low (m : Machine) (hf : Fresh SoladyToken.runtimeCode m)
    (hval : m.frame.msg.value ≠ 0) :
    Halts m (fun _ o => QEDefi.ERC20.Spec.Fails o) := by
  have hF := failH_fails
  have hz := iszero_of_ne hval
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hz]

set_option maxHeartbeats 0 in
/-- **Too few argument words fail**, at any gas. -/
theorem short_low {sel n : Nat} (hsh : (sel, n) ∈ writeShapes) (m : Machine)
    (hf : Fresh SoladyToken.runtimeCode m) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (hsize : 4 ≤ m.frame.msg.data.size) (hshort : m.frame.msg.data.size < 4 + n) :
    Halts m (fun _ o => QEDefi.ERC20.Spec.Fails o) := by
  have hF := failH_fails
  have hsel' := Dispatch.selector_eq hsel
  apply WP.halts_of_false
  simp only [writeShapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hsh
  rcases hsh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    have hlt := lt_size_four' (n := m.frame.msg.data.size) hsize (by omega)
    have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 _))
        = 0 := iszero_slt_short hsize hshort (by decide)
    solady_fresh_intro
    hwp_steps [hsel', hlt, Abi.shr_calldataload_zero, hok]

set_option maxHeartbeats 0 in
/-- **A dirty first `address` argument fails**, at any gas. -/
theorem dirty0_low {sel n : Nat} (hsh : (sel, n) ∈ writeShapes) (m : Machine)
    (hf : Fresh SoladyToken.runtimeCode m) (hsel : Abi.selectorOf m.frame.msg.data = sel)
    (hsize : 4 + n ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : ¬ CleanAddr m.frame.msg.data 0) :
    Halts m (fun _ o => QEDefi.ERC20.Spec.Fails o) := by
  have hF := failH_fails
  have hsel' := Dispatch.selector_eq hsel
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [Verified.Solmate.ERC4626.argWord] at hd'
  apply WP.halts_of_false
  simp only [writeShapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hsh
  rcases hsh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 _))
        = 1 := iszero_slt_calldatasize hsize (by omega)
    solady_fresh_intro
    hwp_steps [hsel', hlt, Abi.shr_calldataload_zero, hok, hd', Solidity.eq_self]

set_option maxHeartbeats 0 in
/-- **A clean first and a dirty second `address` argument fail** (`transferFrom`, `permit`),
at any gas. -/
theorem dirty1_low {sel n : Nat} (hsh : (sel, n) ∈ [(0x23b872dd, 96), (0xd505accf, 224)])
    (m : Machine) (hf : Fresh SoladyToken.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = sel) (hsize : 4 + n ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hc0 : CleanAddr m.frame.msg.data 0)
    (hd : ¬ CleanAddr m.frame.msg.data 1) :
    Halts m (fun _ o => QEDefi.ERC20.Spec.Fails o) := by
  have hF := failH_fails
  have hsel' := Dispatch.selector_eq hsel
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hd' := eq_and_mask_zero hd
  simp only [Verified.Solmate.ERC4626.argWord] at hd'
  have hc0' := cleanAddr_lit hc0
  simp only [Verified.Solmate.ERC4626.argWord] at hc0'
  apply WP.halts_of_false
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hsh
  rcases hsh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 _))
        = 1 := iszero_slt_calldatasize hsize (by omega)
    solady_fresh_intro
    hwp_steps [hsel', hlt, Abi.shr_calldataload_zero, hok, hd', hc0', Solidity.eq_self]

set_option maxHeartbeats 0 in
/-- **A `permit` whose `v` word is 256 or more fails**, at any gas. -/
theorem dirtyV_low (m : Machine) (hf : Fresh SoladyToken.runtimeCode m)
    (hsel : Abi.selectorOf m.frame.msg.data = 0xd505accf) (hsize : 228 ≤ m.frame.msg.data.size)
    (hsize' : m.frame.msg.data.size < 2 ^ 64) (hc0 : CleanAddr m.frame.msg.data 0)
    (hc1 : CleanAddr m.frame.msg.data 1) (hd : ¬ CleanU8 m.frame.msg.data) :
    Halts m (fun _ o => QEDefi.ERC20.Spec.Fails o) := by
  have hF := failH_fails
  have hsel' := Dispatch.selector_eq hsel
  have hlt := lt_size_four' (n := m.frame.msg.data.size) (by omega) (by omega)
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hd' := eq_and_255_zero hd
  simp only [Verified.Solmate.ERC4626.argWord] at hd'
  have hc0' := cleanAddr_lit hc0
  simp only [Verified.Solmate.ERC4626.argWord] at hc0'
  have hc1' := cleanAddr_lit hc1
  simp only [Verified.Solmate.ERC4626.argWord] at hc1'
  apply WP.halts_of_false
  solady_fresh_intro
  hwp_steps [hsel', hlt, Abi.shr_calldataload_zero, hok, hd', hc0', hc1', Solidity.eq_self]

end Verified.Solady.Spec.Malformed
