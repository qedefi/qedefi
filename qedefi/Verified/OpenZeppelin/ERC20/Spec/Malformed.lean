import Verified.OpenZeppelin.ERC20.Spec.Token
import Verified.OpenZeppelin.ERC20.Spec.MalformedRevert
import Verified.OpenZeppelin.ERC20.Spec.MalformedGetters
import Verified.Common.Malformed.Post

/-!
# `ERC20Mock` with any calldata: `MalformedSpec` and the complete spec

**`oz_malformed`**: in every frame of the deployed `ERC20Mock`, with any calldata, any value
and any gas, the frame fails, changes nothing, or is an ERC-20 call or a `mint`/`burn` the
model explains. By selector:

* short calldata or an unknown selector: `oz_fallbackSpec` (it reverts);
* any value: no function is payable, the frame reverts (`value_halts`);
* the six getters (`name`, `symbol`, `decimals`, `balanceOf`, `allowance`, `totalSupply`)
  change nothing, whatever their arguments (`getter_halts`, a read-only region);
* `transfer`, `approve`, `transferFrom`: with every argument word and clean `address` words
  the calldata is the call's ABI encoding (`encodes_transfer`, …) and `oz_callSpec` applies;
  otherwise solc's decoder reverts (`short_halts`, `dirty0_halts`, `dirty1_halts`);
* `mint`, `burn`: likewise, through `ozOps` and `oz_opSpec`.

Below the gas of those code-level summaries (1000 or 2000), a frame fails or ends as with more
gas (`lift`: `ERC20Mock` reads no gas and starts no child).

**`oz_complete`**: `ERC20Spec.Complete` (`ERC20Mock` has no `permit`).
-/

namespace Verified.OpenZeppelin.ERC20.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.Oz Verified.OpenZeppelin.Contracts
open Verified.Common.Malformed
open Verified.OpenZeppelin.ERC20.Spec
open Verified.Solmate.ERC4626 (argWord CleanAddr)

/-! ## Any gas -/

/-- **A frame that reverts from `G` gas fails at any gas** (a property `P` of its message
that does not mention the gas, as `high` keeps every other field). -/
theorem fails_any {G : Nat} {P : Message → Prop} (hP : ∀ msg g, P msg → P { msg with gas := g })
    (h : ∀ m, Fresh OzAsset.runtimeCode m → P m.frame.msg → G ≤ m.frame.gasLeft →
      Halts m (fun _ o => ∃ out, o = .revert out))
    {m : Machine} (hf : Fresh OzAsset.runtimeCode m) (hm : P m.frame.msg) :
    Halts m (fun _ o => Fails o) := by
  by_cases hg : G ≤ m.frame.gasLeft
  · exact (h m hf hm hg).mono fun _ _ _ ⟨_, ho⟩ => by rw [ho]; trivial
  have hG : m.frame.gasLeft ≤ G := by omega
  have hh := h (high G m) (fresh_high hf hG) (hP _ _ hm) (by rw [high_gasLeft hG])
  refine (lift noGasCode_oz hf (G := G) (Q := fun _ _ _ _ => False)
    (hh.mono fun _ _ _ ⟨_, ho⟩ => .inl (by rw [ho]; intro _ h; cases h))).mono
    fun _ _ _ hp => ?_
  rcases hp with hf' | ⟨_, _, hq, _⟩
  · exact fails_of_failed hf'
  · exact hq.elim

/-- **A frame that changes nothing from `G` gas fails or changes nothing at any gas.** -/
theorem unchanged_any {G : Nat} {P : Message → Prop}
    (hP : ∀ msg g, P msg → P { msg with gas := g })
    (h : ∀ m, Fresh OzAsset.runtimeCode m → P m.frame.msg → G ≤ m.frame.gasLeft →
      Halts m (fun mf _ => Unchanged m mf))
    {m : Machine} (hf : Fresh OzAsset.runtimeCode m) (hm : P m.frame.msg) :
    Halts m (fun mf o => Fails o ∨ Unchanged m mf) := by
  by_cases hg : G ≤ m.frame.gasLeft
  · exact (h m hf hm hg).mono fun _ _ _ h => .inr h
  have hG : m.frame.gasLeft ≤ G := by omega
  have hh := h (high G m) (fresh_high hf hG) (hP _ _ hm) (by rw [high_gasLeft hG])
  refine (lift noGasCode_oz hf (G := G)
    (Q := fun _ W T L => W = m.world ∧ T = m.transient ∧ L = m.frame.sub.logs)
    (hh.mono fun mf o _ hu => ?_)).mono fun _ _ _ hp => ?_
  · cases o with
    | success out => exact .inr ⟨out, rfl, hu⟩
    | revert _ => exact .inl fun _ h => by cases h
    | halt _ => exact .inl fun _ h => by cases h
  · rcases hp with hf' | ⟨_, _, hq, _⟩
    · exact .inl (fails_of_failed hf')
    · exact .inr hq

/-! ## By selector -/

section

variable {Act : Finset Address} {m : Machine}

/-- `MalPost` of `ERC20Mock`. -/
abbrev Post (Act : Finset Address) (m : Machine) : Machine → Outcome → Prop :=
  MalPost ozAbs ozModel ozOps ozOpAddrs none Act m

theorem post_value (hS : Start OzAsset.runtimeCode ozAbs ozModel Act m)
    (hv : m.frame.msg.value ≠ 0) : Halts m (Post Act m) :=
  post_fails (fails_any (G := 100) (P := fun msg => msg.value ≠ 0) (fun _ _ h => h)
    (fun m hf hv hg => value_halts m hf hv hg) hS.fresh hv)

theorem post_getter (hS : Start OzAsset.runtimeCode ozAbs ozModel Act m) {sel q : Nat}
    (hge : (sel, q) ∈ getterEntries) (hv : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = sel) (h4 : 4 ≤ m.frame.msg.data.size) :
    Halts m (Post Act m) :=
  (unchanged_any (G := 1000) (P := fun msg => msg.value = 0 ∧
      Abi.selectorOf msg.data = sel ∧ 4 ≤ msg.data.size ∧ msg.data.size < 2 ^ 64)
    (fun _ _ h => h) (fun m hf ⟨hv, hs, h4, h64⟩ hg => getter_halts hge m hf hv hs h4 h64 hg)
    hS.fresh ⟨hv, hsel, h4, hS.size⟩).mono fun _ _ _ h => by
      rcases h with h | h
      · exact .inl h
      · exact .inr (.inl h)

theorem post_short (hS : Start OzAsset.runtimeCode ozAbs ozModel Act m) {sel n : Nat}
    (hsh : (sel, n) ∈ writeShapes) (hv : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = sel) (h4 : 4 ≤ m.frame.msg.data.size)
    (hshort : m.frame.msg.data.size < 4 + n) : Halts m (Post Act m) :=
  post_fails (fails_any (G := 2000) (P := fun msg => msg.value = 0 ∧
      Abi.selectorOf msg.data = sel ∧ 4 ≤ msg.data.size ∧ msg.data.size < 4 + n)
    (fun _ _ h => h) (fun m hf ⟨hv, hs, h4, h⟩ hg => short_halts hsh m hf hv hs h4 h hg)
    hS.fresh ⟨hv, hsel, h4, hshort⟩)

theorem post_dirty0 (hS : Start OzAsset.runtimeCode ozAbs ozModel Act m) {sel n : Nat}
    (hsh : (sel, n) ∈ writeShapes) (hv : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = sel) (hsize : 4 + n ≤ m.frame.msg.data.size)
    (hd : ¬ CleanAddr m.frame.msg.data 0) : Halts m (Post Act m) :=
  post_fails (fails_any (G := 2000) (P := fun msg => msg.value = 0 ∧
      Abi.selectorOf msg.data = sel ∧ 4 + n ≤ msg.data.size ∧ msg.data.size < 2 ^ 64 ∧
      ¬ CleanAddr msg.data 0)
    (fun _ _ h => h) (fun m hf ⟨hv, hs, h4, h64, hd⟩ hg => dirty0_halts hsh m hf hv hs h4 h64 hd hg)
    hS.fresh ⟨hv, hsel, hsize, hS.size, hd⟩)

theorem post_dirty1 (hS : Start OzAsset.runtimeCode ozAbs ozModel Act m)
    (hv : m.frame.msg.value = 0) (hsel : Abi.selectorOf m.frame.msg.data = 0x23b872dd)
    (hsize : 100 ≤ m.frame.msg.data.size) (hc : CleanAddr m.frame.msg.data 0)
    (hd : ¬ CleanAddr m.frame.msg.data 1) : Halts m (Post Act m) :=
  post_fails (fails_any (G := 2000) (P := fun msg => msg.value = 0 ∧
      Abi.selectorOf msg.data = 0x23b872dd ∧ 100 ≤ msg.data.size ∧ msg.data.size < 2 ^ 64 ∧
      CleanAddr msg.data 0 ∧ ¬ CleanAddr msg.data 1)
    (fun _ _ h => h)
    (fun m hf ⟨hv, hs, h4, h64, hc, hd⟩ hg => dirty1_halts m hf hv hs h4 h64 hc hd hg)
    hS.fresh ⟨hv, hsel, hsize, hS.size, hc, hd⟩)

/-- A two-word writing entry point (`transfer`, `approve`, `mint`, `burn`): well formed, or
the decoder reverts. -/
theorem post_two (hS : Start OzAsset.runtimeCode ozAbs ozModel Act m) {sel : Nat}
    (hsh : (sel, 64) ∈ writeShapes) (hv : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = sel) (h4 : 4 ≤ m.frame.msg.data.size)
    (hok : 68 ≤ m.frame.msg.data.size → CleanAddr m.frame.msg.data 0 → Halts m (Post Act m)) :
    Halts m (Post Act m) := by
  by_cases hs : 68 ≤ m.frame.msg.data.size
  · by_cases hc : CleanAddr m.frame.msg.data 0
    · exact hok hs hc
    · exact post_dirty0 hS hsh hv hsel hs hc
  · exact post_short hS hsh hv hsel h4 (by omega)

theorem arg0_eq (d : ByteArray) : arg0 d = argWord d 0 := by simp [arg0, argWord]

theorem arg1_eq (d : ByteArray) : arg1 d = argWord d 1 := by simp [arg1, argWord]

theorem ozOps_mint {d : ByteArray} {caller : Address} {v : ℕ} (hv : v = 0)
    (hsel : Abi.selectorOf d = 0x40c10f19) (hs : 68 ≤ d.size) (hc : CleanAddr d 0) :
    ozOps caller d v = some (.mint caller (Word.toAddress (argWord d 0)) (argWord d 1).toNat) := by
  subst hv
  simp only [ozOps, arg0_eq, arg1_eq, clean_ofAddress hc, hs, hsel, and_self, ite_true]

theorem ozOps_burn {d : ByteArray} {caller : Address} {v : ℕ} (hv : v = 0)
    (hsel : Abi.selectorOf d = 0x9dc29fac) (hs : 68 ≤ d.size) (hc : CleanAddr d 0) :
    ozOps caller d v = some (.burn caller (Word.toAddress (argWord d 0)) (argWord d 1).toNat) := by
  subst hv
  simp only [ozOps, arg0_eq, arg1_eq, clean_ofAddress hc, hs, hsel, and_self,
    ite_true, Nat.reduceEqDiff, ite_false]

end

/-! ## The theorems -/

/-- **`ERC20Mock` with any calldata**: every frame fails, changes nothing, or ends as an
ERC-20 call or a `mint`/`burn` of `ozModel` (exactly, for actors that include every account the
calldata can name). -/
theorem oz_malformed :
    MalformedSpec OzAsset.runtimeCode ozAbs ozModel ozOps ozOpAddrs none [] := by
  refine malformedSpec_of fun Act m hS hcd _ => ?_
  by_cases hfb : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ ozSel
  · exact post_fallback oz_fallbackSpec hS hfb
  simp only [not_or, not_lt, not_not] at hfb
  obtain ⟨h4, hmem⟩ := hfb
  by_cases hv : m.frame.msg.value = 0
  swap
  · exact post_value hS hv
  have hv0 : m.frame.msg.value.toNat = 0 := by rw [hv]; rfl
  rw [ozSel_eq] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h
  · exact post_getter hS (q := 394) (by simp [getterEntries]) hv h h4
  · exact post_two hS (by simp [writeShapes]) hv h h4 fun hs hc =>
      post_approve oz_callSpec hS hcd h hs hc
  · exact post_getter hS (q := 308) (by simp [getterEntries]) hv h h4
  · exact post_two hS (by simp [writeShapes]) hv h h4 fun hs hc =>
      post_op oz_opSpec hS (ozOps_burn hv0 h hs hc)
        (argAddr0_list hcd (by omega))
  · exact post_getter hS (q := 272) (by simp [getterEntries]) hv h h4
  · exact post_two hS (by simp [writeShapes]) hv h h4 fun hs hc =>
      post_op oz_opSpec hS (ozOps_mint hv0 h hs hc)
        (argAddr0_list hcd (by omega))
  · exact post_getter hS (q := 170) (by simp [getterEntries]) hv h h4
  · exact post_getter hS (q := 348) (by simp [getterEntries]) hv h h4
  · exact post_getter hS (q := 235) (by simp [getterEntries]) hv h h4
  · exact post_two hS (by simp [writeShapes]) hv h h4 fun hs hc =>
      post_transfer oz_callSpec hS hcd h hs hc
  · by_cases hs : 100 ≤ m.frame.msg.data.size
    · by_cases hc0 : CleanAddr m.frame.msg.data 0
      · by_cases hc1 : CleanAddr m.frame.msg.data 1
        · exact post_transferFrom oz_callSpec hS hcd h hs hc0 hc1
        · exact post_dirty1 hS hv h hs hc0 hc1
      · exact post_dirty0 hS (n := 96) (by simp [writeShapes]) hv h hs hc0
    · exact post_short hS (n := 96) (by simp [writeShapes]) hv h h4 (by omega)

/-- **The complete spec of `ERC20Mock`**: `ERC20Spec` and `MalformedSpec` (no `permit`). -/
theorem oz_complete :
    ERC20Spec.Complete OzAsset.runtimeCode ozAbs ozModel ozG₀ ozSel ozOps ozOpAddrs none [] :=
  ⟨oz_erc20Spec, fun _ _ h => (by cases h), oz_malformed⟩

end Verified.OpenZeppelin.ERC20.Spec.Malformed
