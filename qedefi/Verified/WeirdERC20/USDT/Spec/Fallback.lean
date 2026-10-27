import Verified.WeirdERC20.USDT.Spec.ViewOut

/-!
# USDT's unknown selectors satisfy `FallbackSpec`

`TetherToken` has no fallback function: calldata shorter than a selector, or a selector the
dispatcher does not know (not in `sel`), reaches the dispatcher's final `REVERT`, whatever the
value, and the model's fallback (`Fallback.revert`) reverts too (`usdt_fallback`).
-/

namespace Verified.WeirdERC20.USDT.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open Verified.WeirdERC20.USDT.Contracts EvmLogic.Program.Nested EvmLogic.GasMono
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.Math

theorem selectorOf_lt (data : ByteArray) : Abi.selectorOf data < 2 ^ 32 := by
  have := Bytes.toNat_lt (readBytes data 0 4)
  rw [size_readBytes] at this
  unfold Abi.selectorOf; simpa using this

theorem sel_lt : ∀ k ∈ sel, k < 2 ^ 32 := by decide

/-- The dispatcher's comparison with a known selector fails for an unknown one. -/
theorem sel_ne {data : ByteArray} (hns : Abi.selectorOf data ∉ sel) (k : Nat) (hk : k ∈ sel) :
    Word.eq (BitVec.ofNat 256 k) (BitVec.ofNat 256 (Abi.selectorOf data)) = 0#256 := by
  apply eq_of_ne
  intro h
  have h1 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h1
  have h2 := sel_lt k hk
  have h3 := selectorOf_lt data
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
  exact hns (h1 ▸ hk)

theorem lt_size_four_one {n : Nat} (h : n < 4) : Word.lt (ofNat n) (BitVec.ofNat 256 4) = 1 := by
  rw [Word.lt_eq_one_iff]; simp only [ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact h

/-- What the lift of a fallback frame ends with: a revert. -/
def FallbackOut (_mf : Machine) (o : Outcome) : Prop := ∃ out, o = .revert out

set_option maxHeartbeats 0 in
/-- **Unknown selectors and short calldata** on the lift: the dispatcher's `REVERT`. -/
theorem fallback_high (m : Machine) (hf : Fresh USDT.runtimeCode m) (d : Nat)
    (hg : g₀ ≤ m.frame.gasLeft + d) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hd : m.frame.msg.data.size < 4 ∨ Abi.selectorOf m.frame.msg.data ∉ sel) :
    WP (lift patchedCode d m) (fun mh' => mh'.frame.pc ∉ patchPcs ∧
      ExitsWith FallbackOut mh') (fun _ _ => False) := by
  simp only [g₀] at hg
  by_cases h4 : m.frame.msg.data.size < 4
  · have hlt := lt_size_four_one h4
    lift_intro
    usdt_run [hlt]
    usdt_revert
    exact ⟨_, rfl⟩
  · have hns := hd.resolve_left h4
    have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
    have h117300739 := sel_ne hns 117300739 (by decide)
    have h122929932 := sel_ne hns 122929932 (by decide)
    have h157198259 := sel_ne hns 157198259 (by decide)
    have h236153625 := sel_ne hns 236153625 (by decide)
    have h248222656 := sel_ne hns 248222656 (by decide)
    have h404098525 := sel_ne hns 404098525 (by decide)
    have h599290589 := sel_ne hns 599290589 (by decide)
    have h647458367 := sel_ne hns 647458367 (by decide)
    have h669136355 := sel_ne hns 669136355 (by decide)
    have h826074471 := sel_ne hns 826074471 (by decide)
    have h892929812 := sel_ne hns 892929812 (by decide)
    have h1051392107 := sel_ne hns 1051392107 (by decide)
    have h1061922874 := sel_ne hns 1061922874 (by decide)
    have h1505696446 := sel_ne hns 1505696446 (by decide)
    have h1550156133 := sel_ne hns 1550156133 (by decide)
    have h1553423035 := sel_ne hns 1553423035 (by decide)
    have h1889567281 := sel_ne hns 1889567281 (by decide)
    have h2220280665 := sel_ne hns 2220280665 (by decide)
    have h2302484712 := sel_ne hns 2302484712 (by decide)
    have h2376452955 := sel_ne hns 2376452955 (by decide)
    have h2514000705 := sel_ne hns 2514000705 (by decide)
    have h2835717307 := sel_ne hns 2835717307 (by decide)
    have h3224521847 := sel_ne hns 3224521847 (by decide)
    have h3431410534 := sel_ne hns 3431410534 (by decide)
    have h3674237557 := sel_ne hns 3674237557 (by decide)
    have h3714247998 := sel_ne hns 3714247998 (by decide)
    have h3714338674 := sel_ne hns 3714338674 (by decide)
    have h3833421920 := sel_ne hns 3833421920 (by decide)
    have h3835264453 := sel_ne hns 3835264453 (by decide)
    have h3853844890 := sel_ne hns 3853844890 (by decide)
    have h4076725131 := sel_ne hns 4076725131 (by decide)
    have h4089299496 := sel_ne hns 4089299496 (by decide)
    lift_intro
    usdt_run [hlt, div_selector,
      h117300739, h122929932, h157198259, h236153625, h248222656, h404098525, h599290589,
      h647458367, h669136355, h826074471, h892929812, h1051392107, h1061922874, h1505696446,
      h1550156133, h1553423035, h1889567281, h2220280665, h2302484712, h2376452955, h2514000705,
      h2835717307, h3224521847, h3431410534, h3674237557, h3714247998, h3714338674, h3833421920,
      h3835264453, h3853844890, h4076725131, h4089299496]
    usdt_revert
    exact ⟨_, rfl⟩

/-- **`FallbackSpec` for USDT.** -/
theorem usdt_fallback : FallbackSpec USDT.runtimeCode usdtAbs M g₀ sel := by
  intro Act m hs hd
  have hcall : M.call (pre usdtAbs Act m) m.frame.msg.caller (.other m.frame.msg.value.toNat) =
      .halt .revert := by
    simp [M, QEDefi.ERC20.Spec.USDT.usdtModel, Variant.model, Variant.call, Variant.step,
      Variant.fallbackCall, Variant.failKind, Variant.guardOk, Variant.usdt, Variant.standard,
      Variant.failWith]
  refine (halts_of_high hs.fresh (Post := FallbackOut) (fun _ _ _ h => by obtain ⟨_, h⟩ := h; cases h)
    (fun _ _ h => h) (fallback_high m hs.fresh _ (by omega) hs.size hd)).mono fun mf o _ h => ?_
  rcases h with ⟨hf, hlt⟩ | h
  · exact .inr ⟨hf, fun h => by omega⟩
  · left
    rw [hcall]
    exact h

end Verified.WeirdERC20.USDT.Spec
