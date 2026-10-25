import Verified.WETH9.Spec.Frame

/-!
# WETH9 satisfies `ViewSpec`

`weth9_viewSpec`: on the deployed bytecode, `balanceOf(a)`, `allowance(o, sp)` and
`totalSupply()` (its actors' accounts) return exactly the model's value
(`weth9Model`, through `weth9Abs`) as one word and change nothing, from gas `weth9Gas` with no
value; with less gas they fail or return the same, and with value they revert.
-/

namespace Verified.WETH9.Spec
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Program.Nested
open EvmLogic.GasMono EvmLogic.Solidity Verified.WETH9.Contracts
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.WETH9

/-- The world of a frame started without value is its snapshot. -/
theorem world_eq_snapshot {code : ByteArray} {σ E : Type} {abs : TokenAbs σ}
    {M : TokenModel σ Address E} {Act : Finset Address} {m : Machine}
    (hS : Start code abs M Act m) (hv : m.frame.msg.value = 0) :
    m.world = m.frame.snapshot.1 := by
  rw [hS.launched, transferValue_zero _ _ hv]

@[simp] theorem weth9Model_balanceOf (s : VState Address) (a : Address) :
    (weth9Model : TokenModel (VState Address) Address (Variant.Op Address)).balanceOf s a =
      s.bal a := rfl

@[simp] theorem weth9Model_allowance (s : VState Address) (o sp : Address) :
    (weth9Model : TokenModel (VState Address) Address (Variant.Op Address)).allowance s o sp =
      s.allowance o sp := by
  simp [weth9Model, Variant.allowanceOf, Variant.weth9, Variant.standard]

@[simp] theorem weth9Model_totalSupply (s : VState Address) :
    (weth9Model : TokenModel (VState Address) Address (Variant.Op Address)).totalSupply s =
      s.ether := rfl

/-- **WETH9's views are exact**, for every gas. -/
theorem weth9_viewSpec (v : View) :
    ViewSpec WETH9.runtimeCode weth9Abs weth9Model weth9Gas v := by
  intro Act m hS hE hA
  refine halts_of_low (g₀ := weth9Gas) hS.fresh ?_ (fun _ _ _ _ _ h => h) ?_
  · intro hg mf o hfo
    exact .inr ⟨fails_of_failed hfo, fun h => hg h.1⟩
  intro g hg
  have hgas : 5000 ≤ g := le_trans (by decide) hg
  cases v with
  | balanceOf a =>
    obtain ⟨hsel, hsize, harg⟩ := hE
    have ha : a ∈ Act := hA a (by simp [View.addrs])
    refine balanceOf_low a hsel (by simpa using hsize) hS.size
      (by simpa using harg 0 (by simp)) hgas
      (fun hv _ _ => .inr ⟨trivial, fun h => hv h.2⟩) ?_
    intro hv mf out hout hw ht hc hl
    subst hout
    refine .inl ⟨_, rfl, ?_, hw, ht, hc, hl⟩
    simp only [View.value, weth9Model_balanceOf, pre, weth9Abs, weth9Read,
      readMap_of_mem ha, world_eq_snapshot hS hv]
  | allowance o sp =>
    obtain ⟨hsel, hsize, harg⟩ := hE
    have ho : o ∈ Act := hA o (by simp [View.addrs])
    have hsp : sp ∈ Act := hA sp (by simp [View.addrs])
    refine allowance_low o sp hsel (by simpa using hsize) hS.size
      (by simpa using harg 0 (by simp)) (by simpa using harg 1 (by simp)) hgas
      (fun hv _ _ => .inr ⟨trivial, fun h => hv h.2⟩) ?_
    intro hv mf out hout hw ht hc hl
    subst hout
    refine .inl ⟨_, rfl, ?_, hw, ht, hc, hl⟩
    simp only [View.value, weth9Model_allowance, pre, weth9Abs, weth9Read, readMap2, ho, hsp,
      and_self, ↓reduceIte, world_eq_snapshot hS hv]
  | totalSupply =>
    obtain ⟨hsel, hsize, -⟩ := hE
    refine totalSupply_low hsel (by simpa using hsize) hS.size hgas
      (fun hv _ _ => .inr ⟨trivial, fun h => hv h.2⟩) ?_
    intro hv mf out hout hw ht hc hl
    subst hout
    refine .inl ⟨_, rfl, ?_, hw, ht, hc, hl⟩
    simp only [View.value, weth9Model_totalSupply, pre, weth9Abs, weth9Read,
      world_eq_snapshot hS hv]

end Verified.WETH9.Spec
