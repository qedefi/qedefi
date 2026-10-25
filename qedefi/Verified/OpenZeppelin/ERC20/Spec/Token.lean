import Verified.OpenZeppelin.ERC20.Spec.Calls
import Verified.OpenZeppelin.ERC20.CalleeMintBurn

/-!
# OpenZeppelin's `ERC20Mock` (v5.7.0) is `ozModel`

**`oz_erc20Spec`**: the deployed runtime code of `ERC20Mock` is the token model `ozModel`
(`Variant.oz` with OpenZeppelin v5's events) through the storage abstraction `ozAbs`, exactly
from `ozG₀ = 100000` gas, with the dispatcher's selectors `ozSel` and the entry points
`mint(address,uint256)` and `burn(address,uint256)` (open to anyone in `ERC20Mock`, not
payable) decoded by `ozOps` into `Op.mint`/`Op.burn`.

The only hypotheses are those of the spec itself (`Start`): the actors' storage rows are
distinct and avoid the supply slot (`ozSound`, a finite set of Keccak values), and the token
is in a state its model can reach (`Variant.oz.WF`: the actors' balances add up to the supply).
-/

namespace Verified.OpenZeppelin.ERC20.Spec
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Solidity.ERC20
open EvmLean.Interpreter QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC20.Spec.Oz QEDefi.Math
open Verified.OpenZeppelin.Contracts
open Verified.Solmate.ERC20 (TwoWordCall)

/-! ## The views -/

section Views

variable {Act : Finset Address} {m : Machine}

theorem readMap_bal {crypto : Crypto} {w : World} {token a : Address} (ha : a ∈ Act) :
    (ozRead crypto Act w token).bal a = (w.sload token (balanceSlot crypto Layout.oz a)).toNat :=
  readMap_of_mem ha w token _

/-- **The three views of `ERC20Mock` are `ozModel`'s.** -/
theorem oz_viewSpec (v : View) : ViewSpec OzAsset.runtimeCode ozAbs ozModel ozG₀ v := by
  refine viewSpec_of_high noGasCode_oz fun Act m hS henc hadd hg => ?_
  by_cases hv : m.frame.msg.value = 0
  swap
  · exact (value_halts m hS.fresh hv (by unfold ozG₀ at hg; omega)).mono
      fun _ _ _ ⟨_, ho⟩ => .inr ⟨by rw [ho]; trivial, fun h => hv h.2⟩
  rw [pre_eq hS hv]
  have hg' : 5000 ≤ m.frame.gasLeft := by unfold ozG₀ at hg; omega
  cases v with
  | balanceOf a =>
    have ha : a ∈ Act := hadd a (by simp [View.addrs])
    refine (balanceOf_halts m hS.fresh a hv henc.selector (by simpa using henc.size) hS.size
      (by simpa using henc.arg 0 (by simp)) (by omega)).mono fun mf o _ h => ?_
    obtain ⟨ho, h1, h2, h3, h4, -⟩ := h
    refine .inl ⟨_, ho, ?_, h1, h2, h3, h4⟩
    simp only [View.value, ozModel, Variant.model_balanceOf, Variant.balanceOf, Variant.oz,
      Variant.standard, Bool.false_eq_true, ↓reduceIte]
    rw [readMap_bal ha]
  | allowance o sp =>
    have ho : o ∈ Act := hadd o (by simp [View.addrs])
    have hs : sp ∈ Act := hadd sp (by simp [View.addrs])
    refine (allowance_halts m hS.fresh o sp hv henc.selector (by simpa using henc.size) hS.size
      (by simpa using henc.arg 0 (by simp)) (by simpa using henc.arg 1 (by simp)) hg').mono
      fun mf out _ h => ?_
    obtain ⟨ho', h1, h2, h3, h4⟩ := h
    refine .inl ⟨_, ho', ?_, h1, h2, h3, h4⟩
    simp only [View.value, ozModel, Variant.model_allowance, Variant.allowanceOf, Variant.oz,
      Variant.standard, reduceCtorEq, ↓reduceIte]
    simp [ozRead, readMap2, ho, hs, allowanceSlot]
  | totalSupply =>
    refine (totalSupply_halts m hS.fresh hv henc.selector (by simpa using henc.size) hS.size
      hg').mono fun mf out _ h => ?_
    obtain ⟨ho', h1, h2, h3, h4⟩ := h
    exact .inl ⟨_, ho', rfl, h1, h2, h3, h4⟩

end Views

/-! ## Unknown selectors -/

/-- The selectors `ERC20Mock`'s dispatcher knows. -/
def ozSel : List Nat := OzAsset.selectors.map fun p => p.2.toNat

theorem ozSel_eq : ozSel = [0xdd62ed3e, 0x095ea7b3, 0x70a08231, 0x9dc29fac, 0x313ce567,
    0x40c10f19, 0x06fdde03, 0x95d89b41, 0x18160ddd, 0xa9059cbb, 0x23b872dd] := rfl

/-- **`ERC20Mock` has no fallback**: short calldata and unknown selectors revert, as
`ozModel` says. -/
theorem oz_fallbackSpec : FallbackSpec OzAsset.runtimeCode ozAbs ozModel ozG₀ ozSel := by
  refine fallbackSpec_of_high noGasCode_oz fun Act m hS hsel hg => ?_
  have hg' : 1000 ≤ m.frame.gasLeft := by unfold ozG₀ at hg; omega
  have hrev : ∀ mf o, (∃ out, o = Outcome.revert out) →
      Matches ozAbs Act m mf o
        (ozModel.events (pre ozAbs Act m) m.frame.msg.caller (.other m.frame.msg.value.toNat))
        (ozModel.call (pre ozAbs Act m) m.frame.msg.caller (.other m.frame.msg.value.toNat)) := by
    intro mf o h
    rw [ozModel_call, oz_call_other]
    exact h
  by_cases hv : m.frame.msg.value = 0
  swap
  · exact (value_halts m hS.fresh hv (by omega)).mono fun mf o _ h => .inl (hrev mf o h)
  rcases hsel with hs | hs
  · exact (short_halts m hS.fresh hv hs (by omega)).mono fun mf o _ h => .inl (hrev mf o h)
  · by_cases h4 : m.frame.msg.data.size < 4
    · exact (short_halts m hS.fresh hv h4 (by omega)).mono fun mf o _ h => .inl (hrev mf o h)
    · rw [ozSel_eq] at hs
      exact (unknown_halts m hS.fresh hv (by omega) hS.size hg' hs).mono
        fun mf o _ h => .inl (hrev mf o h)

/-! ## `mint` and `burn` -/

/-- The first two argument words of the calldata. -/
def arg0 (data : ByteArray) : Word := Bytes.toWord (readBytes data 4 32)
/-- The second argument word. -/
def arg1 (data : ByteArray) : Word := Bytes.toWord (readBytes data 36 32)

/-- **The decoder of `ERC20Mock`'s other entry points**: `mint(to, v)` and `burn(from, v)`,
anyone's, with ABI-encoded arguments (a clean address word) and no value. -/
def ozOps (caller : Address) (data : ByteArray) (value : ℕ) : Option (Variant.Op Address) :=
  if value = 0 ∧ 68 ≤ data.size ∧
      Word.ofAddress (Word.toAddress (arg0 data)) = arg0 data then
    if Abi.selectorOf data = 0x40c10f19 then
      some (.mint caller (Word.toAddress (arg0 data)) (arg1 data).toNat)
    else if Abi.selectorOf data = 0x9dc29fac then
      some (.burn caller (Word.toAddress (arg0 data)) (arg1 data).toNat)
    else none
  else none

/-- The accounts an operation names: the recipient of a mint, the holder of a burn. -/
def ozOpAddrs : Variant.Op Address → List Address
  | .mint _ d _ => [d]
  | .burn _ s _ => [s]
  | _ => []

section Ops

variable {Act : Finset Address} {m : Machine}

theorem oz_op_mint (s : VState Address) (c d : Address) (v : ℕ) :
    ozModel.op s (.mint c d v) = (s.toToken.ozMint d v).map s.withToken :=
  Variant.oz_mint s c d v

theorem oz_op_burn (s : VState Address) (c src : Address) (v : ℕ) :
    ozModel.op s (.burn c src v) = (s.toToken.ozBurn src v).map s.withToken :=
  Variant.oz_burn s c src v

set_option maxHeartbeats 1000000 in
/-- `mint` in a non-static frame without value. -/
theorem mint_normal (hS : Start OzAsset.runtimeCode ozAbs ozModel Act m) {d : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0x40c10f19 (Word.ofAddress d) amount)
    (hdA : d ∈ Act) (hv : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : ozG₀ ≤ m.frame.gasLeft) :
    Halts m fun mf o => OpMatches ozAbs ozModel Act (.mint m.frame.msg.caller d amount.toNat)
      m mf o := by
  have hR : ozSound m.ctx.crypto Act := hS.sound
  have hr := rep_actorView (crypto := m.ctx.crypto) (Act := Act) (w := m.world)
    (token := m.frame.msg.currentTarget)
  have hw := start_wf hS hv
  unfold OpMatches
  rw [pre_eq hS hv, oz_op_mint]
  have hiff := ozMint_isSome_iff hr d amount
  cases ht : (ozRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).toToken.ozMint d
      amount.toNat with
  | some t' =>
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [ht]))
    have hrep := rep_ozMint hr hw hm ht
    have hview := actorView_mintWorld hR hdA hm
    have hm' := hm
    unfold Model.ozMint at hm'
    split at hm'
    · cases hm'
    rename_i hd0
    split at hm'
    · rename_i hov
      refine (mint_halts_ok m hS.fresh hv hst hd hS.size (by unfold ozG₀ at hg; omega) hd0
        hov).mono fun mf o _ hok => ?_
      obtain ⟨ho, hwf, htr, hcr, -, -⟩ := hok
      refine ⟨⟨_, ho⟩, ?_, ?_, htr, hcr⟩
      · show ozRead _ _ _ _ = _
        rw [hwf]
        exact ozRead_of_rep (hview ▸ hrep)
      · rw [hwf]; exact frameKeeps_mintWorld hdA
    · cases hm'
  | none =>
    have hnone : Model.ozMint (actorView m.ctx.crypto Act m.world m.frame.msg.currentTarget)
        d amount = none := by
      cases h : Model.ozMint (actorView m.ctx.crypto Act m.world m.frame.msg.currentTarget)
        d amount
      · rfl
      · have := hiff.1 (by simp [h]); simp [ht] at this
    exact (mint_halts_revert m hS.fresh hv hd hS.size (by unfold ozG₀ at hg; omega)
      (ozMint_none_of hnone)).mono fun _ o _ h => by obtain ⟨⟨_, rfl⟩, -⟩ := h; trivial

set_option maxHeartbeats 1000000 in
/-- `burn` in a non-static frame without value. -/
theorem burn_normal (hS : Start OzAsset.runtimeCode ozAbs ozModel Act m) {src : Address}
    {amount : Word} (hd : TwoWordCall m.frame.msg.data 0x9dc29fac (Word.ofAddress src) amount)
    (hsA : src ∈ Act) (hv : m.frame.msg.value = 0) (hst : m.frame.msg.isStatic = false)
    (hg : ozG₀ ≤ m.frame.gasLeft) :
    Halts m fun mf o => OpMatches ozAbs ozModel Act (.burn m.frame.msg.caller src amount.toNat)
      m mf o := by
  have hR : ozSound m.ctx.crypto Act := hS.sound
  have hr := rep_actorView (crypto := m.ctx.crypto) (Act := Act) (w := m.world)
    (token := m.frame.msg.currentTarget)
  have hw := start_wf hS hv
  unfold OpMatches
  rw [pre_eq hS hv, oz_op_burn]
  have hiff := ozBurn_isSome_iff hr src amount
  cases ht : (ozRead m.ctx.crypto Act m.world m.frame.msg.currentTarget).toToken.ozBurn src
      amount.toNat with
  | some t' =>
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1 (hiff.2 (by simp [ht]))
    have hrep := rep_ozBurn hr hw hm ht
    have hview := actorView_burnWorld hR hsA hm
    have hm' := hm
    unfold Model.ozBurn at hm'
    split at hm'
    · cases hm'
    rename_i hs0
    split at hm'
    · rename_i hbal
      refine (burn_halts_ok m hS.fresh hv hst hd hS.size (by unfold ozG₀ at hg; omega) hs0
        (by rwa [view_balanceOf_eq hsA])).mono fun mf o _ hok => ?_
      obtain ⟨ho, hwf, htr, hcr, -, -⟩ := hok
      refine ⟨⟨_, ho⟩, ?_, ?_, htr, hcr⟩
      · show ozRead _ _ _ _ = _
        rw [hwf]
        exact ozRead_of_rep (hview ▸ hrep)
      · rw [hwf]; exact frameKeeps_burnWorld hsA
    · cases hm'
  | none =>
    have hnone : Model.ozBurn (actorView m.ctx.crypto Act m.world m.frame.msg.currentTarget)
        src amount = none := by
      cases h : Model.ozBurn (actorView m.ctx.crypto Act m.world m.frame.msg.currentTarget)
        src amount
      · rfl
      · have := hiff.1 (by simp [h]); simp [ht] at this
    exact (burn_halts_revert m hS.fresh hv hd hS.size (by unfold ozG₀ at hg; omega)
      (ozBurn_none_of hsA hnone)).mono fun _ o _ h => by obtain ⟨⟨_, rfl⟩, -⟩ := h; trivial

/-- **`mint` and `burn` of `ERC20Mock` are `ozModel`'s operations.** -/
theorem oz_opSpec : OpSpec OzAsset.runtimeCode ozAbs ozModel ozG₀ ozOps ozOpAddrs := by
  refine opSpec_of_high noGasCode_oz fun Act m e hS hops hadd hg => ?_
  unfold ozOps at hops
  split at hops
  swap
  · cases hops
  rename_i hok
  obtain ⟨hv0, hsize, hclean⟩ := hok
  have hv : m.frame.msg.value = 0 := by
    apply BitVec.eq_of_toNat_eq; simpa using hv0
  have hg' : 60000 ≤ m.frame.gasLeft := by unfold ozG₀ at hg; omega
  split at hops
  · rename_i hsel
    cases hops
    have hdA : Word.toAddress (arg0 m.frame.msg.data) ∈ Act := hadd _ (by simp [ozOpAddrs])
    have hd : TwoWordCall m.frame.msg.data 0x40c10f19
        (Word.ofAddress (Word.toAddress (arg0 m.frame.msg.data))) (arg1 m.frame.msg.data) :=
      ⟨hsel, hsize, hclean.symm, rfl⟩
    cases hst : m.frame.msg.isStatic
    · exact (mint_normal hS hd hdA hv hst hg).mono fun _ _ _ h => .inl h
    · exact (mint_static m hS.fresh hv hst hd hS.size hg').mono
        fun _ _ _ h => .inr ⟨h, fun h' => Bool.noConfusion h'.2⟩
  split at hops
  · rename_i _ hsel
    cases hops
    have hsA : Word.toAddress (arg0 m.frame.msg.data) ∈ Act := hadd _ (by simp [ozOpAddrs])
    have hd : TwoWordCall m.frame.msg.data 0x9dc29fac
        (Word.ofAddress (Word.toAddress (arg0 m.frame.msg.data))) (arg1 m.frame.msg.data) :=
      ⟨hsel, hsize, hclean.symm, rfl⟩
    cases hst : m.frame.msg.isStatic
    · exact (burn_normal hS hd hsA hv hst hg).mono fun _ _ _ h => .inl h
    · exact (burn_static m hS.fresh hv hst hd hS.size hg').mono
        fun _ _ _ h => .inr ⟨h, fun h' => Bool.noConfusion h'.2⟩
  · cases hops

end Ops

/-! ## The spec -/

/-- **OpenZeppelin's `ERC20Mock` (v5.7.0), as deployed, is `ozModel`**: OpenZeppelin v5's
`Variant.oz` with its events, through `ozAbs`, exactly from `ozG₀` gas, with no fallback and
open `mint`/`burn`. -/
theorem oz_erc20Spec :
    ERC20Spec OzAsset.runtimeCode ozAbs ozModel ozG₀ ozSel ozOps ozOpAddrs :=
  ⟨oz_callSpec, oz_viewSpec, oz_fallbackSpec, oz_opSpec⟩

end Verified.OpenZeppelin.ERC20.Spec
