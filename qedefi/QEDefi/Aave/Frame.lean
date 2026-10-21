module

public import QEDefi.Aave.Pool
public import QEDefi.Aave.Accrual

/-!
# Frame lemmas: what each Pool entry point does to the reserves

For each entry point: the touched reserve is first brought up to date by `updateState`
(`r ↦ r1`), and then changed `r1 ↦ X` by a `Step`: the indexes stay, the token
well-formedness is kept, and the change is `Backed` — whatever the aToken holders and the
treasury gain (`ΔS + ΔT`, valued at the index) is matched by what the reserve gains
(`ΔV + Δdeficit` plus the debt `ΔD` valued at the borrow index). All the rounding directions
of `TokenMath` show up here, as the inequalities that make each step `Backed`.
-/

section

@[expose] public noncomputable section

namespace QEDefi.Aave
open QEDefi.Math

namespace ReserveState

variable {A : Type} [DecidableEq A]

/-- The change `r ↦ X` is backed: `Φ(X) ≥ Φ(r)` for
`Φ = (V + deficit)·RAY + D·B - (S + T)·I`, written without subtraction. -/
def Backed (r X : ReserveState A) : Prop :=
  (X.aToken.totalSupply + X.accruedToTreasury) * X.liquidityIndex +
      ((r.virtualUnderlyingBalance + r.deficit) * RAY + r.vToken.totalSupply * r.variableBorrowIndex) ≤
    (r.aToken.totalSupply + r.accruedToTreasury) * r.liquidityIndex +
      ((X.virtualUnderlyingBalance + X.deficit) * RAY + X.vToken.totalSupply * X.variableBorrowIndex)

/-- A non-accrual step of an entry point on one reserve. -/
structure Step (r X : ReserveState A) : Prop where
  /-- The change is backed. -/
  backed : Backed r X
  /-- The liquidity index is unchanged. -/
  liquidityIndex : X.liquidityIndex = r.liquidityIndex
  /-- The variable borrow index is unchanged. -/
  variableBorrowIndex : X.variableBorrowIndex = r.variableBorrowIndex
  /-- Token well-formedness is kept. -/
  wf : r.TokensWF → X.TokensWF

theorem Step.refl (r : ReserveState A) : Step r r :=
  ⟨by unfold Backed; omega, rfl, rfl, id⟩

theorem Step.trans {r X Y : ReserveState A} (h1 : Step r X) (h2 : Step X Y) : Step r Y :=
  ⟨by have := h1.backed; have := h2.backed; unfold Backed at *; omega,
   h2.liquidityIndex.trans h1.liquidityIndex, h2.variableBorrowIndex.trans h1.variableBorrowIndex,
   fun h => h2.wf (h1.wf h)⟩

theorem Solvent.of_backed {k : ℕ} {r X : ReserveState A} (hs : r.Solvent k) (hb : Backed r X) :
    X.Solvent k := by
  unfold Solvent Backed at *; omega

theorem updateInterestRates_spec {irs : Strategy} {r r' : ReserveState A} {c : ReserveCache}
    {added taken : ℕ} (h : r.updateInterestRatesAndVirtualBalance irs c added taken = some r') :
    ∃ lr vr v, r' = { r with currentLiquidityRate := lr, currentVariableBorrowRate := vr,
                             virtualUnderlyingBalance := v } ∧
      v + taken = r.virtualUnderlyingBalance + added := by
  unfold updateInterestRatesAndVirtualBalance nextVirtualBalance at h
  simp only [Option.bind_eq_some_iff, Option.ite_none_left_eq_some, Option.map_eq_some_iff] at h
  obtain ⟨td, -, rates, -, -, v, hv, rfl⟩ := h
  refine ⟨_, _, v, rfl, ?_⟩
  obtain ⟨v1, h1, h2⟩ := hv
  split_ifs at h1 h2 with ha ha' ht ht' ht ht' <;>
    simp only [Option.some.injEq] at h1 h2 <;> omega

/-- The rates/virtual-balance update as a `Step` of its own is not backed in general (it moves
liquidity); this records its effect on the fields. -/
theorem updateInterestRates_fields {irs : Strategy} {r r' : ReserveState A} {c : ReserveCache}
    {added taken : ℕ} (h : r.updateInterestRatesAndVirtualBalance irs c added taken = some r') :
    r'.aToken = r.aToken ∧ r'.vToken = r.vToken ∧ r'.accruedToTreasury = r.accruedToTreasury ∧
    r'.deficit = r.deficit ∧ r'.liquidityIndex = r.liquidityIndex ∧
    r'.variableBorrowIndex = r.variableBorrowIndex ∧
    r'.lastUpdateTimestamp = r.lastUpdateTimestamp ∧
    r'.liquidationGracePeriodUntil = r.liquidationGracePeriodUntil ∧
    r'.virtualUnderlyingBalance + taken = r.virtualUnderlyingBalance + added := by
  obtain ⟨lr, vr, v, rfl, hv⟩ := updateInterestRates_spec h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hv⟩

end ReserveState

namespace Market

variable {A R : Type} [DecidableEq A] [DecidableEq R]

@[simp] theorem reserves_setReserve (m : Market A R) (a : R) (r : ReserveState A) :
    (m.setReserve a r).reserves = Function.update m.reserves a r := rfl

@[simp] theorem reserves_setCollateral (m : Market A R) (u : A) (a : R) (b : Bool) :
    (m.setCollateral u a b).reserves = m.reserves := rfl

@[simp] theorem reserves_setBorrowing (m : Market A R) (u : A) (a : R) (b : Bool) :
    (m.setBorrowing u a b).reserves = m.reserves := rfl

@[simp] theorem config_setReserve (m : Market A R) (a : R) (r : ReserveState A) :
    (m.setReserve a r).config = m.config := rfl

@[simp] theorem config_setCollateral (m : Market A R) (u : A) (a : R) (b : Bool) :
    (m.setCollateral u a b).config = m.config := rfl

@[simp] theorem config_setBorrowing (m : Market A R) (u : A) (a : R) (b : Bool) :
    (m.setBorrowing u a b).config = m.config := rfl

theorem reserves_ite {c : Prop} [Decidable c] (m1 m2 : Market A R) :
    (if c then m1 else m2).reserves = if c then m1.reserves else m2.reserves := by
  split_ifs <;> rfl

/-! ## Supply -/

theorem supply_frame {m m' : Market A R} {env : Env R} {asset : R} {amount : ℕ} {user ob : A}
    (h : m.supply env asset amount user ob = some m') :
    ∃ r1 c1 X, (m.reserves asset).updateState ((m.reserves asset).cache (m.config asset))
        env.now = some (r1, c1) ∧
      m'.reserves = Function.update m.reserves asset X ∧ ReserveState.Step r1 X := by
  unfold supply at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.ite_none_left_eq_some] at h
  obtain ⟨⟨r1, c1⟩, hu, sa, hsa, -, -, -, -, -, r2, hr2, res, hmint, rfl⟩ := h
  refine ⟨r1, c1, { r2 with aToken := res.1 }, hu, ?_, ?_⟩
  · split_ifs <;> rfl
  obtain ⟨nI, nB, nT, rfl, -, -, -, hI, -⟩ := ReserveState.updateState_spec hu
  obtain ⟨lr, vr, v, rfl, hv⟩ := ReserveState.updateInterestRates_spec hr2
  obtain ⟨-, e1, -⟩ := ScaledToken.mintScaled_eq_some hmint
  have hb := (rayDivFloor_bounds hsa).1
  simp only at hI hsa hb hv hmint
  rw [hI] at hb hmint
  refine ⟨?_, rfl, rfl, fun hw => ⟨ScaledToken.WF_mintScaled hw.1 hmint, hw.2⟩⟩
  obtain rfl : v = (m.reserves asset).virtualUnderlyingBalance + amount := by omega
  unfold ReserveState.Backed
  simp only [e1, Nat.add_mul]
  omega

/-! ## Withdraw -/

theorem withdraw_frame {m m' : Market A R} {env : Env R} {asset : R} {amount : ℕ} {user dst : A}
    {out : ℕ} (h : m.withdraw env asset amount user dst = some (m', out)) :
    ∃ r1 c1 X, (m.reserves asset).updateState ((m.reserves asset).cache (m.config asset))
        env.now = some (r1, c1) ∧
      m'.reserves = Function.update m.reserves asset X ∧ ReserveState.Step r1 X := by
  unfold withdraw at h
  simp only [Option.bind_eq_some_iff, Option.ite_none_left_eq_some] at h
  obtain ⟨-, ⟨r1, c1⟩, hu, sw, hsw, -, hsub, -, r2, hr2, res, hburn, hfin⟩ := h
  refine ⟨r1, c1, { r2 with aToken := res.1 }, hu, ?_, ?_⟩
  · split_ifs at hfin <;>
      (try simp only [Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hfin) <;>
      (first | obtain ⟨rfl, -⟩ := hfin | obtain ⟨-, -, rfl, -⟩ := hfin) <;>
      first | rfl | simp
  obtain ⟨nI, nB, nT, rfl, -, -, -, hI, -⟩ := ReserveState.updateState_spec hu
  obtain ⟨lr, vr, v, rfl, hv⟩ := ReserveState.updateInterestRates_spec hr2
  obtain ⟨-, -, hle, e1, -⟩ := ScaledToken.burnScaled_eq_some hburn
  simp only at hI hsw hv hburn hle e1 hsub
  -- the amount paid out is covered by the scaled amount burned
  have hb : sw.2 * RAY ≤ sw.1 * nI := by
    split_ifs at hsw
    · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hsw
      rw [hI] at ha; exact (rayMulFloor_bounds ha).1
    · obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 hsw
      rw [hI] at hs; exact (rayDivCeil_bounds hs).1
  rw [hI] at hburn
  refine ⟨?_, rfl, rfl, fun hw => ⟨ScaledToken.WF_burnScaled hw.1 hburn, hw.2⟩⟩
  unfold ReserveState.Backed
  simp only [e1]
  have e2 : (m.reserves asset).aToken.totalSupply * nI =
      ((m.reserves asset).aToken.totalSupply - sw.1) * nI + sw.1 * nI := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hle]
  have e3 : (m.reserves asset).virtualUnderlyingBalance * RAY = v * RAY + sw.2 * RAY := by
    rw [← Nat.add_mul, hv, Nat.add_zero]
  simp only [Nat.add_mul]
  omega

/-! ## Transfer -/

theorem transfer_frame {m m' : Market A R} {env : Env R} {asset : R} {src dst : A} {amount : ℕ}
    (h : m.transfer env asset src dst amount = some m') :
    ∃ X, m'.reserves = Function.update m.reserves asset X ∧
      ReserveState.Step (m.reserves asset) X := by
  unfold transfer at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.ite_none_left_eq_some] at h
  obtain ⟨-, idx, -, sa, -, a', ha', -, hfin⟩ := h
  refine ⟨{ m.reserves asset with aToken := a' }, ?_, ?_⟩
  · split_ifs at hfin <;>
      (try simp only [Option.map_eq_some_iff, Option.some.injEq] at hfin) <;>
      (first | obtain rfl := hfin | obtain ⟨-, -, rfl⟩ := hfin) <;>
      first | rfl | simp
  obtain ⟨e1, -, -⟩ := ScaledToken.transferScaled_eq_some ha'
  refine ⟨?_, rfl, rfl, fun hw => ⟨ScaledToken.WF_transferScaled hw.1 ha', hw.2⟩⟩
  unfold ReserveState.Backed; simp only [e1]; omega

/-! ## Borrow -/

theorem borrow_frame {m m' : Market A R} {env : Env R} {asset : R} {amount : ℕ} {user ob : A}
    (h : m.borrow env asset amount user ob = some m') :
    ∃ r1 c1 X, (m.reserves asset).updateState ((m.reserves asset).cache (m.config asset))
        env.now = some (r1, c1) ∧
      m'.reserves = Function.update m.reserves asset X ∧ ReserveState.Step r1 X := by
  unfold borrow at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.ite_none_left_eq_some] at h
  obtain ⟨⟨r1, c1⟩, hu, sd, hsd, -, -, -, -, -, -, -, -, -, -, -, -, res, hmint, r3, hr3, -, -, rfl⟩ :=
    h
  refine ⟨r1, c1, r3, hu, rfl, ?_⟩
  obtain ⟨nI, nB, nT, rfl, -, -, -, -, hB, -⟩ := ReserveState.updateState_spec hu
  obtain ⟨lr, vr, v, rfl, hv⟩ := ReserveState.updateInterestRates_spec hr3
  obtain ⟨-, e1, -⟩ := ScaledToken.mintScaled_eq_some hmint
  simp only at hB hsd hv hmint e1
  rw [hB] at hsd hmint
  have hb := (rayDivCeil_bounds hsd).1
  refine ⟨?_, rfl, rfl, fun hw => ⟨hw.1, ScaledToken.WF_mintScaled hw.2 hmint⟩⟩
  unfold ReserveState.Backed
  simp only [e1]
  have e3 : (m.reserves asset).virtualUnderlyingBalance * RAY = v * RAY + amount * RAY := by
    rw [← Nat.add_mul, hv, Nat.add_zero]
  simp only [Nat.add_mul]
  omega

/-! ## Repay -/

theorem repay_frame {m m' : Market A R} {env : Env R} {asset : R} {amount : ℕ} {user ob : A}
    {useA : Bool} {out : ℕ} (h : m.repay env asset amount user ob useA = some (m', out)) :
    ∃ r1 c1 X, (m.reserves asset).updateState ((m.reserves asset).cache (m.config asset))
        env.now = some (r1, c1) ∧
      m'.reserves = Function.update m.reserves asset X ∧ ReserveState.Step r1 X := by
  unfold repay at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.ite_none_left_eq_some] at h
  obtain ⟨-, ⟨r1, c1⟩, hu, ud, -, -, -, -, -, pb0, -, sd, hsd, res, hburn, r3, hr3, hfin⟩ := h
  obtain ⟨nI, nB, nT, rfl, -, -, -, hI, hB, -⟩ := ReserveState.updateState_spec hu
  obtain ⟨lr, vr, v, hr3e, hv⟩ := ReserveState.updateInterestRates_spec hr3
  obtain ⟨-, -, hle, e1, -⟩ := ScaledToken.burnScaled_eq_some hburn
  simp only at hI hB hsd hv hburn hle e1 hfin hr3e
  rw [hB] at hsd hburn
  have hbd := (rayDivFloor_bounds hsd).1
  have e2 : (m.reserves asset).vToken.totalSupply * nB =
      ((m.reserves asset).vToken.totalSupply - sd) * nB + sd * nB := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hle]
  cases useA
  · -- repay with the underlying
    refine ⟨_, c1, r3, hu, ?_, ?_⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hfin
      obtain ⟨rfl, -⟩ := hfin
      split_ifs <;> simp
    · subst hr3e
      refine ⟨?_, rfl, rfl, fun hw => ⟨hw.1, ScaledToken.WF_burnScaled hw.2 hburn⟩⟩
      unfold ReserveState.Backed
      simp only [e1]
      replace hv : v = (m.reserves asset).virtualUnderlyingBalance +
          (if ud < pb0 then ud else pb0) := by simpa using hv
      have e3 : v * RAY = (m.reserves asset).virtualUnderlyingBalance * RAY +
          (if ud < pb0 then ud else pb0) * RAY := by
        rw [← Nat.add_mul, ← hv]
      simp only [Nat.add_mul]
      omega
  · -- repay with aTokens
    simp only [↓reduceIte, Option.bind_eq_some_iff] at hfin
    obtain ⟨sa, hsa, ares, haburn, hfin⟩ := hfin
    rw [hI] at hsa haburn
    have hba := (rayDivCeil_bounds hsa).1
    have har : r3.aToken = (m.reserves asset).aToken := by rw [hr3e]
    rw [har] at haburn
    obtain ⟨-, -, hle2, e4, -⟩ := ScaledToken.burnScaled_eq_some haburn
    refine ⟨_, c1, { r3 with aToken := ares.1 }, hu, ?_, ?_⟩
    · split_ifs at hfin <;>
        (try simp only [Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hfin) <;>
        (first | obtain ⟨rfl, -⟩ := hfin | obtain ⟨-, -, rfl, -⟩ := hfin) <;>
        first | rfl | simp
    · subst hr3e
      refine ⟨?_, rfl, rfl, fun hw => ⟨ScaledToken.WF_burnScaled hw.1 haburn,
        ScaledToken.WF_burnScaled hw.2 hburn⟩⟩
      unfold ReserveState.Backed
      simp only [e1, e4]
      replace hv : v = (m.reserves asset).virtualUnderlyingBalance := by simpa using hv
      have e5 : (m.reserves asset).aToken.totalSupply * nI =
          ((m.reserves asset).aToken.totalSupply - sa) * nI + sa * nI := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hle2]
      simp only [Nat.add_mul, hv]
      omega

/-! ## Market-level relations -/

/-- Every reserve of `m'` is a `Step` from the same reserve of `m`. -/
def AllStep (m m' : Market A R) : Prop := ∀ b, ReserveState.Step (m.reserves b) (m'.reserves b)

theorem AllStep.refl (m : Market A R) : AllStep m m := fun _ => ReserveState.Step.refl _

theorem AllStep.trans {m m' m'' : Market A R} (h1 : AllStep m m') (h2 : AllStep m' m'') :
    AllStep m m'' := fun b => (h1 b).trans (h2 b)

theorem AllStep.of_reserves_eq {m m' : Market A R} (h : m'.reserves = m.reserves) :
    AllStep m m' := fun b => h ▸ ReserveState.Step.refl _

theorem AllStep.setReserve {m : Market A R} {a : R} {X : ReserveState A}
    (h : ReserveState.Step (m.reserves a) X) : AllStep m (m.setReserve a X) := by
  intro b
  simp only [reserves_setReserve, Function.update_apply]
  split_ifs with hb
  · subst hb; exact h
  · exact ReserveState.Step.refl _

/-- Each reserve of `m'` is reached from the same reserve of `m` by at most one `updateState`
(at `now`) followed by a `Step`. Every entry point satisfies this (`*_reaches`). -/
def Reaches (m : Market A R) (now : ℕ) (m' : Market A R) : Prop :=
  ∀ b, ∃ r1, (r1 = m.reserves b ∨
      ∃ c1, (m.reserves b).updateState ((m.reserves b).cache (m.config b)) now = some (r1, c1)) ∧
    ReserveState.Step r1 (m'.reserves b)

theorem Reaches.of_frame {m m' : Market A R} {now : ℕ} {a : R}
    (h : ∃ r1 c1 X, (m.reserves a).updateState ((m.reserves a).cache (m.config a)) now =
        some (r1, c1) ∧ m'.reserves = Function.update m.reserves a X ∧ ReserveState.Step r1 X) :
    Reaches m now m' := by
  obtain ⟨r1, c1, X, hu, he, hs⟩ := h
  intro b
  rw [he, Function.update_apply]
  split_ifs with hb
  · subst hb; exact ⟨r1, Or.inr ⟨c1, hu⟩, hs⟩
  · exact ⟨_, Or.inl rfl, ReserveState.Step.refl _⟩

theorem Reaches.of_allStep {m m' : Market A R} {now : ℕ} (h : AllStep m m') : Reaches m now m' :=
  fun b => ⟨_, Or.inl rfl, h b⟩

theorem supply_reaches {m m' : Market A R} {env : Env R} {asset : R} {amount : ℕ} {user ob : A}
    (h : m.supply env asset amount user ob = some m') : Reaches m env.now m' :=
  Reaches.of_frame (supply_frame h)

theorem withdraw_reaches {m m' : Market A R} {env : Env R} {asset : R} {amount : ℕ}
    {user dst : A} {out : ℕ} (h : m.withdraw env asset amount user dst = some (m', out)) :
    Reaches m env.now m' :=
  Reaches.of_frame (withdraw_frame h)

theorem borrow_reaches {m m' : Market A R} {env : Env R} {asset : R} {amount : ℕ} {user ob : A}
    (h : m.borrow env asset amount user ob = some m') : Reaches m env.now m' :=
  Reaches.of_frame (borrow_frame h)

theorem repay_reaches {m m' : Market A R} {env : Env R} {asset : R} {amount : ℕ} {user ob : A}
    {useA : Bool} {out : ℕ} (h : m.repay env asset amount user ob useA = some (m', out)) :
    Reaches m env.now m' :=
  Reaches.of_frame (repay_frame h)

theorem transfer_allStep {m m' : Market A R} {env : Env R} {asset : R} {src dst : A}
    {amount : ℕ} (h : m.transfer env asset src dst amount = some m') : AllStep m m' := by
  obtain ⟨X, he, hs⟩ := transfer_frame h
  have : m' = m.setReserve asset X ∨ True := Or.inr trivial
  intro b
  rw [he, Function.update_apply]
  split_ifs with hb
  · subst hb; exact hs
  · exact ReserveState.Step.refl _

/-! ## `mintToTreasury` -/

theorem mintToTreasuryOne_allStep {m m' : Market A R} {env : Env R} {a : R}
    (h : m.mintToTreasuryOne env a = some m') : AllStep m m' := by
  unfold mintToTreasuryOne at h
  dsimp only at h
  by_cases h1 : (!(m.config a).active) = true
  · rw [if_pos h1] at h; cases h; exact AllStep.refl _
  rw [if_neg h1] at h
  by_cases h2 : (m.reserves a).accruedToTreasury = 0
  · rw [if_pos h2] at h; cases h; exact AllStep.refl _
  rw [if_neg h2] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ni, -, -, -, res, hmint, rfl⟩ := h
  apply AllStep.setReserve
  obtain ⟨-, e1, -⟩ := ScaledToken.mintScaled_eq_some hmint
  refine ⟨?_, rfl, rfl, fun hw => ⟨ScaledToken.WF_mintScaled hw.1 hmint, hw.2⟩⟩
  unfold ReserveState.Backed
  simp only [e1, Nat.add_zero]
  omega

theorem mintToTreasury_allStep {env : Env R} :
    ∀ {assets : List R} {m m' : Market A R}, m.mintToTreasury env assets = some m' → AllStep m m'
  | [], m, m', h => by cases h; exact AllStep.refl _
  | a :: as, m, m', h => by
    cases h1 : m.mintToTreasuryOne env a with
    | none => simp [mintToTreasury, h1] at h
    | some m1 =>
      simp only [mintToTreasury, List.foldlM_cons, h1] at h
      exact (mintToTreasuryOne_allStep h1).trans (mintToTreasury_allStep h)

/-! ## Liquidation legs -/

theorem burnDebtTokens_step {irs : Strategy} {r r' : ReserveState A} {c c' : ReserveCache}
    {borrower : A} {debt actual : ℕ} {noColl nm : Bool}
    (h : burnDebtTokens irs r c borrower debt actual noColl = some (r', c', nm))
    (hB : c.nextVariableBorrowIndex = r.variableBorrowIndex) : ReserveState.Step r r' := by
  unfold burnDebtTokens at h
  simp only [Option.bind_eq_some_iff, Option.ite_none_left_eq_some, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, hda, r2, hr2, r3, hr3, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, -, -⟩ := he
  obtain ⟨lr, vr, v, rfl, hv⟩ := ReserveState.updateInterestRates_spec hr3
  -- the deficit write
  obtain ⟨δ, hd, ha, hvt, hi, hb, htr, hvb, hδ⟩ : ∃ δ, r2.deficit = t.1.deficit + δ ∧
      r2.aToken = t.1.aToken ∧ r2.vToken = t.1.vToken ∧
      r2.liquidityIndex = t.1.liquidityIndex ∧ r2.variableBorrowIndex = t.1.variableBorrowIndex ∧
      r2.accruedToTreasury = t.1.accruedToTreasury ∧
      r2.virtualUnderlyingBalance = t.1.virtualUnderlyingBalance ∧
      ((δ = 0 ∧ (noColl = false ∨ debt = actual)) ∨ (noColl = true ∧ δ = debt - actual)) := by
    by_cases hc : noColl = true ∧ debt - actual ≠ 0
    · rw [if_pos hc] at hr2
      split_ifs at hr2
      cases hr2
      exact ⟨debt - actual, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨hc.1, rfl⟩⟩
    · rw [if_neg hc] at hr2
      cases hr2
      refine ⟨0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, ?_⟩⟩
      cases noColl
      · exact Or.inl rfl
      · exact Or.inr (by simp at hc; omega)
  -- the debt token burn
  obtain ⟨sd, e1, e2, e3, e4, e5, e6, e7, hsd, hwf⟩ : ∃ sd, t.1.aToken = r.aToken ∧
      t.1.deficit = r.deficit ∧ t.1.liquidityIndex = r.liquidityIndex ∧
      t.1.variableBorrowIndex = r.variableBorrowIndex ∧
      t.1.accruedToTreasury = r.accruedToTreasury ∧
      t.1.virtualUnderlyingBalance = r.virtualUnderlyingBalance ∧
      t.1.vToken.totalSupply + sd = r.vToken.totalSupply ∧
      sd * r.variableBorrowIndex ≤ (if noColl = true then debt else actual) * RAY ∧
      (r.TokensWF → t.1.TokensWF) := by
    by_cases hdz : debt ≠ 0
    · rw [if_pos hdz] at ht
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at ht
      obtain ⟨sd, hsd, res, hburn, rfl⟩ := ht
      rw [hB] at hsd hburn
      obtain ⟨-, -, hle, e1, -⟩ := ScaledToken.burnScaled_eq_some hburn
      exact ⟨sd, rfl, rfl, rfl, rfl, rfl, rfl, by simp only [e1]; omega,
        (rayDivFloor_bounds hsd).1, fun hw => ⟨hw.1, ScaledToken.WF_burnScaled hw.2 hburn⟩⟩
    · rw [if_neg hdz] at ht
      cases ht
      have : actual = 0 := by omega
      subst this
      refine ⟨0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp, id⟩
  refine ⟨?_, by simp only [hi, e3], by simp only [hb, e4], fun hw => ?_⟩
  · unfold ReserveState.Backed
    simp only [hd, ha, hvt, hi, hb, htr, e1, e2, e3, e4, e5]
    have hvv : v = r.virtualUnderlyingBalance + actual := by rw [hvb, e6] at hv; omega
    subst hvv
    have hk : (if noColl = true then debt else actual) * RAY ≤ actual * RAY + δ * RAY := by
      rw [← Nat.add_mul]; apply Nat.mul_le_mul_right
      rcases hδ with ⟨rfl, h0 | h0⟩ | ⟨h0, rfl⟩ <;> simp [h0] <;> omega
    have e8 : r.vToken.totalSupply * r.variableBorrowIndex =
        t.1.vToken.totalSupply * r.variableBorrowIndex + sd * r.variableBorrowIndex := by
      rw [← Nat.add_mul, e7]
    simp only [Nat.add_mul] at *
    omega
  · obtain ⟨h1, h2⟩ := hwf hw
    exact ⟨by simp only [ha]; exact e1 ▸ h1, by simp only [hvt]; exact h2⟩

theorem liquidateCollateral_allStep {m m' : Market A R} {env : Env R} {collAsset debtAsset : R}
    {borrower liquidator : A} {recv : Bool} {cc1 : ReserveCache} {nsd collLiq : ℕ}
    (h : m.liquidateCollateral env collAsset debtAsset borrower liquidator recv cc1 nsd collLiq =
      some m')
    (hI : cc1.nextLiquidityIndex = (m.reserves collAsset).liquidityIndex) : AllStep m m' := by
  unfold liquidateCollateral at h
  by_cases hr : recv = true
  · rw [if_pos hr] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨st, -, a', ha', rfl⟩ := h
    apply AllStep.setReserve
    obtain ⟨e1, -, -⟩ := ScaledToken.transferScaled_eq_some ha'
    refine ⟨?_, rfl, rfl, fun hw => ⟨ScaledToken.WF_transferScaled hw.1 ha', hw.2⟩⟩
    unfold ReserveState.Backed; simp only [e1]; omega
  · rw [if_neg hr] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨rc2, hr2, sb, hsb, res, hburn, rfl⟩ := h
    apply AllStep.setReserve
    obtain ⟨lr, vr, v, rfl, hv⟩ := ReserveState.updateInterestRates_spec hr2
    rw [hI] at hsb hburn
    have hb := (rayDivCeil_bounds hsb).1
    obtain ⟨-, -, hle, e1, -⟩ := ScaledToken.burnScaled_eq_some hburn
    refine ⟨?_, rfl, rfl, fun hw => ⟨ScaledToken.WF_burnScaled hw.1 hburn, hw.2⟩⟩
    unfold ReserveState.Backed
    simp only [e1]
    have e2 : (m.reserves collAsset).aToken.totalSupply * (m.reserves collAsset).liquidityIndex =
        ((m.reserves collAsset).aToken.totalSupply - sb) * (m.reserves collAsset).liquidityIndex +
          sb * (m.reserves collAsset).liquidityIndex := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hle]
    have e3 : (m.reserves collAsset).virtualUnderlyingBalance * RAY = v * RAY + collLiq * RAY := by
      rw [← Nat.add_mul, hv, Nat.add_zero]
    simp only [Nat.add_mul]
    omega

theorem transferLiquidationFee_allStep {m m' : Market A R} {collAsset : R} {borrower : A}
    {idx fee : ℕ} (h : m.transferLiquidationFee collAsset borrower idx fee = some m') :
    AllStep m m' := by
  unfold transferLiquidationFee at h
  split_ifs at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨-, -, sf, -, a', ha', rfl⟩ := h
    apply AllStep.setReserve
    obtain ⟨e1, -, -⟩ := ScaledToken.transferScaled_eq_some ha'
    refine ⟨?_, rfl, rfl, fun hw => ⟨ScaledToken.WF_transferScaled hw.1 ha', hw.2⟩⟩
    unfold ReserveState.Backed; simp only [e1]; omega
  · cases h; exact AllStep.refl _

/-! ## Liquidation -/

theorem _root_.QEDefi.Aave.ReserveState.updateState_of_fresh {cfg : ReserveConfig}
    {r : ReserveState A} {now : ℕ} (h : r.lastUpdateTimestamp = now % TS40) :
    r.updateState (r.cache cfg) now = some (r, r.cache cfg) := by
  unfold ReserveState.updateState; simp [ReserveState.cache, h]

/-- The post-validation part of a liquidation is an `AllStep` from the state `M2` in which both
reserves are up to date. -/
theorem liquidation_tail_allStep {M2 M3 m5 m6 m' : Market A R} {env : Env R}
    {collAsset debtAsset : R} {borrower liquidator : A} {recv : Bool} {cd1 cc1 : ReserveCache}
    {bd actual collLiq fee : ℕ} {noColl : Bool}
    {dres : ReserveState A × ReserveCache × Bool}
    (hM3 : M3.reserves = M2.reserves)
    (hdres : burnDebtTokens (env.irs debtAsset) (M3.reserves debtAsset) cd1 borrower bd actual noColl =
      some dres)
    (hm5 : m5.reserves = (M3.setReserve debtAsset dres.1).reserves)
    (hm6 : m5.liquidateCollateral env collAsset debtAsset borrower liquidator recv cc1
      dres.2.1.nextScaledVariableDebt collLiq = some m6)
    (hm7 : m6.transferLiquidationFee collAsset borrower cc1.nextLiquidityIndex fee = some m')
    (hB : cd1.nextVariableBorrowIndex = (M2.reserves debtAsset).variableBorrowIndex)
    (hI : cc1.nextLiquidityIndex = (M2.reserves collAsset).liquidityIndex) :
    AllStep M2 m' := by
  rw [hM3] at hdres
  have s1 : ReserveState.Step (M2.reserves debtAsset) dres.1 := burnDebtTokens_step hdres hB
  have a5 : AllStep M2 m5 := by
    intro b
    rw [hm5, reserves_setReserve, hM3, Function.update_apply]
    split_ifs with hb
    · subst hb; exact s1
    · exact ReserveState.Step.refl _
  have hI5 : cc1.nextLiquidityIndex = (m5.reserves collAsset).liquidityIndex := by
    rw [hI, (a5 collAsset).liquidityIndex]
  exact (a5.trans (liquidateCollateral_allStep hm6 hI5)).trans (transferLiquidationFee_allStep hm7)

theorem liquidationCall_reaches {m m' : Market A R} {env : Env R} {collAsset debtAsset : R}
    {borrower liquidator : A} {dtc : ℕ} {recv : Bool}
    (h : m.liquidationCall env collAsset debtAsset borrower liquidator dtc recv = some m') :
    Reaches m env.now m' := by
  unfold liquidationCall at h
  dsimp only at h
  obtain ⟨⟨rd1, cd1⟩, hud, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨rc1, cc1⟩, huc, h⟩ := Option.bind_eq_some_iff.1 h
  dsimp only at huc h
  set M2 := (m.setReserve debtAsset rd1).setReserve collAsset rc1 with hM2
  obtain ⟨ad, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨collBal, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨bd, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨cdf, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  obtain ⟨dres, hdres, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨m6, hm6, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨m7, hm7, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨-, h⟩ := Option.ite_none_left_eq_some.1 h
  cases h
  obtain ⟨dI, dB, dT, rfl, -, -, -, ecd1, ecd2, -⟩ := ReserveState.updateState_spec hud
  -- both reserves are now up to date in `M2`
  have hfacts : (M2.reserves debtAsset).variableBorrowIndex = cd1.nextVariableBorrowIndex ∧
      (M2.reserves collAsset).liquidityIndex = cc1.nextLiquidityIndex ∧
      ∀ b, ∃ r1, (r1 = m.reserves b ∨ ∃ c1, (m.reserves b).updateState
        ((m.reserves b).cache (m.config b)) env.now = some (r1, c1)) ∧ M2.reserves b = r1 := by
    by_cases hcd : collAsset = debtAsset
    · subst hcd
      simp only [reserves_setReserve, Function.update_self] at huc
      rw [ReserveState.updateState_of_fresh rfl] at huc
      cases huc
      refine ⟨by simp [hM2, ecd2], by simp [hM2, ReserveState.cache], fun b => ?_⟩
      by_cases hb : b = collAsset
      · subst hb; exact ⟨_, Or.inr ⟨cd1, hud⟩, by simp [hM2]⟩
      · exact ⟨m.reserves b, Or.inl rfl, by simp [hM2, Function.update_of_ne hb]⟩
    · simp only [reserves_setReserve, Function.update_of_ne hcd] at huc
      obtain ⟨cI, cB, cT, rfl, -, -, -, ecc1, -⟩ := ReserveState.updateState_spec huc
      refine ⟨by simp [hM2, Function.update_of_ne (Ne.symm hcd), ecd2],
        by simp [hM2, ecc1], fun b => ?_⟩
      by_cases hb : b = collAsset
      · subst hb; exact ⟨_, Or.inr ⟨cc1, huc⟩, by simp [hM2]⟩
      · by_cases hb' : b = debtAsset
        · subst hb'; exact ⟨_, Or.inr ⟨cd1, hud⟩, by simp [hM2, Function.update_of_ne hb]⟩
        · exact ⟨m.reserves b, Or.inl rfl,
            by simp [hM2, Function.update_of_ne hb, Function.update_of_ne hb']⟩
  obtain ⟨hB, hI, hM⟩ := hfacts
  have hall : AllStep M2 m' := by
    split_ifs at hdres hm6 <;>
      exact liquidation_tail_allStep (by simp) hdres (by simp) hm6 hm7 hB.symm hI.symm
  intro b
  obtain ⟨r1, hr1, he⟩ := hM b
  exact ⟨r1, hr1, he ▸ hall b⟩

end Market

end QEDefi.Aave
end

end
