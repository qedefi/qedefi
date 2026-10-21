import QEDefi.ERC20.Rep
import EvmLogic.Solidity.ERC20Oz

/-!
# OpenZeppelin's word-level operations and `Token`'s `oz*` operations

The word-level `ERC20.Model.oz*` (OpenZeppelin v5, `EvmLogic.Solidity.ERC20Oz`) and the `ℕ`
ledger operations `Token.oz*` succeed together (`*_isSome_iff`) and, on a `Token.WF` ledger,
with related results (`rep_*`): the unchecked additions do not wrap while balances sum to a
supply `≤ MAX`.
-/

namespace QEDefi.ERC20

open EvmLean EvmLogic EvmLogic.Solidity QEDefi.Math

variable {s s' : ERC20.State} {t t' : Token Address}

theorem toNat_le_MAX (x : Word) : x.toNat ≤ MAX := by
  have := x.isLt; unfold MAX; omega

/-! ## `transfer` -/

theorem ozTransfer_eq_transfer (t : Token Address) {c d : Address} (hc : c ≠ 0) (hd : d ≠ 0)
    (v : ℕ) : t.ozTransfer c d v = t.transfer c d v := by
  simp only [Token.ozTransfer, Token.ozUpdate, Token.transfer, hc, hd, ↓reduceIte]
  by_cases h : t.balanceOf c < v <;> simp [h]

theorem ozTransfer_isSome_iff (hr : Rep s t) (c d : Address) (amount : Word) :
    (ERC20.Model.ozTransfer s c d amount).isSome ↔ (t.ozTransfer c d amount.toNat).isSome := by
  by_cases hc : c = 0
  · simp [ERC20.Model.ozTransfer, Token.ozTransfer, hc]
  by_cases hd : d = 0
  · simp [ERC20.Model.ozTransfer, Token.ozTransfer, hd]
  rw [ozTransfer_eq_transfer t hc hd]
  simp only [ERC20.Model.ozTransfer, hc, hd, ↓reduceIte]
  exact transfer_isSome_iff hr c d amount

/-- On a well-formed ledger, `Model.ozTransfer` and `Token.ozTransfer` have related results. -/
theorem rep_ozTransfer (hr : Rep s t) (hw : t.WF) {c d : Address} {amount : Word}
    (hm : ERC20.Model.ozTransfer s c d amount = some s')
    (ht : t.ozTransfer c d amount.toNat = some t') : Rep s' t' := by
  unfold ERC20.Model.ozTransfer at hm
  split at hm
  · cases hm
  rename_i hc
  split at hm
  · cases hm
  rename_i hd
  rw [ozTransfer_eq_transfer t hc hd] at ht
  exact rep_transfer hr hw hm ht

/-! ## `approve` -/

theorem ozApprove_isSome_iff (o sp : Address) (x : Word) (n : ℕ) :
    (ERC20.Model.ozApprove s o sp x).isSome ↔ (t.ozApprove o sp n).isSome := by
  unfold ERC20.Model.ozApprove Token.ozApprove
  by_cases ho : o = 0
  · subst ho; simp
  by_cases hs : sp = 0
  · subst hs; simp
  simp only [ho, hs, ↓reduceIte, Option.isSome_some]

/-- `Model.ozApprove` and `Token.ozApprove` of corresponding values have related results. -/
theorem rep_ozApprove (hr : Rep s t) {o sp : Address} {x : Word} {n : ℕ} (hx : x.toNat = n)
    (hm : ERC20.Model.ozApprove s o sp x = some s') (ht : t.ozApprove o sp n = some t') :
    Rep s' t' := by
  unfold ERC20.Model.ozApprove at hm
  unfold Token.ozApprove at ht
  split at hm
  · cases hm
  rename_i ho
  split at hm
  · cases hm
  rename_i hs
  simp only [ho, hs, ↓reduceIte, Option.some.injEq] at ht
  cases hm; subst ht; subst hx
  exact rep_approve hr o sp x

/-! ## `spend` and `transferFrom` -/

theorem ozSpend_isSome_iff (hr : Rep s t) (o sp : Address) (amount : Word) :
    (ERC20.Model.ozSpend s o sp amount).isSome ↔ (t.ozSpend o sp amount.toNat).isSome := by
  unfold ERC20.Model.ozSpend Token.ozSpend
  have ha := hr.allowance o sp trivial
  have hle := toNat_le_MAX (s.allowance o sp)
  by_cases hmax : s.allowance o sp = ERC20.maxWord
  · have : ¬ t.allowance o sp < MAX := by rw [← ha, (eq_maxWord_iff _).1 hmax]; omega
    simp [hmax, this]
  · have hmax' : t.allowance o sp < MAX := by
      rw [← ha]
      have : (s.allowance o sp).toNat ≠ MAX := fun h => hmax ((eq_maxWord_iff _).2 h)
      omega
    simp only [hmax, ↓reduceIte, hmax']
    by_cases h : amount.toNat ≤ (s.allowance o sp).toNat
    · simp only [h, ↓reduceIte, show ¬ t.allowance o sp < amount.toNat by omega]
      exact ozApprove_isSome_iff o sp _ _
    · simp [h, show t.allowance o sp < amount.toNat by omega]

theorem rep_ozSpend (hr : Rep s t) {o sp : Address} {amount : Word}
    (hm : ERC20.Model.ozSpend s o sp amount = some s')
    (ht : t.ozSpend o sp amount.toNat = some t') : Rep s' t' := by
  unfold ERC20.Model.ozSpend at hm
  unfold Token.ozSpend at ht
  have ha := hr.allowance o sp trivial
  have hle := toNat_le_MAX (s.allowance o sp)
  by_cases hmax : s.allowance o sp = ERC20.maxWord
  · have : ¬ t.allowance o sp < MAX := by rw [← ha, (eq_maxWord_iff _).1 hmax]; omega
    simp only [hmax, ↓reduceIte, Option.some.injEq] at hm
    simp only [this, ↓reduceIte, Option.some.injEq] at ht
    subst hm ht; exact hr
  · have hmax' : t.allowance o sp < MAX := by
      rw [← ha]
      have : (s.allowance o sp).toNat ≠ MAX := fun h => hmax ((eq_maxWord_iff _).2 h)
      omega
    simp only [hmax, ↓reduceIte] at hm
    simp only [hmax', ↓reduceIte] at ht
    split at hm
    · rename_i h
      simp only [show ¬ t.allowance o sp < amount.toNat by omega, ↓reduceIte] at ht
      refine rep_ozApprove hr ?_ hm ht
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 h), ha]
    · cases hm

theorem ozTransferFrom_isSome_iff (hr : Rep s t) (sp src dst : Address) (amount : Word) :
    (ERC20.Model.ozTransferFrom s sp src dst amount).isSome ↔
      (t.ozTransferFrom sp src dst amount.toNat).isSome := by
  unfold ERC20.Model.ozTransferFrom Token.ozTransferFrom
  cases h1 : ERC20.Model.ozSpend s src sp amount with
  | none =>
    have h2 : t.ozSpend src sp amount.toNat = none := by
      have := ozSpend_isSome_iff hr src sp amount
      rw [h1] at this
      simpa using this
    simp [h2]
  | some s₁ =>
    obtain ⟨t₁, h2⟩ : ∃ t₁, t.ozSpend src sp amount.toNat = some t₁ := by
      have := (ozSpend_isSome_iff hr src sp amount).1 (by simp [h1])
      exact Option.isSome_iff_exists.1 this
    simp only [Option.bind_some, h2]
    exact ozTransfer_isSome_iff (rep_ozSpend hr h1 h2) src dst amount

/-- On a well-formed ledger, `Model.ozTransferFrom` and `Token.ozTransferFrom` have related
results. -/
theorem rep_ozTransferFrom (hr : Rep s t) (hw : t.WF) {sp src dst : Address} {amount : Word}
    (hm : ERC20.Model.ozTransferFrom s sp src dst amount = some s')
    (ht : t.ozTransferFrom sp src dst amount.toNat = some t') : Rep s' t' := by
  unfold ERC20.Model.ozTransferFrom at hm
  unfold Token.ozTransferFrom at ht
  obtain ⟨s₁, h1, h2⟩ := Option.bind_eq_some_iff.1 hm
  obtain ⟨t₁, h3, h4⟩ := Option.bind_eq_some_iff.1 ht
  exact rep_ozTransfer (rep_ozSpend hr h1 h3) (Token.WF_ozSpend hw h3) h2 h4

/-! ## `mint` and `burn` -/

theorem ozMint_isSome_iff (hr : Rep s t) (d : Address) (amount : Word) :
    (ERC20.Model.ozMint s d amount).isSome ↔ (t.ozMint d amount.toNat).isSome := by
  unfold ERC20.Model.ozMint Token.ozMint Token.ozUpdate
  by_cases hd : d = 0
  · subst hd; simp
  have hts := hr.totalSupply
  by_cases h : s.totalSupply.toNat + amount.toNat < 2 ^ 256
  · simp only [hd, h, ↓reduceIte, show ¬ MAX < t.totalSupply + amount.toNat by unfold MAX; omega,
      Option.map_some, Option.isSome_some]
  · simp only [hd, h, ↓reduceIte, show MAX < t.totalSupply + amount.toNat by unfold MAX; omega,
      Option.map_none, Option.isSome_none]

/-- On a well-formed ledger, `Model.ozMint` and `Token.ozMint` have related results. -/
theorem rep_ozMint (hr : Rep s t) (hw : t.WF) {d : Address} {amount : Word}
    (hm : ERC20.Model.ozMint s d amount = some s') (ht : t.ozMint d amount.toNat = some t') :
    Rep s' t' := by
  unfold ERC20.Model.ozMint at hm
  unfold Token.ozMint Token.ozUpdate at ht
  split at hm
  · cases hm
  rename_i hd
  split at hm
  · rename_i hov
    cases hm
    have hts := hr.totalSupply
    simp only [hd, ↓reduceIte, show ¬ MAX < t.totalSupply + amount.toNat by unfold MAX; omega,
      Option.map_some, Option.some.injEq] at ht
    subst ht
    have hle := Token.balanceOf_le_totalSupply hw d
    refine ⟨?_, fun b => ?_, fun o sp _ => hr.allowance o sp trivial⟩
    · show (amount + s.totalSupply).toNat = t.totalSupply + amount.toNat
      rw [BitVec.toNat_add, hts, Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [ERC20.State.setBalance]
      rw [Token.add_single_apply]
      by_cases hb : b = d
      · subst hb
        simp only [↓reduceIte]
        rw [BitVec.toNat_add, hr.balanceOf b, Nat.mod_eq_of_lt (by omega)]
        omega
      · simp only [hb, Ne.symm hb, ↓reduceIte]
        exact hr.balanceOf b
  · cases hm

theorem ozBurn_isSome_iff (hr : Rep s t) (src : Address) (amount : Word) :
    (ERC20.Model.ozBurn s src amount).isSome ↔ (t.ozBurn src amount.toNat).isSome := by
  unfold ERC20.Model.ozBurn Token.ozBurn Token.ozUpdate
  by_cases hs : src = 0
  · subst hs; simp
  have hb := hr.balanceOf src
  by_cases h : amount.toNat ≤ (s.balanceOf src).toNat
  · simp only [hs, h, ↓reduceIte, show ¬ t.balanceOf src < amount.toNat by omega,
      Option.map_some, Option.isSome_some]
  · simp only [hs, h, ↓reduceIte, show t.balanceOf src < amount.toNat by omega,
      Option.map_none, Option.isSome_none]

/-- On a well-formed ledger, `Model.ozBurn` and `Token.ozBurn` have related results. -/
theorem rep_ozBurn (hr : Rep s t) (hw : t.WF) {src : Address} {amount : Word}
    (hm : ERC20.Model.ozBurn s src amount = some s') (ht : t.ozBurn src amount.toNat = some t') :
    Rep s' t' := by
  unfold ERC20.Model.ozBurn at hm
  unfold Token.ozBurn Token.ozUpdate at ht
  split at hm
  · cases hm
  rename_i hs
  split at hm
  · rename_i hv
    cases hm
    have hbs := hr.balanceOf src
    simp only [hs, ↓reduceIte, show ¬ t.balanceOf src < amount.toNat by omega,
      Option.map_some, Option.some.injEq] at ht
    subst ht
    have hle := Token.balanceOf_le_totalSupply hw src
    refine ⟨?_, fun b => ?_, fun o sp _ => hr.allowance o sp trivial⟩
    · show (s.totalSupply - amount).toNat = t.totalSupply - amount.toNat
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 (by rw [hr.totalSupply]; omega)),
        hr.totalSupply]
    · simp only [ERC20.State.setBalance]
      rw [Token.sub_single_apply]
      by_cases hb : b = src
      · subst hb
        simp only [↓reduceIte]
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hv), hbs]
      · simp only [hb, Ne.symm hb, ↓reduceIte]
        exact hr.balanceOf b
  · cases hm

end QEDefi.ERC20
