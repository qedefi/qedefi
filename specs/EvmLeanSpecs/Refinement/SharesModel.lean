import EvmLeanSpecs.Vault.Token
import EvmLeanProofs.Solidity.SharesExtraErc20

/-!
# Word-level ERC-20 states and `Token` ledgers

The bytecode theorems (`SharesTransfer`, …) are stated on the word-level storage view
`Erc20.view` and its models `Erc20.Model.transfer` / `approve` / `spend` / `transferFrom`
(`EvmLeanProofs.Solidity.Erc20`, `SharesExtraErc20`). The abstract vault (`EvmLeanSpecs.Vault`)
keeps its share ledger as a `Token Address` (`ℕ` balances, `Finsupp`). This file relates the
two:

* `RepOn P s t`: the ledger `t` is the word-level state `s` (`toNat` of every field), for the
  allowance entries satisfying `P` (frames over nested mappings are only available pointwise,
  see `EvmLeanProofs.Solidity.Keccak`); `Rep` is the case `P = ⊤`.
* `rep_transfer`, `rep_approve`, `rep_spend`, `rep_transferFrom`: the word-level operation and
  the `Token` operation succeed together, and their results are again related. Word arithmetic
  is wrapping, `Token` arithmetic is in `ℕ`; they agree on well-formed ledgers (`Token.WF`:
  balances sum to `totalSupply ≤ MAX`), which bound every credited balance.

Nothing here is specific to the vault: it applies to any Solmate `ERC20` (e.g. the asset).
-/

namespace EvmLeanSpecs.Refinement.Shares

open EvmLean EvmLean.Solidity EvmLeanSpecs.Vault

/-- The ℕ-valued ledger `t` is the word-valued ERC-20 state `s`, for the allowance entries
satisfying `P`. -/
structure RepOn (P : Address → Address → Prop) (s : Erc20.State) (t : Token Address) : Prop where
  /-- `totalSupply` agrees. -/
  totalSupply : s.totalSupply.toNat = t.totalSupply
  /-- Every balance agrees. -/
  balanceOf : ∀ a, (s.balanceOf a).toNat = t.balanceOf a
  /-- The allowances satisfying `P` agree. -/
  allowance : ∀ o sp, P o sp → (s.allowance o sp).toNat = t.allowance o sp

/-- `t` is the word-valued state `s`, everywhere. -/
abbrev Rep (s : Erc20.State) (t : Token Address) : Prop := RepOn (fun _ _ => True) s t

/-- Weakening the allowance predicate. -/
theorem RepOn.mono {P Q : Address → Address → Prop} {s : Erc20.State} {t : Token Address}
    (h : RepOn P s t) (hPQ : ∀ o sp, Q o sp → P o sp) : RepOn Q s t :=
  ⟨h.totalSupply, h.balanceOf, fun o sp hq => h.allowance o sp (hPQ o sp hq)⟩

/-- A view that agrees with `s'` (allowances on `P`) represents what `s'` represents. -/
theorem RepOn.of_eq {P : Address → Address → Prop} {v s' : Erc20.State} {t' : Token Address}
    (h1 : v.totalSupply = s'.totalSupply) (h2 : v.balanceOf = s'.balanceOf)
    (h3 : ∀ o sp, P o sp → v.allowance o sp = s'.allowance o sp) (hr : Rep s' t') :
    RepOn P v t' :=
  ⟨h1 ▸ hr.totalSupply, fun a => h2 ▸ hr.balanceOf a,
    fun o sp hp => (h3 o sp hp) ▸ hr.allowance o sp trivial⟩

/-! ## Arithmetic -/

/-- Two distinct balances fit in the total. -/
theorem add_le_total {f : Address →₀ ℕ} {a b : Address} (h : a ≠ b) : f a + f b ≤ total f := by
  have h1 := Token.total_sub_single (f := f) (a := a) (v := f a) le_rfl
  have h2 := Token.le_total (f - Finsupp.single a (f a)) b
  simp only [Token.sub_single_apply, h, ↓reduceIte] at h2
  have h3 := Token.le_total f a
  omega

/-- `type(uint256).max` as a word. -/
theorem toNat_maxWord : Erc20.maxWord.toNat = MAX := by
  simp [Erc20.maxWord, MAX]

/-- A word is `type(uint256).max` iff its value is `MAX`. -/
theorem eq_maxWord_iff (x : Word) : x = Erc20.maxWord ↔ x.toNat = MAX := by
  constructor
  · rintro rfl; exact toNat_maxWord
  · intro h; apply BitVec.eq_of_toNat_eq; rw [h, toNat_maxWord]

/-! ## `transfer` -/

/-- `Model.transfer` and `Token.transfer` succeed together. -/
theorem transfer_isSome_iff {s : Erc20.State} {t : Token Address} (hr : Rep s t)
    (c d : Address) (amount : Word) :
    (Erc20.Model.transfer s c d amount).isSome ↔ (t.transfer c d amount.toNat).isSome := by
  unfold Erc20.Model.transfer Token.transfer
  rw [hr.balanceOf c]
  by_cases h : amount.toNat ≤ t.balanceOf c
  · simp [h, Nat.not_lt.2 h]
  · simp [h, Nat.lt_of_not_le h]

/-- **`transfer` refinement of the models**: on a well-formed ledger, the results of
`Model.transfer` and `Token.transfer` are related (the word additions do not wrap). -/
theorem rep_transfer {s s' : Erc20.State} {t t' : Token Address} (hr : Rep s t) (hw : t.WF)
    {c d : Address} {amount : Word} (hm : Erc20.Model.transfer s c d amount = some s')
    (ht : t.transfer c d amount.toNat = some t') : Rep s' t' := by
  obtain ⟨hv, rfl⟩ := Token.transfer_eq_some.1 ht
  have hal := Erc20.Model.transfer_allowance hm
  have hts := Erc20.Model.transfer_totalSupply hm
  unfold Erc20.Model.transfer at hm
  simp only [show amount.toNat ≤ (s.balanceOf c).toNat by rw [hr.balanceOf c]; exact hv,
    ↓reduceIte] at hm
  cases hm
  refine ⟨hr.totalSupply, ?_, fun o sp _ => hr.allowance o sp trivial⟩
  intro b
  have hsub : (s.balanceOf c - amount).toNat = t.balanceOf c - amount.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 (by rw [hr.balanceOf c]; exact hv)), hr.balanceOf c]
  simp only [Erc20.State.setBalance]
  rw [Token.add_single_apply, Token.sub_single_apply]
  by_cases hbd : b = d
  · subst hbd
    by_cases hcd : c = b
    · subst hcd
      simp only [↓reduceIte]
      rw [BitVec.sub_add_cancel, hr.balanceOf c]
      omega
    · simp only [↓reduceIte, hcd, show ¬ b = c from Ne.symm hcd]
      rw [BitVec.toNat_add, hr.balanceOf b]
      have hle := add_le_total (f := t.balanceOf) hcd
      have : t.balanceOf b + amount.toNat < 2 ^ 256 := by
        have := hw.1; have := hw.2; unfold MAX at *; omega
      rw [Nat.mod_eq_of_lt this]
  · simp only [hbd, Ne.symm hbd, ↓reduceIte]
    by_cases hbc : b = c
    · subst hbc; simp only [↓reduceIte]; exact hsub
    · simp only [hbc, Ne.symm hbc, ↓reduceIte]; exact hr.balanceOf b

/-! ## `approve` -/

/-- **`approve` refinement of the models.** -/
theorem rep_approve {s : Erc20.State} {t : Token Address} (hr : Rep s t) (o sp : Address)
    (amount : Word) : Rep (Erc20.Model.approve s o sp amount) (t.approve o sp amount.toNat) := by
  refine ⟨hr.totalSupply, hr.balanceOf, fun o' sp' _ => ?_⟩
  simp only [Erc20.Model.approve, Erc20.State.setAllowance, Token.approve, Token.setAllowance,
    Function.update_apply]
  by_cases h1 : o' = o <;> by_cases h2 : sp' = sp <;> simp [h1, h2, hr.allowance _ _ trivial]

/-! ## `spend` and `transferFrom` -/

/-- `Model.spend` and `Token.spend` succeed together. -/
theorem spend_isSome_iff {s : Erc20.State} {t : Token Address} (hr : Rep s t)
    (o sp : Address) (amount : Word) :
    (Erc20.Model.spend s o sp amount).isSome ↔ (t.spend o sp amount.toNat).isSome := by
  unfold Erc20.Model.spend Token.spend
  simp only [eq_maxWord_iff, hr.allowance o sp trivial]
  by_cases hm : t.allowance o sp = MAX
  · simp [hm]
  · by_cases h : amount.toNat ≤ t.allowance o sp
    · simp [hm, h, Nat.not_lt.2 h]
    · simp [hm, h, Nat.lt_of_not_le h]

/-- **The allowance step, models.** -/
theorem rep_spend {s s₁ : Erc20.State} {t t₁ : Token Address} (hr : Rep s t)
    {o sp : Address} {amount : Word} (hm : Erc20.Model.spend s o sp amount = some s₁)
    (ht : t.spend o sp amount.toNat = some t₁) : Rep s₁ t₁ := by
  unfold Erc20.Model.spend at hm
  unfold Token.spend at ht
  have ha := hr.allowance o sp trivial
  by_cases hmax : s.allowance o sp = Erc20.maxWord
  · have hmax' : t.allowance o sp = MAX := by rw [← ha, (eq_maxWord_iff _).1 hmax]
    simp only [hmax, ↓reduceIte, Option.some.injEq] at hm
    simp only [hmax', ↓reduceIte, Option.some.injEq] at ht
    subst hm ht; exact hr
  · have hmax' : t.allowance o sp ≠ MAX := by rw [← ha]; exact fun h => hmax ((eq_maxWord_iff _).2 h)
    simp only [hmax, ↓reduceIte] at hm
    simp only [hmax', ↓reduceIte] at ht
    split at hm
    · rename_i hle
      cases hm
      simp only [show ¬ t.allowance o sp < amount.toNat by rw [← ha]; omega, ↓reduceIte] at ht
      cases ht
      refine ⟨hr.totalSupply, hr.balanceOf, fun o' sp' _ => ?_⟩
      simp only [Erc20.State.setAllowance, Token.setAllowance, Function.update_apply]
      by_cases h1 : o' = o <;> by_cases h2 : sp' = sp
      · subst h1 h2
        simp only [and_self, ↓reduceIte, Function.update_self]
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hle), ha]
      all_goals
        simp only [h1, h2, and_false, false_and, ↓reduceIte, Function.update_of_ne, ne_eq,
          not_false_eq_true]
        exact hr.allowance _ _ trivial
    · cases hm

/-- **`transferFrom` refinement of the models**: `Model.transferFrom` and
`Token.transferFrom` succeed together, with related results. -/
theorem transferFrom_isSome_iff {s : Erc20.State} {t : Token Address} (hr : Rep s t)
    (sp src dst : Address) (amount : Word) :
    (Erc20.Model.transferFrom s sp src dst amount).isSome ↔
      (t.transferFrom sp src dst amount.toNat).isSome := by
  unfold Erc20.Model.transferFrom Token.transferFrom
  cases h1 : Erc20.Model.spend s src sp amount with
  | none =>
    have h2 : t.spend src sp amount.toNat = none := by
      have := spend_isSome_iff hr src sp amount
      rw [h1] at this
      simpa using this
    simp [h2]
  | some s₁ =>
    obtain ⟨t₁, h2⟩ : ∃ t₁, t.spend src sp amount.toNat = some t₁ := by
      have := (spend_isSome_iff hr src sp amount).1 (by simp [h1])
      exact Option.isSome_iff_exists.1 this
    simp only [Option.bind_some, h2]
    exact transfer_isSome_iff (rep_spend hr h1 h2) src dst amount

/-- **`transferFrom` refinement of the models**: related results. -/
theorem rep_transferFrom {s s' : Erc20.State} {t t' : Token Address} (hr : Rep s t) (hw : t.WF)
    {sp src dst : Address} {amount : Word}
    (hm : Erc20.Model.transferFrom s sp src dst amount = some s')
    (ht : t.transferFrom sp src dst amount.toNat = some t') : Rep s' t' := by
  unfold Erc20.Model.transferFrom at hm
  unfold Token.transferFrom at ht
  obtain ⟨s₁, h1, h2⟩ := Option.bind_eq_some_iff.1 hm
  obtain ⟨t₁, h3, h4⟩ := Option.bind_eq_some_iff.1 ht
  exact rep_transfer (rep_spend hr h1 h3) (Token.WF_spend hw h3) h2 h4

end EvmLeanSpecs.Refinement.Shares
