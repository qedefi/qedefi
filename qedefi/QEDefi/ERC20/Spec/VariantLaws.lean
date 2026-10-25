module

public import QEDefi.ERC20.Spec.Laws
public import QEDefi.ERC20.VariantExtras

/-!
# The laws of the variants

Every law of `Spec/Laws.lean` decided for every `Variant` instance, as a token model
`V.model ev` with an arbitrary event rule `ev` (no law mentions events): ✓ proved, ✗ refuted
with an explicit witness state, well formed (`Variant.WF`) except where noted.

| Instance | `ReturnsTrue` | `NoFalseReturn` | `RevertsOnly` | `ExactMoves` | `SupplyFixed` | `DebitAuth` | `AllowanceAuth` | `WFInvariant` |
|---|---|---|---|---|---|---|---|---|
| `standard` (Solmate) | ✓ | ✓ | ✓ | ✓ all states | ✓ | ✓ | ✓ | ✓ |
| `oz` | ✓ | ✓ | ✓ | ✓ all states | ✓ | ✓ | ✓ | ✓ |
| `solady p` | ✓ | ✓ | ✓ | ✓ all states | ✓ | ✓ | ✓ | ✓ |
| `weth9` | ✓ | ✓ | ✓ | ✓ all states | ✓ | ✓ | ✓ | ✓ |
| `usdt` | ✗ `approve` returns nothing | ✓ | ✗ `INVALID` on short balance | ✓ on `NoFee` (`bps = 0`); ✗ on `WF` (fee to owner) | ✓ | ✓ | ✓ | ✓ |
| `bnb` | ✗ `transfer` returns nothing | ✓ | ✓ | ✓ all states | ✓ | ✓ | ✓ | ✓ |
| `sta` | ✓ | ✓ | ✗ `INVALID` on fee overflow | ✗ on `WF` (burned fee; no state is `NoFee`) | ✗ burned fee | ✓ | ✓ | ✓ |
| `ampl` | ✓ | ✓ | ✓ | ✓ on `0 < scale` ⊇ `WF`; ✗ at scale `0` (not `WF`) | ✓ | ✓ | ✓ | ✓ |

Theorems: `standard_laws`, `oz_laws`, `solady_laws`, `weth9_laws` (the bundle `Standard` in all
states); `usdt_laws`, `bnb_laws`, `sta_laws`, `ampl_laws` (one conjunction per row, refutations
under `[Nontrivial A]`: with one account there is no transfer between distinct accounts and no
recipient `≠ 0`); witnesses `usdt_approve_empty`, `usdt_invalid_witness`, `usdt_fee_witness`,
`bnb_empty_witness`, `sta_invalid_witness`, `sta_fee_witness`, `ampl_scale_zero_witness`.

The generic lemmas, over any `V : Variant A`, make the rows short:

* `law_returnsTrue`: every `returns` is `.bool` and no `returnFalse` convention;
  `law_noFalseReturn`: no `returnFalse` convention; `law_revertsOnly`: guards and arithmetic
  revert and there is no fee (whose SafeMath computation ends in `INVALID`);
* `law_exactMoves`: `ExactMoves (NoFee V)` for **every** variant, rebasing included (a transfer
  of `v` moves `v · scale` gons and `⌊(g ± v·k)/k⌋ = ⌊g/k⌋ ± v`, so AMPL's rounding never shows in
  a `transfer`/`transferFrom`; its dust moves only with `transferAll`, an operation);
* `law_supplyFixed`: no fee, or the fee is paid to the owner;
* `law_debitAuth`, `law_allowanceAuth`: for **every** variant, unconditionally (a fee raises the
  owner's balance and takes from the recipient's credit at most what it received; a deposit
  credits the caller; a `permit` changes only `(owner, spender)` and only when the recovered
  signer is `owner`; the fallback touches no allowance). Note AMPL's zero-owner permit
  (`ampl_permit_zero_owner`) passes `AllowanceAuth` as stated: the failed recovery returns `0`,
  which *is* the owner `0`;
* `law_wfInvariant`: every `Sane` variant.
-/
@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.VariantLaws
open QEDefi.Math Finsupp QEDefi.ERC20 QEDefi.ERC20.Variant

variable {A : Type} [DecidableEq A] [Zero A]

/-! ## Observable outcomes -/

/-- A successful outcome is the state change of the call with its return data, or a
`returnFalse` failure (state unchanged, return data `false`). -/
theorem law_call_eq_ok (V : Variant A) {s s' : VState A} {caller : A} {c : Call A} {r : RetData}
    (h : V.call s caller c = .ok s' r) :
    (V.step s caller c = some s' ∧ r = V.retData c) ∨
      (V.failKind s caller c = .returnFalse ∧ s' = s ∧ r = .word false) := by
  unfold call at h
  cases hs : V.step s caller c with
  | some t =>
    rw [hs] at h
    cases h
    exact Or.inl ⟨rfl, rfl⟩
  | none =>
    rw [hs] at h
    right
    cases hk : V.failKind s caller c <;> rw [hk] at h <;> cases h
    exact ⟨rfl, rfl, rfl⟩

/-- A failure is the failure kind of the call. -/
theorem law_call_eq_halt (V : Variant A) {s : VState A} {caller : A} {c : Call A} {k : Halt}
    (h : V.call s caller c = .halt k) :
    (V.failKind s caller c = .revert ∧ k = .revert) ∨
      (V.failKind s caller c = .invalid ∧ k = .invalid) := by
  unfold call at h
  cases hs : V.step s caller c with
  | some t => rw [hs] at h; cases h
  | none =>
    rw [hs] at h
    cases hk : V.failKind s caller c <;> rw [hk] at h <;> cases h
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

/-- Without a `returnFalse` convention no failure returns `false`. -/
theorem law_failKind_ne_returnFalse (V : Variant A) (hg : V.guardFail ≠ .returnFalse)
    (ha : V.arithFail ≠ .returnFalse) (s : VState A) (caller : A) (c : Call A) :
    V.failKind s caller c ≠ .returnFalse := by
  unfold failKind
  split_ifs
  · exact hg
  · exact nofun
  · exact ha

/-- Without a fee nothing overflows in the fee computation. -/
theorem law_overflows_of_fee_none (V : Variant A) (hf : V.fee = .none) (s : VState A)
    (caller : A) (c : Call A) : V.overflows s caller c = false := by
  cases c <;> simp [overflows, feeOverflow, hf]

omit [DecidableEq A] [Zero A] in
theorem law_retData_ne_false (V : Variant A) (c : Call A) : V.retData c ≠ .word false := by
  cases c <;> simp only [retData] <;> (try split_ifs) <;> nofun

/-! ## Generic laws -/

variable (V : Variant A) (ev : VState A → A → Call A → List (Event A))

/-- **`ReturnsTrue`** for every variant whose three functions return a `bool` and which never
fails by returning `false`. -/
theorem law_returnsTrue (hr : ∀ f, V.returns f = .bool) (hg : V.guardFail ≠ .returnFalse)
    (ha : V.arithFail ≠ .returnFalse) : (V.model ev).ReturnsTrue := by
  intro s caller c s' r hc h
  rcases law_call_eq_ok V h with ⟨-, rfl⟩ | ⟨hk, -, -⟩
  · cases c <;> simp_all [retData, Call.returnsBool]
  · exact absurd hk (law_failKind_ne_returnFalse V hg ha s caller c)

/-- **`NoFalseReturn`** for every variant without a `returnFalse` convention. -/
theorem law_noFalseReturn (hg : V.guardFail ≠ .returnFalse) (ha : V.arithFail ≠ .returnFalse) :
    (V.model ev).NoFalseReturn := by
  intro s caller c s' h
  rcases law_call_eq_ok V h with ⟨-, hr⟩ | ⟨hk, -, -⟩
  · exact law_retData_ne_false V c hr.symm
  · exact law_failKind_ne_returnFalse V hg ha s caller c hk

/-- **`RevertsOnly`** for every variant whose guards and arithmetic checks revert and which has
no fee (whose SafeMath computation could end in `INVALID`). -/
theorem law_revertsOnly (hg : V.guardFail = .revert) (ha : V.arithFail = .revert)
    (hf : V.fee = .none) : (V.model ev).RevertsOnly := by
  intro s caller c k h
  rcases law_call_eq_halt V h with ⟨-, rfl⟩ | ⟨hk, -⟩
  · rfl
  · unfold failKind at hk
    simp only [law_overflows_of_fee_none V hf, Bool.false_eq_true, ↓reduceIte] at hk
    split_ifs at hk
    · rw [hg] at hk; cases hk
    · rw [ha] at hk; cases hk

/-- **`WFInvariant`** for every `Sane` variant. -/
theorem law_wfInvariant (hV : V.Sane) : (V.model ev).WFInvariant := by
  refine ⟨fun s caller c s' r hw h => ?_, fun s e s' hw h => V.WF_stepOp hV hw h⟩
  rcases law_call_eq_ok V h with ⟨hs, -⟩ | ⟨-, rfl, -⟩
  · exact V.WF_step hV hw hs
  · exact hw

omit [DecidableEq A] [Zero A] in
/-- **`ExactMoves`, monotone in the states**: exact in all `P`-states, exact in all `Q ⊆ P`. -/
theorem law_exactMoves_mono {σ E : Type} {M : TokenModel σ A E} {P Q : σ → Prop}
    (hPQ : ∀ s, Q s → P s) (h : M.ExactMoves P) : M.ExactMoves Q :=
  ⟨fun s c d v s' r hq => h.1 s c d v s' r (hPQ s hq),
    fun s c src d v s' r hq => h.2 s c src d v s' r (hPQ s hq)⟩

/-- The states in which a variant transfers exactly (the predicate of
`QEDefi.ERC4626.Asset.NoFee`): no fee on any value, and a positive scale if it rebases. -/
def NoFee (V : Variant A) (s : VState A) : Prop :=
  (∀ v, V.feeOf s v = 0) ∧ (V.rebasing = true → 0 < s.scale)

omit [DecidableEq A] [Zero A] in
theorem law_feeOf_congr (V : Variant A) {s s' : VState A} (h1 : s'.feeBps = s.feeBps)
    (h2 : s'.feeMax = s.feeMax) (v : ℕ) : V.feeOf s' v = V.feeOf s v := by
  unfold Variant.feeOf; rw [h1, h2]

omit [DecidableEq A] [Zero A] in
theorem law_balanceOf_congr (V : Variant A) {s s' : VState A} (h1 : s'.bal = s.bal)
    (h2 : s'.scale = s.scale) (a : A) : V.balanceOf s' a = V.balanceOf s a := by
  unfold Variant.balanceOf; rw [h1, h2]

theorem law_movesExactly {s s' : VState A} {src dst : A} {v : ℕ} (hP : NoFee V s)
    (hsd : src ≠ dst) (h : V.move s src dst v = some s') :
    (V.model ev).MovesExactly s s' src dst v := by
  obtain ⟨hv, -, hsrc, hdst, hoth, -⟩ := V.move_balanceOf (hP.1 v) hP.2 h
  simp only [TokenModel.MovesExactly, model_balanceOf]
  refine ⟨?_, hdst hsd, hoth⟩
  rw [hsrc hsd]; omega

/-- **`ExactMoves` on fee-free states, for every variant** (rebasing ones included: a transfer
of `v` moves `v · scale` gons, which is exactly `v` in the `balanceOf` view). -/
theorem law_exactMoves : (V.model ev).ExactMoves (NoFee V) := by
  constructor
  · intro s caller dst v s' r hP hcd h hr
    simp only [model_call] at h
    rcases law_call_eq_ok V h with ⟨hs, -⟩ | ⟨-, -, rfl⟩
    · simp only [step, transfer] at hs
      split_ifs at hs
      exact law_movesExactly V ev hP hcd hs
    · exact absurd rfl hr
  · intro s caller src dst v s' r hP hsd h hr
    simp only [model_call] at h
    rcases law_call_eq_ok V h with ⟨hs, -⟩ | ⟨-, -, rfl⟩
    · obtain ⟨s1, h1, h2⟩ := V.transferFrom_eq_some hs
      obtain ⟨e1, -, e3, -, -, -, e7, e8, -⟩ := V.spend_eq_some h1
      have hP1 : NoFee V s1 :=
        ⟨fun w => by rw [law_feeOf_congr V e7 e8]; exact hP.1 w, fun hr => e3 ▸ hP.2 hr⟩
      have := law_movesExactly V ev hP1 hsd h2
      simp only [TokenModel.MovesExactly, model_balanceOf, law_balanceOf_congr V e1 e3] at this ⊢
      exact this
    · exact absurd rfl hr

/-- **`SupplyFixed`** for every variant whose fee (if any) is not burned. -/
theorem law_supplyFixed (hf : V.fee = .none ∨ V.feeSink = .owner) :
    (V.model ev).SupplyFixed := by
  have hmove : ∀ {s s' : VState A} {src dst : A} {v : ℕ}, V.move s src dst v = some s' →
      s'.supply = s.supply ∧ s'.ether = s.ether := by
    intro s s' src dst v h
    refine ⟨?_, ?_⟩
    · rw [V.move_fee_supply h]
      rcases hf with hf | hf
      · simp [feeOf, hf]
      · simp [hf]
    · obtain ⟨-, -, -, rfl⟩ := (V.move_eq_some).1 h
      exact (V.credit_fields _ _ _ _).2.1
  intro s caller c s' r hc h
  simp only [model_call, model_totalSupply] at h ⊢
  rcases law_call_eq_ok V h with ⟨hs, -⟩ | ⟨-, rfl, -⟩
  · have : s'.supply = s.supply ∧ s'.ether = s.ether := by
      cases c with
      | transfer dst v =>
        simp only [step, transfer] at hs; split_ifs at hs; exact hmove hs
      | transferFrom src dst v =>
        obtain ⟨s1, h1, h2⟩ := V.transferFrom_eq_some hs
        obtain ⟨-, e2, -, e4, -⟩ := V.spend_eq_some h1
        obtain ⟨f2, f4⟩ := hmove h2
        exact ⟨f2.trans e2, f4.trans e4⟩
      | approve sp v =>
        simp only [step, approve] at hs; split_ifs at hs; cases hs; exact ⟨rfl, rfl⟩
      | other _ => simp [Call.returnsBool] at hc
      | permit _ _ _ _ _ => simp [Call.returnsBool] at hc
    unfold Variant.totalSupply; rw [this.1, this.2]
  · rfl

/-! ## Who can lower a balance or change an allowance -/

omit [DecidableEq A] [Zero A] in
theorem law_units_le (s : VState A) {u v : ℕ} (h : u ≤ v) : V.units s u ≤ V.units s v := by
  unfold units; split_ifs
  · exact Nat.mul_le_mul_right _ h
  · exact h

omit [Zero A] in
/-- A transfer from `src` lowers no other account's internal balance: the recipient's net
credit is `v − fee ≥ 0`, the fee owner's `fee ≥ 0`. -/
theorem law_credit_bal_le {s : VState A} {src dst o : A} {v : ℕ} (hf : V.feeOf s v ≤ v)
    (ho : o ≠ src) : s.bal o ≤ (V.credit s src dst v).bal o := by
  have hu := law_units_le V s hf
  unfold credit
  split_ifs
  · simp only [Token.add_single_apply, Token.sub_single_apply, ho.symm, ite_false]
    split_ifs <;> omega
  · cases V.feeSink <;>
      simp only [Token.add_single_apply, Token.sub_single_apply, ho.symm, ite_false] <;>
      split_ifs <;> omega

omit [Zero A] in
theorem law_fallback_bal_le {s s' : VState A} {caller o : A} {value : ℕ}
    (h : V.fallbackCall s caller value = some s') : s.bal o ≤ s'.bal o ∧ s'.scale = s.scale := by
  unfold fallbackCall at h
  cases hk : V.fallback <;> simp only [hk, reduceCtorEq] at h
  · cases h; exact ⟨le_rfl, rfl⟩
  · unfold deposit at h; split_ifs at h; cases h
    refine ⟨?_, rfl⟩
    simp only [Token.add_single_apply]; split_ifs <;> omega

theorem law_bal_le_step {s s' : VState A} {caller o : A} {c : Call A}
    (h : V.step s caller c = some s') (ho : o ≠ caller) (hc : ∀ dst v, c ≠ .transferFrom o dst v) :
    s.bal o ≤ s'.bal o ∧ s'.scale = s.scale := by
  cases c with
  | transfer dst v =>
    simp only [step, transfer] at h; split_ifs at h
    obtain ⟨-, -, hf, rfl⟩ := (V.move_eq_some).1 h
    exact ⟨law_credit_bal_le V hf ho, (V.credit_fields _ _ _ _).1⟩
  | transferFrom src dst v =>
    have hos : o ≠ src := by rintro rfl; exact hc dst v rfl
    obtain ⟨s1, h1, h2⟩ := V.transferFrom_eq_some h
    obtain ⟨e1, -, e3, -⟩ := V.spend_eq_some h1
    obtain ⟨-, -, hf, rfl⟩ := (V.move_eq_some).1 h2
    refine ⟨?_, (V.credit_fields _ _ _ _).1.trans e3⟩
    have := law_credit_bal_le V (s := s1) (dst := dst) hf hos
    rwa [e1] at this
  | approve sp v =>
    simp only [step, approve] at h; split_ifs at h; cases h; exact ⟨le_rfl, rfl⟩
  | other value =>
    simp only [step] at h
    exact law_fallback_bal_le V h
  | permit o' sp v live rec =>
    simp only [step, permit] at h
    split_ifs at h
    · exact law_fallback_bal_le V h
    · cases h; exact ⟨le_rfl, rfl⟩

omit [DecidableEq A] [Zero A] in
theorem law_balanceOf_mono {s s' : VState A} {a : A} (h1 : s.bal a ≤ s'.bal a)
    (h2 : s'.scale = s.scale) : V.balanceOf s a ≤ V.balanceOf s' a := by
  unfold Variant.balanceOf; rw [h2]; split_ifs
  · exact Nat.div_le_div_right h1
  · exact h1

/-- **`DebitAuth` for every variant**: fees raise the fee owner's balance (or burn from the
recipient's credit, never below its old balance), rebasing moves the gons of the two parties
only, deposits credit the caller. -/
theorem law_debitAuth : (V.model ev).DebitAuth := by
  intro s caller c s' r o h ho hlt
  simp only [model_call, model_balanceOf] at h hlt
  by_contra hc
  simp only [not_exists] at hc
  rcases law_call_eq_ok V h with ⟨hs, -⟩ | ⟨-, rfl, -⟩
  · obtain ⟨h1, h2⟩ := law_bal_le_step V hs ho hc
    exact absurd (law_balanceOf_mono V h1 h2) (not_le.2 hlt)
  · exact lt_irrefl _ hlt

omit [Zero A] in
theorem law_setAllowance_apply (s : VState A) (o sp a b : A) (v : ℕ) :
    (s.setAllowance o sp v).allowance a b = if a = o ∧ b = sp then v else s.allowance a b := by
  simp only [VState.setAllowance, Function.update_apply]
  by_cases ha : a = o <;> by_cases hb : b = sp <;> simp [ha, hb]

omit [DecidableEq A] [Zero A] in
theorem law_fallback_allowance {s s' : VState A} {caller : A} {value : ℕ}
    (h : V.fallbackCall s caller value = some s') : s'.allowance = s.allowance := by
  unfold fallbackCall at h
  cases hk : V.fallback <;> simp only [hk, reduceCtorEq] at h
  · cases h; rfl
  · unfold deposit at h; split_ifs at h; cases h; rfl

theorem law_allowance_step {s s' : VState A} {caller o sp : A} {c : Call A}
    (h : V.step s caller c = some s') (ho : o ≠ caller)
    (hne : s'.allowance o sp ≠ s.allowance o sp) :
    (sp = caller ∧ ∃ dst v, c = .transferFrom o dst v) ∨
      (∃ v live rec n, c = .permit o sp v live rec ∧ rec n = o) := by
  cases c with
  | transfer dst v =>
    simp only [step, transfer] at h; split_ifs at h
    obtain ⟨-, -, -, rfl⟩ := (V.move_eq_some).1 h
    rw [(V.credit_fields _ _ _ _).2.2.1] at hne
    exact absurd rfl hne
  | transferFrom src dst v =>
    obtain ⟨s1, h1, h2⟩ := V.transferFrom_eq_some h
    obtain ⟨-, -, -, rfl⟩ := (V.move_eq_some).1 h2
    rw [(V.credit_fields _ _ _ _).2.2.1] at hne
    left
    unfold spend at h1
    split_ifs at h1 <;> cases h1 <;> try exact absurd rfl hne
    rw [law_setAllowance_apply] at hne
    split_ifs at hne with hh
    · obtain ⟨rfl, rfl⟩ := hh; exact ⟨rfl, dst, v, rfl⟩
    · exact absurd rfl hne
  | approve sp' v =>
    simp only [step, approve] at h; split_ifs at h; cases h
    rw [law_setAllowance_apply] at hne
    split_ifs at hne with hh
    · exact absurd hh.1 ho
    · exact absurd rfl hne
  | other value =>
    simp only [step] at h
    rw [law_fallback_allowance V h] at hne
    exact absurd rfl hne
  | permit o' sp' v live rec =>
    simp only [step, permit] at h
    split_ifs at h with hp hok
    · rw [law_fallback_allowance V h] at hne
      exact absurd rfl hne
    · cases h
      right
      change (s.setAllowance o' sp' v).allowance o sp ≠ _ at hne
      rw [law_setAllowance_apply] at hne
      split_ifs at hne with hh
      · obtain ⟨rfl, rfl⟩ := hh
        refine ⟨v, live, rec, s.nonces o, rfl, ?_⟩
        unfold permitOk at hok
        cases hr : V.permitRule with
        | none => exact absurd hr hp
        | eip2612 rz w =>
          simp only [hr, Bool.and_eq_true, decide_eq_true_eq] at hok
          exact hok.1.1.2
      · exact absurd rfl hne

/-- **`AllowanceAuth` for every variant**: `approve` sets the caller's own allowances, a
`transferFrom` spends the caller's allowance from `src`, a `permit` sets `(owner, spender)` only
when the recovered signer is `owner`, and the fallback (WETH9 deposits, BNB) touches none. -/
theorem law_allowanceAuth : (V.model ev).AllowanceAuth := by
  intro s caller c s' r o sp h ho hne
  simp only [model_call, model_allowance] at h hne
  rcases law_call_eq_ok V h with ⟨hs, -⟩ | ⟨-, rfl, -⟩
  · unfold allowanceOf at hne
    split_ifs at hne
    · exact absurd rfl hne
    · exact law_allowance_step V hs ho hne
  · exact absurd rfl hne

/-! ## Refuting a law from one outcome -/

theorem law_not_returnsTrue {s s' : VState A} {caller : A} {c : Call A} {r : RetData}
    (hb : c.returnsBool = true) (h : V.call s caller c = .ok s' r) (hr : r ≠ .word true) :
    ¬ (V.model ev).ReturnsTrue :=
  fun hl => hr (hl s caller c s' r hb h)

theorem law_not_revertsOnly {s : VState A} {caller : A} {c : Call A}
    (h : V.call s caller c = .halt .invalid) : ¬ (V.model ev).RevertsOnly :=
  fun hl => by cases hl s caller c _ h

theorem law_not_exactMoves {P : VState A → Prop} {s s' : VState A} {caller dst : A} {v : ℕ}
    {r : RetData} (hP : P s) (hcd : caller ≠ dst) (h : V.call s caller (.transfer dst v) = .ok s' r)
    (hr : r ≠ .word false) (hn : ¬ (V.model ev).MovesExactly s s' caller dst v) :
    ¬ (V.model ev).ExactMoves P :=
  fun hl => hn (hl.1 s caller dst v s' r hP hcd h hr)

theorem law_not_supplyFixed {s s' : VState A} {caller : A} {c : Call A} {r : RetData}
    (hb : c.returnsBool = true) (h : V.call s caller c = .ok s' r)
    (hn : V.totalSupply s' ≠ V.totalSupply s) : ¬ (V.model ev).SupplyFixed :=
  fun hl => hn (hl s caller c s' r hb h)

/-! ## Witness states -/

omit [DecidableEq A] in
/-- A witness state: `holder` owns all `n` tokens, the fee is `bps` basis points capped at `n`
(USDT), the scale is `k` (AMPL); token address and privileged account `0`, no allowances. -/
def wit (holder : A) (n bps k : ℕ) : VState A where
  self := 0
  bal := single holder n
  supply := n
  allowance := fun _ _ => 0
  scale := k
  admin := 0
  paused := false
  blacklisted := fun _ => false
  feeBps := bps
  feeMax := n
  ether := 0
  frozen := 0
  nonces := 0

omit [DecidableEq A] [Zero A] in
theorem law_total_single (a : A) (n : ℕ) : total (single a n) = n := by
  simp [total]

omit [DecidableEq A] [Zero A] in
theorem law_total_zero : total (0 : A →₀ ℕ) = 0 := by
  simp [total]

omit [DecidableEq A] in
/-- The witness is well formed for a non-rebasing variant with a stored supply. -/
theorem law_wit_WF (hr : V.rebasing = false) (hs : V.supply = .stored) (holder : A) {n : ℕ}
    (bps k : ℕ) (hn : n ≤ MAX) : V.WF (wit holder n bps k) := by
  unfold WF
  simp only [hr, hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, wit, law_total_single,
    law_total_zero, Nat.add_zero]
  exact ⟨trivial, hn⟩

/-! ## The witnesses of the refutations

Each refutation is witnessed in a well-formed state (`Variant.WF`), so the failure is not an
artefact of an unreachable state; `a ≠ 0` is a second account (the ones that need two accounts
take `[Nontrivial A]`). -/

/-- **USDT returns nothing**: `approve(sp, 0)` succeeds in every state with empty return data. -/
theorem usdt_approve_empty (s : VState A) (c sp : A) :
    (usdt : Variant A).call s c (.approve sp 0) = .ok (s.setAllowance c sp 0) .empty := by
  simp [call, step, approve, approveOk, usdt, standard, retData]

/-- **USDT fails with `INVALID`** on a short balance, in a well-formed state. -/
theorem usdt_invalid_witness :
    (usdt : Variant A).WF (wit 0 0 0 1) ∧
      (usdt : Variant A).call (wit 0 0 0 1) 0 (.transfer 0 1) = .halt .invalid :=
  ⟨law_wit_WF _ rfl rfl _ _ _ (Nat.zero_le _),
    usdt_call_invalid _ _ _ _ (by simp [usdt_moveOk, wit]) (by simp [wit])⟩

/-- **USDT with a fee is not exact**: at `basisPointsRate = 1` (`setParams` allows `< 20`) a
transfer of `10000` from the owner `0` to `a` charges a fee of `1`, which goes back to the
owner: the sender's balance drops by `9999`, the recipient's rises by `9999`. -/
theorem usdt_fee_witness {a : A} (ha : a ≠ 0) :
    (usdt : Variant A).WF (wit 0 10000 1 1) ∧
      (usdt : Variant A).call (wit 0 10000 1 1) 0 (.transfer a 10000) =
        .ok ((usdt : Variant A).credit (wit 0 10000 1 1) 0 a 10000) .empty ∧
      (usdt : Variant A).balanceOf ((usdt : Variant A).credit (wit 0 10000 1 1) 0 a 10000) 0 = 1 ∧
      (usdt : Variant A).balanceOf ((usdt : Variant A).credit (wit 0 10000 1 1) 0 a 10000) a =
        9999 := by
  have hM : (10000 : ℕ) ≤ MAX := by unfold MAX; omega
  have hfee : (usdt : Variant A).feeOf (wit 0 10000 1 1) 10000 = 1 := by
    rw [usdt_feeOf]; simp [wit]
  have hcr : ((usdt : Variant A).credit (wit 0 10000 1 1) 0 a 10000).bal =
      single 0 10000 - single 0 10000 + single a 10000 - single a 1 + single 0 1 := by
    unfold credit
    simp only [hfee, units_of_not_rebasing (usdt : Variant A) rfl, one_ne_zero, ↓reduceIte]
    rfl
  refine ⟨law_wit_WF _ rfl rfl _ _ _ hM, ?_, ?_, ?_⟩
  · rw [usdt_call_transfer _ _ _ _ (by simp [wit])]
    simp [wit, MAX]
  · rw [balanceOf_of_not_rebasing _ rfl, hcr]
    simp [Token.add_single_apply, Token.sub_single_apply, Ne.symm ha]
  · rw [balanceOf_of_not_rebasing _ rfl, hcr]
    simp [Token.add_single_apply, Token.sub_single_apply, Ne.symm ha]

/-- **STA fails with `INVALID`** when the fee computation overflows: a transfer of the whole
supply `MAX` (`⌈MAX/100⌉ · 100 · 100 > MAX`), in a well-formed state. -/
theorem sta_invalid_witness {a : A} (ha : a ≠ 0) :
    (sta : Variant A).WF (wit 0 MAX 0 1) ∧
      (sta : Variant A).call (wit 0 MAX 0 1) 0 (.transfer a MAX) = .halt .invalid :=
  ⟨law_wit_WF _ rfl rfl _ _ _ le_rfl,
    sta_call_transfer_overflow ha (by simp [wit]) (by unfold MAX; omega)⟩

/-- **STA burns its fee**: a transfer of `1` (the whole supply) burns `⌈1/100⌉ = 1`; the
recipient receives nothing and the supply drops to `0`. -/
theorem sta_fee_witness {a : A} (ha : a ≠ 0) :
    (sta : Variant A).WF (wit 0 1 0 1) ∧
      (sta : Variant A).call (wit 0 1 0 1) 0 (.transfer a 1) =
        .ok ((sta : Variant A).credit (wit 0 1 0 1) 0 a 1) (.word true) ∧
      (sta : Variant A).balanceOf ((sta : Variant A).credit (wit 0 1 0 1) 0 a 1) a = 0 ∧
      (sta : Variant A).totalSupply ((sta : Variant A).credit (wit 0 1 0 1) 0 a 1) = 0 := by
  have hM : (1 : ℕ) ≤ MAX := by unfold MAX; omega
  have hfee : (sta : Variant A).feeOf (wit 0 1 0 1) 1 = 1 := by rw [sta_feeOf]
  have hfo : (sta : Variant A).feeOverflow (wit 0 1 0 1) 1 = false := by
    rw [Bool.eq_false_iff]; intro h; rw [sta_feeOverflow_iff] at h; unfold MAX at h; omega
  have hm : (sta : Variant A).moveOk (wit 0 1 0 1) 0 a 1 = true := by
    simp [moveOk, sta, standard, ha]
  have hcr : (sta : Variant A).credit (wit 0 1 0 1) 0 a 1 =
      { wit 0 1 0 1 with bal := single 0 1 - single 0 1 + single a 1 - single a 1,
                         supply := 1 - 1 } := by
    unfold credit
    simp only [hfee, units_of_not_rebasing (sta : Variant A) rfl, one_ne_zero, ↓reduceIte]
    rfl
  have hstep : (sta : Variant A).step (wit 0 1 0 1) 0 (.transfer a 1) =
      some ((sta : Variant A).credit (wit 0 1 0 1) 0 a 1) := by
    simp only [step, transfer, hm, ↓reduceIte, move, units_of_not_rebasing (sta : Variant A) rfl,
      hfo, hfee,
      Bool.false_eq_true]
    simp [wit]
  refine ⟨law_wit_WF _ rfl rfl _ _ _ hM, ?_, ?_, ?_⟩
  · simp only [call, hstep]; rfl
  · rw [balanceOf_of_not_rebasing _ rfl, hcr]
    simp
  · rw [hcr]; rfl

/-- **BNB's `transfer` returns nothing**: a transfer of `1` to `a ≠ 0` succeeds with empty
return data, in a well-formed state. -/
theorem bnb_empty_witness {a : A} (ha : a ≠ 0) :
    (bnb : Variant A).WF (wit 0 1 0 1) ∧
      (bnb : Variant A).call (wit 0 1 0 1) 0 (.transfer a 1) =
        .ok ((bnb : Variant A).credit (wit 0 1 0 1) 0 a 1) .empty := by
  have hM : (1 : ℕ) ≤ MAX := by unfold MAX; omega
  have hm : (bnb : Variant A).moveOk (wit 0 1 0 1) 0 a 1 = true := by
    simp [moveOk, bnb, standard, ha]
  have hstep : (bnb : Variant A).step (wit 0 1 0 1) 0 (.transfer a 1) =
      some ((bnb : Variant A).credit (wit 0 1 0 1) 0 a 1) := by
    simp only [step, transfer, hm, ↓reduceIte, move, units_of_not_rebasing (bnb : Variant A) rfl]
    simp [wit, feeOverflow, feeOf, bnb, standard]
  refine ⟨law_wit_WF _ rfl rfl _ _ _ hM, ?_⟩
  simp only [call, hstep]; rfl

/-- **AMPL at scale `0`**: every `balanceOf` reads `0`, yet a transfer of `1` succeeds (it
moves `1 · 0` gons). Such a state is not well formed (`WF` forces a positive scale). -/
theorem ampl_scale_zero_witness {a : A} (ha : a ≠ 0) :
    (ampl : Variant A).call (wit 0 0 0 0) 0 (.transfer a 1) =
        .ok ((ampl : Variant A).credit (wit 0 0 0 0) 0 a 1) (.word true) ∧
      ∀ x, (ampl : Variant A).balanceOf ((ampl : Variant A).credit (wit 0 0 0 0) 0 a 1) x = 0 := by
  have hm : (ampl : Variant A).moveOk (wit 0 0 0 0) 0 a 1 = true := by
    simp [moveOk, ampl, standard, ha, wit]
  have hstep : (ampl : Variant A).step (wit 0 0 0 0) 0 (.transfer a 1) =
      some ((ampl : Variant A).credit (wit 0 0 0 0) 0 a 1) := by
    simp only [step, transfer, hm, ↓reduceIte, move]
    simp [wit, feeOverflow, feeOf, units, ampl, standard]
  refine ⟨by simp only [call, hstep]; rfl, fun x => ?_⟩
  have hsc := ((ampl : Variant A).credit_fields (wit 0 0 0 0) 0 a 1).1
  have hr : (ampl : Variant A).rebasing = true := rfl
  simp only [balanceOf, hr, hsc, ↓reduceIte]
  simp [wit]

/-! ## The laws of each variant -/

theorem law_ne_returnFalse {k : OnFail} (h : k = .revert ∨ k = .invalid) : k ≠ .returnFalse := by
  rcases h with rfl | rfl <;> nofun

/-- `ReturnsTrue` for a variant returning `bool` whose failures revert. -/
theorem law_returnsTrue_rev (hr : ∀ f, V.returns f = .bool) (hg : V.guardFail = .revert)
    (ha : V.arithFail = .revert) : (V.model ev).ReturnsTrue :=
  law_returnsTrue V ev hr (law_ne_returnFalse (.inl hg)) (law_ne_returnFalse (.inl ha))

/-- `NoFalseReturn` for a variant whose failures revert or end with `INVALID`. -/
theorem law_noFalseReturn_rev (hg : V.guardFail = .revert)
    (ha : V.arithFail = .revert ∨ V.arithFail = .invalid) : (V.model ev).NoFalseReturn :=
  law_noFalseReturn V ev (law_ne_returnFalse (.inl hg)) (law_ne_returnFalse ha)

omit [DecidableEq A] [Zero A] in
theorem law_noFee_of_fee_none (hf : V.fee = .none) (hr : V.rebasing = false) (s : VState A) :
    NoFee V s :=
  ⟨fun _ => by simp [feeOf, hf], fun h => by rw [hr] at h; cases h⟩

/-- **Solmate: every law, in every state.** -/
theorem standard_laws : ((standard : Variant A).model ev).Standard (fun _ => True) where
  returnsTrue := law_returnsTrue_rev _ ev (fun _ => rfl) rfl rfl
  noFalseReturn := law_noFalseReturn_rev _ ev rfl (.inl rfl)
  revertsOnly := law_revertsOnly _ ev rfl rfl rfl
  exactMoves := law_exactMoves_mono (fun s _ => law_noFee_of_fee_none _ rfl rfl s)
    (law_exactMoves _ ev)
  supplyFixed := law_supplyFixed _ ev (Or.inl rfl)
  debitAuth := law_debitAuth _ ev
  allowanceAuth := law_allowanceAuth _ ev
  wfInvariant := law_wfInvariant _ ev standard_sane

/-- **OpenZeppelin v5: every law, in every state.** -/
theorem oz_laws : ((oz : Variant A).model ev).Standard (fun _ => True) where
  returnsTrue := law_returnsTrue_rev _ ev (fun _ => rfl) rfl rfl
  noFalseReturn := law_noFalseReturn_rev _ ev rfl (.inl rfl)
  revertsOnly := law_revertsOnly _ ev rfl rfl rfl
  exactMoves := law_exactMoves_mono (fun s _ => law_noFee_of_fee_none _ rfl rfl s)
    (law_exactMoves _ ev)
  supplyFixed := law_supplyFixed _ ev (Or.inl rfl)
  debitAuth := law_debitAuth _ ev
  allowanceAuth := law_allowanceAuth _ ev
  wfInvariant := law_wfInvariant _ ev oz_sane

/-- **Solady (Permit2 spender `p`): every law, in every state.** The Permit2 allowance reads
`MAX` and never changes, so `AllowanceAuth` holds for it trivially. -/
theorem solady_laws (p : A) : ((solady p).model ev).Standard (fun _ => True) where
  returnsTrue := law_returnsTrue_rev _ ev (fun _ => rfl) rfl rfl
  noFalseReturn := law_noFalseReturn_rev _ ev rfl (.inl rfl)
  revertsOnly := law_revertsOnly _ ev rfl rfl rfl
  exactMoves := law_exactMoves_mono (fun s _ => law_noFee_of_fee_none _ rfl rfl s)
    (law_exactMoves _ ev)
  supplyFixed := law_supplyFixed _ ev (Or.inl rfl)
  debitAuth := law_debitAuth _ ev
  allowanceAuth := law_allowanceAuth _ ev
  wfInvariant := law_wfInvariant _ ev (solady_sane p)

/-- **WETH9: every law, in every state.** Its `totalSupply` is the ether balance, which no
`transfer`, `transferFrom` or `approve` changes; a phantom `permit` reaches the depositing
fallback with no value and changes nothing. -/
theorem weth9_laws : ((weth9 : Variant A).model ev).Standard (fun _ => True) where
  returnsTrue := law_returnsTrue_rev _ ev (fun _ => rfl) rfl rfl
  noFalseReturn := law_noFalseReturn_rev _ ev rfl (.inl rfl)
  revertsOnly := law_revertsOnly _ ev rfl rfl rfl
  exactMoves := law_exactMoves_mono (fun s _ => law_noFee_of_fee_none _ rfl rfl s)
    (law_exactMoves _ ev)
  supplyFixed := law_supplyFixed _ ev (Or.inl rfl)
  debitAuth := law_debitAuth _ ev
  allowanceAuth := law_allowanceAuth _ ev
  wfInvariant := law_wfInvariant _ ev weth9_sane

omit [DecidableEq A] [Zero A] in
/-- USDT is fee-free exactly when the fee rounds to `0` for every value; in particular at
`basisPointsRate = 0` (the mainnet setting). -/
theorem usdt_noFee_of_feeBps {s : VState A} (h : s.feeBps = 0) : NoFee (usdt : Variant A) s :=
  ⟨fun v => by rw [usdt_feeOf, h]; simp, fun h => by cases h⟩

/-- **USDT.** Fails `ReturnsTrue` (no return data) and `RevertsOnly` (`INVALID` on a short
balance); exact exactly in the fee-free states (`basisPointsRate = 0` in particular), not in
all well-formed ones (a fee paid to the owner); every other law holds. Refutations need two
accounts (`Nontrivial A`). -/
theorem usdt_laws [Nontrivial A] :
    ¬ ((usdt : Variant A).model ev).ReturnsTrue ∧ ((usdt : Variant A).model ev).NoFalseReturn ∧
      ¬ ((usdt : Variant A).model ev).RevertsOnly ∧
      ((usdt : Variant A).model ev).ExactMoves (NoFee usdt) ∧
      ((usdt : Variant A).model ev).ExactMoves (fun s => s.feeBps = 0) ∧
      ¬ ((usdt : Variant A).model ev).ExactMoves (usdt : Variant A).WF ∧
      ((usdt : Variant A).model ev).SupplyFixed ∧ ((usdt : Variant A).model ev).DebitAuth ∧
      ((usdt : Variant A).model ev).AllowanceAuth ∧ ((usdt : Variant A).model ev).WFInvariant := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨hw, hc, h0, -⟩ := usdt_fee_witness ha
  refine ⟨law_not_returnsTrue _ ev rfl (usdt_approve_empty (wit 0 0 0 1) 0 0) nofun,
    law_noFalseReturn_rev _ ev rfl (.inr rfl),
    law_not_revertsOnly _ ev usdt_invalid_witness.2, law_exactMoves _ ev,
    law_exactMoves_mono (fun _ h => usdt_noFee_of_feeBps h) (law_exactMoves _ ev),
    law_not_exactMoves _ ev hw (Ne.symm ha) hc nofun ?_,
    law_supplyFixed _ ev (Or.inr rfl), law_debitAuth _ ev, law_allowanceAuth _ ev,
    law_wfInvariant _ ev usdt_sane⟩
  rintro ⟨h1, -⟩
  simp only [model_balanceOf, h0, balanceOf_of_not_rebasing (usdt : Variant A) rfl] at h1
  simp [wit] at h1

/-- **BNB.** Fails only `ReturnsTrue` (`transfer` returns nothing; `transferFrom` and `approve`
return `true`); exact in every state. -/
theorem bnb_laws [Nontrivial A] :
    ¬ ((bnb : Variant A).model ev).ReturnsTrue ∧ ((bnb : Variant A).model ev).NoFalseReturn ∧
      ((bnb : Variant A).model ev).RevertsOnly ∧
      ((bnb : Variant A).model ev).ExactMoves (fun _ => True) ∧
      ((bnb : Variant A).model ev).SupplyFixed ∧ ((bnb : Variant A).model ev).DebitAuth ∧
      ((bnb : Variant A).model ev).AllowanceAuth ∧ ((bnb : Variant A).model ev).WFInvariant := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  exact ⟨law_not_returnsTrue _ ev rfl (bnb_empty_witness ha).2 nofun,
    law_noFalseReturn_rev _ ev rfl (.inl rfl), law_revertsOnly _ ev rfl rfl rfl,
    law_exactMoves_mono (fun s _ => law_noFee_of_fee_none _ rfl rfl s) (law_exactMoves _ ev),
    law_supplyFixed _ ev (Or.inl rfl), law_debitAuth _ ev, law_allowanceAuth _ ev,
    law_wfInvariant _ ev bnb_sane⟩

/-- STA charges a fee on every positive value, so no state is fee-free: `ExactMoves (NoFee sta)`
holds only vacuously. -/
theorem sta_not_noFee (s : VState A) : ¬ NoFee (sta : Variant A) s := fun h => by
  have := h.1 1
  rw [sta_feeOf] at this
  omega

/-- **STA.** Fails `RevertsOnly` (`INVALID` on a fee overflow), `ExactMoves` (the burned fee),
`SupplyFixed` (the burned fee leaves the supply), all in well-formed states; every other law
holds. -/
theorem sta_laws [Nontrivial A] :
    ((sta : Variant A).model ev).ReturnsTrue ∧ ((sta : Variant A).model ev).NoFalseReturn ∧
      ¬ ((sta : Variant A).model ev).RevertsOnly ∧
      ¬ ((sta : Variant A).model ev).ExactMoves (sta : Variant A).WF ∧
      ¬ ((sta : Variant A).model ev).SupplyFixed ∧ ((sta : Variant A).model ev).DebitAuth ∧
      ((sta : Variant A).model ev).AllowanceAuth ∧ ((sta : Variant A).model ev).WFInvariant := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨hw, hc, h0, hS⟩ := sta_fee_witness ha
  refine ⟨law_returnsTrue_rev _ ev (fun _ => rfl) rfl rfl,
    law_noFalseReturn_rev _ ev rfl (.inl rfl),
    law_not_revertsOnly _ ev (sta_invalid_witness ha).2,
    law_not_exactMoves _ ev hw (Ne.symm ha) hc nofun ?_,
    law_not_supplyFixed _ ev rfl hc ?_, law_debitAuth _ ev, law_allowanceAuth _ ev,
    law_wfInvariant _ ev sta_sane⟩
  · rintro ⟨-, h2, -⟩
    simp only [model_balanceOf, h0] at h2
    simp [balanceOf_of_not_rebasing (sta : Variant A) rfl, wit] at h2
  · rw [hS]; simp [totalSupply, sta, standard, wit]

omit [DecidableEq A] [Zero A] in
/-- AMPL is fee-free exactly in the states with a positive scale. -/
theorem ampl_noFee_iff (s : VState A) : NoFee (ampl : Variant A) s ↔ 0 < s.scale :=
  ⟨fun h => h.2 rfl, fun h => ⟨fun _ => by simp [feeOf, ampl, standard], fun _ => h⟩⟩

/-- Every well-formed AMPL state has a positive scale (`TOTAL_GONS / supply` with
`supply² ≤ TOTAL_GONS`). -/
theorem ampl_scale_pos {s : VState A} (hw : (ampl : Variant A).WF s) : 0 < s.scale := by
  have hr : (ampl : Variant A).rebasing = true := rfl
  unfold WF at hw; simp only [hr, ↓reduceIte] at hw
  obtain ⟨-, hpos, hcap, hsc⟩ := hw
  obtain ⟨-, hsq⟩ := (ampl_sane (A := A)).rebasing_cap hr
  rw [hsc]
  apply Nat.div_pos _ hpos
  calc s.supply ≤ s.supply * s.supply := Nat.le_mul_self _
    _ ≤ (ampl : Variant A).maxSupply ^ 2 := by rw [sq]; exact Nat.mul_le_mul hcap hcap
    _ ≤ _ := hsq

/-- **AMPL.** Every law holds in the `balanceOf` view, `ExactMoves` in every state with a
positive scale (every well-formed one): a transfer of `v` moves `v · scale` gons, and
`⌊(g ± v·k)/k⌋ = ⌊g/k⌋ ± v` exactly, so rounding never shows in a `transfer`/`transferFrom` (the
dust only moves with `transferAll`, an operation, not a call: `ampl_transferAll_balanceOf`). At
scale `0` (not well formed) every balance reads `0` and a transfer of `1` succeeds, so
`ExactMoves` fails in arbitrary states. -/
theorem ampl_laws [Nontrivial A] :
    ((ampl : Variant A).model ev).ReturnsTrue ∧ ((ampl : Variant A).model ev).NoFalseReturn ∧
      ((ampl : Variant A).model ev).RevertsOnly ∧
      ((ampl : Variant A).model ev).ExactMoves (fun s => 0 < s.scale) ∧
      ((ampl : Variant A).model ev).ExactMoves (ampl : Variant A).WF ∧
      ¬ ((ampl : Variant A).model ev).ExactMoves (fun _ => True) ∧
      ((ampl : Variant A).model ev).SupplyFixed ∧ ((ampl : Variant A).model ev).DebitAuth ∧
      ((ampl : Variant A).model ev).AllowanceAuth ∧ ((ampl : Variant A).model ev).WFInvariant := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨hc, h0⟩ := ampl_scale_zero_witness ha
  have hE : ((ampl : Variant A).model ev).ExactMoves (fun s => 0 < s.scale) :=
    law_exactMoves_mono (fun s h => (ampl_noFee_iff s).2 h) (law_exactMoves _ ev)
  refine ⟨law_returnsTrue_rev _ ev (fun _ => rfl) rfl rfl,
    law_noFalseReturn_rev _ ev rfl (.inl rfl), law_revertsOnly _ ev rfl rfl rfl, hE,
    law_exactMoves_mono (fun _ h => ampl_scale_pos h) hE,
    law_not_exactMoves _ ev trivial (Ne.symm ha) hc nofun ?_,
    law_supplyFixed _ ev (Or.inl rfl), law_debitAuth _ ev, law_allowanceAuth _ ev,
    law_wfInvariant _ ev ampl_sane⟩
  rintro ⟨h1, -⟩
  simp only [model_balanceOf, h0] at h1
  simp [balanceOf, ampl, wit] at h1

end QEDefi.ERC20.Spec.VariantLaws
