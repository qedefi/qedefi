module

public import QEDefi.ERC20.Spec.Laws
public import QEDefi.ERC20.VariantExtras

/-!
# YAMv2 as a token model

YAMv2 (`contracts/mainnet/YAMV2/source/YAMv2.sol`, solc 0.6.12) is OpenZeppelin-3's `ERC20`
with 24 decimals and a `minter`:

* `transfer`/`transferFrom`/`approve` return `true`; every failure is a `require` with a string
  reason (`REVERT`); no fallback function (unknown selectors and `permit` revert).
* `_transfer` rejects sender and recipient `0`; `_approve` rejects owner and spender `0`.
* `transferFrom(src, dst, v)` first moves the tokens (`_transfer`), then lowers
  `allowance[src][caller]` by `v` through `_approve`, always (an allowance of `2²⁵⁶ − 1` is
  spent too), emitting `Transfer(src, dst, v)` and then `Approval(src, caller, allowance − v)`.
  Every failure reverts, so the order of the checks does not show in the outcome.
* Recipient balances are added with SafeMath; under the supply bound (`Σ bal ≤ supply ≤ MAX`
  over the balances in the state, `SubSupply`) the addition cannot overflow (distinct
  accounts: `bal dst + v ≤ bal dst + bal src ≤ supply`, `SubSupply.credit_le`; a
  self-transfer subtracts first), so the record's `move` is exact in every `wf` state.
* Other entry points: `mint(dst, v)` by the minter (SafeMath on the supply, `dst ≠ 0`),
  `increaseAllowance`/`decreaseAllowance` (SafeMath `add`/`sub`, then `_approve`'s checks).

The ERC-20 part is the record `variant` (`Variant.model variant events` is the model's ERC-20
part, `model_call`); the other entry points are `Op`, because the record's mint authority
(`Auth`) has no "privileged caller, any recipient" case: `mint` is the record's open `mint`
gated on `caller = admin` (the `minter`), and the allowance helpers are the record's
`.checked` helpers (`spender ≠ 0`, checked arithmetic) gated on `caller ≠ 0` (`_approve`'s
owner check).

`yamv2_laws`: the standard laws all hold (in `WF` states).

The section `Plain` proves the laws for any variant without fee, rebasing, Permit2 or permit,
with a stored supply and a reverting fallback (shared with ZRX).
-/

@[expose] public noncomputable section

namespace QEDefi.ERC20.Spec.YAMV2
open QEDefi.Math Finsupp QEDefi.ERC20 QEDefi.ERC20.Token

/-! ## Laws of plain variants -/

section Plain

variable {A : Type} [DecidableEq A] [Zero A] (V : Variant A)

/-- A variant with no fee, no rebasing, no Permit2 spender, no `permit`, a stored supply and a
reverting fallback. -/
structure Plain : Prop where
  fee : V.fee = .none
  rebasing : V.rebasing = false
  supply : V.supply = .stored
  permit2 : V.permit2 = none
  permitRule : V.permitRule = .none
  fallback : V.fallback = .revert

variable {V}

omit [DecidableEq A] [Zero A] in
theorem Plain.balanceOf (hV : Plain V) (s : VState A) (a : A) : V.balanceOf s a = s.bal a := by
  simp [Variant.balanceOf, hV.rebasing]

omit [DecidableEq A] [Zero A] in
theorem Plain.totalSupply (hV : Plain V) (s : VState A) : V.totalSupply s = s.supply := by
  simp [Variant.totalSupply, hV.supply]

omit [Zero A] in
theorem Plain.allowanceOf (hV : Plain V) (s : VState A) (o sp : A) :
    V.allowanceOf s o sp = s.allowance o sp := by
  simp [Variant.allowanceOf, hV.permit2]

omit [DecidableEq A] [Zero A] in
theorem Plain.feeOf (hV : Plain V) (s : VState A) (v : ℕ) : V.feeOf s v = 0 := by
  simp [Variant.feeOf, hV.fee]

theorem Plain.step_other (hV : Plain V) (s : VState A) (c : A) (value : ℕ) :
    V.step s c (.other value) = none := by
  simp [Variant.step, Variant.fallbackCall, hV.fallback]

theorem Plain.step_permit (hV : Plain V) (s : VState A) (c o sp : A) (v : ℕ) (live : Bool)
    (rec : ℕ → A) : V.step s c (.permit o sp v live rec) = none := by
  simp [Variant.step, Variant.permit, hV.permitRule, Variant.fallbackCall, hV.fallback]

/-- The effect of a successful `move` in a plain variant. -/
theorem Plain.move {hV : Plain V} {s s' : VState A} {src dst : A} {v : ℕ}
    (h : V.move s src dst v = some s') :
    v ≤ s.bal src ∧ s'.bal = s.bal - single src v + single dst v ∧ s'.supply = s.supply ∧
      s'.allowance = s.allowance := by
  obtain ⟨h1, h2, h3⟩ := V.move_exact hV.rebasing (hV.feeOf s v) h
  obtain ⟨-, -, -, rfl⟩ := (V.move_eq_some).1 h
  exact ⟨h1, h2, h3, (V.credit_fields s src dst v).2.2.1⟩

omit [Zero A] in
/-- A successful move of `v` from `src` to `dst ≠ src` moves exactly `v`. -/
theorem moves_of_bal {s s' : VState A} {src dst : A} {v : ℕ} (hne : src ≠ dst)
    (h1 : v ≤ s.bal src) (h2 : s'.bal = s.bal - single src v + single dst v) :
    s'.bal src + v = s.bal src ∧ s'.bal dst = s.bal dst + v ∧
      ∀ a, a ≠ src → a ≠ dst → s'.bal a = s.bal a := by
  rw [h2]
  refine ⟨?_, move_apply_dst _ _ hne, fun a ha hd => move_apply_other _ _ (Ne.symm ha) (Ne.symm hd)⟩
  rw [move_apply_src _ _ hne]; omega

omit [Zero A] in
/-- A move never lowers the balance of an account other than its source. -/
theorem bal_ge_of_move {s s' : VState A} {src dst o : A} {v : ℕ} (ho : o ≠ src)
    (h2 : s'.bal = s.bal - single src v + single dst v) :
    s.bal o ≤ s'.bal o := by
  rw [h2]
  by_cases hd : o = dst
  · subst hd; rw [move_apply_dst _ _ (Ne.symm ho)]; omega
  · rw [move_apply_other _ _ (Ne.symm ho) (Ne.symm hd)]

/-- What a successful `transferFrom` changes in a plain variant: the allowance only by `spend`
(of `allowance[src][caller]`), the balances by a move. -/
theorem Plain.transferFrom {hV : Plain V} {s s' : VState A} {c src dst : A} {v : ℕ}
    (h : V.transferFrom s c src dst v = some s') :
    v ≤ s.bal src ∧ s'.bal = s.bal - single src v + single dst v ∧ s'.supply = s.supply ∧
      ∃ s1, V.spend s src c v = some s1 ∧ s'.allowance = s1.allowance := by
  obtain ⟨s1, h1, h2⟩ := V.transferFrom_eq_some h
  obtain ⟨hb, hs, -⟩ := V.spend_eq_some h1
  obtain ⟨m1, m2, m3, m4⟩ := Plain.move (hV := hV) h2
  rw [hb] at m1 m2; rw [hs] at m3
  exact ⟨m1, m2, m3, s1, h1, m4⟩

theorem Plain.transfer {hV : Plain V} {s s' : VState A} {c dst : A} {v : ℕ}
    (h : V.transfer s c dst v = some s') :
    v ≤ s.bal c ∧ s'.bal = s.bal - single c v + single dst v ∧ s'.supply = s.supply ∧
      s'.allowance = s.allowance := by
  unfold Variant.transfer at h
  split_ifs at h
  exact Plain.move (hV := hV) h

theorem Plain.approve {s s' : VState A} {c sp : A} {v : ℕ} (h : V.approve s c sp v = some s') :
    s' = s.setAllowance c sp v := by
  unfold Variant.approve at h
  split_ifs at h
  exact (Option.some.inj h).symm

/-- `spend` changes `allowance[o][sp]` only for `(o, sp) = (owner, spender)`. -/
theorem spend_allowance {s s1 : VState A} {owner spender o sp : A} {v : ℕ}
    (h : V.spend s owner spender v = some s1) (hne : s1.allowance o sp ≠ s.allowance o sp) :
    o = owner ∧ sp = spender := by
  unfold Variant.spend at h
  split_ifs at h <;> cases h <;> try exact absurd rfl hne
  simp only [VState.setAllowance] at hne
  by_contra hc
  apply hne
  by_cases ho : o = owner
  · subst ho
    have : sp ≠ spender := fun hs => hc ⟨rfl, hs⟩
    simp [Function.update_of_ne this]
  · simp [Function.update_of_ne ho]

omit [Zero A] in
theorem setAllowance_allowance_ne {s : VState A} {c sp o sp' : A} {v : ℕ} (ho : o ≠ c) :
    (s.setAllowance c sp v).allowance o sp' = s.allowance o sp' := by
  simp [VState.setAllowance, Function.update_of_ne ho]

/-- The state change of a successful call of a variant whose failures never return `false`. -/
theorem step_of_call {s s' : VState A} {c : A} {op : Call A} {r : RetData}
    (hg : V.guardFail ≠ .returnFalse) (ha : V.arithFail ≠ .returnFalse)
    (h : V.call s c op = .ok s' r) : V.step s c op = some s' ∧ r = V.retData op := by
  unfold Variant.call at h
  split at h
  · cases h; exact ⟨‹_›, rfl⟩
  · exfalso
    unfold Variant.failKind at h
    split_ifs at h
    · cases hk : V.guardFail <;> simp_all [Variant.failWith]
    · simp [Variant.failWith] at h
    · cases hk : V.arithFail <;> simp_all [Variant.failWith]

/-- A successful call changes the state by `step`, or (a `returnFalse` failure) not at all. -/
theorem step_or_same {s s' : VState A} {c : A} {op : Call A} {r : RetData}
    (h : V.call s c op = .ok s' r) : V.step s c op = some s' ∨ s' = s := by
  unfold Variant.call at h
  split at h
  · cases h; exact Or.inl ‹_›
  · unfold Variant.failWith at h
    split at h <;> cases h
    exact Or.inr rfl

/-- A successful call that does not return `false` changed the state by `step`. -/
theorem step_of_call_ne {s s' : VState A} {c : A} {op : Call A} {r : RetData}
    (h : V.call s c op = .ok s' r) (hr : r ≠ .word false) : V.step s c op = some s' := by
  unfold Variant.call at h
  split at h
  · cases h; assumption
  · unfold Variant.failWith at h
    split at h <;> cases h
    exact absurd rfl hr

/-- **Laws of a plain variant model** (any event rule `ev`): exact moves (in every state),
fixed supply, debits only by `transferFrom`, allowances only by their spender. -/
theorem Plain.exactMoves (hV : Plain V) (ev) (P : VState A → Prop) :
    (Variant.model V ev).ExactMoves P := by
  constructor
  · intro s caller dst v s' r _ hne h hr
    have hst : V.step s caller (.transfer dst v) = some s' := by
      exact step_of_call_ne h hr
    obtain ⟨h1, h2, -, -⟩ := Plain.transfer (hV := hV) hst
    simp only [TokenModel.MovesExactly, Variant.model, hV.balanceOf]
    exact moves_of_bal hne h1 h2
  · intro s caller src dst v s' r _ hne h hr
    have hst : V.step s caller (.transferFrom src dst v) = some s' := by
      exact step_of_call_ne h hr
    obtain ⟨h1, h2, -, -⟩ := Plain.transferFrom (hV := hV) hst
    simp only [TokenModel.MovesExactly, Variant.model, hV.balanceOf]
    exact moves_of_bal hne h1 h2

theorem Plain.supplyFixed (hV : Plain V) (ev) : (Variant.model V ev).SupplyFixed := by
  intro s caller c s' r _ h
  simp only [Variant.model, hV.totalSupply] at h ⊢
  rcases step_or_same h with h | rfl
  · cases c with
    | transfer d v => exact (Plain.transfer (hV := hV) h).2.2.1
    | transferFrom src d v => exact (Plain.transferFrom (hV := hV) h).2.2.1
    | approve sp v => rw [Plain.approve h]; rfl
    | other value => simp [hV.step_other] at h
    | permit o sp v live rec => simp [hV.step_permit] at h
  · rfl

theorem Plain.debitAuth (hV : Plain V) (ev) : (Variant.model V ev).DebitAuth := by
  intro s caller c s' r o h ho hlt
  simp only [Variant.model, hV.balanceOf] at h hlt
  rcases step_or_same h with h | rfl
  · cases c with
    | transfer d v =>
      obtain ⟨h1, h2, -, -⟩ := Plain.transfer (hV := hV) h
      exact absurd (bal_ge_of_move ho h2) (not_le.2 hlt)
    | transferFrom src d v =>
      by_cases hs : o = src
      · exact ⟨d, v, hs ▸ rfl⟩
      · obtain ⟨h1, h2, -, -⟩ := Plain.transferFrom (hV := hV) h
        exact absurd (bal_ge_of_move hs h2) (not_le.2 hlt)
    | approve sp v => rw [Plain.approve h] at hlt; exact absurd hlt (lt_irrefl _)
    | other value => simp [hV.step_other] at h
    | permit o sp v live rec => simp [hV.step_permit] at h
  · exact absurd hlt (lt_irrefl _)

theorem Plain.allowanceAuth (hV : Plain V) (ev) : (Variant.model V ev).AllowanceAuth := by
  intro s caller c s' r o sp h ho hne
  simp only [Variant.model, hV.allowanceOf] at h hne
  rcases step_or_same h with h | rfl
  · cases c with
    | transfer d v => exact absurd (by rw [(Plain.transfer (hV := hV) h).2.2.2]) hne
    | transferFrom src d v =>
      obtain ⟨-, -, -, s1, h1, h2⟩ := Plain.transferFrom (hV := hV) h
      rw [h2] at hne
      obtain ⟨rfl, rfl⟩ := spend_allowance h1 hne
      exact Or.inl ⟨rfl, d, v, rfl⟩
    | approve sp' v => rw [Plain.approve h, setAllowance_allowance_ne ho] at hne; exact absurd rfl hne
    | other value => simp [hV.step_other] at h
    | permit o sp v live rec => simp [hV.step_permit] at h
  · exact absurd rfl hne

/-! ## The supply bound as the actors see it -/

/-- **The supply bound as the actors see it**: the balances in the state sum to at most the
supply, which fits a word. A token abstraction reads only the actors' rows
(`QEDefi.ERC20.Spec.TokenAbs.read crypto Act`), whose sum is at most the supply in every state
the token reaches; `Σ bal = supply` (`Variant.WF`) holds only when the actors hold every
token. -/
def SubSupply (s : VState A) : Prop := total s.bal ≤ s.supply ∧ s.supply ≤ MAX

omit [Zero A] in
theorem add_le_total {f : A →₀ ℕ} {a b : A} (h : a ≠ b) : f a + f b ≤ total f := by
  have h1 := total_sub_single (f := f) (a := a) (le_refl (f a))
  have h2 := le_total (f - single a (f a)) b
  rw [sub_single_apply, ite_eq_right h] at h2
  have := le_total f a
  omega

omit [Zero A] in
/-- Under the bound, crediting `v ≤ bal src` to another account cannot overflow a word. -/
theorem SubSupply.credit_le {s : VState A} {src dst : A} {v : ℕ} (hw : SubSupply s)
    (hne : src ≠ dst) (hv : v ≤ s.bal src) : s.bal dst + v ≤ MAX := by
  have := add_le_total (f := s.bal) hne
  have := hw.1; have := hw.2
  omega

theorem Plain.subSupply_step (hV : Plain V) {s s' : VState A} {c : A} {op : Call A}
    (hw : SubSupply s) (h : V.step s c op = some s') : SubSupply s' := by
  cases op with
  | transfer d v =>
    obtain ⟨h1, h2, h3, -⟩ := Plain.transfer (hV := hV) h
    rw [SubSupply, h2, h3, Variant.total_move h1]; exact hw
  | transferFrom src d v =>
    obtain ⟨h1, h2, h3, -⟩ := Plain.transferFrom (hV := hV) h
    rw [SubSupply, h2, h3, Variant.total_move h1]; exact hw
  | approve sp v => rw [Plain.approve h]; exact hw
  | other value => simp [hV.step_other] at h
  | permit o sp v live rec => simp [hV.step_permit] at h

theorem subSupply_mint (hr : V.rebasing = false) {s s' : VState A} {c d : A} {v : ℕ}
    (hw : SubSupply s) (h : V.mint s c d v = some s') : SubSupply s' := by
  unfold Variant.mint at h
  split_ifs at h with h1 h2 h3 h4
  cases h
  simp only [SubSupply, Variant.units, hr, Bool.false_eq_true, ↓reduceIte, total_add_single]
  have := hw.1
  omega

theorem subSupply_burn (hr : V.rebasing = false) {s s' : VState A} {c src : A} {v : ℕ}
    (hw : SubSupply s) (h : V.burn s c src v = some s') : SubSupply s' := by
  unfold Variant.burn at h
  split_ifs at h with h1 h2 h3 h4
  cases h
  simp only [Variant.units, hr, Bool.false_eq_true, ↓reduceIte] at h4 ⊢
  have h4' : v ≤ s.bal src := by omega
  have := le_total s.bal src
  simp only [SubSupply, total_sub_single h4']
  have := hw.1; have := hw.2
  omega

theorem subSupply_adjust {s s' : VState A} {c sp : A} {up : Bool} {x : ℕ}
    (hw : SubSupply s) (h : V.adjustAllowance s c sp up x = some s') : SubSupply s' := by
  unfold Variant.adjustAllowance at h
  cases hk : V.helpers <;> simp only [hk, reduceCtorEq] at h <;> split_ifs at h <;> cases h <;>
    exact hw

end Plain

/-! ## YAMv2 -/

variable {A : Type} [DecidableEq A] [Zero A]

/-- **YAMv2's ERC-20 part as a policy record**: OpenZeppelin-3 `ERC20` (zero-address checks on
sender, recipient, owner and spender, also in the allowance decrease, which goes through
`_approve`), every allowance spent (`infinite := .none`), no `permit`. `mintAuth := .anyone` and
`helpers := .checked` are the open forms that `stepOp` gates (minter, nonzero owner). -/
def variant : Variant A :=
  { Variant.standard with zero := ⟨true, true, true, true⟩, spendViaApprove := true,
                          infinite := .none, mintAuth := .anyone, burnAuth := .nobody,
                          helpers := .checked, permitRule := .none }

/-- **YAMv2's events**: `transfer` emits `Transfer(caller, dst, v)`; `transferFrom` emits
`Transfer(src, dst, v)` and then, from `_approve`, `Approval(src, caller, allowance − v)`;
`approve` emits `Approval(caller, sp, v)`. (Only consulted for successful calls.) -/
def events (s : VState A) (caller : A) : Call A → List (Event A)
  | .transfer dst v => [.transfer caller dst v]
  | .transferFrom src dst v => [.transfer src dst v, .approval src caller (s.allowance src caller - v)]
  | .approve sp v => [.approval caller sp v]
  | .other _ => []
  | .permit .. => []

/-- YAMv2's other entry points. -/
inductive Op (A : Type) where
  /-- `mint(dst, v)` by `caller`. -/
  | mint (caller dst : A) (v : ℕ)
  /-- `increaseAllowance(sp, x)` by `caller`. -/
  | increaseAllowance (caller sp : A) (x : ℕ)
  /-- `decreaseAllowance(sp, x)` by `caller`. -/
  | decreaseAllowance (caller sp : A) (x : ℕ)

/-- The other entry points: `mint` only by the minter (`admin`); `dst ≠ 0`; the supply must not
overflow (SafeMath). The allowance helpers: `caller ≠ 0`, `sp ≠ 0`, SafeMath `add`/`sub`. -/
def stepOp (s : VState A) : Op A → Option (VState A)
  | .mint c d v => if c = s.admin then (variant : Variant A).mint s c d v else none
  | .increaseAllowance c sp x =>
    if c = 0 then none else (variant : Variant A).adjustAllowance s c sp true x
  | .decreaseAllowance c sp x =>
    if c = 0 then none else (variant : Variant A).adjustAllowance s c sp false x

/-- **The YAMv2 model.** States `VState A` (`admin` is the `minter`; the fee, pause, blacklist,
rebase, ether, frozen and nonce fields are unused), invariant `SubSupply` (`Σ bal ≤ supply ≤
MAX` over the balances in the state: the actors' view of the supply invariant, under which the
SafeMath recipient and supply additions cannot overflow). -/
def model : TokenModel (VState A) A (Op A) where
  balanceOf := (variant : Variant A).balanceOf
  totalSupply := (variant : Variant A).totalSupply
  allowance := (variant : Variant A).allowanceOf
  call := (variant : Variant A).call
  events := events
  op := stepOp
  wf := SubSupply

/-- The ERC-20 part of the model is the record's. -/
theorem model_call : (model : TokenModel (VState A) A (Op A)).call =
    (Variant.model (variant : Variant A) events).call := rfl

omit [DecidableEq A] [Zero A] in
theorem plain : Plain (variant : Variant A) := by constructor <;> rfl

omit [DecidableEq A] [Zero A] in
theorem sane : (variant : Variant A).Sane := by
  constructor <;> simp [variant, Variant.standard]

omit [DecidableEq A] [Zero A] in
theorem guardFail_ne : (variant : Variant A).guardFail ≠ .returnFalse := by
  simp [variant, Variant.standard]

omit [DecidableEq A] [Zero A] in
theorem arithFail_ne : (variant : Variant A).arithFail ≠ .returnFalse := by
  simp [variant, Variant.standard]

theorem returnsTrue : (model : TokenModel (VState A) A (Op A)).ReturnsTrue := by
  intro s caller c s' r hc h
  obtain ⟨-, rfl⟩ := step_of_call guardFail_ne arithFail_ne h
  cases c <;> simp_all [Call.returnsBool, Variant.retData, variant, Variant.standard]

theorem noFalseReturn : (model : TokenModel (VState A) A (Op A)).NoFalseReturn := by
  intro s caller c s' h
  obtain ⟨-, hr⟩ := step_of_call guardFail_ne arithFail_ne h
  cases c <;> simp [Variant.retData, variant, Variant.standard] at hr

theorem failKind_eq (s : VState A) (c : A) (op : Call A) :
    (variant : Variant A).failKind s c op = .revert := by
  unfold Variant.failKind
  have : (variant : Variant A).overflows s c op = false := by
    cases op <;> simp [Variant.overflows, Variant.feeOverflow, variant, Variant.standard]
  rw [this]
  split_ifs <;> first | rfl | contradiction

theorem revertsOnly : (model : TokenModel (VState A) A (Op A)).RevertsOnly := by
  intro s caller c hh h
  simp only [model, Variant.call, failKind_eq] at h
  split at h
  · cases h
  · simp only [Variant.failWith, Result.halt.injEq] at h; exact h.symm

theorem exactMoves (P : VState A → Prop) : (model : TokenModel (VState A) A (Op A)).ExactMoves P :=
  plain.exactMoves events P

theorem supplyFixed : (model : TokenModel (VState A) A (Op A)).SupplyFixed :=
  plain.supplyFixed events

theorem debitAuth : (model : TokenModel (VState A) A (Op A)).DebitAuth := plain.debitAuth events

theorem allowanceAuth : (model : TokenModel (VState A) A (Op A)).AllowanceAuth :=
  plain.allowanceAuth events

theorem wfInvariant : (model : TokenModel (VState A) A (Op A)).WFInvariant := by
  constructor
  · intro s caller c s' r hw h
    obtain ⟨h, -⟩ := step_of_call guardFail_ne arithFail_ne h
    exact plain.subSupply_step hw h
  · intro s e s' (hw : SubSupply s) h
    cases e with
    | mint c d v =>
      simp only [model, stepOp] at h; split_ifs at h
      exact subSupply_mint (V := (variant : Variant A)) rfl hw h
    | increaseAllowance c sp x =>
      simp only [model, stepOp] at h; split_ifs at h
      exact subSupply_adjust hw h
    | decreaseAllowance c sp x =>
      simp only [model, stepOp] at h; split_ifs at h
      exact subSupply_adjust hw h

/-- **YAMv2 satisfies every standard law**, in every state for the moves. -/
theorem yamv2_laws : (model : TokenModel (VState A) A (Op A)).Standard fun _ => True where
  returnsTrue := returnsTrue
  noFalseReturn := noFalseReturn
  revertsOnly := revertsOnly
  exactMoves := exactMoves _
  supplyFixed := supplyFixed
  debitAuth := debitAuth
  allowanceAuth := allowanceAuth
  wfInvariant := wfInvariant

end QEDefi.ERC20.Spec.YAMV2
