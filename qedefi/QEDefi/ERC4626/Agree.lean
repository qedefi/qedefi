import QEDefi.ERC4626.SolmateProps
import QEDefi.Trace.Lift

/-!
# Agreement of model states up to unobserved allowances

Storage frames are pointwise (`QEDefi.ERC20.RepOn`): Keccak hypotheses cannot exclude a
written slot colliding with *some* allowance entry, so concrete states match the model only
up to allowances outside a set `G` of pairs (in practice, the actors of a trace).
`AgreeOn G` is that relation, and `step_rel` shows the model respects it on operations that
only read allowances in `G` (`Reads`).
-/

namespace QEDefi.ERC4626
open QEDefi.Math QEDefi.ERC20 QEDefi.ERC4626.Solmate QEDefi.Trace

variable {A : Type} [DecidableEq A]

/-! ## `Option.Rel` combinators -/

theorem rel_bind {α β γ δ : Type} {R : α → β → Prop} {R' : γ → δ → Prop} {a : Option α}
    {b : Option β} (h : Option.Rel R a b) {f : α → Option γ} {g : β → Option δ}
    (hfg : ∀ x y, R x y → Option.Rel R' (f x) (g y)) : Option.Rel R' (a.bind f) (b.bind g) := by
  cases h with
  | none => exact .none
  | some hxy => exact hfg _ _ hxy

theorem rel_map {α β γ δ : Type} {R : α → β → Prop} {R' : γ → δ → Prop} {a : Option α}
    {b : Option β} (h : Option.Rel R a b) {f : α → γ} {g : β → δ}
    (hfg : ∀ x y, R x y → R' (f x) (g y)) : Option.Rel R' (a.map f) (b.map g) := by
  cases h with
  | none => exact .none
  | some hxy => exact .some (hfg _ _ hxy)

theorem rel_of_eq {α β : Type} {R : α → β → Prop} {f : α → β} {a : Option α}
    (h : ∀ x, R x (f x)) : Option.Rel R a (a.map f) := by
  cases a with
  | none => exact .none
  | some x => exact .some (h x)

theorem rel_refl {α : Type} {R : α → α → Prop} (h : ∀ x, R x x) (a : Option α) :
    Option.Rel R a a := by
  cases a with
  | none => exact .none
  | some x => exact .some (h x)

theorem rel_getD {α : Type} {R : α → α → Prop} {a b : Option α} (h : Option.Rel R a b)
    {x y : α} (hxy : R x y) : R (a.getD x) (b.getD y) := by
  cases h with
  | none => exact hxy
  | some h => exact h

/-! ## Ledgers -/

/-- Two ledgers agree up to the allowances of pairs outside `G`. -/
structure TokAgree (G : A → A → Prop) (t u : Token A) : Prop where
  /-- Same balances. -/
  balanceOf : t.balanceOf = u.balanceOf
  /-- Same total supply. -/
  totalSupply : t.totalSupply = u.totalSupply
  /-- Same allowances on `G`. -/
  allowance : ∀ o sp, G o sp → t.allowance o sp = u.allowance o sp

namespace TokAgree

variable {G : A → A → Prop}

theorem refl (t : Token A) : TokAgree G t t := ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem symm {t u : Token A} (h : TokAgree G t u) : TokAgree G u t :=
  ⟨h.1.symm, h.2.symm, fun o sp hg => (h.3 o sp hg).symm⟩

theorem trans {t u v : Token A} (h₁ : TokAgree G t u) (h₂ : TokAgree G u v) : TokAgree G t v :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2, fun o sp hg => (h₁.3 o sp hg).trans (h₂.3 o sp hg)⟩

theorem mono {G' : A → A → Prop} {t u : Token A} (h : TokAgree G t u)
    (hG : ∀ o sp, G' o sp → G o sp) : TokAgree G' t u :=
  ⟨h.1, h.2, fun o sp hg => h.3 o sp (hG o sp hg)⟩

theorem wf {t u : Token A} (h : TokAgree G t u) (hw : t.WF) : u.WF := by
  unfold Token.WF at *; rw [← h.1, ← h.2]; exact hw

theorem setAllowance {t u : Token A} (h : TokAgree G t u) (o sp : A) (v : ℕ) :
    TokAgree G (t.setAllowance o sp v) (u.setAllowance o sp v) := by
  refine ⟨h.1, h.2, fun o' sp' hg => ?_⟩
  simp only [Token.setAllowance]
  by_cases ho : o' = o
  · subst ho
    by_cases hs : sp' = sp
    · subst hs; simp
    · simp [hs, h.3 o' sp' hg]
  · simp [ho, h.3 o' sp' hg]

theorem transfer {t u : Token A} (h : TokAgree G t u) (src dst : A) (v : ℕ) :
    Option.Rel (TokAgree G) (t.transfer src dst v) (u.transfer src dst v) := by
  unfold Token.transfer
  rw [h.1]
  split
  · exact .none
  · exact .some ⟨rfl, h.2, h.3⟩

theorem spend {t u : Token A} (h : TokAgree G t u) {o sp : A} (hg : G o sp) (v : ℕ) :
    Option.Rel (TokAgree G) (t.spend o sp v) (u.spend o sp v) := by
  unfold Token.spend
  rw [h.3 o sp hg]
  split
  · exact .some h
  · split
    · exact .none
    · exact .some (h.setAllowance o sp _)

theorem transferFrom {t u : Token A} (h : TokAgree G t u) {sp src : A} (hg : G src sp)
    (dst : A) (v : ℕ) :
    Option.Rel (TokAgree G) (t.transferFrom sp src dst v) (u.transferFrom sp src dst v) :=
  rel_bind (h.spend hg v) fun _ _ hxy => hxy.transfer src dst v

theorem approve {t u : Token A} (h : TokAgree G t u) (o sp : A) (v : ℕ) :
    TokAgree G (t.approve o sp v) (u.approve o sp v) :=
  h.setAllowance o sp v

theorem mint {t u : Token A} (h : TokAgree G t u) (dst : A) (v : ℕ) :
    Option.Rel (TokAgree G) (t.mint dst v) (u.mint dst v) := by
  unfold Token.mint
  rw [h.2]
  split
  · exact .none
  · exact .some ⟨by rw [h.1], rfl, h.3⟩

theorem burn {t u : Token A} (h : TokAgree G t u) (src : A) (v : ℕ) :
    Option.Rel (TokAgree G) (t.burn src v) (u.burn src v) := by
  unfold Token.burn
  rw [h.1]
  split
  · exact .none
  · exact .some ⟨rfl, by rw [h.2], h.3⟩

end TokAgree

/-! ## Vault states -/

/-- Two vault states agree up to the allowances (in either ledger) of pairs outside `G`. -/
structure AgreeOn (G : A → A → Prop) (s t : State A) : Prop where
  /-- Same vault address. -/
  self : s.self = t.self
  /-- The asset ledgers agree. -/
  asset : TokAgree G s.asset t.asset
  /-- The share ledgers agree. -/
  shares : TokAgree G s.shares t.shares
  /-- Same `afterDeposit` counter. -/
  afterDeposit : s.afterDepositCount = t.afterDepositCount
  /-- Same `beforeWithdraw` counter. -/
  beforeWithdraw : s.beforeWithdrawCount = t.beforeWithdrawCount

namespace AgreeOn

variable {G : A → A → Prop}

theorem refl (s : State A) : AgreeOn G s s :=
  ⟨rfl, .refl _, .refl _, rfl, rfl⟩

theorem symm {s t : State A} (h : AgreeOn G s t) : AgreeOn G t s :=
  ⟨h.1.symm, h.2.symm, h.3.symm, h.4.symm, h.5.symm⟩

theorem trans {s t u : State A} (h₁ : AgreeOn G s t) (h₂ : AgreeOn G t u) : AgreeOn G s u :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2, h₁.3.trans h₂.3, h₁.4.trans h₂.4, h₁.5.trans h₂.5⟩

theorem equivalence : Equivalence (AgreeOn (A := A) G) :=
  ⟨refl, symm, trans⟩

theorem mono {G' : A → A → Prop} {s t : State A} (h : AgreeOn G s t)
    (hG : ∀ o sp, G' o sp → G o sp) : AgreeOn G' s t :=
  ⟨h.1, h.2.mono hG, h.3.mono hG, h.4, h.5⟩

theorem of_eq {s t : State A} (h : s = t) : AgreeOn G s t := h ▸ refl s

theorem totalSupply {s t : State A} (h : AgreeOn G s t) : s.totalSupply = t.totalSupply :=
  h.shares.totalSupply

theorem totalAssets {s t : State A} (h : AgreeOn G s t) : s.totalAssets = t.totalAssets := by
  unfold State.totalAssets; rw [h.asset.balanceOf, h.self]

theorem inv {s t : State A} (h : AgreeOn G s t) (hi : Inv s) : Inv t :=
  ⟨h.asset.wf hi.1, h.shares.wf hi.2⟩

theorem price {s t : State A} (h : AgreeOn G s t) : s.price = t.price := by
  unfold State.price; rw [h.totalAssets, h.totalSupply]

theorem convertToShares {s t : State A} (h : AgreeOn G s t) (x : ℕ) :
    s.convertToShares x = t.convertToShares x := by
  unfold State.convertToShares; rw [h.totalSupply, h.totalAssets]

theorem convertToAssets {s t : State A} (h : AgreeOn G s t) (x : ℕ) :
    s.convertToAssets x = t.convertToAssets x := by
  unfold State.convertToAssets; rw [h.totalSupply, h.totalAssets]

theorem previewMint {s t : State A} (h : AgreeOn G s t) (x : ℕ) :
    s.previewMint x = t.previewMint x := by
  unfold State.previewMint; rw [h.totalSupply, h.totalAssets]

theorem previewWithdraw {s t : State A} (h : AgreeOn G s t) (x : ℕ) :
    s.previewWithdraw x = t.previewWithdraw x := by
  unfold State.previewWithdraw; rw [h.totalSupply, h.totalAssets]

end AgreeOn

/-! ## The model respects agreement -/

/-- The allowances an operation of the vault at `self` reads are in `G`. -/
def Reads (G : A → A → Prop) (self : A) : Op A → Prop
  | .deposit c _ _ => G c self
  | .mint c _ _ => G c self
  | .withdraw c _ _ o => c ≠ o → G o c
  | .redeem c _ _ o => c ≠ o → G o c
  | .transfer _ _ _ => True
  | .transferFrom c src _ _ => G src c
  | .approve _ _ _ => True
  | .assetTransfer _ _ _ => True
  | .assetTransferFrom c src _ _ => G src c
  | .assetApprove _ _ _ => True
  | .assetMint _ _ => True
  | .assetBurn _ _ => True

variable {G : A → A → Prop}

theorem spendIfNotOwner_rel {t u : Token A} (h : TokAgree G t u) {c o : A} (hg : c ≠ o → G o c)
    (n : ℕ) :
    Option.Rel (TokAgree G) (spendIfNotOwner t c o n) (spendIfNotOwner u c o n) := by
  unfold spendIfNotOwner
  split
  · exact h.spend (hg ‹_›) n
  · exact .some h

theorem deposit_rel {s t : State A} (h : AgreeOn G s t) {c r : A} (hg : G c s.self) (a : ℕ) :
    Option.Rel (fun x y : State A × ℕ => AgreeOn G x.1 y.1 ∧ x.2 = y.2)
      (deposit s c a r) (deposit t c a r) := by
  unfold deposit State.previewDeposit
  rw [h.convertToShares]
  refine rel_bind (rel_refl (R := Eq) (fun _ => rfl) _) fun n _ hn => ?_
  subst hn
  split
  · exact .none
  · rw [← h.self]
    refine rel_bind (h.asset.transferFrom hg s.self a) fun a₁ a₂ ha => ?_
    refine rel_bind (h.shares.mint r n) fun s₁ s₂ hs => ?_
    rw [h.afterDeposit]
    exact rel_map (rel_refl (R := Eq) (fun _ => rfl) _) fun c₁ _ hc =>
      ⟨⟨rfl, ha, hs, hc, h.beforeWithdraw⟩, rfl⟩

theorem mint_rel {s t : State A} (h : AgreeOn G s t) {c r : A} (hg : G c s.self) (n : ℕ) :
    Option.Rel (fun x y : State A × ℕ => AgreeOn G x.1 y.1 ∧ x.2 = y.2)
      (mint s c n r) (mint t c n r) := by
  unfold mint
  rw [h.previewMint]
  refine rel_bind (rel_refl (R := Eq) (fun _ => rfl) _) fun a _ ha => ?_
  subst ha
  rw [← h.self]
  refine rel_bind (h.asset.transferFrom hg s.self a) fun a₁ a₂ ha => ?_
  refine rel_bind (h.shares.mint r n) fun s₁ s₂ hs => ?_
  rw [h.afterDeposit]
  exact rel_map (rel_refl (R := Eq) (fun _ => rfl) _) fun c₁ _ hc =>
    ⟨⟨rfl, ha, hs, hc, h.beforeWithdraw⟩, rfl⟩

theorem withdraw_rel {s t : State A} (h : AgreeOn G s t) {c r o : A} (hg : c ≠ o → G o c)
    (a : ℕ) :
    Option.Rel (fun x y : State A × ℕ => AgreeOn G x.1 y.1 ∧ x.2 = y.2)
      (withdraw s c a r o) (withdraw t c a r o) := by
  unfold withdraw
  rw [h.previewWithdraw]
  refine rel_bind (rel_refl (R := Eq) (fun _ => rfl) _) fun n _ hn => ?_
  subst hn
  refine rel_bind (spendIfNotOwner_rel h.shares hg n) fun s₁ s₂ hs => ?_
  rw [h.beforeWithdraw]
  refine rel_bind (rel_refl (R := Eq) (fun _ => rfl) _) fun c₁ _ hc => ?_
  subst hc
  refine rel_bind (hs.burn o n) fun s₁' s₂' hs' => ?_
  rw [← h.self]
  exact rel_map (h.asset.transfer s.self r a) fun a₁ a₂ ha' =>
    ⟨⟨rfl, ha', hs', h.afterDeposit, rfl⟩, rfl⟩

theorem redeem_rel {s t : State A} (h : AgreeOn G s t) {c r o : A} (hg : c ≠ o → G o c)
    (n : ℕ) :
    Option.Rel (fun x y : State A × ℕ => AgreeOn G x.1 y.1 ∧ x.2 = y.2)
      (redeem s c n r o) (redeem t c n r o) := by
  unfold redeem State.previewRedeem
  refine rel_bind (spendIfNotOwner_rel h.shares hg n) fun s₁ s₂ hs => ?_
  rw [h.convertToAssets]
  refine rel_bind (rel_refl (R := Eq) (fun _ => rfl) _) fun a _ ha => ?_
  subst ha
  split
  · exact .none
  · rw [h.beforeWithdraw]
    refine rel_bind (rel_refl (R := Eq) (fun _ => rfl) _) fun c₁ _ hc => ?_
    subst hc
    refine rel_bind (hs.burn o n) fun s₁' s₂' hs' => ?_
    rw [← h.self]
    exact rel_map (h.asset.transfer s.self r a) fun a₁ a₂ ha' =>
      ⟨⟨rfl, ha', hs', h.afterDeposit, rfl⟩, rfl⟩

/-- On an operation reading only allowances in `G`, two agreeing states both revert or both
succeed with agreeing states. -/
theorem step_rel {s t : State A} (h : AgreeOn G s t) {op : Op A} (hr : Reads G s.self op) :
    Option.Rel (AgreeOn G) (step s op) (step t op) := by
  have hfst : ∀ {x y : Option (State A × ℕ)},
      Option.Rel (fun x y : State A × ℕ => AgreeOn G x.1 y.1 ∧ x.2 = y.2) x y →
        Option.Rel (AgreeOn G) (x.map Prod.fst) (y.map Prod.fst) :=
    fun hxy => rel_map hxy fun _ _ hp => hp.1
  cases op with
  | deposit c a r => exact hfst (deposit_rel h hr a)
  | mint c n r => exact hfst (mint_rel h hr n)
  | withdraw c a r o => exact hfst (withdraw_rel h hr a)
  | redeem c n r o => exact hfst (redeem_rel h hr n)
  | transfer c d v =>
    exact rel_map (h.shares.transfer c d v) fun _ _ hx => ⟨h.self, h.asset, hx, h.4, h.5⟩
  | transferFrom c src d v =>
    exact rel_map (h.shares.transferFrom hr d v) fun _ _ hx => ⟨h.self, h.asset, hx, h.4, h.5⟩
  | approve c sp v => exact .some ⟨h.self, h.asset, h.shares.approve c sp v, h.4, h.5⟩
  | assetTransfer c d v =>
    exact rel_map (h.asset.transfer c d v) fun _ _ hx => ⟨h.self, hx, h.shares, h.4, h.5⟩
  | assetTransferFrom c src d v =>
    exact rel_map (h.asset.transferFrom hr d v) fun _ _ hx => ⟨h.self, hx, h.shares, h.4, h.5⟩
  | assetApprove c sp v => exact .some ⟨h.self, h.asset.approve c sp v, h.shares, h.4, h.5⟩
  | assetMint d v =>
    exact rel_map (h.asset.mint d v) fun _ _ hx => ⟨h.self, hx, h.shares, h.4, h.5⟩
  | assetBurn src v =>
    exact rel_map (h.asset.burn src v) fun _ _ hx => ⟨h.self, hx, h.shares, h.4, h.5⟩

theorem stepD_agree {s t : State A} (h : AgreeOn G s t) {op : Op A} (hr : Reads G s.self op) :
    AgreeOn G (Lift.stepD step s op) (Lift.stepD step t op) := by
  unfold Lift.stepD
  exact rel_getD (step_rel h hr) h

theorem exec_eq (s : State A) (ops : List (Op A)) : exec s ops = Lift.exec step s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih _

theorem self_stepD (s : State A) (op : Op A) : (Lift.stepD step s op).self = s.self := by
  unfold Lift.stepD
  cases e : step s op with
  | none => rfl
  | some s' => exact self_step e

theorem self_exec (s : State A) (ops : List (Op A)) : (Lift.exec step s ops).self = s.self := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (self_stepD s op)

end QEDefi.ERC4626
