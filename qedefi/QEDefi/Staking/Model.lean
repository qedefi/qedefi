import QEDefi.Staking.Deps
import QEDefi.Trace.Time

/-!
# A time-indexed model of Synthetix `StakingRewards`

The reward accounting of Synthetix's `StakingRewards` (`rewardPerToken`, `earned`,
`updateReward`, `stake`, `withdraw`, `getReward`, `notifyRewardAmount`) with the time `t` a
parameter, in `ℕ` with the contract's floor divisions. Accrual is in **closed form**:
`rewardPerToken t = stored + ⌊(min t finish − last) · rate · unit / supply⌋`, piecewise linear in
`t` between updates and constant after `finish` (`rpt_after_finish`, `rpt_mono`).

Theorems, for any users `A` (a `Fintype`), each by one induction over a monotone timed
execution (`QEDefi.Trace.Time`), never by enumerating times:

* **Solvency** (`claimed_add_earned_le`): what users have claimed plus what they have earned
  so far never exceeds the rewards funded by `notifyRewardAmount`, at every time. The
  invariant (`Funded`) is time-free: claims + stored rewards + the accrual not yet stored +
  `rate · (finish − last)` (still to stream) is at most what was funded; each update moves
  accrual from the third term to the second, and the floors only lose dust.
* **No dilution** (`entitlement_mono`): a user's entitlement `earned + claimed` never
  decreases: no action of anyone (stakes, withdrawals, claims, new reward periods) takes away
  rewards already accrued, and time only adds to them.

This is a model-level demonstrator: the bytecode refinement (as for `VestingWallet`) is not
done here.
-/

namespace QEDefi.Staking
open QEDefi.Trace.Lift QEDefi.Trace.Time

/-- Parameters: the reward period's length and the fixed-point unit (`1e18`). -/
structure Params where
  /-- `rewardsDuration`. -/
  duration : Nat
  /-- The fixed-point unit of `rewardPerToken` (`1e18`). -/
  unit : Nat

/-- The contract's state, plus the ghost `funded` (rewards notified so far) and `claimed`
(rewards paid to each user). -/
structure State (A : Type) where
  /-- `_totalSupply`. -/
  supply : Nat
  /-- `_balances`. -/
  bal : A → Nat
  /-- `rewardRate`. -/
  rate : Nat
  /-- `periodFinish`. -/
  finish : Nat
  /-- `lastUpdateTime`. -/
  last : Nat
  /-- `rewardPerTokenStored`. -/
  stored : Nat
  /-- `userRewardPerTokenPaid`. -/
  paid : A → Nat
  /-- `rewards`. -/
  rewards : A → Nat
  /-- Ghost: total rewards notified (and transferred in). -/
  funded : Nat
  /-- Ghost: rewards paid out to each user. -/
  claimed : A → Nat

/-- The operations. -/
inductive Op (A : Type) where
  /-- `stake(x)` by `a`. -/
  | stake (a : A) (x : Nat)
  /-- `withdraw(x)` by `a`. -/
  | withdraw (a : A) (x : Nat)
  /-- `getReward()` by `a`. -/
  | getReward (a : A)
  /-- `notifyRewardAmount(x)` (rewards distribution). -/
  | notify (x : Nat)

variable {A : Type} (P : Params)

/-- `lastTimeRewardApplicable()` at time `t`. -/
def lta (s : State A) (t : Nat) : Nat := min t s.finish

/-- **`rewardPerToken()` at time `t`, in closed form.** -/
def rpt (s : State A) (t : Nat) : Nat :=
  if s.supply = 0 then s.stored
  else s.stored + (lta s t - s.last) * s.rate * P.unit / s.supply

/-- `earned(a)` at time `t`. -/
def earned (s : State A) (t : Nat) (a : A) : Nat :=
  s.rewards a + s.bal a * (rpt P s t - s.paid a) / P.unit

/-- The `updateReward(account)` modifier at time `t` (`none`: `address(0)`). -/
def update [DecidableEq A] (t : Nat) (s : State A) : Option A → State A
  | none => { s with stored := rpt P s t, last := lta s t }
  | some a =>
    { s with
      stored := rpt P s t
      last := lta s t
      rewards := Function.update s.rewards a (earned P s t a)
      paid := Function.update s.paid a (rpt P s t) }

/-- The model step at time `t`, with the contract's reverts (`require(amount > 0)`, the
balance check of `withdraw`, `require(rewardRate <= balance / rewardsDuration)` of
`notifyRewardAmount`, the reward tokens being transferred in by the distributor). -/
def step [DecidableEq A] [Fintype A] (t : Nat) (s : State A) : Op A → Option (State A)
  | .stake a x =>
    if x = 0 then none else
    let s := update P t s (some a)
    some { s with
      supply := s.supply + x
      bal := Function.update s.bal a (s.bal a + x) }
  | .withdraw a x =>
    if x = 0 ∨ s.bal a < x then none else
    let s := update P t s (some a)
    some { s with
      supply := s.supply - x
      bal := Function.update s.bal a (s.bal a - x) }
  | .getReward a =>
    let s := update P t s (some a)
    some { s with
      rewards := Function.update s.rewards a 0
      claimed := Function.update s.claimed a (s.claimed a + s.rewards a) }
  | .notify x =>
    let s := update P t s none
    let rate := if s.finish ≤ t then x / P.duration else (x + (s.finish - t) * s.rate) / P.duration
    if (s.funded + x - ∑ b, s.claimed b) / P.duration < rate then none
    else some { s with
      rate
      last := t
      finish := t + P.duration
      funded := s.funded + x }

/-! ## Closed-form accrual -/

variable {P}

theorem lta_mono (s : State A) {t t' : Nat} (h : t ≤ t') : lta s t ≤ lta s t' := by
  unfold lta; omega

/-- **`rewardPerToken` never decreases in time.** -/
theorem rpt_mono (s : State A) {t t' : Nat} (h : t ≤ t') : rpt P s t ≤ rpt P s t' := by
  unfold rpt
  split
  · exact Nat.le_refl _
  · have := lta_mono s h
    exact Nat.add_le_add_left (Nat.div_le_div_right (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (by omega)))) _

/-- After `periodFinish` nothing more accrues. -/
theorem rpt_after_finish (s : State A) {t : Nat} (h : s.finish ≤ t) : rpt P s t = rpt P s s.finish := by
  unfold rpt lta
  rw [Nat.min_eq_right h, Nat.min_self]

/-- `earned` never decreases in time. -/
theorem earned_mono (s : State A) (a : A) {t t' : Nat} (h : t ≤ t') :
    earned P s t a ≤ earned P s t' a := by
  unfold earned
  have := rpt_mono (P := P) s h
  exact Nat.add_le_add_left (Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))) _

/-- `rewardPerToken` right after an update at `t` is unchanged at `t`. -/
theorem rpt_update [DecidableEq A] (s : State A) (t : Nat) (o : Option A) :
    rpt P (update P t s o) t = rpt P s t := by
  cases o <;>
  · simp only [update, rpt, lta]
    split <;> simp

/-! ## Sums over users -/

section Sums

variable [DecidableEq A] [Fintype A]

theorem sum_update (f : A → Nat) (a : A) (v : Nat) :
    (∑ b, Function.update f a v b) + f a = (∑ b, f b) + v := by
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ a),
    ← Finset.add_sum_erase Finset.univ (Function.update f a v) (Finset.mem_univ a)]
  have : ∑ x ∈ Finset.univ.erase a, Function.update f a v x =
      ∑ x ∈ Finset.univ.erase a, f x :=
    Finset.sum_congr rfl fun x hx => Function.update_of_ne (Finset.ne_of_mem_erase hx) _ _
  rw [this, Function.update_self]
  omega

omit [Fintype A] in
theorem sum_div_le (s : Finset A) (f : A → Nat) (u : Nat) :
    ∑ b ∈ s, f b / u ≤ (∑ b ∈ s, f b) / u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact Nat.le_trans (Nat.add_le_add_left ih _) Nat.div_add_div_le_add_div

end Sums

/-! ## Solvency -/

section Solvency

variable [Fintype A]

/-- What the contract owes in the long run: claims, stored rewards, the accrual not yet
stored (`⌊Σ bal·(stored − paid) / unit⌋`), and what is still to stream. -/
def liability (s : State A) : Nat :=
  (∑ b, s.claimed b) + (∑ b, s.rewards b) + (∑ b, s.bal b * (s.stored - s.paid b)) / P.unit +
    s.rate * (s.finish - s.last)

variable (P) in
/-- **The solvency invariant** (time-free): supply is the sum of balances, users' paid
checkpoints are at most `stored`, `last ≤ finish`, and the liability is funded. -/
structure Funded (s : State A) : Prop where
  /-- `_totalSupply = Σ _balances`. -/
  supply : s.supply = ∑ b, s.bal b
  /-- Checkpoints are at most `rewardPerTokenStored`. -/
  paid : ∀ b, s.paid b ≤ s.stored
  /-- `lastUpdateTime ≤ periodFinish`. -/
  last : s.last ≤ s.finish
  /-- The liability is funded. -/
  funded : liability (P := P) s ≤ s.funded

omit [Fintype A] in
/-- The accrual since `last`, summed over users, is at most what streamed: `supply · Δrpt ≤
(lta − last) · rate · unit`. -/
theorem supply_mul_rpt_sub_le (s : State A) (t : Nat) :
    s.supply * (rpt P s t - s.stored) ≤ (lta s t - s.last) * s.rate * P.unit := by
  unfold rpt
  split
  · simp
  · rw [Nat.add_sub_cancel_left]
    exact Nat.mul_div_le _ _

/-- `Σ bal·(rpt − paid) = Σ bal·(stored − paid) + supply·(rpt − stored)` under `Funded`. -/
theorem sum_bal_rpt (s : State A) (hf : Funded P s) (t : Nat) :
    ∑ b, s.bal b * (rpt P s t - s.paid b) =
      (∑ b, s.bal b * (s.stored - s.paid b)) + s.supply * (rpt P s t - s.stored) := by
  have hst : s.stored ≤ rpt P s t := by
    unfold rpt; split
    · exact Nat.le_refl _
    · exact Nat.le_add_right _ _
  rw [hf.supply, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := hf.paid b
  rw [← Nat.mul_add]
  congr 1
  omega

theorem liability_update [DecidableEq A] (s : State A) (hf : Funded P s) {t : Nat} (ht : s.last ≤ t) (o : Option A) :
    liability (P := P) (update P t s o) ≤ liability (P := P) s := by
  have hl := supply_mul_rpt_sub_le (P := P) s t
  have hsum := sum_bal_rpt s hf t
  have hlast : s.last ≤ lta s t := by unfold lta; have := hf.last; omega
  have hfin : lta s t ≤ s.finish := Nat.min_le_right _ _
  have hu : 0 < P.unit ∨ P.unit = 0 := by omega
  -- the accrual not yet stored, after the update, is at most the old one plus what streamed
  have key : (∑ b, s.bal b * (rpt P s t - s.paid b)) / P.unit ≤
      (∑ b, s.bal b * (s.stored - s.paid b)) / P.unit + (lta s t - s.last) * s.rate := by
    rw [hsum]
    rcases hu with hu | hu
    · calc (∑ b, s.bal b * (s.stored - s.paid b) + s.supply * (rpt P s t - s.stored)) / P.unit
          ≤ (∑ b, s.bal b * (s.stored - s.paid b) + (lta s t - s.last) * s.rate * P.unit) /
              P.unit := Nat.div_le_div_right (by omega)
        _ = _ := Nat.add_mul_div_right _ _ hu
    · simp [hu]
  have hrate : s.rate * (s.finish - lta s t) + (lta s t - s.last) * s.rate =
      s.rate * (s.finish - s.last) := by
    rw [Nat.mul_comm (lta s t - s.last), ← Nat.mul_add]; congr 1; omega
  cases o with
  | none =>
    simp only [liability, update]
    have h0 : ∑ b, s.bal b * (rpt P s t - s.paid b) =
        ∑ b, s.bal b * ((rpt P s t) - s.paid b) := rfl
    omega
  | some a =>
    simp only [liability, update]
    -- the user's accrual moves from the unstored term to `rewards`
    have hr := sum_update s.rewards a (earned P s t a)
    have hb : (∑ b, s.bal b * (rpt P s t - Function.update s.paid a (rpt P s t) b)) +
        s.bal a * (rpt P s t - s.paid a) = ∑ b, s.bal b * (rpt P s t - s.paid b) := by
      have := sum_update (fun b => s.bal b * (rpt P s t - s.paid b)) a 0
      have he : (fun b => Function.update (fun b => s.bal b * (rpt P s t - s.paid b)) a 0 b) =
          fun b => s.bal b * (rpt P s t - Function.update s.paid a (rpt P s t) b) := by
        funext b
        by_cases hb : b = a
        · subst hb; simp
        · simp [Function.update_of_ne hb]
      rw [he] at this
      simpa using this
    have hdiv : s.bal a * (rpt P s t - s.paid a) / P.unit +
        (∑ b, s.bal b * (rpt P s t - Function.update s.paid a (rpt P s t) b)) / P.unit ≤
        (∑ b, s.bal b * (rpt P s t - s.paid b)) / P.unit := by
      rw [← hb, Nat.add_comm (∑ b, _)]
      exact Nat.div_add_div_le_add_div
    have he : earned P s t a = s.rewards a + s.bal a * (rpt P s t - s.paid a) / P.unit := rfl
    have hz : s.rate * (lta s t - lta s t) = 0 := by simp
    omega

theorem funded_update [DecidableEq A] {s : State A} (hf : Funded P s) {t : Nat} (ht : s.last ≤ t)
    (o : Option A) : Funded P (update P t s o) ∧ (update P t s o).last ≤ t := by
  have hst : s.stored ≤ rpt P s t := by
    unfold rpt; split
    · exact Nat.le_refl _
    · exact Nat.le_add_right _ _
  have hl := liability_update s hf ht o
  have hlt : lta s t ≤ t := Nat.min_le_left _ _
  cases o with
  | none =>
    exact ⟨⟨hf.supply, fun b => Nat.le_trans (hf.paid b) hst, Nat.min_le_right _ _,
      Nat.le_trans hl hf.funded⟩, hlt⟩
  | some a =>
    refine ⟨⟨hf.supply, fun b => ?_, Nat.min_le_right _ _, Nat.le_trans hl hf.funded⟩, hlt⟩
    simp only [update]
    by_cases hb : b = a
    · subst hb; simp
    · rw [Function.update_of_ne hb]; exact Nat.le_trans (hf.paid b) hst

/-- Changing the balance of a user whose checkpoint is `stored` leaves the unstored accrual
unchanged. -/
theorem sum_bal_update [DecidableEq A] (s : State A) (a : A) (v : Nat)
    (hpa : s.paid a = s.stored) :
    ∑ b, Function.update s.bal a v b * (s.stored - s.paid b) =
      ∑ b, s.bal b * (s.stored - s.paid b) := by
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : b = a
  · subst hb; simp [hpa]
  · rw [Function.update_of_ne hb]

omit [Fintype A] in
theorem update_paid_self [DecidableEq A] (s : State A) (t : Nat) (a : A) :
    (update P t s (some a)).paid a = (update P t s (some a)).stored := by
  simp [update]

/-- **Every step at a time not before `last` keeps `Funded`.** -/
theorem funded_step [DecidableEq A] {s s' : State A} (hf : Funded P s) {t : Nat}
    (ht : s.last ≤ t) {op : Op A} (h : step P t s op = some s') :
    Funded P s' ∧ s'.last ≤ t := by
  cases op with
  | stake a x =>
    simp only [step] at h
    split at h
    · cases h
    cases h
    obtain ⟨⟨hsup, hpaid, hlast, hfund⟩, hlt⟩ := funded_update hf ht (some a)
    have hsum := sum_update (update P t s (some a)).bal a ((update P t s (some a)).bal a + x)
    refine ⟨⟨by simp only; omega, hpaid, hlast, ?_⟩, hlt⟩
    unfold liability at hfund ⊢
    simp only
    rw [sum_bal_update _ a _ (update_paid_self s t a)]
    exact hfund
  | withdraw a x =>
    simp only [step] at h
    split at h
    · cases h
    rename_i hx
    cases h
    obtain ⟨⟨hsup, hpaid, hlast, hfund⟩, hlt⟩ := funded_update hf ht (some a)
    have hsum := sum_update (update P t s (some a)).bal a ((update P t s (some a)).bal a - x)
    have hba : (update P t s (some a)).bal a = s.bal a := by simp [update]
    have hle := sum_update (update P t s (some a)).bal a 0
    refine ⟨⟨by simp only; omega, hpaid, hlast, ?_⟩, hlt⟩
    unfold liability at hfund ⊢
    simp only
    rw [sum_bal_update _ a _ (update_paid_self s t a)]
    exact hfund
  | getReward a =>
    simp only [step, Option.some.injEq] at h
    subst h
    obtain ⟨⟨hsup, hpaid, hlast, hfund⟩, hlt⟩ := funded_update hf ht (some a)
    have h1 := sum_update (update P t s (some a)).rewards a 0
    have h2 := sum_update (update P t s (some a)).claimed a
      ((update P t s (some a)).claimed a + (update P t s (some a)).rewards a)
    refine ⟨⟨hsup, hpaid, hlast, ?_⟩, hlt⟩
    unfold liability at hfund ⊢
    simp only
    omega
  | notify x =>
    simp only [step] at h
    obtain ⟨⟨hsup, hpaid, hlast, hfund⟩, hlt⟩ := funded_update hf ht none
    have hD : (if (update P t s none).finish ≤ t then x / P.duration
        else (x + ((update P t s none).finish - t) * (update P t s none).rate) / P.duration) *
          P.duration ≤ x + (update P t s none).rate *
            ((update P t s none).finish - (update P t s none).last) := by
      by_cases hft : (update P t s none).finish ≤ t
      · simp only [hft, ↓reduceIte]
        exact Nat.le_trans (Nat.div_mul_le_self _ _) (Nat.le_add_right _ _)
      · simp only [hft, ↓reduceIte]
        have hft' : ¬ s.finish ≤ t := hft
        have : (update P t s none).last = t := by
          show min t s.finish = t
          exact Nat.min_eq_left (by omega)
        rw [this, Nat.mul_comm (update P t s none).rate]
        exact Nat.div_mul_le_self _ _
    generalize (if (update P t s none).finish ≤ t then x / P.duration
        else (x + ((update P t s none).finish - t) * (update P t s none).rate) / P.duration) = r'
      at h hD
    split at h
    · cases h
    cases h
    refine ⟨⟨hsup, hpaid, Nat.le_add_right _ _, ?_⟩, Nat.le_refl _⟩
    unfold liability at hfund ⊢
    -- the new period streams at most the new rewards plus what was left of the old one
    simp only
    rw [Nat.add_sub_cancel_left]
    omega

/-- **The solvency invariant is a time invariant**: kept by every step at the current time,
and by the clock advancing. -/
theorem timeInvariant_funded [DecidableEq A] :
    TimeInvariant (step P) (fun _ => True) (fun t (s : State A) => Funded P s ∧ s.last ≤ t) where
  step _ _ _ _ _ h hs := funded_step h.1 h.2 hs
  advance _ _ _ _ ht h := ⟨h.1, Nat.le_trans h.2 ht⟩

/-- **Solvency at any time**: what users have claimed plus what they have earned is at most
what was funded. -/
theorem claimed_add_earned_le [DecidableEq A] {s : State A} (hf : Funded P s) {t : Nat}
    (ht : s.last ≤ t) : (∑ b, s.claimed b) + ∑ b, earned P s t b ≤ s.funded := by
  have hl := liability_update s hf ht none
  have hdiv := sum_div_le Finset.univ (fun b => s.bal b * (rpt P s t - s.paid b)) P.unit
  have he : ∑ b, earned P s t b =
      (∑ b, s.rewards b) + ∑ b, s.bal b * (rpt P s t - s.paid b) / P.unit := by
    unfold earned; rw [Finset.sum_add_distrib]
  unfold liability at hl
  simp only [update] at hl
  have := hf.funded
  unfold liability at this
  rw [he]
  omega

/-- **Across any monotone timed execution** from a funded state (at `t₀ ≥ last`), at every
time `now` from the last operation on, claims plus earnings are at most the funded rewards;
in particular the total paid out is. -/
theorem claimed_add_earned_texec [DecidableEq A] {s : State A} {t₀ now : Nat}
    (hf : Funded P s) (ht₀ : s.last ≤ t₀) {ops : List (Timed (Op A))} (hmono : Monotone ops)
    (hw : Within t₀ now ops) (ht : t₀ ≤ now) :
    (∑ b, (texec (step P) s ops).claimed b) + ∑ b, earned P (texec (step P) s ops) now b ≤
      (texec (step P) s ops).funded := by
  have := (texec_timeInvariant (fun _ _ _ _ _ _ => trivial) (timeInvariant_funded (P := P))
    hmono trivial ⟨hf, ht₀⟩ hw ht).2
  exact claimed_add_earned_le this.1 this.2

end Solvency

/-! ## No dilution -/

section Fairness

variable [DecidableEq A] [Fintype A]

variable (P) in
/-- A user's entitlement at time `t`: earned and not claimed, plus claimed. -/
def entitlement (s : State A) (t : Nat) (a : A) : Nat := earned P s t a + s.claimed a

omit [DecidableEq A] [Fintype A] in
theorem rpt_of_last {s : State A} {t : Nat} (h : lta s t ≤ s.last) : rpt P s t = s.stored := by
  unfold rpt
  split
  · rfl
  · rw [Nat.sub_eq_zero_of_le h]; simp

omit [Fintype A] in
theorem lta_update (s : State A) (t : Nat) (o : Option A) :
    lta (update P t s o) t = (update P t s o).last := by
  cases o <;> simp [update, lta]

/-- `rewardPerToken` at `t` is unchanged by any step at `t`. -/
theorem rpt_step {s s' : State A} {t : Nat} {op : Op A} (h : step P t s op = some s') :
    rpt P s' t = rpt P s t := by
  cases op with
  | stake a x =>
    simp only [step] at h
    split at h
    · cases h
    cases h
    rw [rpt_of_last (by exact Nat.le_of_eq (lta_update (P := P) s t (some a)))]
    simp [update]
  | withdraw a x =>
    simp only [step] at h
    split at h
    · cases h
    cases h
    rw [rpt_of_last (by exact Nat.le_of_eq (lta_update (P := P) s t (some a)))]
    simp [update]
  | getReward a =>
    simp only [step, Option.some.injEq] at h
    subst h
    rw [rpt_of_last (by exact Nat.le_of_eq (lta_update (P := P) s t (some a)))]
    simp [update]
  | notify x =>
    simp only [step] at h
    generalize (if (update P t s none).finish ≤ t then x / P.duration
        else (x + ((update P t s none).finish - t) * (update P t s none).rate) / P.duration) = r'
      at h
    split at h
    · cases h
    cases h
    rw [rpt_of_last (by simp [lta])]
    simp [update]

/-- **No dilution**: a user's entitlement (earned + claimed) at time `t` is exactly kept by
every step at `t`, whoever takes it. -/
theorem entitlement_step {s s' : State A} {t : Nat} {op : Op A} (h : step P t s op = some s')
    (a : A) : entitlement P s' t a = entitlement P s t a := by
  have hr := rpt_step h
  unfold entitlement earned
  rw [hr]
  cases op with
  | stake b x =>
    simp only [step] at h
    split at h
    · cases h
    cases h
    by_cases hab : a = b
    · subst hab; simp [update, earned]
    · simp [update, Function.update_of_ne hab]
  | withdraw b x =>
    simp only [step] at h
    split at h
    · cases h
    cases h
    by_cases hab : a = b
    · subst hab; simp [update, earned]
    · simp [update, Function.update_of_ne hab]
  | getReward b =>
    simp only [step, Option.some.injEq] at h
    subst h
    by_cases hab : a = b
    · subst hab; simp [update, earned]; omega
    · simp [update, Function.update_of_ne hab]
  | notify x =>
    simp only [step] at h
    generalize (if (update P t s none).finish ≤ t then x / P.duration
        else (x + ((update P t s none).finish - t) * (update P t s none).rate) / P.duration) = r'
      at h
    split at h
    · cases h
    cases h
    simp [update]

/-- **No dilution across time**: along any monotone timed execution, a user's entitlement
never decreases — time only adds to it, and nobody's action takes accrued rewards away. -/
theorem entitlement_mono (a : A) {s : State A} {t₀ t₁ : Nat} {ops : List (Timed (Op A))}
    (hmono : Monotone ops) (hw : Within t₀ t₁ ops) (ht : t₀ ≤ t₁) :
    entitlement P s t₀ a ≤ entitlement P (texec (step P) s ops) t₁ a :=
  texec_quantity_mono (Inv := fun _ => True) (fun _ _ _ _ _ _ => trivial)
    (f := fun t s => entitlement P s t a)
    (fun _ _ _ _ _ hs => Nat.le_of_eq (entitlement_step hs a).symm)
    (fun _ _ s _ htt => Nat.add_le_add_right (earned_mono s a htt) _) hmono trivial hw ht

/-- **Across blocks** (model level): blocks with non-decreasing times in `[t₀, now]`, any
operations in each, from a funded state — claims plus earnings stay within the funded
rewards, and no user's entitlement decreases. -/
theorem invariants_blocks {B : Type} (time : B → Nat) {bs : List B}
    (hmono : bs.Pairwise fun b b' => time b ≤ time b') (opss : List (List (Op A)))
    {s : State A} {t₀ now : Nat} (hf : Funded P s) (ht₀ : s.last ≤ t₀)
    (hwithin : ∀ b ∈ bs, t₀ ≤ time b ∧ time b ≤ now) (ht : t₀ ≤ now) :
    (∑ b, (texec (step P) s (stamp time bs opss)).claimed b) +
        ∑ b, earned P (texec (step P) s (stamp time bs opss)) now b ≤
      (texec (step P) s (stamp time bs opss)).funded ∧
    ∀ a, entitlement P s t₀ a ≤ entitlement P (texec (step P) s (stamp time bs opss)) now a :=
  ⟨claimed_add_earned_texec hf ht₀ (monotone_stamp hmono opss) (within_stamp hwithin opss) ht,
    fun a => entitlement_mono a (monotone_stamp hmono opss) (within_stamp hwithin opss) ht⟩

end Fairness

end QEDefi.Staking
