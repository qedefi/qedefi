import QEDefi.Trace.Time

/-!
# A time-indexed model of linear vesting (OpenZeppelin `VestingWallet`)

The schedule of OpenZeppelin's `VestingWallet` in **closed form**, with the time `t` a
parameter: nothing before `start`, everything from `start + duration`, and
`⌊total · (t − start) / duration⌋` in between (`Schedule.vested`). Every property is proved
once for a symbolic `t` (monotone in time and in the allocation, bounded by the allocation),
never by enumerating times.

`State` is the wallet's ETH accounting: the balance it holds and what it has released. The
operations are `release` (pay out what has vested and not been released) and `deposit a`
(any inflow of `a` wei: plain transfers, `SELFDESTRUCT`, fees, withdrawals). `step t s op`
mirrors the contract including its reverts (checked `+`, `*`, `-` on 256-bit words), so the
bytecode refines it exactly; `vestedAmount`, `releasable` are its views.

Properties along any monotone timed execution (`QEDefi.Trace.Time`): `released ≤ vested(now)
≤ total allocation` is a time invariant (`timeInvariant_released`), the allocation is the
initial one plus the deposits (`total_texec`), and `vested(now, allocation)` never decreases
(`vested_texec_mono`).
-/

namespace QEDefi.Vesting
open QEDefi.Trace.Lift QEDefi.Trace.Time

/-! ## The schedule -/

/-- A linear vesting schedule. -/
structure Schedule where
  /-- The time vesting starts. -/
  start : Nat
  /-- How long vesting lasts. -/
  duration : Nat

namespace Schedule

variable (p : Schedule)

/-- **The vested amount of an allocation `total` at time `t`**, in closed form
(`_vestingSchedule`). -/
def vested (total t : Nat) : Nat :=
  if t < p.start then 0
  else if p.start + p.duration ≤ t then total
  else total * (t - p.start) / p.duration

variable {p}

theorem vested_of_lt {total t : Nat} (h : t < p.start) : p.vested total t = 0 := by
  simp [vested, h]

theorem vested_of_end {total t : Nat} (h : p.start + p.duration ≤ t) : p.vested total t = total := by
  have : ¬ t < p.start := by omega
  simp [vested, h, this]

theorem vested_of_mid {total t : Nat} (h₁ : p.start ≤ t) (h₂ : t < p.start + p.duration) :
    p.vested total t = total * (t - p.start) / p.duration := by
  have : ¬ t < p.start := by omega
  have : ¬ p.start + p.duration ≤ t := by omega
  simp [vested, *]

/-- Nothing beyond the allocation vests. -/
theorem vested_le (total t : Nat) : p.vested total t ≤ total := by
  unfold vested
  split
  · exact Nat.zero_le _
  split
  · exact Nat.le_refl _
  · apply Nat.div_le_of_le_mul
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (by omega)

/-- **The vested amount never decreases in time.** -/
theorem vested_mono_time (total : Nat) {t t' : Nat} (h : t ≤ t') :
    p.vested total t ≤ p.vested total t' := by
  by_cases h₁ : t < p.start
  · rw [vested_of_lt h₁]; exact Nat.zero_le _
  by_cases h₂ : p.start + p.duration ≤ t'
  · rw [vested_of_end h₂]; exact vested_le _ _
  rw [vested_of_mid (by omega) (by omega), vested_of_mid (by omega) (by omega)]
  exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))

/-- **The vested amount never decreases in the allocation.** -/
theorem vested_mono_total {total total' : Nat} (t : Nat) (h : total ≤ total') :
    p.vested total t ≤ p.vested total' t := by
  unfold vested
  split
  · exact Nat.le_refl _
  split
  · exact h
  · exact Nat.div_le_div_right (Nat.mul_le_mul_right _ h)

/-- Monotone in both arguments. -/
theorem vested_mono {total total' t t' : Nat} (h : total ≤ total') (ht : t ≤ t') :
    p.vested total t ≤ p.vested total' t' :=
  Nat.le_trans (vested_mono_total t h) (vested_mono_time total' ht)

/-- Everything has vested from `start + duration` on. -/
theorem vested_eq_total {total t : Nat} (h : p.start + p.duration ≤ t) : p.vested total t = total :=
  vested_of_end h

end Schedule

/-! ## The wallet -/

/-- The wallet's ETH accounting. -/
structure State where
  /-- The ETH the wallet holds. -/
  balance : Nat
  /-- What it has released so far (`_released`). -/
  released : Nat
  deriving DecidableEq

/-- The total allocation: what is held plus what was released. -/
def State.total (s : State) : Nat := s.balance + s.released

/-- The model's operations. -/
inductive Op where
  /-- `release()`: pay out what has vested and not been released. -/
  | release
  /-- An inflow of `amount` wei. -/
  | deposit (amount : Nat)
  deriving DecidableEq

/-- The word size. -/
abbrev W : Nat := 2 ^ 256

variable (p : Schedule)

/-- **`vestedAmount(t)` as the contract computes it**: the allocation `balance + released` and
the product `total · (t − start)` are checked against `2²⁵⁶` (a revert is `none`); otherwise
the closed form. -/
def vestedAmount (t : Nat) (s : State) : Option Nat :=
  if W ≤ s.total then none
  else if t < p.start then some 0
  else if p.start + p.duration ≤ t then some s.total
  else if W ≤ s.total * (t - p.start) then none
  else some (s.total * (t - p.start) / p.duration)

/-- **`releasable()` at time `t`**: `vestedAmount(t) − released`, checked. -/
def releasable (t : Nat) (s : State) : Option Nat :=
  match vestedAmount p t s with
  | none => none
  | some v => if v < s.released then none else some (v - s.released)

/-- **The model step at time `t`.** `release` pays out `releasable(t)` (it cannot exceed the
balance: `releasable_le_balance`); `deposit a` adds `a`. -/
def step (t : Nat) (s : State) : Op → Option State
  | .release =>
    match releasable p t s with
    | none => none
    | some a => if s.balance < a then none else some ⟨s.balance - a, s.released + a⟩
  | .deposit a => some ⟨s.balance + a, s.released⟩

variable {p}

/-! The branches of `vestedAmount`, as the bytecode proofs meet them. -/

theorem vestedAmount_overflow {t : Nat} {s : State} (h : W ≤ s.total) :
    vestedAmount p t s = none := by
  simp [vestedAmount, h]

theorem vestedAmount_before {t : Nat} {s : State} (hW : s.total < W) (h : t < p.start) :
    vestedAmount p t s = some 0 := by
  simp [vestedAmount, Nat.not_le.mpr hW, h]

theorem vestedAmount_after {t : Nat} {s : State} (hW : s.total < W) (h₁ : p.start ≤ t)
    (h₂ : p.start + p.duration ≤ t) : vestedAmount p t s = some s.total := by
  simp [vestedAmount, Nat.not_le.mpr hW, Nat.not_lt.mpr h₁, h₂]

theorem vestedAmount_mid_overflow {t : Nat} {s : State} (hW : s.total < W) (h₁ : p.start ≤ t)
    (h₂ : t < p.start + p.duration) (h : W ≤ s.total * (t - p.start)) :
    vestedAmount p t s = none := by
  simp [vestedAmount, Nat.not_le.mpr hW, Nat.not_lt.mpr h₁, Nat.not_le.mpr h₂, h]

theorem vestedAmount_mid {t : Nat} {s : State} (hW : s.total < W) (h₁ : p.start ≤ t)
    (h₂ : t < p.start + p.duration) (h : s.total * (t - p.start) < W) :
    vestedAmount p t s = some (s.total * (t - p.start) / p.duration) := by
  simp [vestedAmount, Nat.not_le.mpr hW, Nat.not_lt.mpr h₁, Nat.not_le.mpr h₂, Nat.not_le.mpr h]

theorem vestedAmount_eq_some {t : Nat} {s : State} {v : Nat} (h : vestedAmount p t s = some v) :
    v = p.vested s.total t ∧ s.total < W := by
  unfold vestedAmount at h
  split at h
  · cases h
  rename_i hW
  split at h
  · cases h; exact ⟨(Schedule.vested_of_lt (by assumption)).symm, by omega⟩
  split at h
  · cases h; exact ⟨(Schedule.vested_of_end (by assumption)).symm, by omega⟩
  split at h
  · cases h
  · cases h; exact ⟨(Schedule.vested_of_mid (by omega) (by omega)).symm, by omega⟩

/-- `vestedAmount` is the closed form whenever it does not revert. -/
theorem vestedAmount_eq {t : Nat} {s : State} (hW : s.total < W)
    (hmul : p.start ≤ t → t < p.start + p.duration → s.total * (t - p.start) < W) :
    vestedAmount p t s = some (p.vested s.total t) := by
  have hW' : ¬ W ≤ s.total := by omega
  unfold vestedAmount
  by_cases h₁ : t < p.start
  · simp only [hW', h₁, ↓reduceIte, Schedule.vested_of_lt h₁]
  by_cases h₂ : p.start + p.duration ≤ t
  · simp only [hW', h₁, h₂, ↓reduceIte, Schedule.vested_of_end h₂]
  have h₃ : ¬ W ≤ s.total * (t - p.start) := by
    have := hmul (by omega) (by omega); omega
  simp only [hW', h₁, h₂, h₃, ↓reduceIte,
    Schedule.vested_of_mid (p := p) (total := s.total) (t := t) (by omega) (by omega)]

theorem releasable_eq_some {t : Nat} {s : State} {a : Nat} (h : releasable p t s = some a) :
    a = p.vested s.total t - s.released ∧ s.released ≤ p.vested s.total t ∧ s.total < W := by
  unfold releasable at h
  split at h
  · cases h
  rename_i v hv
  obtain ⟨rfl, hW⟩ := vestedAmount_eq_some hv
  split at h
  · cases h
  · cases h; exact ⟨rfl, by omega, hW⟩

/-- What is releasable never exceeds the balance (so `release`'s balance check never fails). -/
theorem releasable_le_balance {t : Nat} {s : State} {a : Nat} (h : releasable p t s = some a) :
    a ≤ s.balance := by
  obtain ⟨rfl, -, -⟩ := releasable_eq_some h
  have := Schedule.vested_le (p := p) s.total t
  have ht : s.total = s.balance + s.released := rfl
  generalize p.vested s.total t = v at *
  omega

/-- **`release` at time `t`**: when it succeeds, the released amount becomes `vested(t)` and
the allocation is unchanged. -/
theorem step_release {t : Nat} {s s' : State} (h : step p t s .release = some s') :
    s'.released = p.vested s.total t ∧ s'.total = s.total ∧ s.released ≤ p.vested s.total t := by
  simp only [step] at h
  split at h
  · cases h
  rename_i a ha
  obtain ⟨rfl, hle, -⟩ := releasable_eq_some ha
  split at h
  · cases h
  · cases h
    have h1 := Schedule.vested_le (p := p) s.total t
    have ht : s.total = s.balance + s.released := rfl
    refine ⟨?_, ?_, hle⟩ <;> generalize p.vested s.total t = v at *
    · show s.released + (v - s.released) = v
      omega
    · show (s.balance - (v - s.released)) + (s.released + (v - s.released)) = s.total
      omega

/-- The inflow of an operation: `a` for `deposit a`, nothing for `release`. -/
def Op.inflow : Op → Nat
  | .release => 0
  | .deposit a => a

/-- The allocation after a successful step: unchanged by `release`, `+ a` by `deposit a`. -/
theorem total_step {t : Nat} {s s' : State} {op : Op} (h : step p t s op = some s') :
    s'.total = s.total + op.inflow := by
  cases op with
  | release => exact (step_release h).2.1
  | deposit a =>
    simp only [step, Option.some.injEq] at h
    subst h
    simp only [State.total, Op.inflow]
    omega

/-- **Releasable is exactly what has vested and not been released**, when it does not
revert. -/
theorem releasable_eq {t : Nat} {s : State} (hW : s.total < W)
    (hmul : p.start ≤ t → t < p.start + p.duration → s.total * (t - p.start) < W)
    (hle : s.released ≤ p.vested s.total t) :
    releasable p t s = some (p.vested s.total t - s.released) := by
  unfold releasable
  rw [vestedAmount_eq hW hmul]
  simp only [Nat.not_lt.mpr hle, ite_false]

/-! ## Invariants over time -/

/-- **The time invariant**: at time `t`, the wallet has released at most what has vested. -/
def ReleasedLe (p : Schedule) (t : Nat) (s : State) : Prop := s.released ≤ p.vested s.total t

/-- `ReleasedLe` is preserved by every successful step at the current time and by advancing
the clock: no case split on time, only `vested_mono_time` and `vested_mono_total`. -/
theorem timeInvariant_released : TimeInvariant (step p) (fun _ => True) (ReleasedLe p) where
  step t s op s' _ h hs := by
    unfold ReleasedLe at h ⊢
    cases op with
    | release => rw [(step_release hs).1, (step_release hs).2.1]; exact Nat.le_refl _
    | deposit a =>
      have ht := total_step hs
      simp only [step, Option.some.injEq] at hs
      subst hs
      exact Nat.le_trans h (Schedule.vested_mono_total t (by rw [ht]; exact Nat.le_add_right _ _))
  advance t t' s _ ht h := Nat.le_trans h (Schedule.vested_mono_time _ ht)

/-- The deposits of a list of timed operations. -/
def deposits (ops : List (Timed Op)) : Nat := (ops.map fun o => o.op.inflow).sum

/-- **Funds are conserved**: after any timed execution, the allocation is the initial one plus
the deposits (`release` moves funds from `balance` to `released`). -/
theorem total_texec (s : State) (ops : List (Timed Op)) :
    (texec (step p) s ops).total = s.total + deposits ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    rw [texec, exec_cons, ← texec, ih]
    have h : (stepD (atTime (step p)) s o).total = s.total + o.op.inflow := by
      unfold stepD atTime
      cases e : step p o.time s o.op with
      | none =>
        cases ho : o.op with
        | release => simp [Op.inflow]
        | deposit a => rw [ho] at e; simp [step] at e
      | some s' => exact total_step e
    rw [h]
    simp only [deposits, List.map_cons, List.sum_cons]
    omega

/-- **`released ≤ vested(now) ≤ allocation`** after any monotone timed execution in
`[t₀, now]` from a state satisfying it at `t₀`. -/
theorem released_le_vested {s : State} {t₀ now : Nat} (h : ReleasedLe p t₀ s)
    {ops : List (Timed Op)} (hmono : Monotone ops) (hw : Within t₀ now ops) (ht : t₀ ≤ now) :
    (texec (step p) s ops).released ≤ p.vested (texec (step p) s ops).total now ∧
      p.vested (texec (step p) s ops).total now ≤ (texec (step p) s ops).total :=
  ⟨(texec_timeInvariant (fun _ _ _ _ _ _ => trivial) timeInvariant_released hmono trivial h hw
    ht).2, Schedule.vested_le _ _⟩

/-- **The vested amount never decreases** along a monotone timed execution: in time, and
because `release` keeps the allocation while deposits grow it. -/
theorem vested_texec_mono {s : State} {t₀ t₁ : Nat} {ops : List (Timed Op)} (hmono : Monotone ops)
    (hw : Within t₀ t₁ ops) (ht : t₀ ≤ t₁) :
    p.vested s.total t₀ ≤ p.vested (texec (step p) s ops).total t₁ :=
  texec_quantity_mono (Inv := fun _ => True) (fun _ _ _ _ _ _ => trivial)
    (f := fun t (s : State) => p.vested s.total t)
    (fun t s op s' _ hs => Schedule.vested_mono_total t (by rw [total_step hs]; omega))
    (fun _ _ _ _ ht => Schedule.vested_mono_time _ ht) hmono trivial hw ht

/-- After `release` at time `t`, nothing more is releasable at `t`. -/
theorem releasable_after_release {t : Nat} {s s' : State} (h : step p t s .release = some s')
    (hW : s'.total < W)
    (hmul : p.start ≤ t → t < p.start + p.duration → s'.total * (t - p.start) < W) :
    releasable p t s' = some 0 := by
  obtain ⟨hr, htot, -⟩ := step_release h
  rw [releasable_eq hW hmul (by rw [hr, htot]; exact Nat.le_refl _)]
  rw [hr, htot, Nat.sub_self]

end QEDefi.Vesting
