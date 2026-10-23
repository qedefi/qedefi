import QEDefi.Actor.Lib.AccessControl
import QEDefi.Actor.Delay

/-!
# Component: OpenZeppelin `TimelockController` (v5.6.0, unchanged in 5.7.0)

`docs/access-control/oz-gov-proxy.md` §1. An `AccessControl` contract `tl` (the
`AccessControl` component at `tl`, through the lens `acL`) with operations `k : K`. Operation ids
are content-addressed: `calls k` (targets and calldata) and `pred k` (predecessor) are functions of
the id. `ts k` is `_timestamps[id]` exactly: `0` unset, `1` done, otherwise the ready time.

- `schedule(k, delay)`: `PROPOSER_ROLE`; `k` unset; `delay ≥ minDelay`; sets `ts k := now + delay`;
- `cancel(k)`: `CANCELLER_ROLE`; `k` pending (`ts k > 1`, waiting or ready); sets `ts k := 0`;
- `execute(k)`: `EXECUTOR_ROLE`, or anyone when `address(0)` holds it (`zero`); `k` ready
  (`1 < ts k ≤ now`: ready **at** the ready time); predecessor done. Performs `calls k` with
  `msg.sender = tl` (run by the host: `execute_sound`), then requires `k` still ready and marks it
  done (`afterCall`). Ready operations never expire;
- `updateDelay(d)`: only `tl` itself, i.e. through an executed operation.

- `run_sound`, `execute_sound`, `afterCall_sound`, `ac_le`: per-call soundness in any host;
- `Closes`, `closed`: the component's part of a host's "who can";
- `no_call`: keys without a proposer role on its admin chain make the timelock call only what was
  already pending; `delayed`: the `Delayed` instance (notice), from `TsOk` per step.
-/

namespace QEDefi.Actor.Timelock

open Classical

variable {C R A K M H : Type}

/-- The configuration fragment: the role table, the operation timestamps, the minimum delay. -/
structure Cfg (R A K : Type) where
  ac : AccessControl.Cfg R A
  ts : K → ℕ
  minDelay : ℕ

/-- The role table. -/
def acL : Lens (Cfg R A K) (AccessControl.Cfg R A) := ⟨Cfg.ac, fun a x => { x with ac := a }⟩

/-- The deployment: the timelock, its roles, `address(0)`, and the content of each operation id. -/
structure Params (R A K M : Type) where
  tl : A
  proposer : R
  executor : R
  canceller : R
  zero : A
  calls : K → List (A × M)
  pred : K → Option K

/-- The timelock's own functions (role management is the `AccessControl` component's). -/
inductive Msg (K : Type) where
  | schedule (k : K) (delay : ℕ)
  | execute (k : K)
  | cancel (k : K)
  | updateDelay (d : ℕ)

variable (P : Params R A K M)

/-- `onlyRoleOrOpenRole(EXECUTOR_ROLE)`. -/
def CanExecute (x : Cfg R A K) (b : A) : Prop :=
  x.ac.has P.executor b ∨ x.ac.has P.executor P.zero

/-- The predecessor, if any, is done. -/
def PredDone (x : Cfg R A K) (k : K) : Prop := ∀ p, P.pred k = some p → x.ts p = 1

/-- `execute(k)` by `b` at time `now` passes its checks before the calls. -/
def Executes (now : ℕ) (x : Cfg R A K) (b : A) (k : K) : Prop :=
  CanExecute P x b ∧ 1 < x.ts k ∧ x.ts k ≤ now ∧ PredDone P x k

/-- `_afterCall`: after the calls, `k` must still be ready; it becomes done. -/
noncomputable def afterCall (now : ℕ) (x : Cfg R A K) (k : K) : Option (Cfg R A K) :=
  if 1 < x.ts k ∧ x.ts k ≤ now then some { x with ts := Function.update x.ts k 1 } else none

/-- **One call** from `b` at time `now` (`execute` is run by the host). -/
noncomputable def run (now : ℕ) (x : Cfg R A K) (b : A) : Msg K → Option (Cfg R A K)
  | .schedule k d =>
    if x.ac.has P.proposer b ∧ x.ts k = 0 ∧ x.minDelay ≤ d then
      some { x with ts := Function.update x.ts k (now + d) } else none
  | .cancel k =>
    if x.ac.has P.canceller b ∧ 1 < x.ts k then some { x with ts := Function.update x.ts k 0 }
    else none
  | .updateDelay d => if b = P.tl then some { x with minDelay := d } else none
  | .execute _ => none

/-- **The access checks as rules** (time-free: readiness is over-approximated by pendency). -/
inductive Base (ι : Msg K → M) : Cfg R A K → A × Action A M H → Set (A × Action A M H) → Prop
  | schedule (x : Cfg R A K) (b : A) (k : K) (d : ℕ) (hb : x.ac.has P.proposer b)
      (h0 : x.ts k = 0) (hd : x.minDelay ≤ d) :
      Base ι x (P.tl, .act (ι (.schedule k d))) {(b, .call P.tl (ι (.schedule k d)))}
  | cancel (x : Cfg R A K) (b : A) (k : K) (hb : x.ac.has P.canceller b) (hk : 1 < x.ts k) :
      Base ι x (P.tl, .act (ι (.cancel k))) {(b, .call P.tl (ι (.cancel k)))}
  | execute (x : Cfg R A K) (b : A) (k : K) (hb : CanExecute P x b) (hk : 1 < x.ts k)
      (hp : PredDone P x k) :
      Base ι x (P.tl, .act (ι (.execute k))) {(b, .call P.tl (ι (.execute k)))}
  | relay (x : Cfg R A K) (k : K) (t : A) (m : M) (h : (t, m) ∈ P.calls k) :
      Base ι x (P.tl, .call t m) {(P.tl, .act (ι (.execute k)))}
  | updateDelay (x : Cfg R A K) (d : ℕ) :
      Base ι x (P.tl, .act (ι (.updateDelay d))) {(P.tl, .call P.tl (ι (.updateDelay d)))}

/-- **The configuration changes.** -/
inductive Chg (ι : Msg K → M) : A × Action A M H → Cfg R A K → Cfg R A K → Prop
  | schedule (x : Cfg R A K) (k : K) (d now : ℕ) (h0 : x.ts k = 0) (hd : x.minDelay ≤ d) :
      Chg ι (P.tl, .act (ι (.schedule k d))) x { x with ts := Function.update x.ts k (now + d) }
  | cancel (x : Cfg R A K) (k : K) (hk : 1 < x.ts k) :
      Chg ι (P.tl, .act (ι (.cancel k))) x { x with ts := Function.update x.ts k 0 }
  | execute (x : Cfg R A K) (k : K) (hk : 1 < x.ts k) :
      Chg ι (P.tl, .act (ι (.execute k))) x { x with ts := Function.update x.ts k 1 }
  | updateDelay (x : Cfg R A K) (d : ℕ) :
      Chg ι (P.tl, .act (ι (.updateDelay d))) x { x with minDelay := d }

/-- The timelock's own rules. -/
def own (ι : Msg K → M) : Sys (Cfg R A K) A (Action A M H) := ⟨Base P ι, Chg P ι⟩

/-- **The component**: its own rules and `AccessControl` at `tl` (no `onlyRole` host functions:
the role checks of `schedule`, `cancel`, `execute` are in `own`). -/
def sys (ι : Msg K → M) (ιa : AccessControl.Msg R A → M) : Sys (Cfg R A K) A (Action A M H) :=
  (own P ι).union ((AccessControl.sys P.tl ιa (fun _ => none)).lift acL)

variable {P} {ι : Msg K → M} {ιa : AccessControl.Msg R A → M} {S : Sys C A (Action A M H)}
  {L : Lens C (Cfg R A K)}

/-! ## Per-call soundness, in any host -/

theorem own_le (hS : (sys P ι ιa).lift L ≤ S) : (own P ι).lift L ≤ S :=
  Sys.le_trans (Sys.lift_mono Sys.le_union_left) hS

/-- The role table in a host: use `AccessControl.run_sound` with this. -/
theorem ac_le (hS : (sys P ι ιa).lift L ≤ S) :
    (AccessControl.sys (H := H) P.tl ιa (fun _ => none)).lift (L.comp acL) ≤ S :=
  Sys.le_trans Sys.lift_comp_le (Sys.le_trans (Sys.lift_mono Sys.le_union_right) hS)

/-- **Every successful `schedule`, `cancel`, `updateDelay` makes a derivable change.** -/
theorem run_sound (hS : (sys P ι ιa).lift L ≤ S) {now : ℕ} {c : C} {K' : Set A} {b : A}
    {m : Msg K} {x' : Cfg R A K} (hr : run P now (L.get c) b m = some x')
    (hd : Derives S.auth c K' (b, .call P.tl (ι m))) :
    ∃ e, S.chg e c (L.set x' c) ∧ Derives S.auth c K' e := by
  have h := own_le hS
  cases m with
  | schedule k d =>
    simp only [run] at hr; split_ifs at hr with hc; cases hr
    exact ⟨_, h.chg_lift (K := own P ι) (Chg.schedule _ k d now hc.2.1 hc.2.2),
      h.derive_lift (K := own P ι) (Base.schedule _ b k d hc.1 hc.2.1 hc.2.2) hd⟩
  | cancel k =>
    simp only [run] at hr; split_ifs at hr with hc; cases hr
    exact ⟨_, h.chg_lift (K := own P ι) (Chg.cancel _ k hc.2),
      h.derive_lift (K := own P ι) (Base.cancel _ b k hc.1 hc.2) hd⟩
  | updateDelay d =>
    simp only [run] at hr; split_ifs at hr with hc; cases hr; subst hc
    exact ⟨_, h.chg_lift (K := own P ι) (Chg.updateDelay _ d),
      h.derive_lift (K := own P ι) (Base.updateDelay _ d) hd⟩
  | execute k => simp [run] at hr

/-- **`execute(k)`**: the executor's call makes the timelock act on `k` and issue its calls. -/
theorem execute_sound (hS : (sys P ι ιa).lift L ≤ S) {now : ℕ} {c : C} {K' : Set A} {b : A}
    {k : K} (he : Executes P now (L.get c) b k) (hd : Derives S.auth c K' (b, .call P.tl (ι (.execute k)))) :
    Derives S.auth c K' (P.tl, .act (ι (.execute k))) ∧
      ∀ p ∈ P.calls k, Derives S.auth c K' (P.tl, .call p.1 p.2) := by
  have h := own_le hS
  have ha := h.derive_lift (K := own P ι) (Base.execute _ b k he.1 he.2.1 he.2.2.2) hd
  exact ⟨ha, fun p hp => h.derive_lift (K := own P ι) (Base.relay _ k p.1 p.2 hp) ha⟩

/-- **Marking done** is a change by the act on `k` (derivable at the start of the step by
`execute_sound`), at whatever configuration the calls left. -/
theorem afterCall_sound (hS : (sys P ι ιa).lift L ≤ S) {now : ℕ} {c : C} {k : K}
    {x' : Cfg R A K} (hr : afterCall now (L.get c) k = some x') :
    S.chg (P.tl, .act (ι (.execute k))) c (L.set x' c) := by
  simp only [afterCall] at hr; split_ifs at hr with hc; cases hr
  exact (own_le hS).chg_lift (K := own P ι) (Chg.execute _ k hc.1)

/-! ## Notice -/

/-- The ready time of a pending operation. -/
def eta (x : Cfg R A K) (k : K) : Option ℕ := if 1 < x.ts k then some (x.ts k) else none

/-- **A step at time `now` sets ready times only `minDelay` (as before the step) ahead**: each
timestamp is kept, cleared or marked done, or set at least `now + minDelay`. -/
def TsOk (now : ℕ) (x x' : Cfg R A K) : Prop :=
  ∀ k, x'.ts k = x.ts k ∨ x'.ts k ≤ 1 ∨ now + x.minDelay ≤ x'.ts k

theorem TsOk.of_ts {now : ℕ} {x x' : Cfg R A K} (h : x'.ts = x.ts) : TsOk now x x' :=
  fun k => Or.inl (congrFun h k)

/-- Sequencing calls within a step: sound while the minimum delay does not decrease. A batch that
lowers `minDelay` and then schedules (`updateDelay` then `schedule` by a proposer, all in one
execution) breaks this: the new operation's notice is only the lowered delay. -/
theorem TsOk.trans {now : ℕ} {x y z : Cfg R A K} (h₁ : TsOk now x y) (h₂ : TsOk now y z)
    (hd : x.minDelay ≤ y.minDelay) : TsOk now x z := fun k => by
  rcases h₂ k with h | h | h
  · rcases h₁ k with h' | h' | h'
    · exact Or.inl (h.trans h')
    · exact Or.inr (Or.inl (h ▸ h'))
    · exact Or.inr (Or.inr (h ▸ h'))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by omega))

theorem run_tsOk {now : ℕ} {x x' : Cfg R A K} {b : A} {m : Msg K}
    (hr : run P now x b m = some x') : TsOk now x x' := by
  cases m with
  | schedule k d =>
    simp only [run] at hr; split_ifs at hr with hc; cases hr
    intro k'
    by_cases hk : k' = k
    · subst hk; simp only [Function.update_self]; exact Or.inr (Or.inr (by omega))
    · simp [Function.update_of_ne hk]
  | cancel k =>
    simp only [run] at hr; split_ifs at hr; cases hr
    intro k'
    by_cases hk : k' = k
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  | updateDelay d => simp only [run] at hr; split_ifs at hr; cases hr; exact TsOk.of_ts rfl
  | execute k => simp [run] at hr

theorem afterCall_tsOk {now : ℕ} {x x' : Cfg R A K} {k : K} (hr : afterCall now x k = some x') :
    TsOk now x x' := by
  simp only [afterCall] at hr; split_ifs at hr; cases hr
  intro k'
  by_cases hk : k' = k
  · subst hk; simp
  · simp [Function.update_of_ne hk]

/-- **The `Delayed` instance.** In a host whose steps (`get`: the timelock's configuration) satisfy
`TsOk` and break `Keep` only by executing a ready operation, `Delayed.notice` applies: every
breaking step runs no earlier than a ready time that was pending at the start or set at least
`minDelay` (as of then) after the step that set it. -/
theorem delayed {St O : Type} {step : St → O → Option St} {time : O → ℕ}
    {get : St → Cfg R A K} {Keep : St → St → Prop} (hrefl : ∀ s, Keep s s)
    (hts : ∀ s op s', step s op = some s' → TsOk (time op) (get s) (get s'))
    (hripe : ∀ s op s', step s op = some s' → ¬ Keep s s' →
      ∃ k, 1 < (get s).ts k ∧ (get s).ts k ≤ time op) :
    Delayed step time (fun k s => eta (get s) k) (fun s => (get s).minDelay) Keep := by
  refine ⟨hrefl, fun s op s' he hk => ?_, fun s op s' k η he hs hne => ?_⟩
  · obtain ⟨k, h1, h2⟩ := hripe s op s' he hk
    exact ⟨k, _, by simp [eta, h1], h2⟩
  · simp only [eta] at hs hne
    split_ifs at hs with h1; cases hs
    rcases hts s op s' he k with h | h | h
    · rw [h] at h1 hne; simp [h1] at hne
    · omega
    · exact h

/-! ## Who can -/

/-- **The timelock's own rules in a host's closed set**, as first-order conditions. -/
structure Closes (P : Params R A K M) (ι : Msg K → M) (L : Lens C (Cfg R A K))
    (D : A × Action A M H → Prop) (Inv : C → Prop) : Prop where
  schedule : ∀ c, Inv c → ∀ b k d, (L.get c).ac.has P.proposer b → (L.get c).ts k = 0 →
    (L.get c).minDelay ≤ d → D (b, .call P.tl (ι (.schedule k d))) →
    D (P.tl, .act (ι (.schedule k d)))
  cancel : ∀ c, Inv c → ∀ b k, (L.get c).ac.has P.canceller b → 1 < (L.get c).ts k →
    D (b, .call P.tl (ι (.cancel k))) → D (P.tl, .act (ι (.cancel k)))
  execute : ∀ c, Inv c → ∀ b k, CanExecute P (L.get c) b → 1 < (L.get c).ts k →
    PredDone P (L.get c) k → D (b, .call P.tl (ι (.execute k))) → D (P.tl, .act (ι (.execute k)))
  relay : ∀ k t m, (t, m) ∈ P.calls k → D (P.tl, .act (ι (.execute k))) → D (P.tl, .call t m)
  updateDelay : ∀ d, D (P.tl, .call P.tl (ι (.updateDelay d))) → D (P.tl, .act (ι (.updateDelay d)))
  scheduleChg : ∀ c k d now, Inv c → (L.get c).ts k = 0 → (L.get c).minDelay ≤ d →
    D (P.tl, .act (ι (.schedule k d))) →
    Inv (L.set { L.get c with ts := Function.update (L.get c).ts k (now + d) } c)
  cancelChg : ∀ c k, Inv c → 1 < (L.get c).ts k → D (P.tl, .act (ι (.cancel k))) →
    Inv (L.set { L.get c with ts := Function.update (L.get c).ts k 0 } c)
  executeChg : ∀ c k, Inv c → 1 < (L.get c).ts k → D (P.tl, .act (ι (.execute k))) →
    Inv (L.set { L.get c with ts := Function.update (L.get c).ts k 1 } c)
  updateDelayChg : ∀ c d, Inv c → D (P.tl, .act (ι (.updateDelay d))) →
    Inv (L.set { L.get c with minDelay := d } c)

theorem closed {D : A × Action A M H → Prop} {Inv : C → Prop} (h : Closes P ι L D Inv)
    (hac : AccessControl.Closes P.tl ιa (fun _ => none) (L.comp acL) D Inv) :
    Sys.Closed ((sys P ι ιa).lift L) D Inv := by
  refine Sys.Closed.mono (Sys.Closed.union ?_ ((AccessControl.closed hac).mono Sys.lift_lift_le))
    Sys.lift_union_le
  refine Sys.Closed.lift (fun e c x' hc hD hI => ?_) (fun c hI q Y hb hY => ?_)
  · rcases hc with ⟨_, k, d, now, h0, hd⟩ | ⟨_, k, hk⟩ | ⟨_, k, hk⟩ | ⟨_, d⟩
    · exact h.scheduleChg c k d now hI h0 hd hD
    · exact h.cancelChg c k hI hk hD
    · exact h.executeChg c k hI hk hD
    · exact h.updateDelayChg c d hI hD
  · cases hb with
    | schedule b k d hb h0 hd => exact h.schedule c hI b k d hb h0 hd (hY _ rfl)
    | cancel b k hb hk => exact h.cancel c hI b k hb hk (hY _ rfl)
    | execute b k hb hk hp => exact h.execute c hI b k hb hk hp (hY _ rfl)
    | relay k t m hm => exact h.relay k t m hm (hY _ rfl)
    | updateDelay d => exact h.updateDelay d (hY _ rfl)

/-- What keys `T` can make the timelock do when they hold no role of `Adm` (the proposer role and
its admins): their own capabilities, grants and revocations of roles administered outside `Adm`,
executing or cancelling an operation pending at the start, and that operation's calls. -/
def Outsider (P : Params R A K M) (ι : Msg K → M) (ιa : AccessControl.Msg R A → M) (T : Set A)
    (Adm : Set R) (x₀ : Cfg R A K) (q : A × Action A M H) : Prop :=
  q.1 ∈ T ∨
  (∃ r a, (q = (P.tl, .act (ιa (.grantRole r a))) ∨ q = (P.tl, .act (ιa (.revokeRole r a)))) ∧
    x₀.ac.adminOf r ∉ Adm) ∨
  (∃ k, 1 < x₀.ts k ∧ (q = (P.tl, .act (ι (.execute k))) ∨ q = (P.tl, .act (ι (.cancel k))))) ∨
  (∃ k, 1 < x₀.ts k ∧ ∃ p ∈ P.calls k, q = (P.tl, .call p.1 p.2))

/-- **Who can, standalone.** Let `Adm` contain the proposer role and be closed under `adminOf`.
Keys `T` that include neither the timelock nor a holder of an `Adm` role, from a state where no
pending operation calls the timelock itself, derive only `Outsider` capabilities, whatever they
do (execute, cancel, grant other roles, renounce). -/
theorem outsider {T : Set A} {x₀ : Cfg R A K} {Adm : Set R}
    (hAdm : ∀ r ∈ Adm, x₀.ac.adminOf r ∈ Adm) (hp : P.proposer ∈ Adm) (htl : P.tl ∉ T)
    (hrole : ∀ r ∈ Adm, ∀ a, x₀.ac.has r a → a ∉ T)
    (hself : ∀ k, 1 < x₀.ts k → ∀ p ∈ P.calls k, p.1 ≠ P.tl)
    (hι : Function.Injective ι) (hιa : Function.Injective ιa) (hdisj : ∀ m₁ m₂, ι m₁ ≠ ιa m₂)
    {q : A × Action A M H} (hd : Derives (sys P ι ιa).auth x₀ T q) :
    Outsider P ι ιa T Adm x₀ q := by
  let D := Outsider (H := H) P ι ιa T Adm x₀
  let Inv : Cfg R A K → Prop := fun x => x.ac.adminOf = x₀.ac.adminOf ∧
    (∀ r ∈ Adm, ∀ a, x.ac.has r a → x₀.ac.has r a) ∧ ∀ k, 1 < x.ts k → 1 < x₀.ts k
  -- Calls to the timelock in `D` come from `T`.
  have hcall : ∀ b m, D (b, .call P.tl m) → b ∈ T := by
    rintro b m (h | ⟨_, _, h, -⟩ | ⟨_, -, h⟩ | ⟨k, hk, p, hp', h⟩)
    · exact h
    · rcases h with h | h <;> cases h
    · rcases h with h | h <;> cases h
    · simp only [Prod.mk.injEq, Action.call.injEq] at h
      exact absurd h.2.1.symm (hself k hk p hp')
  -- No act of the timelock on its own messages but `execute`/`cancel` of pending operations.
  have hact : ∀ m, D (P.tl, .act (ι m)) → ∃ k, 1 < x₀.ts k ∧ (m = .execute k ∨ m = .cancel k) := by
    rintro m (h | ⟨_, _, h, -⟩ | ⟨k, hk, h⟩ | ⟨_, -, _, -, h⟩)
    · exact absurd h htl
    · rcases h with h | h <;> simp only [Prod.mk.injEq, Action.act.injEq] at h <;>
        exact absurd h.2 (hdisj _ _)
    · refine ⟨k, hk, ?_⟩
      rcases h with h | h <;> simp only [Prod.mk.injEq, Action.act.injEq] at h
      · exact Or.inl (hι h.2)
      · exact Or.inr (hι h.2)
    · cases h
  have hInvAc : ∀ x a', Inv x → a'.adminOf = x₀.ac.adminOf →
      (∀ r ∈ Adm, ∀ a, a'.has r a → x₀.ac.has r a) → Inv { x with ac := a' } :=
    fun x a' hI h1 h2 => ⟨h1, h2, hI.2.2⟩
  have hts : ∀ x k v, Inv x → v ≤ 1 → Inv { x with ts := Function.update x.ts k v } := by
    intro x k v hI hv
    refine ⟨hI.1, hI.2.1, fun k' hk' => ?_⟩
    by_cases hk : k' = k
    · subst hk; simp at hk'; omega
    · simp only [Function.update_of_ne hk] at hk'; exact hI.2.2 k' hk'
  have hc : Closes P ι (Lens.id _) D Inv := by
    refine ⟨fun c hI b k d hb _ _ hD => ?_, fun c hI b k _ hk _ =>
      Or.inr (Or.inr (Or.inl ⟨k, hI.2.2 k hk, Or.inr rfl⟩)), fun c hI b k _ hk _ _ =>
      Or.inr (Or.inr (Or.inl ⟨k, hI.2.2 k hk, Or.inl rfl⟩)), fun k t m hm hD => ?_,
      fun d hD => absurd (hcall _ _ hD) htl, fun c k d now hI _ _ hD => ?_,
      fun c k hI _ _ => hts c k 0 hI (by omega), fun c k hI _ _ => hts c k 1 hI le_rfl,
      fun c d hI _ => hI⟩
    · exact absurd (hcall _ _ hD) (hrole _ hp b (hI.2.1 _ hp b hb))
    · obtain ⟨k', hk', h⟩ := hact _ hD
      rcases h with h | h
      · rw [← Msg.execute.inj h] at hk'
        exact Or.inr (Or.inr (Or.inr ⟨k, hk', (t, m), hm, rfl⟩))
      · cases h
    · obtain ⟨_, -, h⟩ := hact _ hD
      rcases h with h | h <;> cases h
  have hac : AccessControl.Closes P.tl ιa (fun _ => none) ((Lens.id _).comp acL) D Inv := by
    refine AccessControl.Closes.outsider (T := T) (x₀ := x₀.ac) (Adm := Adm)
      (fun c hI => ⟨hI.1, hI.2.1⟩) (fun c a' hI h1 h2 => hInvAc c a' hI h1 h2) hrole hcall
      (fun m r hr => by cases hr) (fun r a hra => ⟨Or.inr (Or.inl ⟨r, a, Or.inl rfl, hra⟩),
        Or.inr (Or.inl ⟨r, a, Or.inr rfl, hra⟩)⟩) ?_
    rintro r a (h | ⟨r', a', h, hra⟩ | ⟨_, -, h⟩ | ⟨_, -, _, -, h⟩) hr
    · exact htl h
    · rcases h with h | h <;> simp only [Prod.mk.injEq, Action.act.injEq] at h <;>
        have h := hιa h.2 <;> cases h
      exact hra (hAdm r hr)
    · rcases h with h | h <;> simp only [Prod.mk.injEq, Action.act.injEq] at h <;>
        exact absurd h.2.symm (hdisj _ _)
    · cases h
  exact Sys.le_of_closed (closed hc hac) (fun a ha _ => Or.inl ha)
    ⟨rfl, fun _ _ _ h => h, fun _ h => h⟩ ((Sys.le_lift_id _).derives hd)

/-- **The timelock calls only what was pending.** Under the hypotheses of `outsider`, every call
the keys `T` can make the timelock issue belongs to an operation pending at the start. -/
theorem no_call {T : Set A} {x₀ : Cfg R A K} {Adm : Set R}
    (hAdm : ∀ r ∈ Adm, x₀.ac.adminOf r ∈ Adm) (hp : P.proposer ∈ Adm) (htl : P.tl ∉ T)
    (hrole : ∀ r ∈ Adm, ∀ a, x₀.ac.has r a → a ∉ T)
    (hself : ∀ k, 1 < x₀.ts k → ∀ p ∈ P.calls k, p.1 ≠ P.tl)
    (hι : Function.Injective ι) (hιa : Function.Injective ιa) (hdisj : ∀ m₁ m₂, ι m₁ ≠ ιa m₂)
    {t : A} {m : M} (hd : Derives (sys (H := H) P ι ιa).auth x₀ T (P.tl, .call t m)) :
    ∃ k, 1 < x₀.ts k ∧ (t, m) ∈ P.calls k := by
  rcases outsider hAdm hp htl hrole hself hι hιa hdisj hd with
    h | ⟨_, _, h, -⟩ | ⟨_, -, h⟩ | ⟨k, hk, p, hp', h⟩
  · exact absurd h htl
  · rcases h with h | h <;> cases h
  · rcases h with h | h <;> cases h
  · simp only [Prod.mk.injEq, Action.call.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact ⟨k, hk, hp'⟩

/-- **Not vacuous**: a proposer schedules. -/
theorem proposer_can {x : Cfg R A K} {b : A} (hb : x.ac.has P.proposer b) {k : K} {d : ℕ}
    (h0 : x.ts k = 0) (hd : x.minDelay ≤ d) :
    Derives (sys (H := H) P ι ιa).auth x {b} (P.tl, .act (ι (.schedule k d))) :=
  (Sys.le_union_left).derive₁ (S₁ := own P ι) (Base.schedule x b k d hb h0 hd) (.key _ rfl)

end QEDefi.Actor.Timelock
