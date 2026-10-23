import QEDefi.Actor.Trace

/-!
# Authority over authority: closing rules under configuration changes

Authority depends on a **configuration** `cfg s : C` (owners, role tables, thresholds, module
sets, stored approvals, scheduled operations), and changing the configuration is itself an
action: `chg e c c'` when performing capability `e` (typically `(t, act m)` for an
administrative message `m`) takes configuration `c` to `c'`. Whoever can perform a change
controls everything the changed configuration grants: who can make ProxyAdmin transfer its
ownership to `o` can upgrade through `o`; who can grant a role holds it; who can execute a
hash its owners approved can do what that hash does.

`close chg R` adds exactly these escalation rules: in configuration `c`, `q` follows from `Y`
plus the changes `es` whenever some path of changes `es` leads to a configuration `c'` where
`R c' q Y`. With these rules, stability is mechanical (`stable_of_cfg`): a step either keeps the
configuration or performs changes its consenters could derive. Writing escalation rules by
hand is unnecessary and cannot be forgotten.

Non-derivability is proved with `close_le_of_closed`: an invariant of the configurations
reachable through changes in a set `D`, and `D` closed under the base rules at all of them.
-/

namespace QEDefi.Actor

variable {S O C A P : Type}

/-- A sequence of configuration changes, each by a capability. -/
inductive Path (chg : A × P → C → C → Prop) : C → List (A × P) → C → Prop
  | nil (c : C) : Path chg c [] c
  | cons {e : A × P} {c c₁ c₂ : C} {es : List (A × P)} :
      chg e c c₁ → Path chg c₁ es c₂ → Path chg c (e :: es) c₂

theorem Path.append {chg : A × P → C → C → Prop} {c₁ c₂ c₃ : C} {es₁ es₂ : List (A × P)}
    (h₁ : Path chg c₁ es₁ c₂) (h₂ : Path chg c₂ es₂ c₃) : Path chg c₁ (es₁ ++ es₂) c₃ := by
  induction h₁ with
  | nil => exact h₂
  | cons he _ ih => exact .cons he (ih h₂)

/-- **Rules closed under configuration changes.** -/
def close (chg : A × P → C → C → Prop) (R : Rules C A P) : Rules C A P := fun c q X =>
  ∃ c' es Y, Path chg c es c' ∧ R c' q Y ∧ X = Y ∪ {e | e ∈ es}

variable {chg : A × P → C → C → Prop} {R : Rules C A P}

/-- The base rules are among the closed rules. -/
theorem close_base {c : C} {q : A × P} {Y : Set (A × P)} (h : R c q Y) : close chg R c q Y :=
  ⟨c, [], Y, .nil c, h, by ext; simp⟩

/-- A base rule as a derivation step. -/
theorem Derives.base {c : C} {T : Set A} {q : A × P} {Y : Set (A × P)} (h : R c q Y)
    (hY : ∀ r ∈ Y, Derives (fun c => close chg R c) c T r) :
    Derives (fun c => close chg R c) c T q :=
  .rule (close_base h) hY

/-- **Derivations after derivable changes are derivable before them.** -/
theorem Derives.of_path {c c' : C} {es : List (A × P)} {X : Set A} {q : A × P}
    (hp : Path chg c es c') (he : ∀ e ∈ es, Derives (fun c => close chg R c) c X e)
    (h : Derives (fun c => close chg R c) c' X q) : Derives (fun c => close chg R c) c X q := by
  induction h with
  | key p ha => exact .key p ha
  | @rule q Z hr _ ih =>
    obtain ⟨c'', es', Y, hp', hR, rfl⟩ := hr
    refine .rule ⟨c'', es ++ es', Y, hp.append hp', hR, rfl⟩ ?_
    intro r hr
    rcases hr with hr | hr
    · exact ih r (Or.inl hr)
    · rcases List.mem_append.1 hr with hr | hr
      · exact he r hr
      · exact ih r (Or.inr hr)

/-- **Stability from configurations.** If every successful step keeps the configuration or
performs changes that its consenters could derive, the closed rules are stable. -/
theorem stable_of_cfg {step : S → O → Option S} {consent : O → Set A} {cfg : S → C}
    (h : ∀ s op s', step s op = some s' → ∃ es, Path chg (cfg s) es (cfg s') ∧
      ∀ e ∈ es, Derives (fun c => close chg R c) (cfg s) (consent op) e) :
    Stable step consent (fun s => close chg R (cfg s)) := by
  intro s op s' he X r hd
  obtain ⟨es, hp, hes⟩ := h s op s' he
  have hd' : Derives (fun c => close chg R c) (cfg s') X r :=
    Derives.mono_rules (R := fun s => close chg R (cfg s)) (s := s') (fun _ _ hr => hr) hd
  have := Derives.of_path hp (fun e he' => (hes e he').mono_keys Set.subset_union_right)
    (hd'.mono_keys Set.subset_union_left)
  exact Derives.mono_rules (s' := s) (R' := fun s => close chg R (cfg s)) (fun _ _ hr => hr) this

/-- The configuration is unchanged: the empty path. -/
theorem path_of_eq {c c' : C} (h : c' = c) : Path chg c [] c' := by subst h; exact .nil _

/-- One derivable change. -/
theorem path_single {e : A × P} {c c' : C} (h : chg e c c') : Path chg c [e] c' :=
  .cons h (.nil c')

/-- An invariant kept by every change whose capability is in `D` holds along paths of such
changes. -/
theorem Path.inv {D : A × P → Prop} {Inv : C → Prop}
    (hchg : ∀ e c c', chg e c c' → D e → Inv c → Inv c') {c c' : C} {es : List (A × P)}
    (hp : Path chg c es c') (hes : ∀ e ∈ es, D e) (h : Inv c) : Inv c' := by
  induction hp with
  | nil => exact h
  | @cons e c c₁ c₂ es hc _ ih =>
    exact ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
      (hchg e c c₁ hc (hes e List.mem_cons_self) h)

/-- **Non-derivability under the closed rules.** Let `D` contain the keys' capabilities, let
`Inv` hold of `c₀` and be kept by changes whose capability is in `D`, and let `D` be closed under
the base rules at every configuration satisfying `Inv`. Then every capability derivable at `c₀`
is in `D`. -/
theorem close_le_of_closed {D : A × P → Prop} {Inv : C → Prop} {c₀ : C} {T : Set A}
    (hT : ∀ a ∈ T, ∀ p, D (a, p)) (h₀ : Inv c₀)
    (hchg : ∀ e c c', chg e c c' → D e → Inv c → Inv c')
    (hR : ∀ c, Inv c → ∀ q Y, R c q Y → (∀ r ∈ Y, D r) → D q) {q : A × P}
    (h : Derives (fun c => close chg R c) c₀ T q) : D q := by
  refine Derives.le_of_closed hT (fun q X hr hX => ?_) h
  obtain ⟨c', es, Y, hp, hR', rfl⟩ := hr
  have hinv : Inv c' := hp.inv hchg (fun e he => hX e (Or.inr he)) h₀
  exact hR c' hinv q Y hR' (fun r hr => hX r (Or.inl hr))

end QEDefi.Actor
