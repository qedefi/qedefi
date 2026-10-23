import QEDefi.Actor.Action
import QEDefi.Actor.Config

/-!
# Components: authority systems that compose

A **system** (`Sys C A P`) is what `docs/access-control.md` §3 asks a model to write: base rules
and configuration changes, over configurations `C`. Its authority is `close chg base` (`Sys.auth`):
every escalation through configuration changes is derived.

Library components (`QEDefi.Actor.Lib.*`) are systems over their own configuration fragment
(an owner, a role table, a Safe's owners and modules), parameterised by the contract's address
and by an embedding of their messages into the host's message type. A protocol model

1. puts each fragment in its configuration and gives a **lens** (`Lens C X`) to it;
2. takes its system as the union (`Sys.union`, `Sys.iUnion`) of the components' lifts
   (`Sys.lift`) and of its own rules (`Sys.ofRules` of the shapes of `Action.lean`);
3. uses each component's `run_sound` (in a host containing it: `K.lift L ≤ S`) to prove its own
   per-call soundness, then `Sys.stable` for the stability obligation;
4. proves "who can" with `Sys.le_of_closed`: a set `D` of capabilities and an invariant `Inv`
   with `Closed S D Inv`, which splits over the union (`Closed.union`) into one obligation per
   component, each discharged by that component's `closed` lemma from first-order conditions.
-/

namespace QEDefi.Actor

variable {C X Y A P : Type}

/-! ## Lenses -/

/-- A view of a part `X` of a configuration `C`. -/
structure Lens (C X : Type) where
  get : C → X
  set : X → C → C

/-- The whole configuration. -/
def Lens.id (C : Type) : Lens C C := ⟨fun c => c, fun x _ => x⟩

/-- A part of a part. -/
def Lens.comp (L : Lens C X) (L' : Lens X Y) : Lens C Y :=
  ⟨fun c => L'.get (L.get c), fun y c => L.set (L'.set y (L.get c)) c⟩

/-! ## Systems -/

/-- **An authority system**: base rules and configuration changes over configurations `C`. -/
structure Sys (C A P : Type) where
  base : Rules C A P
  chg : A × P → C → C → Prop

namespace Sys

/-- The authority of a system: its base rules closed under its changes. -/
abbrev auth (S : Sys C A P) : Rules C A P := close S.chg S.base

/-- Rules with no configuration change. -/
def ofRules (R : Rules C A P) : Sys C A P := ⟨R, fun _ _ _ => False⟩

/-- The union of two systems. -/
def union (S₁ S₂ : Sys C A P) : Sys C A P :=
  ⟨fun c q Y => S₁.base c q Y ∨ S₂.base c q Y, fun e c c' => S₁.chg e c c' ∨ S₂.chg e c c'⟩

/-- The union of a family of systems (e.g. one role manager per address). -/
def iUnion {I : Type} (S : I → Sys C A P) : Sys C A P :=
  ⟨fun c q Y => ∃ i, (S i).base c q Y, fun e c c' => ∃ i, (S i).chg e c c'⟩

/-- **A component in a host**: its rules read the part `L.get c`, its changes write it. -/
def lift (L : Lens C X) (S : Sys X A P) : Sys C A P :=
  ⟨fun c => S.base (L.get c), fun e c c' => ∃ x', S.chg e (L.get c) x' ∧ c' = L.set x' c⟩

/-- `S₁` is part of `S₂`. -/
structure Le (S₁ S₂ : Sys C A P) : Prop where
  base : ∀ c q Y, S₁.base c q Y → S₂.base c q Y
  chg : ∀ e c c', S₁.chg e c c' → S₂.chg e c c'

instance : LE (Sys C A P) := ⟨Le⟩

variable {S S₁ S₂ S₃ : Sys C A P}

theorem le_refl (S : Sys C A P) : S ≤ S := ⟨fun _ _ _ h => h, fun _ _ _ h => h⟩

theorem le_trans (h₁ : S₁ ≤ S₂) (h₂ : S₂ ≤ S₃) : S₁ ≤ S₃ :=
  ⟨fun c q Y h => h₂.base c q Y (h₁.base c q Y h), fun e c c' h => h₂.chg e c c' (h₁.chg e c c' h)⟩

theorem le_union_left : S₁ ≤ S₁.union S₂ := ⟨fun _ _ _ h => Or.inl h, fun _ _ _ h => Or.inl h⟩

theorem le_union_right : S₂ ≤ S₁.union S₂ := ⟨fun _ _ _ h => Or.inr h, fun _ _ _ h => Or.inr h⟩

theorem le_iUnion {I : Type} (S : I → Sys C A P) (i : I) : S i ≤ iUnion S :=
  ⟨fun _ _ _ h => ⟨i, h⟩, fun _ _ _ h => ⟨i, h⟩⟩

theorem le_lift_id (S : Sys C A P) : S ≤ S.lift (Lens.id C) :=
  ⟨fun _ _ _ h => h, fun _ _ c' h => ⟨c', h, rfl⟩⟩

theorem lift_mono {L : Lens C X} {K₁ K₂ : Sys X A P} (h : K₁ ≤ K₂) : K₁.lift L ≤ K₂.lift L :=
  ⟨fun c q Y hb => h.base (L.get c) q Y hb,
    fun _ _ _ ⟨x', hc, he⟩ => ⟨x', h.chg _ _ _ hc, he⟩⟩

/-- Lifting along a part of a part. -/
theorem lift_lift_le {L : Lens C X} {L' : Lens X Y} {K : Sys Y A P} :
    (K.lift L').lift L ≤ K.lift (L.comp L') :=
  ⟨fun _ _ _ h => h, fun _ _ _ ⟨_, ⟨y', hc, rfl⟩, he⟩ => ⟨y', hc, he⟩⟩

theorem lift_comp_le {L : Lens C X} {L' : Lens X Y} {K : Sys Y A P} :
    K.lift (L.comp L') ≤ (K.lift L').lift L :=
  ⟨fun _ _ _ h => h, fun _ _ _ ⟨y', hc, he⟩ => ⟨_, ⟨y', hc, rfl⟩, he⟩⟩

theorem lift_union_le {L : Lens C X} {K₁ K₂ : Sys X A P} :
    (K₁.union K₂).lift L ≤ (K₁.lift L).union (K₂.lift L) :=
  ⟨fun _ _ _ h => h, fun _ _ _ ⟨x', hc, he⟩ => hc.imp (fun h => ⟨x', h, he⟩) (fun h => ⟨x', h, he⟩)⟩

/-! ## Authority in a host -/

theorem _root_.QEDefi.Actor.Path.mono {chg₁ chg₂ : A × P → C → C → Prop}
    (h : ∀ e c c', chg₁ e c c' → chg₂ e c c') {c c' : C} {es : List (A × P)}
    (hp : Path chg₁ c es c') : Path chg₂ c es c' := by
  induction hp with
  | nil c => exact .nil c
  | cons he _ ih => exact .cons (h _ _ _ he) ih

/-- A part's rule is a rule of the whole. -/
theorem Le.auth (h : S₁ ≤ S₂) {c : C} {q : A × P} {Y : Set (A × P)} (hr : S₁.auth c q Y) :
    S₂.auth c q Y := by
  obtain ⟨c', es, Z, hp, hR, rfl⟩ := hr
  exact ⟨c', es, Z, hp.mono h.chg, h.base _ _ _ hR, rfl⟩

/-- A part derives less. -/
theorem Le.derives (h : S₁ ≤ S₂) {c : C} {T : Set A} {q : A × P}
    (hd : Derives S₁.auth c T q) : Derives S₂.auth c T q :=
  Derives.mono_rules (fun _ _ hr => h.auth hr) hd

/-- A base rule of a part, as a derivation step of the whole. -/
theorem Le.derive (h : S₁ ≤ S₂) {c : C} {T : Set A} {q : A × P} {Y : Set (A × P)}
    (hr : S₁.base c q Y) (hY : ∀ r ∈ Y, Derives S₂.auth c T r) : Derives S₂.auth c T q :=
  .rule (close_base (h.base _ _ _ hr)) hY

/-- A base rule of a part with one premise. -/
theorem Le.derive₁ (h : S₁ ≤ S₂) {c : C} {T : Set A} {q r : A × P}
    (hr : S₁.base c q {r}) (hY : Derives S₂.auth c T r) : Derives S₂.auth c T q :=
  h.derive hr (fun _ hm => by rw [Set.mem_singleton_iff.1 hm]; exact hY)

/-- A base rule of a lifted component with one premise. -/
theorem Le.derive_lift {L : Lens C X} {K : Sys X A P} (h : K.lift L ≤ S) {c : C} {T : Set A}
    {q r : A × P} (hr : K.base (L.get c) q {r}) (hY : Derives S.auth c T r) :
    Derives S.auth c T q :=
  h.derive₁ (S₁ := K.lift L) hr hY

/-- A change of a lifted component is a change of the host. -/
theorem Le.chg_lift {L : Lens C X} {K : Sys X A P} (h : K.lift L ≤ S) {e : A × P} {c : C}
    {x' : X} (hc : K.chg e (L.get c) x') : S.chg e c (L.set x' c) :=
  h.chg _ _ _ ⟨x', hc, rfl⟩

/-- Derivations after a derivable path of changes are derivable before it. -/
theorem derives_of_path {c c' : C} {es : List (A × P)} {T : Set A} {q : A × P}
    (hp : Path S.chg c es c') (he : ∀ e ∈ es, Derives S.auth c T e)
    (h : Derives S.auth c' T q) : Derives S.auth c T q :=
  Derives.of_path hp he h

/-! ## Stability -/

/-- **Stability from per-step soundness**: each successful step keeps the configuration or makes
one change its consenters could derive. -/
theorem stable {St O : Type} {step : St → O → Option St} {consent : O → Set A} {cfg : St → C}
    (S : Sys C A P)
    (h : ∀ s op s', step s op = some s' → cfg s' = cfg s ∨
      ∃ e, S.chg e (cfg s) (cfg s') ∧ Derives S.auth (cfg s) (consent op) e) :
    Stable step consent (fun s => S.auth (cfg s)) := by
  refine stable_of_cfg (chg := S.chg) (R := S.base) (cfg := cfg) (fun s op s' he => ?_)
  rcases h s op s' he with hc | ⟨e, hc, hd⟩
  · exact ⟨[], path_of_eq hc, fun _ h => (List.not_mem_nil h).elim⟩
  · exact ⟨[e], path_single hc, fun e' h => by rw [List.mem_singleton.1 h]; exact hd⟩

/-! ## Non-derivability, componentwise -/

/-- **`D` is closed in `S` at configurations satisfying `Inv`**: changes by capabilities in `D`
keep `Inv`, and every base rule with premises in `D` concludes in `D`. -/
structure Closed (S : Sys C A P) (D : A × P → Prop) (Inv : C → Prop) : Prop where
  chg : ∀ e c c', S.chg e c c' → D e → Inv c → Inv c'
  base : ∀ c, Inv c → ∀ q Y, S.base c q Y → (∀ r ∈ Y, D r) → D q

variable {D : A × P → Prop} {Inv : C → Prop}

/-- **Who can**: everything the keys `T` derive is in a closed `D` containing their capabilities. -/
theorem le_of_closed (hS : Closed S D Inv) {T : Set A} (hT : ∀ a ∈ T, ∀ p, D (a, p)) {c₀ : C}
    (h₀ : Inv c₀) {q : A × P} (h : Derives S.auth c₀ T q) : D q :=
  close_le_of_closed hT h₀ hS.chg hS.base h

theorem Closed.union (h₁ : Closed S₁ D Inv) (h₂ : Closed S₂ D Inv) :
    Closed (S₁.union S₂) D Inv :=
  ⟨fun e c c' hc hD hI => hc.elim (fun h => h₁.chg e c c' h hD hI) (fun h => h₂.chg e c c' h hD hI),
    fun c hI q Y hb hY => hb.elim (fun h => h₁.base c hI q Y h hY) (fun h => h₂.base c hI q Y h hY)⟩

theorem Closed.iUnion {I : Type} {S : I → Sys C A P} (h : ∀ i, Closed (S i) D Inv) :
    Closed (iUnion S) D Inv :=
  ⟨fun e c c' ⟨i, hc⟩ hD hI => (h i).chg e c c' hc hD hI,
    fun c hI q Y ⟨i, hb⟩ hY => (h i).base c hI q Y hb hY⟩

theorem Closed.mono (h : Closed S₂ D Inv) (hle : S₁ ≤ S₂) : Closed S₁ D Inv :=
  ⟨fun e c c' hc => h.chg e c c' (hle.chg e c c' hc),
    fun c hI q Y hb => h.base c hI q Y (hle.base c q Y hb)⟩

/-- Closedness of a lifted component, from its rules and changes on the part. -/
theorem Closed.lift {L : Lens C X} {K : Sys X A P}
    (hc : ∀ e c x', K.chg e (L.get c) x' → D e → Inv c → Inv (L.set x' c))
    (hb : ∀ c, Inv c → ∀ q Y, K.base (L.get c) q Y → (∀ r ∈ Y, D r) → D q) :
    Closed (K.lift L) D Inv :=
  ⟨fun e c _ ⟨x', hx, he⟩ hD hI => he ▸ hc e c x' hx hD hI, hb⟩

theorem Closed.ofRules {R : Rules C A P}
    (h : ∀ c, Inv c → ∀ q Y, R c q Y → (∀ r ∈ Y, D r) → D q) : Closed (ofRules R) D Inv :=
  ⟨fun _ _ _ hc => hc.elim, h⟩

end Sys

/-! ## The shapes of `Action.lean` as systems -/

section Shapes

variable {M H : Type} {D : A × Action A M H → Prop} {Inv : C → Prop}

theorem Sys.Closed.endpoint {t : A} {may : C → A → M → Prop}
    (h : ∀ c, Inv c → ∀ b m, may c b m → D (b, .call t m) → D (t, .act m)) :
    Sys.Closed (Sys.ofRules (endpoint t may)) D Inv :=
  Sys.Closed.ofRules fun c hI _ _ ⟨b, m, hq, hm, hY⟩ hD => by
    subst hq hY; exact h c hI b m hm (hD _ rfl)

theorem Sys.Closed.relay {t : A} {out : C → M → Action A M H → Prop}
    (h : ∀ c, Inv c → ∀ m p, out c m p → D (t, .act m) → D (t, p)) :
    Sys.Closed (Sys.ofRules (relay t out)) D Inv :=
  Sys.Closed.ofRules fun c hI q _ ⟨m, hq, ho, hY⟩ hD => by
    subst hY; obtain ⟨a, p⟩ := q; simp only at hq; subst hq
    exact h c hI m p ho (hD _ rfl)

theorem Sys.Closed.facts {F : C → A × Action A M H → Prop}
    (h : ∀ c, Inv c → ∀ q, F c q → D q) : Sys.Closed (Sys.ofRules (facts F)) D Inv :=
  Sys.Closed.ofRules fun c hI q _ ⟨hF, _⟩ _ => h c hI q hF

end Shapes

end QEDefi.Actor
