module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Finset.Card

/-!
# Authority as derivation

The actor model of a system of contracts, independent of the EVM. A **capability** `(a, p)`
says that principal `a` can be made to perform action `p`: issue a call, sign a digest,
exercise a role, cause an effect. The system's **rules** in state `s` say which sets of
capabilities yield which capability (`rule s q X`: `q` follows from all of `X`); a set `T` of
**keys** (the externally owned accounts that consent to the transactions considered, by
sending them or signing) performs every action. `Derives R s T q` is the least set closed
under both.

Every access-control mechanism surveyed in `docs/access-control.md` is a family of rules:

- a role check is a rule `(t, eff) ← {(b, call)}` for each holder `b`;
- a threshold is a rule whose premise is any large enough set of signatures (`threshold`);
- a contract that holds a role is a *relay*: its own rules derive the calls it issues;
- stored consent (approved hashes, scheduled operations, pending owners) is a rule with an
  empty premise, a fact of the state;
- an open function (initialiser, permissionless executor) is a rule with an empty premise.

Rules may **over-approximate** authority (e.g. ignore delays): every theorem stays sound. They
may not under-approximate it: the stability obligation of `QEDefi.Actor.Sound` fails then.
-/

@[expose] public section

namespace QEDefi.Actor

variable {S A P : Type}

/-- The rules of an authority structure: `R s q X` when, in state `s`, capability `q` follows
from all capabilities in `X`. -/
abbrev Rules (S A P : Type) := S → A × P → Set (A × P) → Prop

/-- **The derivable capabilities** in state `s` when the keys `T` act. -/
inductive Derives (R : Rules S A P) (s : S) (T : Set A) : A × P → Prop
  /-- A key that acts performs any action. -/
  | key {a : A} (p : P) : a ∈ T → Derives R s T (a, p)
  /-- A rule whose premises are all derivable. -/
  | rule {q : A × P} {X : Set (A × P)} : R s q X → (∀ r ∈ X, Derives R s T r) →
      Derives R s T q

namespace Derives

variable {R : Rules S A P} {s : S} {T T' : Set A} {q : A × P}

/-- **Induction principle**: a set containing the keys' capabilities and closed under the rules
contains every derivable capability. This is how non-derivability is proved. -/
theorem le_of_closed {C : A × P → Prop} (hT : ∀ a ∈ T, ∀ p, C (a, p))
    (hR : ∀ q X, R s q X → (∀ r ∈ X, C r) → C q) (h : Derives R s T q) : C q := by
  induction h with
  | key p ha => exact hT _ ha p
  | rule hr _ ih => exact hR _ _ hr ih

/-- More acting keys derive more. -/
theorem mono_keys (hT : T ⊆ T') (h : Derives R s T q) : Derives R s T' q :=
  le_of_closed (fun _ ha p => key p (hT ha)) (fun _ _ hr hX => rule hr hX) h

/-- More rules derive more (the states may be of different types, e.g. a state and its
configuration). -/
theorem mono_rules {S' : Type} {R' : Rules S' A P} {s' : S'} (hR : ∀ q X, R s q X → R' s' q X)
    (h : Derives R s T q) : Derives R' s' T q :=
  le_of_closed (fun _ ha p => key p ha) (fun _ _ hr hX => rule (hR _ _ hr) hX) h

/-- **Substitution**: if every capability of the keys `T` is derivable from `T'`, everything
derivable from `T` is. -/
theorem subst (hT : ∀ a ∈ T, ∀ p, Derives R s T' (a, p)) (h : Derives R s T q) :
    Derives R s T' q :=
  le_of_closed hT (fun _ _ hr hX => rule hr hX) h

/-- A rule with no premise is a fact. -/
theorem fact (hr : R s q ∅) : Derives R s T q := rule hr (fun _ h => h.elim)

/-- A rule with one premise. -/
theorem single {r : A × P} (hr : R s q {r}) (h : Derives R s T r) : Derives R s T q :=
  rule hr (fun _ hm => by rw [Set.mem_singleton_iff.1 hm]; exact h)

/-- Nothing derives from no keys under no rules. -/
theorem not_of_empty (hR : ∀ q X, ¬ R s q X) : ¬ Derives R s ∅ q := fun h =>
  le_of_closed (C := fun _ => False) (fun _ ha => ha.elim) (fun q X hr _ => hR q X hr) h

end Derives

/-! ## Rule combinators -/

/-- The union of two rule families. -/
def Rules.union (R₁ R₂ : Rules S A P) : Rules S A P := fun s q X => R₁ s q X ∨ R₂ s q X

/-- Rules about one subject only: `(c, p) ← X` when `F s p X`. -/
def Rules.at (c : A) (F : S → P → Set (A × P) → Prop) : Rules S A P :=
  fun s q X => q.1 = c ∧ F s q.2 X

/-- The premise sets of a `k`-of-`owners` threshold over the actions `act o` of each owner
(e.g. `act o = (o, sign h)`): the images of the subsets of `owners` with at least `k` members. -/
def threshold [DecidableEq A] (owners : Finset A) (k : ℕ) (act : A → A × P) :
    Set (Set (A × P)) :=
  {X | ∃ Y : Finset A, Y ⊆ owners ∧ k ≤ Y.card ∧ X = act '' (Y : Set A)}

theorem threshold_mem [DecidableEq A] {owners Y : Finset A} {k : ℕ} {act : A → A × P}
    (hY : Y ⊆ owners) (hk : k ≤ Y.card) : act '' (Y : Set A) ∈ threshold owners k act :=
  ⟨Y, hY, hk, rfl⟩

/-- A threshold premise is derivable when at least `k` owners' actions are. -/
theorem Derives.threshold [DecidableEq A] {R : Rules S A P} {s : S} {T : Set A} {q : A × P}
    {owners Y : Finset A} {k : ℕ} {act : A → A × P}
    (hr : ∀ X ∈ QEDefi.Actor.threshold owners k act, R s q X) (hY : Y ⊆ owners) (hk : k ≤ Y.card)
    (h : ∀ o ∈ Y, Derives R s T (act o)) : Derives R s T q :=
  Derives.rule (hr _ (threshold_mem hY hk)) (by
    rintro _ ⟨o, ho, rfl⟩
    exact h o ho)

/-- **No threshold from too few.** If every derivable `act o` of an owner `o` has `o ∈ T`, and
fewer than `k` owners are in `T`, no threshold premise is fully derivable. -/
theorem threshold_not [DecidableEq A] {C : A × P → Prop} {owners : Finset A} {k : ℕ}
    {act : A → A × P} {T : Finset A} (hC : ∀ o ∈ owners, C (act o) → o ∈ T)
    (hk : (owners ∩ T).card < k) :
    ∀ X ∈ QEDefi.Actor.threshold owners k act, ¬ ∀ r ∈ X, C r := by
  rintro _ ⟨Y, hY, hYk, rfl⟩ hall
  have hsub : Y ⊆ owners ∩ T := fun o ho =>
    Finset.mem_inter.2 ⟨hY ho, hC o (hY ho) (hall _ ⟨o, ho, rfl⟩)⟩
  exact absurd (hYk.trans (Finset.card_le_card hsub)) (by omega)

end QEDefi.Actor

end
