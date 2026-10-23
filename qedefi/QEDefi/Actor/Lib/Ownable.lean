import QEDefi.Actor.Lib.Sys

/-!
# Component: OpenZeppelin `Ownable` (v5.7.0)

`docs/access-control/oz-access.md` §1. One principal, the owner (`none` is `address(0)`, after
`renounceOwnership`). `onlyOwner` functions act when called by the owner; `transferOwnership(n)`
(owner only, `n ≠ address(0)`: the address type `A` has no zero) sets the owner; renouncing is
absorbing. Solmate `Owned` and Solady `Ownable` (without handover) have the same authority.

Parameters: the contract `t`, the embedding `ι` of these messages into the host's, and the host
functions `G` that are `onlyOwner`.

- `run_sound`, `act_of_owner`: per-call soundness in any host containing the component;
- `Closes`, `closed`: the component's part of a host's "who can" (`Sys.Closed`);
- `no_act`: who can act, standalone; `owner_can`: the owner can (not vacuous).
-/

namespace QEDefi.Actor.Ownable

variable {C A M H : Type}

/-- The configuration fragment: the owner. -/
abbrev Cfg (A : Type) := Option A

/-- The component's own functions. -/
inductive Msg (A : Type) where
  /-- `transferOwnership(n)`, owner only. -/
  | transferOwnership (n : A)
  /-- `renounceOwnership()`, owner only. -/
  | renounceOwnership

/-- **One call** from `b` (`none`: it reverts). -/
def run [DecidableEq A] (x : Cfg A) (b : A) : Msg A → Option (Cfg A)
  | .transferOwnership n => if x = some b then some (some n) else none
  | .renounceOwnership => if x = some b then some none else none

/-- The messages that pass `onlyOwner`: the host's guarded functions and the component's own. -/
def Guarded (ι : Msg A → M) (G : M → Prop) (m : M) : Prop := G m ∨ ∃ m₀, m = ι m₀

/-- **The access check as a rule.** -/
inductive Base (t : A) (ι : Msg A → M) (G : M → Prop) :
    Cfg A → A × Action A M H → Set (A × Action A M H) → Prop
  | own (x : Cfg A) (o : A) (m : M) (ho : x = some o) (hm : Guarded ι G m) :
      Base t ι G x (t, .act m) {(o, .call t m)}

/-- **The configuration changes.** -/
inductive Chg (t : A) (ι : Msg A → M) : A × Action A M H → Cfg A → Cfg A → Prop
  | transfer (x : Cfg A) (n : A) : Chg t ι (t, .act (ι (.transferOwnership n))) x (some n)
  | renounce (x : Cfg A) : Chg t ι (t, .act (ι .renounceOwnership)) x none

/-- The component. -/
def sys (t : A) (ι : Msg A → M) (G : M → Prop) : Sys (Cfg A) A (Action A M H) :=
  ⟨Base t ι G, Chg t ι⟩

variable {t : A} {ι : Msg A → M} {G : M → Prop} {S : Sys C A (Action A M H)} {L : Lens C (Cfg A)}

/-! ## Per-call soundness, in any host -/

/-- **`onlyOwner`**: a guarded call by the owner acts. -/
theorem act_of_owner (hS : (sys t ι G).lift L ≤ S) {c : C} {K : Set A} {b : A} {m : M}
    (ho : L.get c = some b) (hm : Guarded ι G m) (hd : Derives S.auth c K (b, .call t m)) :
    Derives S.auth c K (t, .act m) :=
  hS.derive_lift (K := sys t ι G) (Base.own _ b m ho hm) hd

/-- **Every successful call of the component's functions makes a derivable change.** -/
theorem run_sound [DecidableEq A] (hS : (sys t ι G).lift L ≤ S) {c : C} {K : Set A} {b : A}
    {m : Msg A} {x' : Cfg A} (hr : run (L.get c) b m = some x')
    (hd : Derives S.auth c K (b, .call t (ι m))) :
    ∃ e, S.chg e c (L.set x' c) ∧ Derives S.auth c K e := by
  cases m with
  | transferOwnership n =>
    simp only [run] at hr; split_ifs at hr with ho; cases hr
    exact ⟨_, hS.chg_lift (K := sys t ι G) (Chg.transfer _ n),
      act_of_owner hS ho (Or.inr ⟨_, rfl⟩) hd⟩
  | renounceOwnership =>
    simp only [run] at hr; split_ifs at hr with ho; cases hr
    exact ⟨_, hS.chg_lift (K := sys t ι G) (Chg.renounce _),
      act_of_owner hS ho (Or.inr ⟨_, rfl⟩) hd⟩

/-! ## Who can -/

/-- **The component's part of a host's closed set**, as first-order conditions. -/
structure Closes (t : A) (ι : Msg A → M) (G : M → Prop) (L : Lens C (Cfg A))
    (D : A × Action A M H → Prop) (Inv : C → Prop) : Prop where
  own : ∀ c, Inv c → ∀ o m, L.get c = some o → Guarded ι G m → D (o, .call t m) → D (t, .act m)
  transfer : ∀ c n, Inv c → D (t, .act (ι (.transferOwnership n))) → Inv (L.set (some n) c)
  renounce : ∀ c, Inv c → D (t, .act (ι .renounceOwnership)) → Inv (L.set none c)

theorem closed {D : A × Action A M H → Prop} {Inv : C → Prop} (h : Closes t ι G L D Inv) :
    Sys.Closed ((sys t ι G).lift L) D Inv := by
  refine Sys.Closed.lift (fun e c x' hc hD hI => ?_) (fun c hI q Y hb hY => ?_)
  · cases hc with
    | transfer _ n => exact h.transfer c n hI hD
    | renounce => exact h.renounce c hI hD
  · cases hb with
    | own o m ho hm => exact h.own c hI o m ho hm (hY _ rfl)

/-- **The usual case**: the owner is fixed at `x₀` (`Inv` says so), its guarded calls lead into
`D` only as they should, and `D` holds none of the component's own acts. -/
theorem Closes.frozen {D : A × Action A M H → Prop} {Inv : C → Prop} {x₀ : Cfg A}
    (hInv : ∀ c, Inv c → L.get c = x₀)
    (hown : ∀ o, x₀ = some o → ∀ m, Guarded ι G m → D (o, .call t m) → D (t, .act m))
    (hadm : ∀ m₀, ¬ D (t, .act (ι m₀))) : Closes t ι G L D Inv :=
  ⟨fun c hI o m ho => hown o (hInv c hI ▸ ho) m, fun _ _ _ hD => (hadm _ hD).elim,
    fun _ _ hD => (hadm _ hD).elim⟩

/-- **Who can act, standalone.** Keys `T` that include neither the contract nor its owner make it
act on no message, whatever they do. -/
theorem no_act {T : Set A} {x₀ : Cfg A} (ht : t ∉ T) (ho : ∀ o, x₀ = some o → o ∉ T)
    (m : M) : ¬ Derives (sys (H := H) t ι G).auth x₀ T (t, .act m) := by
  intro hd
  have hc : Closes t ι G (Lens.id _) (fun q : A × Action A M H => q.1 ∈ T) (fun x => x = x₀) :=
    Closes.frozen (fun _ h => h) (fun o h _ _ hD => absurd hD (ho o h)) (fun _ hD => ht hD)
  exact ht (Sys.le_of_closed (closed hc) (fun a ha _ => ha) rfl
    ((Sys.le_lift_id _).derives hd) (D := fun q => q.1 ∈ T))

/-- **Not vacuous**: the owner acts. -/
theorem owner_can {x : Cfg A} {o : A} (ho : x = some o) {m : M} (hm : Guarded ι G m) :
    Derives (sys (H := H) t ι G).auth x {o} (t, .act m) :=
  (Sys.le_refl _).derive₁ (S₁ := sys t ι G) (Base.own x o m ho hm) (.key _ rfl)

end QEDefi.Actor.Ownable
