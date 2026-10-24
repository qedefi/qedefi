import QEDefi.Actor.Lib.Sys

/-!
# Component: OpenZeppelin `Ownable2Step` (v5.7.0)

`access/Ownable2Step.sol`. Two principals, the owner and the pending owner (`none` is
`address(0)`):

- `transferOwnership(n)` (owner only, no zero check: `none` cancels) sets the pending owner;
- `acceptOwnership()` (pending owner only) makes the caller owner and clears the pending owner;
- `renounceOwnership()` (owner only) clears the owner **and the pending owner** (the v5
  `_transferOwnership` override deletes `_pendingOwner`).

A pending transfer never expires. Chainlink `ConfirmedOwner` has the same authority.

- `run_sound`, `act_of_owner`: per-call soundness in any host containing the component;
- `Closes`, `closed`: the component's part of a host's "who can";
- `no_act`: neither owner nor pending owner, no act; `pending_can`: **the pending owner is a
  controller**, derived through the acceptance (`close`), not written as a rule.
-/

namespace QEDefi.Actor.Ownable2Step

variable {C A M H : Type}

/-- The configuration fragment. -/
structure Cfg (A : Type) where
  owner : Option A
  pending : Option A

/-- The component's own functions. -/
inductive Msg (A : Type) where
  /-- `transferOwnership(n)`, owner only; `none` (address 0) cancels a pending transfer. -/
  | transferOwnership (n : Option A)
  /-- `acceptOwnership()`, pending owner only. -/
  | acceptOwnership
  /-- `renounceOwnership()`, owner only. -/
  | renounceOwnership

/-- **One call** from `b`. -/
def run [DecidableEq A] (x : Cfg A) (b : A) : Msg A → Option (Cfg A)
  | .transferOwnership n => if x.owner = some b then some { x with pending := n } else none
  | .acceptOwnership => if x.pending = some b then some ⟨some b, none⟩ else none
  | .renounceOwnership => if x.owner = some b then some ⟨none, none⟩ else none

/-- The messages that pass `onlyOwner`: the host's guarded functions and the component's
owner-only ones. -/
def Guarded (ι : Msg A → M) (G : M → Prop) (m : M) : Prop :=
  G m ∨ (∃ n, m = ι (.transferOwnership n)) ∨ m = ι .renounceOwnership

/-- **The access checks as rules.** -/
inductive Base (t : A) (ι : Msg A → M) (G : M → Prop) :
    Cfg A → A × Action A M H → Set (A × Action A M H) → Prop
  | own (x : Cfg A) (o : A) (m : M) (ho : x.owner = some o) (hm : Guarded ι G m) :
      Base t ι G x (t, .act m) {(o, .call t m)}
  | accept (x : Cfg A) (p : A) (hp : x.pending = some p) :
      Base t ι G x (t, .act (ι .acceptOwnership)) {(p, .call t (ι .acceptOwnership))}

/-- **The configuration changes.** The new owner on acceptance is the pending owner (the caller). -/
inductive Chg (t : A) (ι : Msg A → M) : A × Action A M H → Cfg A → Cfg A → Prop
  | transfer (x : Cfg A) (n : Option A) :
      Chg t ι (t, .act (ι (.transferOwnership n))) x { x with pending := n }
  | accept (x : Cfg A) (p : A) (hp : x.pending = some p) :
      Chg t ι (t, .act (ι .acceptOwnership)) x ⟨some p, none⟩
  | renounce (x : Cfg A) : Chg t ι (t, .act (ι .renounceOwnership)) x ⟨none, none⟩

/-- The component. -/
def sys (t : A) (ι : Msg A → M) (G : M → Prop) : Sys (Cfg A) A (Action A M H) :=
  ⟨Base t ι G, Chg t ι⟩

variable {t : A} {ι : Msg A → M} {G : M → Prop} {S : Sys C A (Action A M H)} {L : Lens C (Cfg A)}

/-! ## Per-call soundness, in any host -/

/-- **`onlyOwner`**: a guarded call by the owner acts. -/
theorem act_of_owner (hS : (sys t ι G).lift L ≤ S) {c : C} {K : Set A} {b : A} {m : M}
    (ho : (L.get c).owner = some b) (hm : Guarded ι G m)
    (hd : Derives S.auth c K (b, .call t m)) : Derives S.auth c K (t, .act m) :=
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
      act_of_owner hS ho (Or.inr (Or.inl ⟨n, rfl⟩)) hd⟩
  | acceptOwnership =>
    simp only [run] at hr; split_ifs at hr with hp; cases hr
    exact ⟨_, hS.chg_lift (K := sys t ι G) (Chg.accept _ b hp),
      hS.derive_lift (K := sys t ι G) (Base.accept _ b hp) hd⟩
  | renounceOwnership =>
    simp only [run] at hr; split_ifs at hr with ho; cases hr
    exact ⟨_, hS.chg_lift (K := sys t ι G) (Chg.renounce _),
      act_of_owner hS ho (Or.inr (Or.inr rfl)) hd⟩

/-! ## Who can -/

/-- **The component's part of a host's closed set**, as first-order conditions. -/
structure Closes (t : A) (ι : Msg A → M) (G : M → Prop) (L : Lens C (Cfg A))
    (D : A × Action A M H → Prop) (Inv : C → Prop) : Prop where
  own : ∀ c, Inv c → ∀ o m, (L.get c).owner = some o → Guarded ι G m → D (o, .call t m) →
    D (t, .act m)
  accept : ∀ c, Inv c → ∀ p, (L.get c).pending = some p → D (p, .call t (ι .acceptOwnership)) →
    D (t, .act (ι .acceptOwnership))
  transfer : ∀ c n, Inv c → D (t, .act (ι (.transferOwnership n))) →
    Inv (L.set { L.get c with pending := n } c)
  acceptChg : ∀ c p, Inv c → (L.get c).pending = some p → D (t, .act (ι .acceptOwnership)) →
    Inv (L.set ⟨some p, none⟩ c)
  renounce : ∀ c, Inv c → D (t, .act (ι .renounceOwnership)) → Inv (L.set ⟨none, none⟩ c)

theorem closed {D : A × Action A M H → Prop} {Inv : C → Prop} (h : Closes t ι G L D Inv) :
    Sys.Closed ((sys t ι G).lift L) D Inv := by
  refine Sys.Closed.lift (fun e c x' hc hD hI => ?_) (fun c hI q Y hb hY => ?_)
  · cases hc with
    | transfer _ n => exact h.transfer c n hI hD
    | accept _ p hp => exact h.acceptChg c p hI hp hD
    | renounce => exact h.renounce c hI hD
  · cases hb with
    | own o m ho hm => exact h.own c hI o m ho hm (hY _ rfl)
    | accept p hp => exact h.accept c hI p hp (hY _ rfl)

/-- **The usual case**: owner and pending owner fixed at `x₀`, neither of them leads into `D`
except as it should, and `D` holds none of the component's own acts. -/
theorem Closes.frozen {D : A × Action A M H → Prop} {Inv : C → Prop} {x₀ : Cfg A}
    (hInv : ∀ c, Inv c → L.get c = x₀)
    (hown : ∀ o, x₀.owner = some o → ∀ m, Guarded ι G m → D (o, .call t m) → D (t, .act m))
    (hpen : ∀ p, x₀.pending = some p → ¬ D (p, .call t (ι .acceptOwnership)))
    (hadm : ∀ m₀, ¬ D (t, .act (ι m₀))) : Closes t ι G L D Inv :=
  ⟨fun c hI o m ho => hown o (hInv c hI ▸ ho) m,
    fun c hI p hp hD => (hpen p (hInv c hI ▸ hp) hD).elim,
    fun _ _ _ hD => (hadm _ hD).elim, fun _ _ _ _ hD => (hadm _ hD).elim,
    fun _ _ hD => (hadm _ hD).elim⟩

/-- **Who can act, standalone.** Keys `T` that include neither the contract, its owner nor its
pending owner make it act on no message. -/
theorem no_act {T : Set A} {x₀ : Cfg A} (ht : t ∉ T) (ho : ∀ o, x₀.owner = some o → o ∉ T)
    (hp : ∀ p, x₀.pending = some p → p ∉ T) (m : M) : ¬ Derives (sys (H := H) t ι G).auth x₀ T (t, .act m) := by
  intro hd
  have hc : Closes t ι G (Lens.id _) (fun q : A × Action A M H => q.1 ∈ T) (fun x => x = x₀) :=
    Closes.frozen (fun _ h => h) (fun o h _ _ hD => absurd hD (ho o h)) (fun p h hD => hp p h hD)
      (fun _ hD => ht hD)
  exact ht (Sys.le_of_closed (closed hc) (fun a ha _ => ha) rfl
    ((Sys.le_lift_id _).derives hd) (D := fun q => q.1 ∈ T))

/-- **Not vacuous**: the owner acts. -/
theorem owner_can {x : Cfg A} {o : A} (ho : x.owner = some o) {m : M} (hm : Guarded ι G m) :
    Derives (sys (H := H) t ι G).auth x {o} (t, .act m) :=
  (Sys.le_refl _).derive₁ (S₁ := sys t ι G) (Base.own x o m ho hm) (.key _ rfl)

/-- **The pending owner is a controller**: it acts on every guarded message, by accepting first. -/
theorem pending_can {x : Cfg A} {p : A} (hp : x.pending = some p) {m : M} (hm : Guarded ι G m) :
    Derives (sys (H := H) t ι G).auth x {p} (t, .act m) := by
  have hacc : Derives (sys (H := H) t ι G).auth x {p} (t, .act (ι .acceptOwnership)) :=
    (Sys.le_refl _).derive₁ (S₁ := sys t ι G) (Base.accept x p hp) (.key _ rfl)
  exact Sys.derives_of_path (path_single (Chg.accept x p hp))
    (fun e he => by rw [List.mem_singleton.1 he]; exact hacc) (owner_can rfl hm)

end QEDefi.Actor.Ownable2Step
