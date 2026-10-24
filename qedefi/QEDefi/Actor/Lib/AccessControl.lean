import QEDefi.Actor.Lib.Sys

/-!
# Component: OpenZeppelin `AccessControl` (v5.7.0)

`access/AccessControl.sol`. Roles `R` held by addresses (`has r a`), each with an
admin role (`adminOf r`; `DEFAULT_ADMIN_ROLE` administers itself by default, which is just a
value of `adminOf`):

- `onlyRole(r)` functions of the host (`role m = some r`) act when called by a holder of `r`;
- `grantRole(r, a)` / `revokeRole(r, a)`: holders of `adminOf r` only;
- `renounceRole(r, c)`: requires `c == msg.sender` (`AccessControlBadConfirmation`), revokes the
  caller's own role. Its change is labelled by the caller's call, as consent of the holder.

`adminOf` has no public setter (`_setRoleAdmin` is internal): the component never changes it.
`AccessControlEnumerable` has the same authority (enumeration only reports).

- `run_sound`, `act_of_role`: per-call soundness in any host;
- `Closes`, `closed`, `Closes.outsider`: the component's part of a host's "who can";
- `no_act`: **the admin chain**: keys holding no role of a set `Adm` closed under `adminOf` never
  exercise a role of `Adm` nor grant one; `admin_can`: the admin of a role holds it (escalation
  derived by `close`).
-/

namespace QEDefi.Actor.AccessControl

open Classical

variable {C R A M H : Type}

/-- The configuration fragment: the role table and the admin of each role. -/
structure Cfg (R A : Type) where
  has : R → A → Prop
  adminOf : R → R

/-- Set whether `a` holds `r` to `v`. -/
noncomputable def Cfg.setRole (x : Cfg R A) (r : R) (a : A) (v : Prop) : Cfg R A :=
  { x with has := fun r' a' => if r' = r ∧ a' = a then v else x.has r' a' }

@[simp] theorem Cfg.setRole_adminOf (x : Cfg R A) (r : R) (a : A) (v : Prop) :
    (x.setRole r a v).adminOf = x.adminOf := rfl

theorem Cfg.has_setRole_false {x : Cfg R A} {r r' : R} {a a' : A}
    (h : (x.setRole r a False).has r' a') : x.has r' a' := by
  simp only [Cfg.setRole] at h; split_ifs at h; exact h

theorem Cfg.has_setRole_true {x : Cfg R A} {r r' : R} {a a' : A}
    (h : (x.setRole r a True).has r' a') : x.has r' a' ∨ (r' = r ∧ a' = a) := by
  simp only [Cfg.setRole] at h; split_ifs at h with hx
  · exact Or.inr hx
  · exact Or.inl h

theorem Cfg.has_setRole_self (x : Cfg R A) (r : R) (a : A) : (x.setRole r a True).has r a := by
  simp [Cfg.setRole]

/-- The component's own functions. -/
inductive Msg (R A : Type) where
  | grantRole (r : R) (a : A)
  | revokeRole (r : R) (a : A)
  /-- `renounceRole(r, callerConfirmation)`. -/
  | renounceRole (r : R) (c : A)

/-- **One call** from `b`. -/
noncomputable def run (x : Cfg R A) (b : A) : Msg R A → Option (Cfg R A)
  | .grantRole r a => if x.has (x.adminOf r) b then some (x.setRole r a True) else none
  | .revokeRole r a => if x.has (x.adminOf r) b then some (x.setRole r a False) else none
  | .renounceRole r c => if c = b then some (x.setRole r b False) else none

/-- **The access checks as rules.** `role m = some r`: the host function `m` is `onlyRole(r)`. -/
inductive Base (t : A) (ι : Msg R A → M) (role : M → Option R) :
    Cfg R A → A × Action A M H → Set (A × Action A M H) → Prop
  | guard (x : Cfg R A) (b : A) (m : M) (r : R) (hr : role m = some r) (hb : x.has r b) :
      Base t ι role x (t, .act m) {(b, .call t m)}
  | grant (x : Cfg R A) (b : A) (r : R) (a : A) (hb : x.has (x.adminOf r) b) :
      Base t ι role x (t, .act (ι (.grantRole r a))) {(b, .call t (ι (.grantRole r a)))}
  | revoke (x : Cfg R A) (b : A) (r : R) (a : A) (hb : x.has (x.adminOf r) b) :
      Base t ι role x (t, .act (ι (.revokeRole r a))) {(b, .call t (ι (.revokeRole r a)))}

/-- **The configuration changes.** -/
inductive Chg (t : A) (ι : Msg R A → M) : A × Action A M H → Cfg R A → Cfg R A → Prop
  | grant (x : Cfg R A) (r : R) (a : A) :
      Chg t ι (t, .act (ι (.grantRole r a))) x (x.setRole r a True)
  | revoke (x : Cfg R A) (r : R) (a : A) :
      Chg t ι (t, .act (ι (.revokeRole r a))) x (x.setRole r a False)
  | renounce (x : Cfg R A) (b : A) (r : R) :
      Chg t ι (b, .call t (ι (.renounceRole r b))) x (x.setRole r b False)

/-- The component. -/
def sys (t : A) (ι : Msg R A → M) (role : M → Option R) : Sys (Cfg R A) A (Action A M H) :=
  ⟨Base t ι role, Chg t ι⟩

variable {t : A} {ι : Msg R A → M} {role : M → Option R} {S : Sys C A (Action A M H)}
  {L : Lens C (Cfg R A)}

/-! ## Per-call soundness, in any host -/

/-- **`onlyRole(r)`**: a call by a holder of `r` acts. -/
theorem act_of_role (hS : (sys t ι role).lift L ≤ S) {c : C} {K : Set A} {b : A} {m : M} {r : R}
    (hr : role m = some r) (hb : (L.get c).has r b) (hd : Derives S.auth c K (b, .call t m)) :
    Derives S.auth c K (t, .act m) :=
  hS.derive_lift (K := sys t ι role) (Base.guard _ b m r hr hb) hd

/-- **Every successful call of the component's functions makes a derivable change.** -/
theorem run_sound (hS : (sys t ι role).lift L ≤ S) {c : C} {K : Set A} {b : A}
    {m : Msg R A} {x' : Cfg R A} (hr : run (L.get c) b m = some x')
    (hd : Derives S.auth c K (b, .call t (ι m))) :
    ∃ e, S.chg e c (L.set x' c) ∧ Derives S.auth c K e := by
  cases m with
  | grantRole r a =>
    simp only [run] at hr; split_ifs at hr with hb; cases hr
    exact ⟨_, hS.chg_lift (K := sys t ι role) (Chg.grant _ r a),
      hS.derive_lift (K := sys t ι role) (Base.grant _ b r a hb) hd⟩
  | revokeRole r a =>
    simp only [run] at hr; split_ifs at hr with hb; cases hr
    exact ⟨_, hS.chg_lift (K := sys t ι role) (Chg.revoke _ r a),
      hS.derive_lift (K := sys t ι role) (Base.revoke _ b r a hb) hd⟩
  | renounceRole r c' =>
    simp only [run] at hr; split_ifs at hr with hc; cases hr; subst hc
    exact ⟨_, hS.chg_lift (K := sys t ι role) (Chg.renounce _ c' r), hd⟩

/-! ## Who can -/

/-- **The component's part of a host's closed set**, as first-order conditions. -/
structure Closes (t : A) (ι : Msg R A → M) (role : M → Option R) (L : Lens C (Cfg R A))
    (D : A × Action A M H → Prop) (Inv : C → Prop) : Prop where
  guard : ∀ c, Inv c → ∀ b m r, role m = some r → (L.get c).has r b → D (b, .call t m) →
    D (t, .act m)
  grant : ∀ c, Inv c → ∀ b r a, (L.get c).has ((L.get c).adminOf r) b →
    D (b, .call t (ι (.grantRole r a))) → D (t, .act (ι (.grantRole r a)))
  revoke : ∀ c, Inv c → ∀ b r a, (L.get c).has ((L.get c).adminOf r) b →
    D (b, .call t (ι (.revokeRole r a))) → D (t, .act (ι (.revokeRole r a)))
  grantChg : ∀ c r a, Inv c → D (t, .act (ι (.grantRole r a))) →
    Inv (L.set ((L.get c).setRole r a True) c)
  revokeChg : ∀ c r a, Inv c → D (t, .act (ι (.revokeRole r a))) →
    Inv (L.set ((L.get c).setRole r a False) c)
  renounceChg : ∀ c b r, Inv c → D (b, .call t (ι (.renounceRole r b))) →
    Inv (L.set ((L.get c).setRole r b False) c)

theorem closed {D : A × Action A M H → Prop} {Inv : C → Prop} (h : Closes t ι role L D Inv) :
    Sys.Closed ((sys t ι role).lift L) D Inv := by
  refine Sys.Closed.lift (fun e c x' hc hD hI => ?_) (fun c hI q Y hb hY => ?_)
  · cases hc with
    | grant _ r a => exact h.grantChg c r a hI hD
    | revoke _ r a => exact h.revokeChg c r a hI hD
    | renounce _ b r => exact h.renounceChg c b r hI hD
  · cases hb with
    | guard b m r hr hb => exact h.guard c hI b m r hr hb (hY _ rfl)
    | grant b r a hb => exact h.grant c hI b r a hb (hY _ rfl)
    | revoke b r a hb => exact h.revoke c hI b r a hb (hY _ rfl)

/-- **The admin chain, in a host.** Let `Inv` keep the admin map of `x₀` and allow no new holders
of the roles in `Adm`. If the calls to `t` in `D` come
from keys `T` holding no `Adm` role, `D` contains the acts of non-`Adm` roles and the grants and
revocations whose admin role is not in `Adm`, and grants in `D` are of non-`Adm` roles, the
component is closed. -/
theorem Closes.outsider {D : A × Action A M H → Prop} {Inv : C → Prop} {T : Set A}
    {x₀ : Cfg R A} {Adm : Set R}
    (hInv : ∀ c, Inv c → (L.get c).adminOf = x₀.adminOf ∧
      ∀ r ∈ Adm, ∀ a, (L.get c).has r a → x₀.has r a)
    (hset : ∀ c x', Inv c → x'.adminOf = x₀.adminOf → (∀ r ∈ Adm, ∀ a, x'.has r a → x₀.has r a) →
      Inv (L.set x' c))
    (hrole : ∀ r ∈ Adm, ∀ a, x₀.has r a → a ∉ T)
    (hcall : ∀ b m, D (b, .call t m) → b ∈ T)
    (hguard : ∀ m r, role m = some r → r ∉ Adm → D (t, .act m))
    (hgrant : ∀ r a, x₀.adminOf r ∉ Adm →
      D (t, .act (ι (.grantRole r a))) ∧ D (t, .act (ι (.revokeRole r a))))
    (hgrantD : ∀ r a, D (t, .act (ι (.grantRole r a))) → r ∉ Adm) :
    Closes t ι role L D Inv := by
  -- A key holding a role at a reachable configuration: the role is not in `Adm`.
  have hout : ∀ c, Inv c → ∀ r b, (L.get c).has r b → b ∈ T → r ∉ Adm :=
    fun c hI r b hb hbT hr => hrole r hr b ((hInv c hI).2 r hr b hb) hbT
  -- Removing a holder keeps `Inv`.
  have hfalse : ∀ c r a, Inv c → Inv (L.set ((L.get c).setRole r a False) c) := fun c r a hI =>
    hset c _ hI (hInv c hI).1 fun r' hr' a' h => (hInv c hI).2 r' hr' a' (Cfg.has_setRole_false h)
  refine ⟨fun c hI b m r hr hb hD => hguard m r hr (hout c hI r b hb (hcall b m hD)),
    fun c hI b r a hb hD => (hgrant r a ((hInv c hI).1 ▸ hout c hI _ b hb (hcall _ _ hD))).1,
    fun c hI b r a hb hD => (hgrant r a ((hInv c hI).1 ▸ hout c hI _ b hb (hcall _ _ hD))).2,
    fun c r a hI hD => ?_, fun c r a hI _ => hfalse c r a hI, fun c b r hI _ => hfalse c r b hI⟩
  refine hset c _ hI (hInv c hI).1 fun r' hr' a' h => ?_
  rcases Cfg.has_setRole_true h with h | ⟨rfl, -⟩
  · exact (hInv c hI).2 r' hr' a' h
  · exact absurd hr' (hgrantD r' a hD)

/-- `m` needs role `r`: it is `onlyRole(r)`, or it grants or revokes a role administered by `r`. -/
def Needs (ι : Msg R A → M) (role : M → Option R) (adm : R → R) (m : M) (r : R) : Prop :=
  role m = some r ∨ ∃ r' a, (m = ι (.grantRole r' a) ∨ m = ι (.revokeRole r' a)) ∧ adm r' = r

/-- **Who can, standalone: the admin chain.** Let `Adm` be a set of roles closed under `adminOf`
(e.g. a role and its admins up to `DEFAULT_ADMIN_ROLE`). Keys `T` that include neither the
contract nor a holder of a role in `Adm` never perform a message that needs a role of `Adm`
(nor grant one), whatever they do: grant and revoke other roles, renounce, call anything. -/
theorem no_act {T : Set A} {x₀ : Cfg R A} {Adm : Set R} (hAdm : ∀ r ∈ Adm, x₀.adminOf r ∈ Adm)
    (ht : t ∉ T) (hrole : ∀ r ∈ Adm, ∀ a, x₀.has r a → a ∉ T) (hι : Function.Injective ι)
    (hιr : ∀ m₀, role (ι m₀) = none) {m : M} {r : R} (hr : r ∈ Adm)
    (hm : Needs ι role x₀.adminOf m r) :
    ¬ Derives (sys (H := H) t ι role).auth x₀ T (t, .act m) := by
  intro hd
  let D : A × Action A M H → Prop := fun q =>
    q.1 ∈ T ∨ (q.1 = t ∧ ∃ m, q.2 = .act m ∧ ∀ r ∈ Adm, ¬ Needs ι role x₀.adminOf m r)
  let Inv : Cfg R A → Prop := fun x =>
    x.adminOf = x₀.adminOf ∧ ∀ r ∈ Adm, ∀ a, x.has r a → x₀.has r a
  have hc : Closes t ι role (Lens.id _) D Inv := by
    refine Closes.outsider (T := T) (x₀ := x₀) (fun _ h => h) (fun _ x' _ h₁ h₂ => ⟨h₁, h₂⟩)
      hrole ?_ ?_ ?_ ?_
    · rintro b m (h | ⟨-, _, h, -⟩)
      · exact h
      · cases h
    · intro m r hr hrA
      refine Or.inr ⟨rfl, m, rfl, fun r' hr' hn => ?_⟩
      rcases hn with hn | ⟨_, _, hm', -⟩
      · rw [hr] at hn; cases hn; exact hrA hr'
      · rcases hm' with rfl | rfl <;> simp [hιr] at hr
    · intro r a hra
      refine ⟨Or.inr ⟨rfl, _, rfl, fun r' hr' hn => ?_⟩, Or.inr ⟨rfl, _, rfl, fun r' hr' hn => ?_⟩⟩
      · rcases hn with hn | ⟨r'', a', hm', rfl⟩
        · rw [hιr] at hn; cases hn
        · rcases hm' with hm' | hm' <;> have := hι hm' <;> cases this
          exact hra hr'
      · rcases hn with hn | ⟨r'', a', hm', rfl⟩
        · rw [hιr] at hn; cases hn
        · rcases hm' with hm' | hm' <;> have := hι hm' <;> cases this
          exact hra hr'
    · rintro r a (h | ⟨-, _, h, hn⟩) hrA
      · exact ht h
      · cases h
        exact hn _ (hAdm r hrA) (Or.inr ⟨r, a, Or.inl rfl, rfl⟩)
  rcases Sys.le_of_closed (closed hc) (fun a ha _ => Or.inl ha) ⟨rfl, fun _ _ _ h => h⟩
    ((Sys.le_lift_id _).derives hd) with h | ⟨-, _, h, hn⟩
  · exact ht h
  · cases h; exact hn r hr hm

/-- **Not vacuous: the admin of a role holds it**, by granting it to itself first. -/
theorem admin_can {x : Cfg R A} {b : A} {r : R} (hb : x.has (x.adminOf r) b) {m : M}
    (hr : role m = some r) : Derives (sys (H := H) t ι role).auth x {b} (t, .act m) := by
  have hg : Derives (sys (H := H) t ι role).auth x {b} (t, .act (ι (.grantRole r b))) :=
    (Sys.le_refl _).derive₁ (S₁ := sys t ι role) (Base.grant x b r b hb) (.key _ rfl)
  exact Sys.derives_of_path (path_single (Chg.grant x r b))
    (fun e he => by rw [List.mem_singleton.1 he]; exact hg)
    ((Sys.le_refl _).derive₁ (S₁ := sys t ι role)
      (Base.guard _ b m r hr (Cfg.has_setRole_self x r b)) (.key _ rfl))

end QEDefi.Actor.AccessControl
