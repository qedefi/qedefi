import QEDefi.Actor.Lib.Sys

/-!
# Component: Safe (v1.5.0; 1.3.0 and 1.4.1 have the same authority)

`docs/access-control/safe-zodiac.md` §1. A Safe `sf` with owners, a threshold, modules and
approved hashes. Parameters: the Safe's address, the embedding `ι` of its messages into the host's
(`Msg A M H` carries host messages: the Safe relays them), and the digest `dig t m` of a Safe
transaction calling `t` with `m` (nonce and gas parameters abstracted: an over-approximation).

- `execTransaction(t, m, signatures)`: anyone, with `thr ≥ 1` (GS001) distinct current owners each
  approving the digest by a signature (the transaction's signers), a stored `approveHash`, or by
  being the sender (signature type 1 with `r = msg.sender`). The Safe then calls `t` with `m`.
- `execTransactionFromModule(t, m)`: any enabled module, no signature.
- `addOwnerWithThreshold`, `removeOwner`, `swapOwner`, `changeThreshold`, `enableModule`,
  `disableModule`: `authorized` (sender is the Safe itself), with the checks of
  `OwnerManager`/`ModuleManager` (GS201–GS205, GS101–GS103; the address type `A` has neither
  `address(0)` nor the sentinel). The threshold is checked only when it changes.
- `approveHash(h)`: owners only; approvals are never cleared.

Not covered: DelegateCall operations (they give the target the Safe's whole authority, including
its configuration), guards and module guards (vetoes only: ignoring them over-approximates),
EIP-1271 contract owners (a host adds them as relays), `setup`.

- `exec_sound`, `module_sound`, `run_sound`: per-call soundness in any host;
- `Closes`, `closed`, `Closes.outsider`: the component's part of a host's "who can";
- `no_call`: fewer than `thr` counted owners and no module make the Safe call nothing;
  `owners_can`: `thr` owners do.
-/

namespace QEDefi.Actor.Safe

open Classical

variable {C A M H : Type}

/-- The configuration fragment. -/
structure Cfg (A H : Type) where
  owners : Finset A
  thr : ℕ
  modules : Set A
  approved : A → H → Prop

/-- The configuration after owner `b` approves `h`. -/
def Cfg.approve (x : Cfg A H) (b : A) (h : H) : Cfg A H :=
  { x with approved := fun o h' => x.approved o h' ∨ (o = b ∧ h' = h) }

/-- The Safe's functions; transactions carry a host message `m` for the target `t`. -/
inductive Msg (A M H : Type) where
  | execTransaction (t : A) (m : M)
  | execFromModule (t : A) (m : M)
  | addOwnerWithThreshold (o : A) (k : ℕ)
  | removeOwner (o : A) (k : ℕ)
  | swapOwner (old new : A)
  | changeThreshold (k : ℕ)
  | enableModule (mod : A)
  | disableModule (mod : A)
  | approveHash (h : H)

/-- The `authorized` functions (sender must be the Safe). -/
def IsAdmin : Msg A M H → Prop
  | .addOwnerWithThreshold _ _ | .removeOwner _ _ | .swapOwner _ _ | .changeThreshold _
  | .enableModule _ | .disableModule _ => True
  | .execTransaction _ _ | .execFromModule _ _ | .approveHash _ => False

/-- **One call** from `b` to the Safe's configuration functions. Transactions (`none` here) relay
a host call and are run by the host, with `exec_sound` and `module_sound`. -/
noncomputable def run (sf : A) (x : Cfg A H) (b : A) : Msg A M H → Option (Cfg A H)
  | .addOwnerWithThreshold o k =>
    if b = sf ∧ o ≠ sf ∧ o ∉ x.owners ∧ (k = x.thr ∨ 1 ≤ k ∧ k ≤ x.owners.card + 1) then
      some { x with owners := insert o x.owners, thr := k } else none
  | .removeOwner o k =>
    if b = sf ∧ o ∈ x.owners ∧ k ≤ x.owners.card - 1 ∧ (k = x.thr ∨ 1 ≤ k) then
      some { x with owners := x.owners.erase o, thr := k } else none
  | .swapOwner old new =>
    if b = sf ∧ new ≠ sf ∧ new ∉ x.owners ∧ old ∈ x.owners then
      some { x with owners := insert new (x.owners.erase old) } else none
  | .changeThreshold k =>
    if b = sf ∧ 1 ≤ k ∧ k ≤ x.owners.card then some { x with thr := k } else none
  | .enableModule mod =>
    if b = sf ∧ mod ∉ x.modules then some { x with modules := insert mod x.modules } else none
  | .disableModule mod =>
    if b = sf ∧ mod ∈ x.modules then some { x with modules := x.modules \ {mod} } else none
  | .approveHash h => if b ∈ x.owners then some (x.approve b h) else none
  | .execTransaction _ _ | .execFromModule _ _ => none

/-- The signature check of `execTransaction` sent by `b` with signers `sigs`. -/
def Approves (dig : A → M → H) (sigs : Set A) (x : Cfg A H) (b t : A) (m : M) : Prop :=
  1 ≤ x.thr ∧ ∃ Y : Finset A, Y ⊆ x.owners ∧ x.thr ≤ Y.card ∧
    ∀ o ∈ Y, o ∈ sigs ∨ x.approved o (dig t m) ∨ o = b

/-- **The access checks as rules.** -/
inductive Base (sf : A) (ι : Msg A M H → M) (dig : A → M → H) :
    Cfg A H → A × Action A M H → Set (A × Action A M H) → Prop
  | quorum (x : Cfg A H) (t : A) (m : M) (Y : Finset A) (h1 : 1 ≤ x.thr) (hY : Y ⊆ x.owners)
      (hk : x.thr ≤ Y.card) :
      Base sf ι dig x (sf, .act (ι (.execTransaction t m)))
        ((fun o => (o, Action.sign (dig t m))) '' (Y : Set A))
  | signByCall (x : Cfg A H) (o t : A) (m : M) :
      Base sf ι dig x (o, .sign (dig t m)) {(o, .call sf (ι (.execTransaction t m)))}
  | approved (x : Cfg A H) (o : A) (h : H) (ha : x.approved o h) : Base sf ι dig x (o, .sign h) ∅
  | module (x : Cfg A H) (b t : A) (m : M) (hb : b ∈ x.modules) :
      Base sf ι dig x (sf, .act (ι (.execFromModule t m))) {(b, .call sf (ι (.execFromModule t m)))}
  | execRelay (x : Cfg A H) (t : A) (m : M) :
      Base sf ι dig x (sf, .call t m) {(sf, .act (ι (.execTransaction t m)))}
  | moduleRelay (x : Cfg A H) (t : A) (m : M) :
      Base sf ι dig x (sf, .call t m) {(sf, .act (ι (.execFromModule t m)))}
  | self (x : Cfg A H) (m : Msg A M H) (hm : IsAdmin m) :
      Base sf ι dig x (sf, .act (ι m)) {(sf, .call sf (ι m))}

/-- **The configuration changes**: exactly the successful configuration calls. Self-administration
is labelled by the Safe's act, an approval by the owner's call (its consent). -/
inductive Chg (sf : A) (ι : Msg A M H → M) : A × Action A M H → Cfg A H → Cfg A H → Prop
  | admin (x x' : Cfg A H) (m : Msg A M H) (hm : IsAdmin m) (hr : run sf x sf m = some x') :
      Chg sf ι (sf, .act (ι m)) x x'
  | approve (x x' : Cfg A H) (b : A) (h : H) (hr : run sf x b (.approveHash h : Msg A M H) = some x') :
      Chg sf ι (b, .call sf (ι (.approveHash h))) x x'

/-- The component. -/
def sys (sf : A) (ι : Msg A M H → M) (dig : A → M → H) : Sys (Cfg A H) A (Action A M H) :=
  ⟨Base sf ι dig, Chg sf ι⟩

theorem run_sender {sf : A} {x x' : Cfg A H} {b : A} {m : Msg A M H} (hm : IsAdmin m)
    (hr : run sf x b m = some x') : b = sf := by
  cases m <;> simp only [IsAdmin] at hm <;> simp only [run] at hr <;> split_ifs at hr with h <;>
    exact h.1

theorem run_approveHash {sf : A} {x x' : Cfg A H} {b : A} {h : H}
    (hr : run sf x b (.approveHash h : Msg A M H) = some x') : b ∈ x.owners ∧ x' = x.approve b h := by
  simp only [run] at hr; split_ifs at hr with hb; cases hr; exact ⟨hb, rfl⟩

variable {sf : A} {ι : Msg A M H → M} {dig : A → M → H} {S : Sys C A (Action A M H)}
  {L : Lens C (Cfg A H)}

/-! ## Per-call soundness, in any host -/

/-- **`execTransaction`**: an approved transaction makes the Safe call its target. -/
theorem exec_sound (hS : (sys sf ι dig).lift L ≤ S) {sigs K : Set A} (hK : sigs ⊆ K) {c : C}
    {b t : A} {m : M} (ha : Approves dig sigs (L.get c) b t m)
    (hd : Derives S.auth c K (b, .call sf (ι (.execTransaction t m)))) :
    Derives S.auth c K (sf, .call t m) := by
  obtain ⟨h1, Y, hY, hk, hsig⟩ := ha
  have hq : Derives S.auth c K (sf, .act (ι (.execTransaction t m))) :=
    hS.derive (S₁ := (sys sf ι dig).lift L) (Base.quorum (L.get c) t m Y h1 hY hk) (by
      rintro _ ⟨o, ho, rfl⟩
      rcases hsig o ho with hs | ha | rfl
      · exact .key _ (hK hs)
      · exact hS.derive (S₁ := (sys sf ι dig).lift L) (Base.approved _ o _ ha) (fun _ h => h.elim)
      · exact hS.derive_lift (K := sys sf ι dig) (Base.signByCall _ o t m) hd)
  exact hS.derive_lift (K := sys sf ι dig) (Base.execRelay _ t m) hq

/-- **`execTransactionFromModule`**: an enabled module makes the Safe call anything. -/
theorem module_sound (hS : (sys sf ι dig).lift L ≤ S) {K : Set A} {c : C} {b t : A} {m : M}
    (hb : b ∈ (L.get c).modules) (hd : Derives S.auth c K (b, .call sf (ι (.execFromModule t m)))) :
    Derives S.auth c K (sf, .call t m) :=
  hS.derive_lift (K := sys sf ι dig) (Base.moduleRelay _ t m)
    (hS.derive_lift (K := sys sf ι dig) (Base.module _ b t m hb) hd)

/-- **Every successful configuration call makes a derivable change.** -/
theorem run_sound (hS : (sys sf ι dig).lift L ≤ S) {c : C} {K : Set A} {b : A}
    {m : Msg A M H} {x' : Cfg A H} (hr : run sf (L.get c) b m = some x')
    (hd : Derives S.auth c K (b, .call sf (ι m))) :
    ∃ e, S.chg e c (L.set x' c) ∧ Derives S.auth c K e := by
  by_cases hm : IsAdmin m
  · have hb := run_sender hm hr
    rw [hb] at hr hd
    exact ⟨_, hS.chg_lift (K := sys sf ι dig) (Chg.admin _ _ m hm hr),
      hS.derive_lift (K := sys sf ι dig) (Base.self _ m hm) hd⟩
  · cases m with
    | approveHash h => exact ⟨_, hS.chg_lift (K := sys sf ι dig) (Chg.approve _ _ b h hr), hd⟩
    | execTransaction | execFromModule => simp [run] at hr
    | _ => exact absurd trivial hm

/-! ## Who can -/

/-- **The component's part of a host's closed set**, as first-order conditions. -/
structure Closes (sf : A) (ι : Msg A M H → M) (dig : A → M → H) (L : Lens C (Cfg A H))
    (D : A × Action A M H → Prop) (Inv : C → Prop) : Prop where
  quorum : ∀ c, Inv c → ∀ t m (Y : Finset A), 1 ≤ (L.get c).thr → Y ⊆ (L.get c).owners →
    (L.get c).thr ≤ Y.card → (∀ o ∈ Y, D (o, .sign (dig t m))) →
    D (sf, .act (ι (.execTransaction t m)))
  signByCall : ∀ o t m, D (o, .call sf (ι (.execTransaction t m))) → D (o, .sign (dig t m))
  approved : ∀ c, Inv c → ∀ o h, (L.get c).approved o h → D (o, .sign h)
  module : ∀ c, Inv c → ∀ b t m, b ∈ (L.get c).modules →
    D (b, .call sf (ι (.execFromModule t m))) → D (sf, .act (ι (.execFromModule t m)))
  execRelay : ∀ t m, D (sf, .act (ι (.execTransaction t m))) → D (sf, .call t m)
  moduleRelay : ∀ t m, D (sf, .act (ι (.execFromModule t m))) → D (sf, .call t m)
  self : ∀ m, IsAdmin m → D (sf, .call sf (ι m)) → D (sf, .act (ι m))
  admin : ∀ c m x', Inv c → IsAdmin m → run sf (L.get c) sf m = some x' → D (sf, .act (ι m)) →
    Inv (L.set x' c)
  approve : ∀ c b h x', Inv c → run sf (L.get c) b (.approveHash h : Msg A M H) = some x' →
    D (b, .call sf (ι (.approveHash h))) → Inv (L.set x' c)

theorem closed {D : A × Action A M H → Prop} {Inv : C → Prop} (h : Closes sf ι dig L D Inv) :
    Sys.Closed ((sys sf ι dig).lift L) D Inv := by
  refine Sys.Closed.lift (fun e c x' hc hD hI => ?_) (fun c hI q Y hb hY => ?_)
  · rcases hc with ⟨_, _, m, hm, hr⟩ | ⟨_, _, b, k, hr⟩
    · exact h.admin c m x' hI hm hr hD
    · exact h.approve c b k x' hI hr hD
  · cases hb with
    | quorum t m Y' h1 hY' hk => exact h.quorum c hI t m Y' h1 hY' hk (fun o ho => hY _ ⟨o, ho, rfl⟩)
    | signByCall o t m => exact h.signByCall o t m (hY _ rfl)
    | approved o k ha => exact h.approved c hI o k ha
    | module b t m hb => exact h.module c hI b t m hb (hY _ rfl)
    | execRelay t m => exact h.execRelay t m (hY _ rfl)
    | moduleRelay t m => exact h.moduleRelay t m (hY _ rfl)
    | self m hm => exact h.self m hm (hY _ rfl)

/-- The owners that could count towards the threshold for keys `T`: keys, or holders of an
approved hash. -/
noncomputable def counted (T : Set A) (x : Cfg A H) : Finset A :=
  x.owners.filter (fun o => o ∈ T ∨ ∃ h, x.approved o h)

/-- **Outsiders, in a host.** Let `Inv` freeze owners, threshold and modules at `x₀` and allow new
approvals only by keys `T`. If fewer than `thr` owners are counted, no module and not the Safe
is in `T`, the calls to the Safe in `D` come from `T`, the signatures in `D` are those of `T` and
of stored approvals, and `D` holds no act of the Safe, the component is closed. -/
theorem Closes.outsider {D : A × Action A M H → Prop} {Inv : C → Prop} {T : Set A}
    {x₀ : Cfg A H}
    (hInv : ∀ c, Inv c → (L.get c).owners = x₀.owners ∧ (L.get c).thr = x₀.thr ∧
      (L.get c).modules = x₀.modules ∧ ∀ o h, (L.get c).approved o h → x₀.approved o h ∨ o ∈ T)
    (hset : ∀ c x', Inv c → x'.owners = x₀.owners → x'.thr = x₀.thr → x'.modules = x₀.modules →
      (∀ o h, x'.approved o h → x₀.approved o h ∨ o ∈ T) → Inv (L.set x' c))
    (hcnt : (counted T x₀).card < x₀.thr) (hsfT : sf ∉ T) (hmod : ∀ b ∈ x₀.modules, b ∉ T)
    (hT : ∀ a ∈ T, ∀ p, D (a, p)) (happ : ∀ o h, x₀.approved o h → D (o, .sign h))
    (hsign : ∀ o h, D (o, .sign h) → o ∈ T ∨ x₀.approved o h)
    (hcall : ∀ b m, D (b, .call sf m) → b ∈ T) (hsfa : ∀ m, ¬ D (sf, .act m)) :
    Closes sf ι dig L D Inv := by
  refine ⟨fun c hI t m Y _ hY hk hall => ?_, fun o t m hD => hT o (hcall _ _ hD) _,
    fun c hI o h ha => ?_, fun c hI b t m hb hD => ?_, fun _ _ hD => (hsfa _ hD).elim,
    fun _ _ hD => (hsfa _ hD).elim, fun _ _ hD => absurd (hcall _ _ hD) hsfT,
    fun _ _ _ _ _ _ hD => (hsfa _ hD).elim, fun c b h x' hI hr hD => ?_⟩
  · obtain ⟨ho, ht, -, -⟩ := hInv c hI
    have hsub : Y ⊆ counted T x₀ := fun o hoY => Finset.mem_filter.2 ⟨ho ▸ hY hoY,
      (hsign o _ (hall o hoY)).imp id fun h => ⟨_, h⟩⟩
    have := Finset.card_le_card hsub
    omega
  · rcases (hInv c hI).2.2.2 o h ha with h' | h'
    · exact happ o h h'
    · exact hT o h' _
  · exact absurd (hcall _ _ hD) (hmod b ((hInv c hI).2.2.1 ▸ hb))
  · obtain ⟨-, rfl⟩ := run_approveHash hr
    obtain ⟨h1, h2, h3, h4⟩ := hInv c hI
    refine hset c _ hI h1 h2 h3 fun o h' ha => ?_
    rcases ha with ha | ⟨rfl, -⟩
    · exact h4 o h' ha
    · exact Or.inr (hcall _ _ hD)

/-- **Who can, standalone.** Keys `T` that include neither the Safe nor an enabled module, with
fewer than `thr` owners among them or holding an approved hash, never make the Safe call
anything, whatever they do: approve hashes, send transactions, sign. -/
theorem no_call {T : Set A} {x₀ : Cfg A H} (hsfT : sf ∉ T) (hmod : ∀ b ∈ x₀.modules, b ∉ T)
    (hcnt : (counted T x₀).card < x₀.thr) (t : A) (m : M) :
    ¬ Derives (sys sf ι dig).auth x₀ T (sf, .call t m) := by
  intro hd
  let D : A × Action A M H → Prop := fun q => q.1 ∈ T ∨ ∃ h, q.2 = .sign h ∧ x₀.approved q.1 h
  let Inv : Cfg A H → Prop := fun x => x.owners = x₀.owners ∧ x.thr = x₀.thr ∧
    x.modules = x₀.modules ∧ ∀ o h, x.approved o h → x₀.approved o h ∨ o ∈ T
  have hc : Closes sf ι dig (Lens.id _) D Inv := by
    refine Closes.outsider (T := T) (x₀ := x₀) (fun _ h => h)
      (fun _ _ _ h1 h2 h3 h4 => ⟨h1, h2, h3, h4⟩) hcnt hsfT hmod (fun a ha _ => Or.inl ha)
      (fun o h ha => Or.inr ⟨h, rfl, ha⟩) ?_ ?_ ?_
    · rintro o h (h' | ⟨_, he, ha⟩)
      · exact Or.inl h'
      · cases he; exact Or.inr ha
    · rintro b m (h' | ⟨_, he, -⟩)
      · exact h'
      · cases he
    · rintro m (h' | ⟨_, he, -⟩)
      · exact hsfT h'
      · cases he
  rcases Sys.le_of_closed (closed hc) (fun a ha _ => Or.inl ha)
    ⟨rfl, rfl, rfl, fun o h ha => Or.inl ha⟩ ((Sys.le_lift_id _).derives hd) with h | ⟨_, he, -⟩
  · exact hsfT h
  · cases he

/-- **Not vacuous**: `thr` owners make the Safe call anything (one of them sends, all sign). -/
theorem owners_can {x : Cfg A H} {Y : Finset A} (h1 : 1 ≤ x.thr) (hY : Y ⊆ x.owners)
    (hk : x.thr ≤ Y.card) (t : A) (m : M) :
    Derives (sys sf ι dig).auth x (Y : Set A) (sf, .call t m) :=
  (Sys.le_refl _).derive₁ (S₁ := sys sf ι dig) (Base.execRelay x t m)
    ((Sys.le_refl _).derive (S₁ := sys sf ι dig) (Base.quorum x t m Y h1 hY hk)
      (by rintro _ ⟨o, ho, rfl⟩; exact .key _ ho))

end QEDefi.Actor.Safe
