import QEDefi.Actor.Action
import QEDefi.Actor.Config

/-!
# Worked example: roles from a replaceable role manager, two-step ownership

The pattern of `AccessControlled` contracts (seen in deployed systems): the target `tgt` checks
`onlyRole(r)` by asking its role manager `acm.hasRole(r, msg.sender)`, an OpenZeppelin
`AccessControl` contract; the target's `Ownable2Step` owner may replace `acm`. Every address is
a potential manager (anyone can deploy an `AccessControl` in which they are admin), so the
configuration has a role table for every manager address.

- `stable`, `guards`: the two obligations for "the paused flag only changes by a derivable
  `setPaused`";
- `no_pause`: keys `T` that are neither owner nor pending owner, and hold no role on the
  admin chain of `PAUSER` at the current manager, cannot change the flag, whatever they do
  (grant and revoke in other managers, renounce, call anything);
- `owner_can_pause`: the owner **does** control `PAUSER`, through `setAcm` to a manager in
  which it administers `PAUSER`: the escalation is derived by `close`, not written by hand.

Role holders are treated as acting principals (no relays in this model; a holder that is a
contract adds its own rules, as in `SafeProxyAdmin`).
-/

namespace Examples.Actor.RoleOracle

open QEDefi.Actor QEDefi.Trace.Lift
open Classical

variable {A R : Type}

/-- The functions: the target's, and those of an `AccessControl` manager. -/
inductive Msg (A R : Type) where
  /-- `tgt.setPaused(b)`: `onlyRole(PAUSER)`, asking `acm`. -/
  | setPaused (b : Bool)
  /-- `tgt.setAcm(m)`: owner only. -/
  | setAcm (m : A)
  /-- `tgt.transferOwnership(o)`: owner only, sets the pending owner. -/
  | transferOwnership (o : A)
  /-- `tgt.acceptOwnership()`: pending owner only. -/
  | acceptOwnership
  /-- `tgt.renounceOwnership()`: owner only (clears the pending owner too). -/
  | renounceOwnership
  /-- `m.grantRole(r, a)`: holders of `r`'s admin role at `m`. -/
  | grantRole (r : R) (a : A)
  /-- `m.revokeRole(r, a)`: holders of `r`'s admin role at `m`. -/
  | revokeRole (r : R) (a : A)
  /-- `m.renounceRole(r, msg.sender)`. -/
  | renounceRole (r : R)

abbrev Act (A R : Type) := Action A (Msg A R) Unit

/-- The configuration: target ownership, the manager pointer, every manager's role table. -/
structure Cfg (A R : Type) where
  owner : Option A
  pending : Option A
  acm : A
  has : A → R → A → Prop
  adminOf : A → R → R

structure St (A R : Type) where
  cfg : Cfg A R
  paused : Bool

/-- The target and its pauser role. -/
structure Params (A R : Type) where
  tgt : A
  pauser : R

variable (D : Params A R)

/-- Grant (`true`) or revoke (`false`) role `r` of `a` at manager `m`. -/
def Cfg.setRole (c : Cfg A R) (m : A) (r : R) (a : A) (v : Prop) : Cfg A R :=
  { c with has := fun m' r' a' => if m' = m ∧ r' = r ∧ a' = a then v else c.has m' r' a' }

/-- **One call** `m` from `b` to `t`. -/
noncomputable def run (s : St A R) (b t : A) : Msg A R → Option (St A R)
  | .setPaused v => if t = D.tgt ∧ s.cfg.has s.cfg.acm D.pauser b then some { s with paused := v }
    else none
  | .setAcm m => if t = D.tgt ∧ s.cfg.owner = some b then
      some { s with cfg := { s.cfg with acm := m } } else none
  | .transferOwnership o => if t = D.tgt ∧ s.cfg.owner = some b then
      some { s with cfg := { s.cfg with pending := some o } } else none
  | .acceptOwnership => if t = D.tgt ∧ s.cfg.pending = some b then
      some { s with cfg := { s.cfg with owner := some b, pending := none } } else none
  | .renounceOwnership => if t = D.tgt ∧ s.cfg.owner = some b then
      some { s with cfg := { s.cfg with owner := none, pending := none } } else none
  | .grantRole r a => if t ≠ D.tgt ∧ s.cfg.has t (s.cfg.adminOf t r) b then
      some { s with cfg := s.cfg.setRole t r a True } else none
  | .revokeRole r a => if t ≠ D.tgt ∧ s.cfg.has t (s.cfg.adminOf t r) b then
      some { s with cfg := s.cfg.setRole t r a False } else none
  | .renounceRole r => if t ≠ D.tgt then some { s with cfg := s.cfg.setRole t r b False } else none

structure Tx (A R : Type) where
  sender : A
  target : A
  msg : Msg A R

noncomputable def step (s : St A R) (tx : Tx A R) : Option (St A R) :=
  run D s tx.sender tx.target tx.msg

def consent (tx : Tx A R) : Set A := {tx.sender}

/-! ## Authority -/

/-- **The access checks as rules.** -/
inductive Base : Cfg A R → A × Act A R → Set (A × Act A R) → Prop
  | pause (c : Cfg A R) (a : A) (v : Bool) (ha : c.has c.acm D.pauser a) :
      Base c (D.tgt, .act (.setPaused v)) {(a, .call D.tgt (.setPaused v))}
  | setAcm (c : Cfg A R) (o m : A) (ho : c.owner = some o) :
      Base c (D.tgt, .act (.setAcm m)) {(o, .call D.tgt (.setAcm m))}
  | transfer (c : Cfg A R) (o o' : A) (ho : c.owner = some o) :
      Base c (D.tgt, .act (.transferOwnership o')) {(o, .call D.tgt (.transferOwnership o'))}
  | accept (c : Cfg A R) (p : A) (hp : c.pending = some p) :
      Base c (D.tgt, .act .acceptOwnership) {(p, .call D.tgt .acceptOwnership)}
  | renounce (c : Cfg A R) (o : A) (ho : c.owner = some o) :
      Base c (D.tgt, .act .renounceOwnership) {(o, .call D.tgt .renounceOwnership)}
  | grant (c : Cfg A R) (m b : A) (r : R) (a : A) (hm : m ≠ D.tgt)
      (hb : c.has m (c.adminOf m r) b) :
      Base c (m, .act (.grantRole r a)) {(b, .call m (.grantRole r a))}
  | revoke (c : Cfg A R) (m b : A) (r : R) (a : A) (hm : m ≠ D.tgt)
      (hb : c.has m (c.adminOf m r) b) :
      Base c (m, .act (.revokeRole r a)) {(b, .call m (.revokeRole r a))}

/-- **The configuration changes.** The new owner on acceptance is the pending owner, who is
the caller: acceptance is a change by the pending owner's call. -/
inductive Chg : A × Act A R → Cfg A R → Cfg A R → Prop
  | setAcm (c : Cfg A R) (m : A) : Chg (D.tgt, .act (.setAcm m)) c { c with acm := m }
  | transfer (c : Cfg A R) (o : A) :
      Chg (D.tgt, .act (.transferOwnership o)) c { c with pending := some o }
  | accept (c : Cfg A R) (p : A) (hp : c.pending = some p) :
      Chg (D.tgt, .act .acceptOwnership) c { c with owner := some p, pending := none }
  | renounce (c : Cfg A R) :
      Chg (D.tgt, .act .renounceOwnership) c { c with owner := none, pending := none }
  | grant (c : Cfg A R) (m : A) (r : R) (a : A) :
      Chg (m, .act (.grantRole r a)) c (c.setRole m r a True)
  | revoke (c : Cfg A R) (m : A) (r : R) (a : A) :
      Chg (m, .act (.revokeRole r a)) c (c.setRole m r a False)
  | renounceRole (c : Cfg A R) (m b : A) (r : R) :
      Chg (b, .call m (.renounceRole r)) c (c.setRole m r b False)

abbrev Auth : Rules (Cfg A R) A (Act A R) := fun c => close (Chg D) (Base D) c

abbrev Rl : Rules (St A R) A (Act A R) := fun s => close (Chg D) (Base D) s.cfg

/-! ## Soundness of the model's authority -/

/-- One premise. -/
theorem single_prem {c : Cfg A R} {K : Set A} {r : A × Act A R}
    (h : Derives (Auth D) c K r) : ∀ r' ∈ ({r} : Set (A × Act A R)), Derives (Auth D) c K r' :=
  fun _ hr => by rw [Set.mem_singleton_iff.1 hr]; exact h

/-- **Every successful call is authorised**: it changes the flag by a derivable `setPaused`
and keeps the configuration, or keeps the flag and makes a derivable configuration change. -/
theorem run_sound {K : Set A} (s s' : St A R) (b t : A) (m : Msg A R)
    (hr : run D s b t m = some s') (hd : Derives (Auth D) s.cfg K (b, .call t m)) :
    (s'.cfg = s.cfg ∧ (s'.paused = s.paused ∨
      Derives (Auth D) s.cfg K (D.tgt, .act (.setPaused s'.paused)))) ∨
    (s'.paused = s.paused ∧ ∃ e, Chg D e s.cfg s'.cfg ∧ Derives (Auth D) s.cfg K e) := by
  cases m with
  | setPaused v =>
    simp only [run] at hr; split_ifs at hr with h; obtain ⟨rfl, ha⟩ := h; cases hr
    exact Or.inl ⟨rfl, Or.inr (Derives.base (Base.pause s.cfg b v ha) (single_prem D hd))⟩
  | setAcm m =>
    simp only [run] at hr; split_ifs at hr with h; obtain ⟨rfl, ho⟩ := h; cases hr
    exact Or.inr ⟨rfl, _, Chg.setAcm s.cfg m,
      Derives.base (Base.setAcm s.cfg b m ho) (single_prem D hd)⟩
  | transferOwnership o =>
    simp only [run] at hr; split_ifs at hr with h; obtain ⟨rfl, ho⟩ := h; cases hr
    exact Or.inr ⟨rfl, _, Chg.transfer s.cfg o,
      Derives.base (Base.transfer s.cfg b o ho) (single_prem D hd)⟩
  | acceptOwnership =>
    simp only [run] at hr; split_ifs at hr with h; obtain ⟨rfl, hp⟩ := h; cases hr
    exact Or.inr ⟨rfl, _, Chg.accept s.cfg b hp,
      Derives.base (Base.accept s.cfg b hp) (single_prem D hd)⟩
  | renounceOwnership =>
    simp only [run] at hr; split_ifs at hr with h; obtain ⟨rfl, ho⟩ := h; cases hr
    exact Or.inr ⟨rfl, _, Chg.renounce s.cfg,
      Derives.base (Base.renounce s.cfg b ho) (single_prem D hd)⟩
  | grantRole r a =>
    simp only [run] at hr; split_ifs at hr with h; obtain ⟨hm, hb⟩ := h; cases hr
    exact Or.inr ⟨rfl, _, Chg.grant s.cfg t r a,
      Derives.base (Base.grant s.cfg t b r a hm hb) (single_prem D hd)⟩
  | revokeRole r a =>
    simp only [run] at hr; split_ifs at hr with h; obtain ⟨hm, hb⟩ := h; cases hr
    exact Or.inr ⟨rfl, _, Chg.revoke s.cfg t r a,
      Derives.base (Base.revoke s.cfg t b r a hm hb) (single_prem D hd)⟩
  | renounceRole r =>
    simp only [run] at hr; split_ifs at hr with h; cases hr
    exact Or.inr ⟨rfl, _, Chg.renounceRole s.cfg t b r, hd⟩

/-- **Obligation 1: stability.** -/
theorem stable : Stable (step D) consent (Rl D) := by
  refine stable_of_cfg (chg := Chg D) (R := Base D) (cfg := St.cfg) ?_
  intro s tx s' hr
  rcases run_sound D (K := consent tx) s s' tx.sender tx.target tx.msg hr
    (.key _ (Set.mem_singleton _)) with ⟨hc, -⟩ | ⟨-, e, he, hd⟩
  · exact ⟨[], path_of_eq hc, fun _ h => (List.not_mem_nil h).elim⟩
  · exact ⟨[e], path_single he, fun e' h => by rw [List.mem_singleton.1 h]; exact hd⟩

/-- The protected capabilities: setting the flag to either value. -/
def Pauses (q : A × Act A R) : Prop := ∃ v, q = (D.tgt, .act (.setPaused v))

/-- **Obligation 2: the flag changes only by a derivable `setPaused`.** -/
theorem guards : Guards (step D) consent (Rl D) (Pauses D) (Same St.paused) := by
  refine Guards.same (fun s tx s' hr hq => ?_)
  rcases run_sound D (K := consent tx) s s' tx.sender tx.target tx.msg hr
    (.key _ (Set.mem_singleton _)) with ⟨-, hi | hd⟩ | ⟨hi, -⟩
  · exact hi
  · exact absurd (Derives.mono_rules (R := Auth D) (s := s.cfg) (R' := Rl D) (s' := s)
      (fun _ _ h => h) hd) (hq _ ⟨s'.paused, rfl⟩)
  · exact hi

/-! ## Who controls `PAUSER` -/

/-- **Outsiders cannot pause.** Let `Adm` be a set of roles containing `PAUSER` and closed under
the current manager's `adminOf` (the admin chain). Keys `T` that include neither the target,
the manager, the owner nor the pending owner, and hold no role of `Adm` at the manager, derive
no `setPaused`. -/
theorem no_pause {T : Set A} {s₀ : St A R} {Adm : Set R} (hp : D.pauser ∈ Adm)
    (hAdm : ∀ r ∈ Adm, s₀.cfg.adminOf s₀.cfg.acm r ∈ Adm)
    (htgt : D.tgt ∉ T) (hacm : s₀.cfg.acm ∉ T)
    (hown : ∀ o, s₀.cfg.owner = some o → o ∉ T) (hpen : ∀ o, s₀.cfg.pending = some o → o ∉ T)
    (hrole : ∀ r ∈ Adm, ∀ a, s₀.cfg.has s₀.cfg.acm r a → a ∉ T) :
    ∀ q, Pauses D q → ¬ Derives (Rl D) s₀ T q := by
  rintro _ ⟨v, rfl⟩ hd
  -- `acm₀` and the admin chain at it.
  let m₀ := s₀.cfg.acm
  -- The capabilities `T` can have: its own, and grants/revokes at managers for roles whose
  -- admin is not on the chain at `m₀`.
  let C : A × Act A R → Prop := fun q =>
    q.1 ∈ T ∨ (q.1 ≠ D.tgt ∧ ∃ r a, (q.2 = .act (.grantRole r a) ∨ q.2 = .act (.revokeRole r a)) ∧
      (q.1 = m₀ → s₀.cfg.adminOf m₀ r ∉ Adm))
  let Inv : Cfg A R → Prop := fun c =>
    c.owner = s₀.cfg.owner ∧ c.pending = s₀.cfg.pending ∧ c.acm = m₀ ∧ c.adminOf = s₀.cfg.adminOf ∧
      ∀ r ∈ Adm, ∀ a, c.has m₀ r a → s₀.cfg.has m₀ r a
  have hd' : Derives (Auth D) s₀.cfg T (D.tgt, .act (.setPaused v)) :=
    Derives.mono_rules (R := Rl D) (s := s₀) (fun _ _ h => h) hd
  have hC : C (D.tgt, .act (.setPaused v)) := by
    refine close_le_of_closed (D := C) (Inv := Inv) (fun a ha p => Or.inl ha)
      ⟨rfl, rfl, rfl, rfl, fun r _ a ha => ha⟩ ?_ ?_ hd'
    · intro e c c' hc he ⟨h1, h2, h3, h4, h5⟩
      cases hc with
      | setAcm => rcases he with he | ⟨he, -⟩
                  · exact absurd he htgt
                  · exact absurd rfl he
      | transfer => rcases he with he | ⟨he, -⟩
                    · exact absurd he htgt
                    · exact absurd rfl he
      | accept => rcases he with he | ⟨he, -⟩
                  · exact absurd he htgt
                  · exact absurd rfl he
      | renounce => rcases he with he | ⟨he, -⟩
                    · exact absurd he htgt
                    · exact absurd rfl he
      | grant c m r a =>
        refine ⟨h1, h2, h3, h4, fun r' hr' a' ha' => ?_⟩
        simp only [Cfg.setRole] at ha'
        split_ifs at ha' with hx
        · obtain ⟨rfl, rfl, rfl⟩ := hx
          -- A grant at `m₀` of a role on the chain: its admin is on the chain.
          rcases he with he | ⟨-, r₁, a₁, hra, hm⟩
          · exact absurd he hacm
          · rcases hra with hra | hra <;> cases hra
            exact absurd (hAdm r' hr') (hm rfl)
        · exact h5 r' hr' a' ha'
      | revoke c m r a =>
        refine ⟨h1, h2, h3, h4, fun r' hr' a' ha' => ?_⟩
        dsimp only [Cfg.setRole] at ha'
        by_cases hx : m₀ = m ∧ r' = r ∧ a' = a
        · simp only [hx, and_self, ↓reduceIte] at ha'
        · simp only [hx, ↓reduceIte] at ha'; exact h5 r' hr' a' ha'
      | renounceRole c m b r =>
        refine ⟨h1, h2, h3, h4, fun r' hr' a' ha' => ?_⟩
        dsimp only [Cfg.setRole] at ha'
        by_cases hx : m₀ = m ∧ r' = r ∧ a' = b
        · simp only [hx, and_self, ↓reduceIte] at ha'
        · simp only [hx, ↓reduceIte] at ha'; exact h5 r' hr' a' ha'
    · intro c ⟨h1, h2, h3, h4, h5⟩ q Y hR hY
      have hsingle : ∀ {r : A × Act A R}, (∀ r' ∈ ({r} : Set (A × Act A R)), C r') → C r :=
        fun h => h _ rfl
      cases hR with
      | pause a _ ha =>
        rw [h3] at ha
        rcases hsingle hY with h | ⟨-, _, _, h, -⟩
        · exact absurd h (hrole _ hp a (h5 _ hp a ha))
        · rcases h with h | h <;> cases h
      | setAcm o _ ho =>
        rcases hsingle hY with h | ⟨-, _, _, h, -⟩
        · exact absurd h (hown o (h1 ▸ ho))
        · rcases h with h | h <;> cases h
      | transfer o _ ho =>
        rcases hsingle hY with h | ⟨-, _, _, h, -⟩
        · exact absurd h (hown o (h1 ▸ ho))
        · rcases h with h | h <;> cases h
      | accept p hp' =>
        rcases hsingle hY with h | ⟨-, _, _, h, -⟩
        · exact absurd h (hpen p (h2 ▸ hp'))
        · rcases h with h | h <;> cases h
      | renounce o ho =>
        rcases hsingle hY with h | ⟨-, _, _, h, -⟩
        · exact absurd h (hown o (h1 ▸ ho))
        · rcases h with h | h <;> cases h
      | grant m b r a hm hb =>
        rcases hsingle hY with h | ⟨-, _, _, h, -⟩
        · refine Or.inr ⟨hm, r, a, Or.inl rfl, fun hm₀ => fun hadm => ?_⟩
          subst hm₀
          rw [h4] at hb
          exact hrole _ hadm b (h5 _ hadm b hb) h
        · rcases h with h | h <;> cases h
      | revoke m b r a hm hb =>
        rcases hsingle hY with h | ⟨-, _, _, h, -⟩
        · refine Or.inr ⟨hm, r, a, Or.inr rfl, fun hm₀ => fun hadm => ?_⟩
          subst hm₀
          rw [h4] at hb
          exact hrole _ hadm b (h5 _ hadm b hb) h
        · rcases h with h | h <;> cases h
  rcases hC with h | ⟨h, -⟩
  · exact htgt h
  · exact h rfl

/-- **Headline.** Along every sequence of transactions sent by such keys `T`, the flag never
changes. -/
theorem paused_kept {T : Set A} {s₀ : St A R} {Adm : Set R} (hp : D.pauser ∈ Adm)
    (hAdm : ∀ r ∈ Adm, s₀.cfg.adminOf s₀.cfg.acm r ∈ Adm)
    (htgt : D.tgt ∉ T) (hacm : s₀.cfg.acm ∉ T)
    (hown : ∀ o, s₀.cfg.owner = some o → o ∉ T) (hpen : ∀ o, s₀.cfg.pending = some o → o ∉ T)
    (hrole : ∀ r ∈ Adm, ∀ a, s₀.cfg.has s₀.cfg.acm r a → a ∉ T) (ops : List (Tx A R))
    (hops : ∀ op ∈ ops, consent op ⊆ T) : (exec (step D) s₀ ops).paused = s₀.paused :=
  (guards D).exec_keep (stable D) s₀ ops hops
    (no_pause D hp hAdm htgt hacm hown hpen hrole)

/-- **The owner holds `PAUSER`**: if it administers `PAUSER` in some manager `m` (e.g. one it
deployed), it derives `setPaused` by pointing the target at `m` and granting itself the role. -/
theorem owner_can_pause {s : St A R} {o m : A} (ho : s.cfg.owner = some o) (hm : m ≠ D.tgt)
    (hadm : s.cfg.has m (s.cfg.adminOf m D.pauser) o) (v : Bool) :
    Derives (Rl D) s {o} (D.tgt, .act (.setPaused v)) := by
  -- The changes: `setAcm m` by the target (on the owner's call), then the grant at `m`.
  let c₁ : Cfg A R := { s.cfg with acm := m }
  let c₂ : Cfg A R := c₁.setRole m D.pauser o True
  have hkey : ∀ p, Derives (Auth D) s.cfg {o} (o, p) := fun p => .key p rfl
  have hset : Derives (Auth D) s.cfg {o} (D.tgt, .act (.setAcm m)) :=
    Derives.base (Base.setAcm s.cfg o m ho) (single_prem D (hkey _))
  have hgrant : Derives (Auth D) s.cfg {o} (m, .act (.grantRole D.pauser o)) :=
    Derives.base (Base.grant s.cfg m o D.pauser o hm hadm) (single_prem D (hkey _))
  have hp : Path (Chg D) s.cfg [(D.tgt, .act (.setAcm m)), (m, .act (.grantRole D.pauser o))] c₂ :=
    .cons (Chg.setAcm s.cfg m) (.cons (Chg.grant c₁ m D.pauser o) (.nil _))
  have hpause : Derives (Auth D) c₂ {o} (D.tgt, .act (.setPaused v)) :=
    Derives.base (Base.pause c₂ o v (by simp [c₂, c₁, Cfg.setRole]))
      (single_prem D (.key _ rfl))
  have := Derives.of_path hp (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hset
    · exact hgrant) hpause
  exact Derives.mono_rules (R := Auth D) (s := s.cfg) (R' := Rl D) (s' := s) (fun _ _ h => h) this

end Examples.Actor.RoleOracle
