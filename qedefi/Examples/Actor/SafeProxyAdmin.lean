import QEDefi.Actor.Action
import QEDefi.Actor.Config

/-!
# Worked example: a Safe owns the ProxyAdmin of a transparent proxy

The upgrade path of most deployed protocols (OpenZeppelin v5): a `TransparentUpgradeableProxy`
`px` whose immutable admin is a `ProxyAdmin` `pa` (`Ownable`), owned by a Safe `sf` (owners,
threshold, modules, on-chain approved hashes, self-administration). The model:

- `run` is one transaction: a Safe transaction executes its inner call with `msg.sender = sf`;
  `ProxyAdmin.upgradeAndCall` calls the proxy with `msg.sender = pa`. Signatures are abstracted
  to the set `sigs` of signers the transaction carries (what `ecrecover` returns, for keys that
  did sign under `SigUnforgeable`); an owner also counts if it approved the digest on chain or
  sends the transaction itself (Safe signature types 1).
- `Base` are the access checks as rules, `Chg` the configuration changes (ProxyAdmin ownership,
  owners and threshold, modules, approved hashes). The escalation rules ("whoever can make `pa`
  transfer ownership to `o` can upgrade through `o`") come from `close`.

Results:

- `stable`, `guards`: the two obligations, so `QEDefi.Actor.Guards.exec_keep` applies;
- `no_upgrade`: if fewer than `thr` owners are among the acting keys `T` or hold approved hashes,
  no enabled module acts, and none of the three contracts is a key, `T` cannot upgrade;
- `impl_kept`: hence **the implementation is unchanged along every transaction sequence by
  `T`**, whatever `T` does (configuration changes, approvals, nested Safe calls included);
- `upgrade_by_owners`: conversely `thr` owners do upgrade (the statement is not vacuous).

Modules are external contracts: the statement treats any action by a module as possible (it
assumes none acts), rather than modelling its own access control.
-/

namespace Examples.Actor.SafeProxyAdmin

open QEDefi.Actor QEDefi.Trace.Lift
open Classical

variable {A : Type}

/-! ## Messages, configurations, states -/

/-- The functions of the three contracts. -/
inductive Msg (A : Type) where
  /-- `px.upgradeToAndCall(impl, "")` (admin only). -/
  | upgrade (impl : A)
  /-- `pa.upgradeAndCall(px, impl, "")` (owner only). -/
  | adminUpgrade (impl : A)
  /-- `pa.transferOwnership(o)`; `none` is `renounceOwnership()` (owner only). -/
  | transferOwnership (o : Option A)
  /-- `sf.execTransaction(t, m, signatures)`. -/
  | exec (t : A) (m : Msg A)
  /-- `sf.execTransactionFromModule(t, m)` (enabled modules only). -/
  | execFromModule (t : A) (m : Msg A)
  /-- `sf.addOwnerWithThreshold(o, k)` (the Safe itself only). -/
  | addOwner (o : A) (k : ℕ)
  /-- `sf.removeOwner(o, k)` (the Safe itself only). -/
  | removeOwner (o : A) (k : ℕ)
  /-- `sf.enableModule(mod)` (the Safe itself only). -/
  | enableModule (mod : A)
  /-- `sf.approveHash(digest of (t, m))` (owners only). -/
  | approveHash (t : A) (m : Msg A)

/-- Actions; digests are the Safe transactions they approve (target, message). -/
abbrev Act (A : Type) := Action A (Msg A) (A × Msg A)

/-- The configuration: everything authority depends on. -/
structure Cfg (A : Type) where
  paOwner : Option A
  owners : Finset A
  thr : ℕ
  modules : Set A
  approved : A → A × Msg A → Prop

/-- The state: the configuration and the protected implementation. -/
structure St (A : Type) where
  cfg : Cfg A
  impl : A

/-- The deployment. -/
structure Addrs (A : Type) where
  px : A
  pa : A
  sf : A

variable (D : Addrs A)

/-! ## Semantics -/

/-- The Safe's signature check: some `thr` owners each signed, approved on chain, or sent it. -/
def Approves (sigs : Set A) (c : Cfg A) (b : A) (h : A × Msg A) : Prop :=
  ∃ Y : Finset A, Y ⊆ c.owners ∧ c.thr ≤ Y.card ∧ ∀ o ∈ Y, o ∈ sigs ∨ c.approved o h ∨ o = b

/-- The configuration after `b` approves `h`. -/
def Cfg.approve (c : Cfg A) (b : A) (h : A × Msg A) : Cfg A :=
  { c with approved := fun o h' => c.approved o h' ∨ (o = b ∧ h' = h) }

/-- **One call** `m` from `b` to `t`, carrying the signatures `sigs` (`none`: it reverts). -/
noncomputable def run (sigs : Set A) : St A → A → A → Msg A → Option (St A)
  | s, b, t, .upgrade x => if t = D.px ∧ b = D.pa then some { s with impl := x } else none
  | s, b, t, .adminUpgrade x =>
    -- `pa` calls `px.upgradeToAndCall` with `msg.sender = pa`.
    if t = D.pa ∧ s.cfg.paOwner = some b then some { s with impl := x } else none
  | s, b, t, .transferOwnership o =>
    if t = D.pa ∧ s.cfg.paOwner = some b then some { s with cfg := { s.cfg with paOwner := o } }
    else none
  | s, b, t, .exec t' m =>
    if t = D.sf ∧ Approves sigs s.cfg b (t', m) then run sigs s D.sf t' m else none
  | s, b, t, .execFromModule t' m =>
    if t = D.sf ∧ b ∈ s.cfg.modules then run sigs s D.sf t' m else none
  | s, b, t, .addOwner o k =>
    if t = D.sf ∧ b = D.sf then
      some { s with cfg := { s.cfg with owners := insert o s.cfg.owners, thr := k } }
    else none
  | s, b, t, .removeOwner o k =>
    if t = D.sf ∧ b = D.sf then
      some { s with cfg := { s.cfg with owners := s.cfg.owners.erase o, thr := k } }
    else none
  | s, b, t, .enableModule mod =>
    if t = D.sf ∧ b = D.sf then
      some { s with cfg := { s.cfg with modules := insert mod s.cfg.modules } }
    else none
  | s, b, t, .approveHash t' m =>
    if t = D.sf ∧ b ∈ s.cfg.owners then some { s with cfg := s.cfg.approve b (t', m) } else none

/-- A top-level transaction. -/
structure Tx (A : Type) where
  sender : A
  sigs : Set A
  target : A
  msg : Msg A

/-- The model step. -/
noncomputable def step (s : St A) (tx : Tx A) : Option (St A) :=
  run D tx.sigs s tx.sender tx.target tx.msg

/-- The keys that consent to a transaction: its sender and its signers. -/
def consent (tx : Tx A) : Set A := insert tx.sender tx.sigs

/-! ## Authority -/

/-- **The access checks as rules.** -/
inductive Base : Cfg A → A × Act A → Set (A × Act A) → Prop
  | upgrade (c : Cfg A) (x : A) :
      Base c (D.px, .act (.upgrade x)) {(D.pa, .call D.px (.upgrade x))}
  | paUpgrade (c : Cfg A) (o x : A) (ho : c.paOwner = some o) :
      Base c (D.pa, .act (.adminUpgrade x)) {(o, .call D.pa (.adminUpgrade x))}
  | paTransfer (c : Cfg A) (o : A) (o' : Option A) (ho : c.paOwner = some o) :
      Base c (D.pa, .act (.transferOwnership o')) {(o, .call D.pa (.transferOwnership o'))}
  | paRelay (c : Cfg A) (x : A) :
      Base c (D.pa, .call D.px (.upgrade x)) {(D.pa, .act (.adminUpgrade x))}
  | quorum (c : Cfg A) (t : A) (m : Msg A) (Y : Finset A) (hY : Y ⊆ c.owners)
      (hk : c.thr ≤ Y.card) :
      Base c (D.sf, .act (.exec t m)) ((fun o => (o, Action.sign (t, m))) '' (Y : Set A))
  | signByCall (c : Cfg A) (o t : A) (m : Msg A) :
      Base c (o, .sign (t, m)) {(o, .call D.sf (.exec t m))}
  | approved (c : Cfg A) (o : A) (h : A × Msg A) (ha : c.approved o h) : Base c (o, .sign h) ∅
  | module (c : Cfg A) (b t : A) (m : Msg A) (hb : b ∈ c.modules) :
      Base c (D.sf, .act (.execFromModule t m)) {(b, .call D.sf (.execFromModule t m))}
  | sfExec (c : Cfg A) (t : A) (m : Msg A) : Base c (D.sf, .call t m) {(D.sf, .act (.exec t m))}
  | sfModule (c : Cfg A) (t : A) (m : Msg A) :
      Base c (D.sf, .call t m) {(D.sf, .act (.execFromModule t m))}
  | addOwner (c : Cfg A) (o : A) (k : ℕ) :
      Base c (D.sf, .act (.addOwner o k)) {(D.sf, .call D.sf (.addOwner o k))}
  | removeOwner (c : Cfg A) (o : A) (k : ℕ) :
      Base c (D.sf, .act (.removeOwner o k)) {(D.sf, .call D.sf (.removeOwner o k))}
  | enableModule (c : Cfg A) (mod : A) :
      Base c (D.sf, .act (.enableModule mod)) {(D.sf, .call D.sf (.enableModule mod))}
  | approveHash (c : Cfg A) (o t : A) (m : Msg A) (ho : o ∈ c.owners) :
      Base c (D.sf, .act (.approveHash t m)) {(o, .call D.sf (.approveHash t m))}

/-- **The configuration changes**, each by the capability that performs it. -/
inductive Chg : A × Act A → Cfg A → Cfg A → Prop
  | transfer (c : Cfg A) (o : Option A) :
      Chg (D.pa, .act (.transferOwnership o)) c { c with paOwner := o }
  | addOwner (c : Cfg A) (o : A) (k : ℕ) :
      Chg (D.sf, .act (.addOwner o k)) c { c with owners := insert o c.owners, thr := k }
  | removeOwner (c : Cfg A) (o : A) (k : ℕ) :
      Chg (D.sf, .act (.removeOwner o k)) c { c with owners := c.owners.erase o, thr := k }
  | enableModule (c : Cfg A) (mod : A) :
      Chg (D.sf, .act (.enableModule mod)) c { c with modules := insert mod c.modules }
  | approve (c : Cfg A) (b t : A) (m : Msg A) :
      Chg (b, .call D.sf (.approveHash t m)) c (c.approve b (t, m))

/-- The authority of a configuration: the access checks closed under configuration changes. -/
abbrev Auth : Rules (Cfg A) A (Act A) := fun c => close (Chg D) (Base D) c

/-! ## Soundness of the model's authority -/

/-- **Every successful call is authorised.** If `b`'s call is derivable from keys `K` (that
include the signers), the call either keeps the configuration and changes the implementation
only by a derivable upgrade, or keeps the implementation and makes a derivable configuration
change. -/
theorem run_sound {sigs K : Set A} (hK : sigs ⊆ K) :
    ∀ (m : Msg A) (s s' : St A) (b t : A), run D sigs s b t m = some s' →
      Derives (Auth D) s.cfg K (b, .call t m) →
      (s'.cfg = s.cfg ∧
        (s'.impl = s.impl ∨ Derives (Auth D) s.cfg K (D.px, .act (.upgrade s'.impl)))) ∨
      (s'.impl = s.impl ∧ ∃ e, Chg D e s.cfg s'.cfg ∧ Derives (Auth D) s.cfg K e) := by
  intro m
  induction m with
  | upgrade x =>
    intro s s' b t hr hd
    simp only [run] at hr
    split_ifs at hr with h
    obtain ⟨rfl, rfl⟩ := h
    cases hr
    exact Or.inl ⟨rfl, Or.inr (Derives.base (Base.upgrade s.cfg x) (by
      intro r hr; rw [Set.mem_singleton_iff.1 hr]; exact hd))⟩
  | adminUpgrade x =>
    intro s s' b t hr hd
    simp only [run] at hr
    split_ifs at hr with h
    obtain ⟨rfl, ho⟩ := h
    cases hr
    have h₁ : Derives (Auth D) s.cfg K (D.pa, .act (.adminUpgrade x)) :=
      Derives.base (Base.paUpgrade s.cfg b x ho) (by
        intro r hr; rw [Set.mem_singleton_iff.1 hr]; exact hd)
    have h₂ : Derives (Auth D) s.cfg K (D.pa, .call D.px (.upgrade x)) :=
      Derives.base (Base.paRelay s.cfg x) (by
        intro r hr; rw [Set.mem_singleton_iff.1 hr]; exact h₁)
    exact Or.inl ⟨rfl, Or.inr (Derives.base (Base.upgrade s.cfg x) (by
      intro r hr; rw [Set.mem_singleton_iff.1 hr]; exact h₂))⟩
  | transferOwnership o =>
    intro s s' b t hr hd
    simp only [run] at hr
    split_ifs at hr with h
    obtain ⟨rfl, ho⟩ := h
    cases hr
    exact Or.inr ⟨rfl, _, Chg.transfer s.cfg o, Derives.base (Base.paTransfer s.cfg b o ho) (by
      intro r hr; rw [Set.mem_singleton_iff.1 hr]; exact hd)⟩
  | exec t' m ih =>
    intro s s' b t hr hd
    simp only [run] at hr
    split_ifs at hr with h
    obtain ⟨rfl, Y, hY, hk, hsig⟩ := h
    have hq : Derives (Auth D) s.cfg K (D.sf, .act (.exec t' m)) :=
      Derives.base (Base.quorum s.cfg t' m Y hY hk) (by
        rintro _ ⟨o, ho, rfl⟩
        rcases hsig o ho with hs | ha | rfl
        · exact .key _ (hK hs)
        · exact Derives.base (Base.approved s.cfg o _ ha) (fun _ h => h.elim)
        · exact Derives.base (Base.signByCall s.cfg o t' m) (by
            intro r hr; rw [Set.mem_singleton_iff.1 hr]; exact hd))
    exact ih s s' D.sf t' hr (Derives.base (Base.sfExec s.cfg t' m) (by
      intro r hr; rw [Set.mem_singleton_iff.1 hr]; exact hq))
  | execFromModule t' m ih =>
    intro s s' b t hr hd
    simp only [run] at hr
    split_ifs at hr with h
    obtain ⟨rfl, hb⟩ := h
    have hq : Derives (Auth D) s.cfg K (D.sf, .act (.execFromModule t' m)) :=
      Derives.base (Base.module s.cfg b t' m hb) (by
        intro r hr; rw [Set.mem_singleton_iff.1 hr]; exact hd)
    exact ih s s' D.sf t' hr (Derives.base (Base.sfModule s.cfg t' m) (by
      intro r hr; rw [Set.mem_singleton_iff.1 hr]; exact hq))
  | addOwner o k =>
    intro s s' b t hr hd
    simp only [run] at hr
    split_ifs at hr with h
    obtain ⟨rfl, rfl⟩ := h
    cases hr
    exact Or.inr ⟨rfl, _, Chg.addOwner s.cfg o k, Derives.base (Base.addOwner s.cfg o k) (by
      intro r hr; rw [Set.mem_singleton_iff.1 hr]; exact hd)⟩
  | removeOwner o k =>
    intro s s' b t hr hd
    simp only [run] at hr
    split_ifs at hr with h
    obtain ⟨rfl, rfl⟩ := h
    cases hr
    exact Or.inr ⟨rfl, _, Chg.removeOwner s.cfg o k, Derives.base (Base.removeOwner s.cfg o k) (by
      intro r hr; rw [Set.mem_singleton_iff.1 hr]; exact hd)⟩
  | enableModule mod =>
    intro s s' b t hr hd
    simp only [run] at hr
    split_ifs at hr with h
    obtain ⟨rfl, rfl⟩ := h
    cases hr
    exact Or.inr ⟨rfl, _, Chg.enableModule s.cfg mod, Derives.base (Base.enableModule s.cfg mod) (by
      intro r hr; rw [Set.mem_singleton_iff.1 hr]; exact hd)⟩
  | approveHash t' m _ =>
    intro s s' b t hr hd
    simp only [run] at hr
    split_ifs at hr with h
    obtain ⟨rfl, -⟩ := h
    cases hr
    exact Or.inr ⟨rfl, _, Chg.approve s.cfg b t' m, hd⟩

/-- The rules of the model, on states. -/
abbrev Rl : Rules (St A) A (Act A) := fun s => close (Chg D) (Base D) s.cfg

/-- The protected capabilities: upgrading to any implementation. -/
def Upgrades (q : A × Act A) : Prop := ∃ x, q = (D.px, .act (.upgrade x))

/-- **Obligation 1: stability.** -/
theorem stable : Stable (step D) consent (Rl D) := by
  refine stable_of_cfg (chg := Chg D) (R := Base D) (cfg := St.cfg) ?_
  intro s tx s' hr
  rcases run_sound D (Set.subset_insert tx.sender tx.sigs) tx.msg s s' tx.sender tx.target hr
    (.key _ (Set.mem_insert _ _)) with ⟨hc, -⟩ | ⟨-, e, he, hd⟩
  · exact ⟨[], path_of_eq hc, fun _ h => (List.not_mem_nil h).elim⟩
  · exact ⟨[e], path_single he, fun e' h => by rw [List.mem_singleton.1 h]; exact hd⟩

/-- **Obligation 2: the implementation changes only by a derivable upgrade.** -/
theorem guards : Guards (step D) consent (Rl D) (Upgrades D) (Same St.impl) := by
  refine Guards.same (fun s tx s' hr hq => ?_)
  rcases run_sound D (Set.subset_insert tx.sender tx.sigs) tx.msg s s' tx.sender tx.target hr
    (.key _ (Set.mem_insert _ _)) with ⟨-, hi | hd⟩ | ⟨hi, -⟩
  · exact hi
  · exact absurd (Derives.mono_rules (R := Auth D) (s := s.cfg) (R' := Rl D) (s' := s)
      (fun _ _ h => h) hd)
      (hq _ ⟨s'.impl, rfl⟩)
  · exact hi

/-! ## Who can upgrade -/

/-- The owners that could count towards the threshold: acting keys or holders of an approved
hash. -/
noncomputable def counted (T : Set A) (c : Cfg A) : Finset A :=
  c.owners.filter (fun o => o ∈ T ∨ ∃ h, c.approved o h)

/-- **Fewer than `thr` counted owners cannot upgrade.** With the ProxyAdmin owned by the Safe,
no enabled module and none of the contracts among the acting keys `T`, `T` derives no upgrade,
not even through configuration changes (adding owners, lowering the threshold, transferring
ProxyAdmin ownership, approving hashes, enabling modules). -/
theorem no_upgrade {T : Set A} {s₀ : St A} (hpa : s₀.cfg.paOwner = some D.sf)
    (hpx : D.px ∉ T) (hpaT : D.pa ∉ T) (hsf : D.sf ∉ T) (hmod : ∀ b ∈ s₀.cfg.modules, b ∉ T)
    (hthr : (counted T s₀.cfg).card < s₀.cfg.thr) :
    ∀ q, Upgrades D q → ¬ Derives (Rl D) s₀ T q := by
  rintro _ ⟨x, rfl⟩ hd
  -- The capabilities `T` can have.
  let C : A × Act A → Prop := fun q =>
    q.1 ∈ T ∨ (∃ h, q.2 = .sign h ∧ s₀.cfg.approved q.1 h) ∨
      (q.1 = D.sf ∧ ∃ t m, q.2 = .act (.approveHash t m))
  -- The configurations reachable through those capabilities.
  let Inv : Cfg A → Prop := fun c =>
    c.paOwner = some D.sf ∧ c.owners = s₀.cfg.owners ∧ c.thr = s₀.cfg.thr ∧
      c.modules = s₀.cfg.modules ∧ ∀ o h, c.approved o h → s₀.cfg.approved o h ∨ o ∈ T
  have hd' : Derives (Auth D) s₀.cfg T (D.px, .act (.upgrade x)) :=
    Derives.mono_rules (R := Rl D) (s := s₀) (fun _ _ h => h) hd
  have hC : C (D.px, .act (.upgrade x)) := by
    refine close_le_of_closed (D := C) (Inv := Inv) (fun a ha p => Or.inl ha)
      ⟨hpa, rfl, rfl, rfl, fun o h ha => Or.inl ha⟩ ?_ ?_ hd'
    · intro e c c' hc he ⟨h1, h2, h3, h4, h5⟩
      cases hc with
      | transfer => rcases he with he | ⟨_, he, -⟩ | ⟨-, _, _, he⟩
                    · exact absurd he hpaT
                    · cases he
                    · cases he
      | addOwner => rcases he with he | ⟨_, he, -⟩ | ⟨-, _, _, he⟩
                    · exact absurd he hsf
                    · cases he
                    · cases he
      | removeOwner => rcases he with he | ⟨_, he, -⟩ | ⟨-, _, _, he⟩
                       · exact absurd he hsf
                       · cases he
                       · cases he
      | enableModule => rcases he with he | ⟨_, he, -⟩ | ⟨-, _, _, he⟩
                        · exact absurd he hsf
                        · cases he
                        · cases he
      | approve c b t m =>
        rcases he with hb | ⟨_, he, -⟩ | ⟨-, _, _, he⟩
        · refine ⟨h1, h2, h3, h4, fun o h ha => ?_⟩
          rcases ha with ha | ⟨rfl, -⟩
          · exact h5 o h ha
          · exact Or.inr hb
        · cases he
        · cases he
    · intro c ⟨h1, h2, h3, h4, h5⟩ q Y hR hY
      have hsingle : ∀ {r : A × Act A}, (∀ r' ∈ ({r} : Set (A × Act A)), C r') → C r :=
        fun h => h _ rfl
      cases hR with
      | upgrade =>
        rcases hsingle hY with h | ⟨_, h, -⟩ | ⟨-, _, _, h⟩
        · exact absurd h hpaT
        · cases h
        · cases h
      | paUpgrade o _ ho =>
        rw [h1] at ho; cases ho
        rcases hsingle hY with h | ⟨_, h, -⟩ | ⟨-, _, _, h⟩
        · exact absurd h hsf
        · cases h
        · cases h
      | paTransfer o _ ho =>
        rw [h1] at ho; cases ho
        rcases hsingle hY with h | ⟨_, h, -⟩ | ⟨-, _, _, h⟩
        · exact absurd h hsf
        · cases h
        · cases h
      | paRelay =>
        rcases hsingle hY with h | ⟨_, h, -⟩ | ⟨-, _, _, h⟩
        · exact absurd h hpaT
        · cases h
        · cases h
      | quorum t m Y' hY' hk =>
        exfalso
        have hsub : Y' ⊆ counted T s₀.cfg := by
          intro o ho
          refine Finset.mem_filter.2 ⟨h2 ▸ hY' ho, ?_⟩
          rcases hY _ ⟨o, ho, rfl⟩ with h | ⟨h, he, ha⟩ | ⟨-, _, _, he⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, ha⟩
          · cases he
        have := Finset.card_le_card hsub
        omega
      | signByCall o =>
        rcases hsingle hY with h | ⟨_, h, -⟩ | ⟨-, _, _, h⟩
        · exact Or.inl h
        · cases h
        · cases h
      | approved o h ha =>
        rcases h5 o h ha with h' | h'
        · exact Or.inr (Or.inl ⟨h, rfl, h'⟩)
        · exact Or.inl h'
      | module b _ _ hb =>
        rcases hsingle hY with h | ⟨_, h, -⟩ | ⟨-, _, _, h⟩
        · exact absurd h (hmod b (h4 ▸ hb))
        · cases h
        · cases h
      | sfExec =>
        rcases hsingle hY with h | ⟨_, h, -⟩ | ⟨-, _, _, h⟩
        · exact absurd h hsf
        · cases h
        · cases h
      | sfModule =>
        rcases hsingle hY with h | ⟨_, h, -⟩ | ⟨-, _, _, h⟩
        · exact absurd h hsf
        · cases h
        · cases h
      | addOwner =>
        rcases hsingle hY with h | ⟨_, h, -⟩ | ⟨-, _, _, h⟩
        · exact absurd h hsf
        · cases h
        · cases h
      | removeOwner =>
        rcases hsingle hY with h | ⟨_, h, -⟩ | ⟨-, _, _, h⟩
        · exact absurd h hsf
        · cases h
        · cases h
      | enableModule =>
        rcases hsingle hY with h | ⟨_, h, -⟩ | ⟨-, _, _, h⟩
        · exact absurd h hsf
        · cases h
        · cases h
      | approveHash o t m _ => exact Or.inr (Or.inr ⟨rfl, t, m, rfl⟩)
  rcases hC with h | ⟨_, h, -⟩ | ⟨-, _, _, h⟩
  · exact hpx h
  · cases h
  · cases h

/-- **Headline.** Along every sequence of transactions whose senders and signers are among `T`,
from a state where fewer than `thr` owners are in `T` or hold approved hashes (and the side
conditions of `no_upgrade`), the implementation never changes. -/
theorem impl_kept {T : Set A} {s₀ : St A} (hpa : s₀.cfg.paOwner = some D.sf)
    (hpx : D.px ∉ T) (hpaT : D.pa ∉ T) (hsf : D.sf ∉ T) (hmod : ∀ b ∈ s₀.cfg.modules, b ∉ T)
    (hthr : (counted T s₀.cfg).card < s₀.cfg.thr) (ops : List (Tx A))
    (hops : ∀ op ∈ ops, consent op ⊆ T) : (exec (step D) s₀ ops).impl = s₀.impl :=
  (guards D).exec_keep (stable D) s₀ ops hops (no_upgrade D hpa hpx hpaT hsf hmod hthr)

/-- **Not vacuous**: `thr` owners signing a Safe transaction that calls
`pa.upgradeAndCall(px, x)` upgrade the proxy. -/
theorem upgrade_by_owners {s : St A} (hpa : s.cfg.paOwner = some D.sf) {Y : Finset A}
    (hY : Y ⊆ s.cfg.owners) (hk : s.cfg.thr ≤ Y.card) (sender x : A) :
    step D s ⟨sender, Y, D.sf, .exec D.pa (.adminUpgrade x)⟩ = some { s with impl := x } := by
  have hap : Approves (Y : Set A) s.cfg sender (D.pa, .adminUpgrade x) :=
    ⟨Y, hY, hk, fun o ho => Or.inl ho⟩
  simp [step, run, hap, hpa]

end Examples.Actor.SafeProxyAdmin
