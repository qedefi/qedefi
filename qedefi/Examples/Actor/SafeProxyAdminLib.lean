import QEDefi.Actor.Lib.Safe
import QEDefi.Actor.Lib.Ownable

/-!
# Worked example, from components: a Safe owns the ProxyAdmin of a transparent proxy

`SafeProxyAdmin.lean` again, with the authority taken from the library components instead of
written by hand: the system is the union of the `Safe` component at `sf`, the `Ownable` component
at `pa` (whose `onlyOwner` function is `upgradeAndCall`), and two rules of the protocol itself,
the proxy's admin check (`endpoint`) and ProxyAdmin's call to the proxy (`relay`).

- `run_sound`: per-call soundness, from the components' `run_sound`, `exec_sound`,
  `module_sound`, `act_of_owner`;
- `stable`, `guards`: the two obligations (`Sys.stable`);
- `no_upgrade`: who can upgrade, by `Sys.le_of_closed` over the union: `Safe.Closes.outsider`,
  `Ownable.Closes.frozen`, `Closed.endpoint`, `Closed.relay`, with no case analysis on rules;
- `impl_kept`, `upgrade_by_owners`: the headline and its converse.

The Safe model here is the component's, more exact than the original example's (thresholds are
at least 1, owner and module functions have their checks, `swapOwner`, `changeThreshold` and
`disableModule` exist).
-/

namespace Examples.Actor.SafeProxyAdminLib

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
  /-- ProxyAdmin's `Ownable` functions. -/
  | own (m : Ownable.Msg A)
  /-- The Safe's functions; digests are the Safe transactions (target, message). -/
  | safe (m : Safe.Msg A (Msg A) (A × Msg A))

abbrev Dig (A : Type) := A × Msg A

abbrev Act (A : Type) := Action A (Msg A) (Dig A)

/-- The configuration: the components' fragments. -/
structure Cfg (A : Type) where
  pa : Ownable.Cfg A
  safe : Safe.Cfg A (Dig A)

structure St (A : Type) where
  cfg : Cfg A
  impl : A

structure Addrs (A : Type) where
  px : A
  pa : A
  sf : A

def paL : Lens (Cfg A) (Ownable.Cfg A) := ⟨Cfg.pa, fun x c => { c with pa := x }⟩

def sfL : Lens (Cfg A) (Safe.Cfg A (Dig A)) := ⟨Cfg.safe, fun x c => { c with safe := x }⟩

/-- ProxyAdmin's `onlyOwner` functions besides `Ownable`'s. -/
def G (m : Msg A) : Prop := ∃ x, m = .adminUpgrade x

variable (D : Addrs A)

/-- The proxy's admin check: the immutable admin `pa` upgrades. -/
def proxyMay (_ : Cfg A) (b : A) (m : Msg A) : Prop := b = D.pa ∧ ∃ x, m = .upgrade x

/-- `pa.upgradeAndCall(px, x)` calls `px.upgradeToAndCall(x)`. -/
def paOut (_ : Cfg A) (m : Msg A) (p : Act A) : Prop :=
  ∃ x, m = .adminUpgrade x ∧ p = .call D.px (.upgrade x)

/-- **The authority of the system**: components and the protocol's own rules. -/
def sys : Sys (Cfg A) A (Act A) :=
  ((Safe.sys D.sf Msg.safe Prod.mk).lift sfL).union
    (((Ownable.sys D.pa Msg.own G).lift paL).union
      ((Sys.ofRules (endpoint D.px (proxyMay D))).union (Sys.ofRules (relay D.pa (paOut D)))))

theorem safe_le : (Safe.sys D.sf Msg.safe Prod.mk).lift sfL ≤ sys D := Sys.le_union_left

theorem own_le : (Ownable.sys D.pa Msg.own G).lift paL ≤ sys D :=
  Sys.le_trans Sys.le_union_left Sys.le_union_right

theorem endpoint_le : Sys.ofRules (endpoint D.px (proxyMay D)) ≤ sys D :=
  Sys.le_trans Sys.le_union_left (Sys.le_trans Sys.le_union_right Sys.le_union_right)

theorem relay_le : Sys.ofRules (relay D.pa (paOut D)) ≤ sys D :=
  Sys.le_trans Sys.le_union_right (Sys.le_trans Sys.le_union_right Sys.le_union_right)

/-! ## Semantics -/

/-- A call to one of the Safe's configuration functions. -/
noncomputable def safeCall (s : St A) (b t : A) (m : Safe.Msg A (Msg A) (Dig A)) : Option (St A) :=
  if t = D.sf then (Safe.run D.sf s.cfg.safe b m).map fun x => { s with cfg := { s.cfg with safe := x } }
  else none

/-- **One call** `m` from `b` to `t`, carrying the signatures `sigs` (`none`: it reverts). -/
noncomputable def run (sigs : Set A) : St A → A → A → Msg A → Option (St A)
  | s, b, t, .upgrade x => if t = D.px ∧ b = D.pa then some { s with impl := x } else none
  | s, b, t, .adminUpgrade x =>
    if t = D.pa ∧ s.cfg.pa = some b then some { s with impl := x } else none
  | s, b, t, .own m =>
    if t = D.pa then (Ownable.run s.cfg.pa b m).map fun x => { s with cfg := { s.cfg with pa := x } }
    else none
  | s, b, t, .safe (.execTransaction t' m) =>
    if t = D.sf ∧ Safe.Approves Prod.mk sigs s.cfg.safe b t' m then run sigs s D.sf t' m else none
  | s, b, t, .safe (.execFromModule t' m) =>
    if t = D.sf ∧ b ∈ s.cfg.safe.modules then run sigs s D.sf t' m else none
  | s, b, t, .safe (.addOwnerWithThreshold o k) => safeCall D s b t (.addOwnerWithThreshold o k)
  | s, b, t, .safe (.removeOwner o k) => safeCall D s b t (.removeOwner o k)
  | s, b, t, .safe (.swapOwner o n) => safeCall D s b t (.swapOwner o n)
  | s, b, t, .safe (.changeThreshold k) => safeCall D s b t (.changeThreshold k)
  | s, b, t, .safe (.enableModule mod) => safeCall D s b t (.enableModule mod)
  | s, b, t, .safe (.disableModule mod) => safeCall D s b t (.disableModule mod)
  | s, b, t, .safe (.approveHash h) => safeCall D s b t (.approveHash h)

structure Tx (A : Type) where
  sender : A
  sigs : Set A
  target : A
  msg : Msg A

noncomputable def step (s : St A) (tx : Tx A) : Option (St A) :=
  run D tx.sigs s tx.sender tx.target tx.msg

def consent (tx : Tx A) : Set A := insert tx.sender tx.sigs

/-! ## Soundness -/

theorem safeCall_sound {K : Set A} {s s' : St A} {b t : A} {m : Safe.Msg A (Msg A) (Dig A)}
    (hr : safeCall D s b t m = some s') (hd : Derives (sys D).auth s.cfg K (b, .call t (.safe m))) :
    s'.impl = s.impl ∧ ∃ e, (sys D).chg e s.cfg s'.cfg ∧ Derives (sys D).auth s.cfg K e := by
  simp only [safeCall] at hr; split_ifs at hr with ht; subst ht
  obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 hr
  exact ⟨rfl, Safe.run_sound (safe_le D) (L := sfL) (c := s.cfg) hx' hd⟩

/-- **Every successful call is authorised**: it keeps the configuration and changes the
implementation only by a derivable upgrade, or keeps the implementation and makes a derivable
configuration change. -/
theorem run_sound {sigs K : Set A} (hK : sigs ⊆ K) :
    ∀ (m : Msg A) (s s' : St A) (b t : A), run D sigs s b t m = some s' →
      Derives (sys D).auth s.cfg K (b, .call t m) →
      (s'.cfg = s.cfg ∧
        (s'.impl = s.impl ∨ Derives (sys D).auth s.cfg K (D.px, .act (.upgrade s'.impl)))) ∨
      (s'.impl = s.impl ∧ ∃ e, (sys D).chg e s.cfg s'.cfg ∧ Derives (sys D).auth s.cfg K e)
  | .upgrade x, s, s', b, t, hr, hd => by
    simp only [run] at hr; split_ifs at hr with h; obtain ⟨rfl, rfl⟩ := h; cases hr
    exact Or.inl ⟨rfl, Or.inr ((endpoint_le D).derive₁ (S₁ := Sys.ofRules (endpoint D.px (proxyMay D)))
      ⟨D.pa, .upgrade x, rfl, ⟨rfl, x, rfl⟩, rfl⟩ hd)⟩
  | .adminUpgrade x, s, s', b, t, hr, hd => by
    simp only [run] at hr; split_ifs at hr with h; obtain ⟨rfl, ho⟩ := h; cases hr
    have h₁ := Ownable.act_of_owner (own_le D) (L := paL) (c := s.cfg) ho (Or.inl ⟨x, rfl⟩) hd
    have h₂ := (relay_le D).derive₁ (S₁ := Sys.ofRules (relay D.pa (paOut D)))
      (q := (D.pa, .call D.px (.upgrade x))) ⟨.adminUpgrade x, rfl, ⟨x, rfl, rfl⟩, rfl⟩ h₁
    exact Or.inl ⟨rfl, Or.inr ((endpoint_le D).derive₁ (S₁ := Sys.ofRules (endpoint D.px (proxyMay D)))
      ⟨D.pa, .upgrade x, rfl, ⟨rfl, x, rfl⟩, rfl⟩ h₂)⟩
  | .own m, s, s', b, t, hr, hd => by
    simp only [run] at hr; split_ifs at hr with ht; subst ht
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 hr
    exact Or.inr ⟨rfl, Ownable.run_sound (own_le D) (L := paL) (c := s.cfg) hx' hd⟩
  | .safe (.execTransaction t' m), s, s', b, t, hr, hd => by
    simp only [run] at hr; split_ifs at hr with h; obtain ⟨rfl, ha⟩ := h
    exact run_sound hK m s s' D.sf t' hr
      (Safe.exec_sound (safe_le D) (L := sfL) (c := s.cfg) hK ha hd)
  | .safe (.execFromModule t' m), s, s', b, t, hr, hd => by
    simp only [run] at hr; split_ifs at hr with h; obtain ⟨rfl, hb⟩ := h
    exact run_sound hK m s s' D.sf t' hr
      (Safe.module_sound (safe_le D) (L := sfL) (c := s.cfg) hb hd)
  | .safe (.addOwnerWithThreshold _ _), _, _, _, _, hr, hd => Or.inr (safeCall_sound D hr hd)
  | .safe (.removeOwner _ _), _, _, _, _, hr, hd => Or.inr (safeCall_sound D hr hd)
  | .safe (.swapOwner _ _), _, _, _, _, hr, hd => Or.inr (safeCall_sound D hr hd)
  | .safe (.changeThreshold _), _, _, _, _, hr, hd => Or.inr (safeCall_sound D hr hd)
  | .safe (.enableModule _), _, _, _, _, hr, hd => Or.inr (safeCall_sound D hr hd)
  | .safe (.disableModule _), _, _, _, _, hr, hd => Or.inr (safeCall_sound D hr hd)
  | .safe (.approveHash _), _, _, _, _, hr, hd => Or.inr (safeCall_sound D hr hd)

/-- The rules of the model, on states. -/
abbrev Rl : Rules (St A) A (Act A) := fun s => (sys D).auth s.cfg

/-- The protected capabilities: upgrading to any implementation. -/
def Upgrades (q : A × Act A) : Prop := ∃ x, q = (D.px, .act (.upgrade x))

theorem derives_rl {s : St A} {T : Set A} {q : A × Act A} (h : Derives (Rl D) s T q) :
    Derives (sys D).auth s.cfg T q :=
  Derives.mono_rules (R := Rl D) (s := s) (fun _ _ h => h) h

/-- **Obligation 1: stability.** -/
theorem stable : Stable (step D) consent (Rl D) :=
  Sys.stable (cfg := St.cfg) (sys D) fun s tx s' hr => by
    rcases run_sound D (Set.subset_insert tx.sender tx.sigs) tx.msg s s' tx.sender tx.target hr
      (.key _ (Set.mem_insert _ _)) with ⟨hc, -⟩ | ⟨-, e, he, hd⟩
    · exact Or.inl hc
    · exact Or.inr ⟨e, he, hd⟩

/-- **Obligation 2: the implementation changes only by a derivable upgrade.** -/
theorem guards : Guards (step D) consent (Rl D) (Upgrades D) (Same St.impl) := by
  refine Guards.same (fun s tx s' hr hq => ?_)
  rcases run_sound D (Set.subset_insert tx.sender tx.sigs) tx.msg s s' tx.sender tx.target hr
    (.key _ (Set.mem_insert _ _)) with ⟨-, hi | hd⟩ | ⟨hi, -⟩
  · exact hi
  · exact absurd (Derives.mono_rules (R := (sys D).auth) (s := s.cfg) (R' := Rl D) (s' := s)
      (fun _ _ h => h) hd) (hq _ ⟨s'.impl, rfl⟩)
  · exact hi

/-! ## Who can upgrade -/

/-- **Fewer than `thr` counted owners cannot upgrade**, through any configuration change. The
proof is the union of the components' closure lemmas. -/
theorem no_upgrade {T : Set A} {s₀ : St A} (hpa : s₀.cfg.pa = some D.sf)
    (hpx : D.px ∉ T) (hpaT : D.pa ∉ T) (hsf : D.sf ∉ T)
    (hmod : ∀ b ∈ s₀.cfg.safe.modules, b ∉ T)
    (hthr : (Safe.counted T s₀.cfg.safe).card < s₀.cfg.safe.thr) :
    ∀ q, Upgrades D q → ¬ Derives (Rl D) s₀ T q := by
  rintro _ ⟨x, rfl⟩ hd
  let x₀ := s₀.cfg.safe
  -- What `T` can do: its own capabilities, and the stored approvals.
  let Dq : A × Act A → Prop := fun q => q.1 ∈ T ∨ ∃ h, q.2 = .sign h ∧ x₀.approved q.1 h
  let Inv : Cfg A → Prop := fun c => c.pa = some D.sf ∧ c.safe.owners = x₀.owners ∧
    c.safe.thr = x₀.thr ∧ c.safe.modules = x₀.modules ∧
    ∀ o h, c.safe.approved o h → x₀.approved o h ∨ o ∈ T
  have hcall : ∀ b (t : A) (m : Msg A), Dq (b, .call t m) → b ∈ T := by
    rintro b t m (h | ⟨_, h, -⟩)
    · exact h
    · cases h
  have hact : ∀ a (m : Msg A), a ∉ T → ¬ Dq (a, .act m) := by
    rintro a m ha (h | ⟨_, h, -⟩)
    · exact ha h
    · cases h
  have hS : Sys.Closed (sys D) Dq Inv := by
    refine (Safe.closed (Safe.Closes.outsider (L := sfL) (T := T) (x₀ := x₀)
      (fun c hI => hI.2) (fun c x' hI h1 h2 h3 h4 => ⟨hI.1, h1, h2, h3, h4⟩) hthr hsf hmod
      (fun a ha _ => Or.inl ha) (fun o h ha => Or.inr ⟨h, rfl, ha⟩) ?_
      (fun b m => hcall b D.sf m) (fun m => hact D.sf m hsf))).union
      ((Ownable.closed (Ownable.Closes.frozen (L := paL) (x₀ := some D.sf) (fun c hI => hI.1)
        (fun o ho _ _ h => absurd (hcall _ _ _ h) (Option.some.inj ho ▸ hsf))
        (fun m => hact D.pa _ hpaT))).union
      ((Sys.Closed.endpoint fun _ _ b _ ⟨hb, _⟩ h => absurd (hb ▸ hcall b _ _ h) hpaT).union
        (Sys.Closed.relay fun _ _ m _ _ h => absurd h (hact D.pa m hpaT))))
    rintro o h (h' | ⟨_, he, ha⟩)
    · exact Or.inl h'
    · cases he; exact Or.inr ha
  have hq := Sys.le_of_closed hS (fun a ha _ => Or.inl ha)
    ⟨hpa, rfl, rfl, rfl, fun o h ha => Or.inl ha⟩ (derives_rl D hd)
  exact hact D.px _ hpx hq

/-- **Headline.** Along every sequence of transactions whose senders and signers are among `T`,
from a state where fewer than `thr` owners are in `T` or hold approved hashes (and the side
conditions of `no_upgrade`), the implementation never changes. -/
theorem impl_kept {T : Set A} {s₀ : St A} (hpa : s₀.cfg.pa = some D.sf)
    (hpx : D.px ∉ T) (hpaT : D.pa ∉ T) (hsf : D.sf ∉ T)
    (hmod : ∀ b ∈ s₀.cfg.safe.modules, b ∉ T)
    (hthr : (Safe.counted T s₀.cfg.safe).card < s₀.cfg.safe.thr) (ops : List (Tx A))
    (hops : ∀ op ∈ ops, consent op ⊆ T) : (exec (step D) s₀ ops).impl = s₀.impl :=
  (guards D).exec_keep (stable D) s₀ ops hops (no_upgrade D hpa hpx hpaT hsf hmod hthr)

/-- **Not vacuous**: `thr ≥ 1` owners signing a Safe transaction that calls
`pa.upgradeAndCall(px, x)` upgrade the proxy. -/
theorem upgrade_by_owners {s : St A} (hpa : s.cfg.pa = some D.sf) {Y : Finset A}
    (h1 : 1 ≤ s.cfg.safe.thr) (hY : Y ⊆ s.cfg.safe.owners) (hk : s.cfg.safe.thr ≤ Y.card)
    (sender x : A) :
    step D s ⟨sender, Y, D.sf, .safe (.execTransaction D.pa (.adminUpgrade x))⟩ =
      some { s with impl := x } := by
  have hap : Safe.Approves Prod.mk (Y : Set A) s.cfg.safe sender D.pa (.adminUpgrade x) :=
    ⟨h1, Y, hY, hk, fun o ho => Or.inl ho⟩
  simp [step, run, hap, hpa]

end Examples.Actor.SafeProxyAdminLib
