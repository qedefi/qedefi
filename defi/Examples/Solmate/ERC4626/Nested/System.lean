import Examples.Solmate.ERC4626.Invariants.Deployed
import EvmLogic.Program.Nested.Run

/-!
# Nested calls: the vault system as an instance of the machine-level simulation

`EvmLeanProofs.Program.NestedExtraRun` proves, for any set `P` of protected accounts and any
property `Good` of worlds that only depends on their storage and code, that a top-level
message call — running **arbitrary code** at every other account, calling the protected
accounts any number of times at any depth, reverting or running out of gas around those calls
— ends in a `Good` world, provided every *dangerous* frame (a non-static frame running at a
protected account) ends in a `Good` world (a frame summary). This file instantiates it:

* `Prot vault asset`: the vault and its asset;
* `Follows crypto vault asset Act K w₀ w` (the `Good` of the simulation): the vault and the
  asset are deployed in `w` and the abstraction of `w` agrees (up to non-actor allowances,
  `AgreeOn (ActorPairs Act)`) with `Solmate.exec (abs w₀)` of some list of **admitted** model
  calls (`Admitted Act K`: actors in `Act`, kind admitted by `K`);
* `FrameOk m`: the frame summary in model terms — a dangerous frame, if it succeeds, ends in a
  deployed world whose abstraction is reached from the frame's starting abstraction by some
  admitted calls (one for a state-changing function, none for a view);
* `follows_of_frameOk`: a `FrameOk` frame keeps `Follows` (on success by composing the call
  lists, on revert or exceptional halt because the frame's snapshot is restored);
* `processMessageCall_follows`: **any top-level message call** from a `Follows` world, whose
  dangerous frames are `FrameOk`, ends in a `Follows` world.

Model laws used: `AgreeOn` is an equivalence preserving `Solmate.Inv`; `Solmate.step` preserves
`Inv` and respects `AgreeOn` on admitted operations (`stepD_agree`, the actor allowances are
the only ones the operations read).
-/

namespace EvmLeanSpecs.Refinement.Nested

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift
open EvmLeanSpecs.Refinement.Invariants
open EvmLean.Program.Nested (Keep KeepP GoodOk DangerStart Danger TopOk Reaches)

variable {crypto : Crypto} {vault asset : Address} {Act : List Address} {K : VCall → Prop}
  {w₀ : World}

/-! ## The protected accounts and the simulation's `Good` -/

/-- The protected accounts: the vault and its asset. -/
def Prot (vault asset : Address) (a : Address) : Prop := a = vault ∨ a = asset

/-- A modelled call is admitted: its actors are in `Act` (so the trace-level hash hypothesis
`SlotsOk` covers it) and its kind is admitted by `K`. -/
def Admitted (Act : List Address) (K : VCall → Prop) (c : VCall) : Prop :=
  (∀ a ∈ c.actors, a ∈ Act) ∧ K c

/-- **The simulation relation**: `w` is deployed and its abstraction agrees with the model's
execution, from `abs w₀`, of some admitted calls. -/
def Follows (crypto : Crypto) (vault asset : Address) (Act : List Address) (K : VCall → Prop)
    (w₀ w : World) : Prop :=
  Deployed w vault asset ∧ ∃ cs : List VCall, (∀ c ∈ cs, Admitted Act K c) ∧
    AgreeOn (ActorPairs Act) (abs crypto w vault asset)
      (Solmate.exec (abs crypto w₀ vault asset) (cs.map VCall.op))

/-! ## Model laws -/

/-- Executions of admitted calls respect `AgreeOn` and keep the invariant. -/
theorem exec_agree (hs : SlotsOk crypto vault Act) {s t : State Address}
    (hst : AgreeOn (ActorPairs Act) s t) (hi : Solmate.Inv s) (hself : s.self = vault)
    {cs : List VCall} (hcs : ∀ c ∈ cs, Admitted Act K c) :
    AgreeOn (ActorPairs Act) (Solmate.exec s (cs.map VCall.op))
        (Solmate.exec t (cs.map VCall.op)) ∧
      Solmate.Inv (Solmate.exec s (cs.map VCall.op)) ∧
      (Solmate.exec s (cs.map VCall.op)).self = vault := by
  induction cs generalizing s t with
  | nil => exact ⟨hst, hi, hself⟩
  | cons c cs ih =>
    have hc := hcs c (List.mem_cons_self ..)
    have hr : Reads (ActorPairs Act) s.self c.op := by
      rw [hself]; exact reads_of_actors hs.vault_mem hc.1
    have h1 := stepD_agree hst hr
    have hi1 : Solmate.Inv (Lift.stepD step s c.op) := by
      unfold Lift.stepD
      cases e : step s c.op with
      | none => exact hi
      | some s' => exact Inv_step hi e
    have hs1 : (Lift.stepD step s c.op).self = vault := (self_stepD s c.op).trans hself
    exact ih h1 hi1 hs1 (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))

/-- `Solmate.exec` of a concatenation. -/
theorem exec_append' (s : State Address) (l₁ l₂ : List (Op Address)) :
    Solmate.exec s (l₁ ++ l₂) = Solmate.exec (Solmate.exec s l₁) l₂ := by
  rw [exec_eq, exec_eq, exec_eq, Lift.exec_append]

/-- `Follows` is transitive along executions: a world following `w₀` by `cs₀`, then a world
whose abstraction agrees with a further execution of admitted calls. -/
theorem Follows.trans (hs : SlotsOk crypto vault Act)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {w w' : World}
    (h : Follows crypto vault asset Act K w₀ w) (hd : Deployed w' vault asset)
    {cs : List VCall} (hcs : ∀ c ∈ cs, Admitted Act K c)
    (ha : AgreeOn (ActorPairs Act) (abs crypto w' vault asset)
      (Solmate.exec (abs crypto w vault asset) (cs.map VCall.op))) :
    Follows crypto vault asset Act K w₀ w' := by
  obtain ⟨-, cs₀, hcs₀, ha₀⟩ := h
  obtain ⟨-, hi₀, hself₀⟩ := exec_agree (K := K) hs (AgreeOn.refl _) hinv rfl hcs₀
  have hi : Solmate.Inv (abs crypto w vault asset) := ha₀.symm.inv hi₀
  obtain ⟨h1, -, -⟩ := exec_agree (K := K) hs ha₀ hi rfl hcs
  refine ⟨hd, cs₀ ++ cs, fun c hc => ?_, ?_⟩
  · rcases List.mem_append.1 hc with hc | hc
    · exact hcs₀ c hc
    · exact hcs c hc
  · rw [List.map_append, exec_append']
    exact ha.trans h1

/-- `Follows` gives the model invariant of the abstraction. -/
theorem Follows.inv (hs : SlotsOk crypto vault Act)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {w : World}
    (h : Follows crypto vault asset Act K w₀ w) : Solmate.Inv (abs crypto w vault asset) := by
  obtain ⟨-, cs₀, hcs₀, ha₀⟩ := h
  obtain ⟨-, hi₀, -⟩ := exec_agree (K := K) hs (AgreeOn.refl _) hinv rfl hcs₀
  exact ha₀.symm.inv hi₀

/-- The initial world follows itself. -/
theorem follows_refl {w₀ : World} (hd : Deployed w₀ vault asset) :
    Follows crypto vault asset Act K w₀ w₀ :=
  ⟨hd, [], ⟨fun _ h => absurd h List.not_mem_nil, AgreeOn.refl _⟩⟩

/-! ## The simulation's requirements -/

/-- The vault's code is not empty. -/
theorem size_vaultCode_ne {w : World} (hd : Deployed w vault asset) : (w.code vault).size ≠ 0 := by
  obtain ⟨i, -, hc⟩ := hd.vaultCode
  rw [hc]; have := Shares.size_code i; simp only [Shares.code] at this; rw [this]; decide

/-- The asset's code is not empty. -/
theorem size_assetCode_ne {w : World} (hd : Deployed w vault asset) : (w.code asset).size ≠ 0 := by
  obtain ⟨ia, hc⟩ := hd.assetCode
  rw [hc, size_assetCode]; decide

/-- Keeping the storage and code of the vault and the asset keeps the deployment and the
abstraction. -/
theorem deployed_abs_of_keep {w w' : World} (hd : Deployed w vault asset)
    (hk : KeepP (Prot vault asset) w w') :
    Deployed w' vault asset ∧ abs crypto w' vault asset = abs crypto w vault asset := by
  have hv := hk vault (.inl rfl)
  have ha := hk asset (.inr rfl)
  exact ⟨hd.of_code hv.code ha.code, abs_congr hv.sload ha.sload⟩

/-- **`Follows` meets the simulation's requirements.** -/
theorem goodOk {w₀ : World} :
    GoodOk (Prot vault asset) (Follows crypto vault asset Act K w₀) where
  keep w w' h hk := by
    obtain ⟨hd, cs, hcs, ha⟩ := h
    obtain ⟨hd', habs⟩ := deployed_abs_of_keep hd hk
    exact ⟨hd', cs, hcs, habs ▸ ha⟩
  code w h p hp := by
    rcases hp with rfl | rfl
    · exact size_vaultCode_ne h.1
    · exact size_assetCode_ne h.1
  deleg w h p hp := by
    rcases hp with rfl | rfl
    · obtain ⟨i, -, hc⟩ := h.1.vaultCode
      rw [hc]; exact Shares.delegatedAddress?_code i
    · obtain ⟨ia, hc⟩ := h.1.assetCode
      rw [hc]; exact delegatedAddress?_assetCode ia

/-! ## Frame summaries -/

/-- **The frame summary** a dangerous frame of the vault or the asset must satisfy: if it
succeeds, the world is deployed and its abstraction is reached from the frame's starting
abstraction by admitted calls (one for a modelled state-changing function, none for a view).
Reverts and exceptional halts are unconstrained: the frame's snapshot is restored. -/
def FrameOk (crypto : Crypto) (vault asset : Address) (Act : List Address) (K : VCall → Prop)
    (m : Machine) : Prop :=
  Halts m (fun mf o => ∀ out, o = .success out → Deployed mf.world vault asset ∧
    ∃ cs : List VCall, (∀ c ∈ cs, Admitted Act K c) ∧
      AgreeOn (ActorPairs Act) (abs crypto mf.world vault asset)
        (Solmate.exec (abs crypto m.world vault asset) (cs.map VCall.op)))

/-- **A `FrameOk` frame keeps `Follows`**, whatever its outcome. -/
theorem follows_of_frameOk (hs : SlotsOk crypto vault Act)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {G : Nat} {m : Machine}
    (hd : DangerStart (Prot vault asset) (Follows crypto vault asset Act K w₀) G m)
    (h : FrameOk crypto vault asset Act K m) :
    Halts m (fun mf o => Follows crypto vault asset Act K w₀ (frameResult mf o).2.1) := by
  have hw : Follows crypto vault asset Act K w₀ m.world := goodOk.keep _ _ hd.snapshot hd.keep
  obtain ⟨ko, ks, hfr⟩ := hd.fresh
  refine h.mono fun mf o hsf hpost => ?_
  have hk : mf.frame.kind = .call ko ks := by rw [hsf.kind, hfr]; rfl
  have hsnap : mf.frame.snapshot = m.frame.snapshot := hsf.snapshot
  cases o with
  | success out =>
    rw [frameResult_success_call hk]
    obtain ⟨hdep, cs, hcs, ha⟩ := hpost out rfl
    exact hw.trans hs hinv hdep hcs ha
  | revert out => rw [frameResult_revert, hsnap]; exact hd.snapshot
  | halt e => rw [frameResult_halt, hsnap]; exact hd.snapshot

/-- **Any top-level message call keeps `Follows`**, given frame summaries of every dangerous
frame it reaches outside dangerous frames (calls made by unprotected code). The message is any `TopOk` message (caller not the vault or the asset, any
target and code, any value and calldata) with at most `G` gas, before Prague or without
EIP-7702 authorizations; the context's hash is `crypto`. -/
theorem processMessageCall_follows (hs : SlotsOk crypto vault Act)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {G fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (hw : Follows crypto vault asset Act K w₀ w)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w msg) (hG : msg.gas ≤ G)
    (hsum : ∀ m, Reaches ctx w tr msg m →
      DangerStart (Prot vault asset) (Follows crypto vault asset Act K w₀) G m →
      (∀ f ∈ m.parents, ¬ Danger (Prot vault asset) f) → FrameOk crypto vault asset Act K m)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    Follows crypto vault asset Act K w₀ r.world :=
  EvmLean.Program.Nested.processMessageCall_good goodOk hw hdeleg hmsg hG
    (fun m hm hd hp => follows_of_frameOk hs hinv hd (hsum m hm hd hp)) hr

end EvmLeanSpecs.Refinement.Nested
