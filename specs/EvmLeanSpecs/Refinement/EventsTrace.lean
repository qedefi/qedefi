import EvmLeanSpecs.Refinement.EventsEntry
import EvmLeanSpecs.Refinement.EventsAsset
import EvmLeanSpecs.Refinement.EventsShares
import EvmLeanSpecs.Refinement.InvariantsDepositMint

/-!
# The event stream of a trace

The trace-level corollary of the per-call event theorems: along any trace of modelled
top-level calls (interleaved with environment steps), the logs of the calls' results,
concatenated in order, are the encoding of the model's event stream
`Solmate.stream (abs w₀) ops` from the initial world's abstraction.

* `CallStepLogs … w c w' L`: `CallStep` (a terminating top-level call `c` from `w` to `w'`)
  whose result has logs `L`; `LogTrace … w₀ cs w L`: a trace (`Invariants.Trace`) recording
  the concatenated logs `L` of its calls (environment steps contribute nothing: their logs are
  not about the modelled calls).
* `OpEventsAt … c`: the per-call obligation, in the shape of `OpRefinesAt`: under `SlotsOk`,
  from a deployed world with a well-formed abstraction, a call `c` has the logs
  `encode vault asset (events (abs w) c.op)`. `opEvents_all`: every call kind, from the
  top-level theorems `*_events_call` (`250000 ≤ minGas`, the fixed-slot hypothesis of
  `refinesFor_all_of`).
* `events_agree`: the model's events only read what `AgreeOn` keeps (balances, supplies,
  counters, the allowances of actor pairs), so the drift of the concrete abstraction from
  `Solmate.exec` (up to non-actor allowances) does not change them.
* **`trace_logs`**: `LogTrace … w₀ cs w L` from a deployed `w₀` with `Solmate.Inv (abs w₀)`,
  actors in `Act`, under `SlotsOk` and the fixed-slot hypothesis ⇒
  `L = encode vault asset (Solmate.stream (abs crypto w₀ vault asset) (cs.map VCall.op))`.
-/

namespace EvmLeanSpecs.Refinement.Invariants

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

/-! ## Events only read what agreement keeps -/

/-- Related options are both `some` or both `none`. -/
theorem rel_isSome {α β : Type} {R : α → β → Prop} {a : Option α} {b : Option β}
    (h : Option.Rel R a b) : a.isSome = b.isSome := by
  cases h <;> rfl

/-- The events of an entry point only depend on the returned amount. -/
theorem rel_snd {β : Type} {R : State Address → State Address → Prop}
    {a b : Option (State Address × ℕ)} (h : Option.Rel (fun x y => R x.1 y.1 ∧ x.2 = y.2) a b)
    (f : Option (State Address × ℕ) → β) (hf : ∀ s t v, f (some (s, v)) = f (some (t, v))) :
    f a = f b := by
  cases h with
  | none => rfl
  | some hxy =>
    rename_i x y
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    obtain ⟨-, rfl⟩ := hxy
    exact hf _ _ _

/-- **The model's events respect agreement** on operations that read only allowances in
`G`. -/
theorem events_agree {G : Address → Address → Prop} {s t : State Address} (h : AgreeOn G s t)
    {op : Op Address} (hr : Reads G s.self op) : events s op = events t op := by
  cases op with
  | deposit c a r =>
    simp only [events]
    rw [← h.self]
    exact rel_snd (deposit_rel h hr a) _ fun _ _ _ => rfl
  | mint c n r =>
    simp only [events]
    rw [← h.self]
    exact rel_snd (mint_rel h hr n) _ fun _ _ _ => rfl
  | withdraw c a r o =>
    simp only [events]
    rw [← h.self]
    exact rel_snd (withdraw_rel h hr a) _ fun _ _ _ => rfl
  | redeem c n r o =>
    simp only [events]
    rw [← h.self]
    exact rel_snd (redeem_rel h hr n) _ fun _ _ _ => rfl
  | transfer c d v =>
    simp only [events, Events.transfer, rel_isSome (h.shares.transfer c d v)]
  | transferFrom c src d v =>
    simp only [events, Events.transferFrom, rel_isSome (h.shares.transferFrom hr d v)]
  | approve c sp v => rfl
  | assetTransfer c d v =>
    simp only [events, Events.transfer, rel_isSome (h.asset.transfer c d v)]
  | assetTransferFrom c src d v =>
    simp only [events, Events.transferFrom, rel_isSome (h.asset.transferFrom hr d v)]
  | assetApprove c sp v => rfl
  | assetMint d v => simp only [events, Events.mint, rel_isSome (h.asset.mint d v)]
  | assetBurn src v => simp only [events, Events.burn, rel_isSome (h.asset.burn src v)]

/-! ## Calls with their logs -/

/-- **A modelled call with its logs**: `CallStep` whose result has the logs `L`. -/
def CallStepLogs (crypto : Crypto) (vault asset : Address) (minGas : Nat) (w : World)
    (c : VCall) (w' : World) (L : Array Log) : Prop :=
  ∃ (ctx : Context) (tr : TransientStorage) (gas : Nat) (wa : AddressSet) (wk : StorageKeySet)
    (r : MessageResult),
    ctx.crypto = crypto ∧ (ctx.fork < .prague ∨ ctx.tx.authorizations = []) ∧
    minGas ≤ gas ∧ gas < 2 ^ 64 ∧ c.caller ≠ vault ∧ c.caller ≠ asset ∧
    Terminates ctx w tr (callMsg (w.code (c.target vault asset)) (c.target vault asset) c.caller
      c.data gas wa wk) r ∧
    r.world = w' ∧ r.logs = L

/-- A call with its logs is a call. -/
theorem CallStepLogs.callStep {w w' : World} {c : VCall} {L : Array Log}
    (h : CallStepLogs crypto vault asset minGas w c w' L) :
    CallStep crypto vault asset minGas w c w' :=
  let ⟨ctx, tr, gas, wa, wk, r, h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := h
  ⟨ctx, tr, gas, wa, wk, r, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **The per-call events obligation** of call `c`, in the shape of `OpRefinesAt`. -/
def OpEventsAt (crypto : Crypto) (vault asset : Address) (minGas : Nat) (Act : List Address)
    (c : VCall) : Prop :=
  SlotsOk crypto vault Act → (∀ a ∈ c.actors, a ∈ Act) →
    ∀ w w' L, Deployed w vault asset → Inv (abs crypto w vault asset) →
      CallStepLogs crypto vault asset minGas w c w' L →
      L = encode vault asset (events (abs crypto w vault asset) c.op)

/-- `OpEventsAt` from a top-level theorem about every large enough fuel. -/
theorem opEvents_of {c : VCall}
    (h : SlotsOk crypto vault Act → (∀ a ∈ c.actors, a ∈ Act) →
      ∀ (w : World) (ctx : Context) (tr : TransientStorage) (gas : Nat) (wa : AddressSet)
        (wk : StorageKeySet), ctx.crypto = crypto → Deployed w vault asset →
        Inv (abs crypto w vault asset) → (ctx.fork < .prague ∨ ctx.tx.authorizations = []) →
        minGas ≤ gas → gas < 2 ^ 64 →
        ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
          (callMsg (w.code (c.target vault asset)) (c.target vault asset) c.caller c.data gas wa
            wk) = .ok res ∧
          res.logs = encode vault asset (events (abs crypto w vault asset) c.op)) :
    OpEventsAt crypto vault asset minGas Act c := by
  rintro hs hact w w' L hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, hg', -, -, ⟨n, hn⟩,
    -, hL⟩
  obtain ⟨n', hn'⟩ := h hs hact w ctx tr gas wa wk hcr hdep hinv hdeleg hg hg'
  obtain ⟨res, hrun, hres⟩ := hn' (max n n') (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hrun
  rw [← hL, hres]

set_option maxHeartbeats 1000000 in
/-- **Every call kind emits the model's events**, under `SlotsOk` and the fixed-slot
hypothesis of `refinesFor_all_of`. -/
theorem opEvents_all (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256]) (c : VCall) :
    OpEventsAt crypto vault asset minGas Act c := by
  apply opEvents_of
  intro hs hact w ctx tr gas wa wk hcr hdep hinv hdeleg hg hg'
  subst hcr
  have hmem : ∀ a ∈ c.actors, a ∈ Act := hact
  cases c with
  | deposit c a r =>
    have hc : c ∈ Act := hmem c (by simp [VCall.actors])
    have hr : r ∈ Act := hmem r (by simp [VCall.actors])
    exact deposit_events_call hdep hdeleg (by omega) hg' hk (hs.bal c hc)
      (hs.bal vault hs.vault_mem) (hs.bal r hr) (hs.allow c hc vault hs.vault_mem) hinv a
  | mint c n r =>
    have hc : c ∈ Act := hmem c (by simp [VCall.actors])
    have hr : r ∈ Act := hmem r (by simp [VCall.actors])
    exact mint_events_call hdep hdeleg (by omega) hg' hk (hs.bal c hc)
      (hs.bal vault hs.vault_mem) (hs.bal r hr) (hs.allow c hc vault hs.vault_mem) hinv n
  | withdraw c a r o =>
    have hc : c ∈ Act := hmem c (by simp [VCall.actors])
    have hr : r ∈ Act := hmem r (by simp [VCall.actors])
    have ho : o ∈ Act := hmem o (by simp [VCall.actors])
    exact withdraw_events_call hdep hdeleg (by omega) hg'
      (outSlots_of hs (KeccakAvoids.sub hk (by simp)) hc hr ho) hinv a
  | redeem c n r o =>
    have hc : c ∈ Act := hmem c (by simp [VCall.actors])
    have hr : r ∈ Act := hmem r (by simp [VCall.actors])
    have ho : o ∈ Act := hmem o (by simp [VCall.actors])
    exact redeem_events_call hdep hdeleg (by omega) hg'
      (outSlots_of hs (KeccakAvoids.sub hk (by simp)) hc hr ho) hinv n
  | transfer c d v =>
    exact Shares.transfer_events_call hdep hdeleg (by omega) d v
  | transferFrom c src d v =>
    have hc : c ∈ Act := hmem c (by simp [VCall.actors])
    have hsr : src ∈ Act := hmem src (by simp [VCall.actors])
    exact Shares.transferFrom_events_call hdep hdeleg (by omega) (hs.allow src hsr c hc) d v
  | approve c sp v =>
    exact Shares.approve_events_call hdep hdeleg (by omega) sp v
  | assetTransfer c d v =>
    exact assetTransfer_events_call hdep hdeleg (by omega) d v
  | assetTransferFrom c src d v =>
    have hc : c ∈ Act := hmem c (by simp [VCall.actors])
    have hsr : src ∈ Act := hmem src (by simp [VCall.actors])
    exact assetTransferFrom_events_call hdep hdeleg (by omega) (hs.allow src hsr c hc) d v
  | assetApprove c sp v =>
    exact assetApprove_events_call hdep hdeleg (by omega) sp v
  | assetMint c d v =>
    exact assetMint_events_call hdep hdeleg (by omega) d v
  | assetBurn c src v =>
    exact assetBurn_events_call hdep hdeleg (by omega) src v

/-! ## Traces with logs -/

/-- **A trace recording the logs of its calls**, concatenated in order (environment steps
contribute none). -/
inductive LogTrace (crypto : Crypto) (vault asset : Address) (minGas : Nat) :
    World → List VCall → World → Array Log → Prop
  /-- The empty trace. -/
  | refl (w : World) : LogTrace crypto vault asset minGas w [] w #[]
  /-- An environment step, then a trace. -/
  | env {w w' w'' : World} {cs : List VCall} {L : Array Log} :
      EnvStep vault asset w w' → LogTrace crypto vault asset minGas w' cs w'' L →
      LogTrace crypto vault asset minGas w cs w'' L
  /-- A call with logs `L₁`, then a trace with logs `L₂`. -/
  | call {w w' w'' : World} {c : VCall} {cs : List VCall} {L₁ L₂ : Array Log} :
      CallStepLogs crypto vault asset minGas w c w' L₁ →
      LogTrace crypto vault asset minGas w' cs w'' L₂ →
      LogTrace crypto vault asset minGas w (c :: cs) w'' (L₁ ++ L₂)

/-- A trace with logs is a trace. -/
theorem LogTrace.trace {w w' : World} {cs : List VCall} {L : Array Log}
    (h : LogTrace crypto vault asset minGas w cs w' L) : Trace crypto vault asset minGas w cs w' := by
  induction h with
  | refl w => exact Trace.nil w
  | env he _ ih => exact Trace.env he ih
  | call hc _ ih => exact Trace.cons hc.callStep ih

/-- The logs of a trace follow the event stream of any model state the initial abstraction
agrees with. -/
theorem logTrace_stream (hs : SlotsOk crypto vault Act)
    (hR : RefinesFor crypto vault asset minGas Act (fun _ => True))
    (hE : ∀ c, OpEventsAt crypto vault asset minGas Act c) {w w' : World} {cs : List VCall}
    {L : Array Log} (htr : LogTrace crypto vault asset minGas w cs w' L)
    (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act) (hdep : Deployed w vault asset)
    {s : State Address} (hsi : Inv s) (hself : s.self = vault)
    (hag : AgreeOn (ActorPairs Act) (abs crypto w vault asset) s) :
    L = encode vault asset (stream s (cs.map VCall.op)) := by
  have href := refinement (K := fun _ => True) (minGas := minGas) (asset := asset) hs
    (fun c _ => hR c trivial)
  induction htr generalizing s with
  | refl => rfl
  | env he _ ih =>
    obtain ⟨hdep', habs⟩ := href.env _ _ hdep he
    exact ih hact hdep' hsi hself (by
      have : abs crypto _ vault asset = abs crypto _ vault asset := habs
      rw [this]; exact hag)
  | @call w₁ w₂ w₃ c cs L₁ L₂ hc _ ih =>
    have hokc : ∀ a ∈ c.actors, a ∈ Act := hact c (by simp)
    have hi : Inv (abs crypto w₁ vault asset) := hag.symm.inv hsi
    obtain ⟨hdep₂, hag₂⟩ := href.call_stepD (w := w₁) (op := c) hdep ⟨hi, rfl⟩ ⟨hokc, trivial⟩
      hc.callStep
    have hreads : Reads (ActorPairs Act) (abs crypto w₁ vault asset).self c.op :=
      reads_of_actors hs.vault_mem hokc
    have hev : events (abs crypto w₁ vault asset) c.op = events s c.op := events_agree hag hreads
    have hL₁ := hE c hs hokc w₁ w₂ L₁ hdep hi hc
    have hstep : AgreeOn (ActorPairs Act) (stepD step (abs crypto w₁ vault asset) c.op)
        (stepD step s c.op) := stepD_agree hag hreads
    have hs' : Inv ((step s c.op).getD s) := by
      cases e : step s c.op with
      | none => exact hsi
      | some s' => exact Inv_step hsi e
    have hself' : ((step s c.op).getD s).self = vault := by
      rw [← hself]; exact self_stepD s c.op
    have := ih (fun c' hc' => hact c' (by simp [hc'])) hdep₂ hs' hself' (hag₂.trans hstep)
    rw [hL₁, hev, this]
    simp only [List.map_cons, stream, encode_append]

/-- **The event stream of a trace**: along any trace of modelled top-level calls (any callers
and arguments, actors in `Act`, interleaved with environment steps) from a deployed world with
well-formed ledgers, under `SlotsOk` and the fixed-slot hypothesis, the concatenated logs of
the calls' results are the encoding of the model's event stream from the initial
abstraction. -/
theorem trace_logs (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} {cs : List VCall} {L : Array Log}
    (htr : LogTrace crypto vault asset minGas w₀ cs w L)
    (hact : ∀ c ∈ cs, ∀ a ∈ c.actors, a ∈ Act) (hdep : Deployed w₀ vault asset)
    (hinv : Inv (abs crypto w₀ vault asset)) :
    L = encode vault asset (stream (abs crypto w₀ vault asset) (cs.map VCall.op)) :=
  logTrace_stream hs (refinesFor_all_of hmin hk) (fun c => opEvents_all hmin hk c) htr hact hdep
    hinv rfl (AgreeOn.refl _)

end EvmLeanSpecs.Refinement.Invariants
