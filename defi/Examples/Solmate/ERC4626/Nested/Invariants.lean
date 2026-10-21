import Examples.Solmate.ERC4626.Nested.Permit
import Examples.Solmate.ERC4626.Nested.Views

/-!
# The invariants for arbitrary transactions

The headline invariants for any transaction (`*_any_tx`) and any sequence of transactions
(`TxTrace`, `*_nested`): a top-level call to any code that calls the vault and the asset any
number of times, at any depth, with any calldata and value, possibly reverting afterwards.
Hypothesis: `TxOk` (every vault/asset frame started by other code is `Covered` and commits
admitted calls). See `docs/erc4626/details.md` §4.
-/

namespace Examples.Solmate.ERC4626.Nested
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace
open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.Math Defi.ERC20 Defi.ERC4626.Solmate Defi.Trace.Lift
open Examples.Solmate.ERC4626.Invariants
open EvmLogic.Program.Nested (Keep KeepP GoodOk DangerStart Danger TopOk Reaches bottom)

variable {crypto : Crypto} {vault asset : Address} {Act : List Address} {K : VCall → Prop}
  {minGas : Nat}

/-! ## Covered frames -/

/-- A funded call: no value, at least `minGas` gas, room for one more call level (for the
vault, which calls the asset), calldata below `2⁶⁴` bytes. -/
structure FundedCall (vault : Address) (minGas : Nat) (m : Machine) : Prop where
  value : m.frame.msg.value = 0
  gas : minGas ≤ m.frame.gasLeft
  depth : m.frame.msg.currentTarget = vault → m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit
  size : m.frame.msg.data.size < 2 ^ 64

/-- **The frames with a proved frame summary**: a call carrying value (it reverts), or a funded
call executing a modelled function, a covered view, `permit` with `PermitFrame`, an unknown
selector (`UnknownData`) or malformed calldata (`MalformedData`). -/
def Covered (vault asset : Address) (minGas : Nat) (m : Machine) : Prop :=
  (m.frame.msg.value ≠ 0 ∧ 100 ≤ m.frame.gasLeft) ∨
  (FundedCall vault minGas m ∧ ((∃ c, Executes vault asset m c) ∨ ViewData vault asset m ∨
    ((∃ c, PermitData vault asset m c) ∧ PermitFrame m) ∨ UnknownData vault asset m ∨
    MalformedData vault asset m))

/-- **The model calls a frame commits are admitted**: the modelled call it executes, and a
`permit`'s approval, whose owner's nonce slot must also be fresh (`NonceSlotOk`). -/
structure FrameAdmitted (crypto : Crypto) (vault asset : Address) (Act : List Address)
    (K : VCall → Prop) (m : Machine) : Prop where
  calls : ∀ c, Executes vault asset m c → Admitted Act K c
  permits : ∀ c, PermitData vault asset m c → Admitted Act K c ∧ NonceSlotOk crypto Act c.caller

/-- **A covered transaction**: every non-static vault/asset frame started by unprotected code
is `Covered` and `FrameAdmitted`. The vault's own calls into the asset are part of the vault's
frame summary. -/
def TxOk (vault asset : Address) (minGas : Nat) (Act : List Address) (K : VCall → Prop)
    (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message) : Prop :=
  ∀ m, Reaches ctx w tr msg m → VaultStart vault asset m →
    (∀ f ∈ m.parents, ¬ Danger (Prot vault asset) f) →
    Covered vault asset minGas m ∧ FrameAdmitted ctx.crypto vault asset Act K m

/-- **The uncovered frames' summaries** (low gas, the vault at depth 1024, the uncovered
`name`/`symbol`/`DOMAIN_SEPARATOR()`/`permit` cases), as a hypothesis. -/
def PendingFrames (crypto : Crypto) (vault asset : Address) (minGas : Nat) (Act : List Address)
    (K : VCall → Prop) : Prop :=
  ∀ m, VaultStart vault asset m → Deployed m.world vault asset →
    Solmate.Inv (abs crypto m.world vault asset) → m.ctx.crypto = crypto →
    m.frame.gasLeft < 2 ^ 64 → ¬ Covered vault asset minGas m →
    FrameOk crypto vault asset Act K m

theorem frameOk_of_covered (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {m : Machine} (hv : VaultStart vault asset m)
    (hdep : Deployed m.world vault asset) (hinv : Solmate.Inv (abs crypto m.world vault asset))
    (hcr : m.ctx.crypto = crypto) (hlt : m.frame.gasLeft < 2 ^ 64)
    (hc : Covered vault asset minGas m) (hadm : FrameAdmitted crypto vault asset Act K m) :
    FrameOk crypto vault asset Act K m := by
  rcases hc with ⟨hval, hg⟩ | ⟨hf, hx⟩
  · exact frameOk_value hv hdep hval hg
  · have h : FrameHyp crypto vault asset Act minGas m :=
      ⟨hv, hdep, hinv, hcr, ⟨hf.value, hf.gas, hlt, hf.depth, hf.size⟩, hs⟩
    rcases hx with ⟨c, hx⟩ | hx | ⟨⟨c, hx⟩, hp⟩ | hx | hx
    · exact frameOk_of_executes hmin hk h hx (hadm.calls c hx)
    · exact frameOk_view (by omega) h hx
    · exact frameOk_permit (by omega) h hp hx (hadm.permits c hx).1 (hadm.permits c hx).2
    · exact frameOk_unknown hv hdep hf.value hf.size (by have := hf.gas; omega) hx
    · exact frameOk_malformed hv hdep hf.value hf.size (by have := hf.gas; omega) hx

theorem DangerStart.gasLt {Good : World → Prop} {G : Nat} {m : Machine}
    (h : DangerStart (Prot vault asset) Good G m) (hG : G < 2 ^ 64) : m.frame.gasLeft < 2 ^ 64 := by
  obtain ⟨o, s, hf⟩ := h.fresh
  have : m.frame.gasLeft = m.frame.msg.gas := by rw [hf]; rfl
  rw [this]; exact Nat.lt_of_le_of_lt h.gas hG

/-! ## Direct transactions -/

/-- **A direct transaction to the vault or the asset is covered** when its own frame is (every
later vault/asset frame runs above it). -/
theorem txOk_direct {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hdel : delegatedAddress? msg.code = none) (hprot : Prot vault asset msg.currentTarget)
    (hstatic : msg.isStatic = false)
    (hcov : ∀ m : Machine, m.frame.msg = msg → m.frame.gasLeft = msg.gas →
      Covered vault asset minGas m ∧ FrameAdmitted ctx.crypto vault asset Act K m) :
    TxOk vault asset minGas Act K ctx w tr msg := by
  intro m hm hv hp
  have hb := hm.bottom
  rw [EvmLean.Interpreter.applyTopLevelDelegation_eq hdeleg hdel] at hb
  cases hpar : m.parents with
  | nil =>
    have hmsg : m.frame.msg = msg := by
      have : bottom m = m.frame := by simp [bottom, hpar]
      rw [← this]; exact hb
    obtain ⟨-, -, -, -, -, hg, -⟩ := hv.fresh.frame
    exact hcov m hmsg (by rw [hg, hmsg])
  | cons f fs =>
    exfalso
    have hmem : bottom m ∈ m.parents := by
      rw [hpar]
      simp only [bottom, hpar]
      cases h' : (f :: fs).getLast? with
      | none => simp at h'
      | some l => exact List.mem_of_getLast? h'
    refine hp _ hmem ⟨?_, ?_⟩
    · rw [hb]; exact hprot
    · rw [hb]; exact hstatic

/-! ## One transaction -/

/-- **One transaction, with the uncovered frames' summaries as a hypothesis** (`PendingFrames`
instead of `TxOk`'s coverage) keeps `Follows`. -/
theorem follows_tx_pending (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) (hpend : PendingFrames crypto vault asset minGas Act K)
    {w₀ w : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hw : Follows crypto vault asset Act K w₀ w) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w msg) (hgas : msg.gas < 2 ^ 64)
    (hadm : ∀ m, Reaches ctx w tr msg m → VaultStart vault asset m →
      (∀ f ∈ m.parents, ¬ Danger (Prot vault asset) f) →
      FrameAdmitted ctx.crypto vault asset Act K m)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    Follows crypto vault asset Act K w₀ r.world := by
  refine processMessageCall_follows hs hinv hw hdeleg hmsg (le_refl _) (fun m hm hd hp => ?_) hr
  have hv := DangerStart.vaultStart hd
  have hwm : Follows crypto vault asset Act K w₀ m.world := goodOk.keep _ _ hd.snapshot hd.keep
  have hcr' : m.ctx.crypto = crypto := by rw [hm.ctx]; exact hcr
  have hlt := DangerStart.gasLt hd hgas
  by_cases hc : Covered vault asset minGas m
  · exact frameOk_of_covered hmin hk hs hv hwm.1 (hwm.inv hs hinv) hcr' hlt hc
      (hcr ▸ hadm m hm hv hp)
  · exact hpend m hv hwm.1 (hwm.inv hs hinv) hcr' hlt hc

/-- **One covered transaction keeps `Follows`.** -/
theorem follows_tx (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hw : Follows crypto vault asset Act K w₀ w) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOk vault asset minGas Act K ctx w tr msg)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    Follows crypto vault asset Act K w₀ r.world := by
  refine processMessageCall_follows hs hinv hw hdeleg hmsg (le_refl _) (fun m hm hd hp => ?_) hr
  have hv := DangerStart.vaultStart hd
  have hwm : Follows crypto vault asset Act K w₀ m.world := goodOk.keep _ _ hd.snapshot hd.keep
  have hcr' : m.ctx.crypto = crypto := by rw [hm.ctx]; exact hcr
  exact frameOk_of_covered hmin hk hs hv hwm.1 (hwm.inv hs hinv) hcr' (DangerStart.gasLt hd hgas)
    (hok m hm hv hp).1 (hcr ▸ (hok m hm hv hp).2)

/-! ## Sequences of transactions -/

/-- **One step of a sequence of arbitrary transactions**: a covered top-level message call, or
any transition that keeps the storage and code of the vault and the asset. -/
inductive TxStep (crypto : Crypto) (vault asset : Address) (minGas : Nat) (Act : List Address)
    (K : VCall → Prop) : World → World → Prop
  | call {w : World} {ctx : Context} {tr : TransientStorage} {msg : Message} {fuel : Nat}
      {r : MessageResult} : ctx.crypto = crypto →
      (ctx.fork < .prague ∨ ctx.tx.authorizations = []) → TopOk (Prot vault asset) w msg →
      msg.gas < 2 ^ 64 → TxOk vault asset minGas Act K ctx w tr msg →
      processMessageCall fuel ctx w tr msg = .ok r → TxStep crypto vault asset minGas Act K w r.world
  | env {w w' : World} : EnvStep vault asset w w' → TxStep crypto vault asset minGas Act K w w'

/-- **Sequences of arbitrary transactions.** -/
def TxTrace (crypto : Crypto) (vault asset : Address) (minGas : Nat) (Act : List Address)
    (K : VCall → Prop) : World → World → Prop :=
  Relation.ReflTransGen (TxStep crypto vault asset minGas Act K)

theorem Follows.env {w₀ w w' : World} (h : Follows crypto vault asset Act K w₀ w)
    (he : EnvStep vault asset w w') : Follows crypto vault asset Act K w₀ w' := by
  obtain ⟨hd, cs, hcs, ha⟩ := h
  refine ⟨hd.of_code he.2.2.1 he.2.2.2, cs, hcs, ?_⟩
  rw [abs_congr he.1 he.2.1]; exact ha

/-- **Every sequence of covered transactions keeps `Follows`.** -/
theorem follows_trace (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTrace crypto vault asset minGas Act K w₀ w) :
    Follows crypto vault asset Act K w₀ w := by
  induction htr with
  | refl => exact follows_refl hdep
  | tail _ hst ih =>
    cases hst with
    | call hcr hdeleg hmsg hgas hok hr => exact follows_tx hmin hk hs hinv ih hcr hdeleg hmsg hgas hok hr
    | env he => exact ih.env he

/-! ## Headline theorems -/

/-- **The lifting theorem for arbitrary transactions.** After any covered transaction from a
deployed world with well-formed ledgers: deployed, well formed, and `abs` agrees (up to
non-actor allowances) with the model's execution of the admitted calls it committed. -/
theorem lift_any_tx (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOk vault asset minGas Act K ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) :
    Deployed r.world vault asset ∧ Solmate.Inv (abs crypto r.world vault asset) ∧
      ∃ cs : List VCall, (∀ c ∈ cs, Admitted Act K c) ∧
        AgreeOn (ActorPairs Act) (abs crypto r.world vault asset)
          (Solmate.exec (abs crypto w₀ vault asset) (cs.map VCall.op)) := by
  have h := follows_tx hmin hk hs hinv (follows_refl hdep) hcr hdeleg hmsg hgas hok hr
  exact ⟨h.1, h.inv hs hinv, h.2⟩

/-- **The lifting theorem for sequences of arbitrary transactions.** -/
theorem lift_nested (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTrace crypto vault asset minGas Act K w₀ w) :
    Deployed w vault asset ∧ Solmate.Inv (abs crypto w vault asset) ∧
      ∃ cs : List VCall, (∀ c ∈ cs, Admitted Act K c) ∧
        AgreeOn (ActorPairs Act) (abs crypto w vault asset)
          (Solmate.exec (abs crypto w₀ vault asset) (cs.map VCall.op)) := by
  have h := follows_trace hmin hk hs hdep hinv htr
  exact ⟨h.1, h.inv hs hinv, h.2⟩

/-- **Invariants transfer, for sequences of arbitrary transactions**: every model invariant
preserved by every successful step and insensitive to non-actor allowances holds. -/
theorem invariant_nested (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {I : State Address → Prop}
    (hI : ∀ s op s', Solmate.Inv s → I s → step s op = some s' → I s')
    (hIa : ∀ s t, AgreeOn (ActorPairs Act) s t → I s → I t)
    {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTrace crypto vault asset minGas Act K w₀ w) (hI₀ : I (abs crypto w₀ vault asset)) :
    I (abs crypto w vault asset) := by
  obtain ⟨-, -, cs, -, ha⟩ := lift_nested hmin hk hs hdep hinv htr
  have := (exec_induction (step := step) (Inv := Solmate.Inv) (fun _ _ _ hi h => Inv_step hi h)
    hI hinv hI₀ (cs.map VCall.op)).2
  rw [← exec_eq] at this
  exact hIa _ _ ha.symm this

/-- **`totalSupply` = Σ `balanceOf`, for sequences of arbitrary transactions**, for the
shares and for the asset, read from storage. -/
theorem supply_eq_sum_nested (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTrace crypto vault asset minGas Act K w₀ w) :
    (w.sload vault 2#256).toNat =
        ∑ a : Address, (w.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (w.sload asset 2#256).toNat =
        ∑ a : Address, (w.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat := by
  obtain ⟨-, hi, -⟩ := lift_nested hmin hk hs hdep hinv htr
  exact ⟨supply_eq_sum_of_wf hi.2, supply_eq_sum_of_wf hi.1⟩

/-- **Solvency, for sequences of arbitrary transactions**: `Σₐ ⌊shares[a]·T/S⌋ ≤ T`, read from
storage. -/
theorem solvent_nested (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTrace crypto vault asset minGas Act K w₀ w) :
    ∑ a : Address, sharesAt crypto w vault a * assetsAt crypto w vault asset / supplyAt w vault ≤
      assetsAt crypto w vault asset := by
  obtain ⟨-, hi, -⟩ := lift_nested hmin hk hs hdep hinv htr
  have := Solmate.solvent _ hi
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)] at this
  simpa only [abs_sharesOf, abs_totalAssets', abs_totalSupply'] using this

/-- **Price monotonicity, for sequences of arbitrary transactions** whose committed calls `cs`
are user operations: unless a prefix of `cs` empties the vault, `T/S` never decreased. -/
theorem price_mono_nested (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTrace crypto vault asset minGas Act (fun c => UserOp vault c.op) w₀ w) :
    ∃ cs : List VCall, (∀ c ∈ cs, (∀ a ∈ c.actors, a ∈ Act) ∧ UserOp vault c.op) ∧
      ((∀ k ≤ cs.length,
          (Solmate.exec (abs crypto w₀ vault asset) ((cs.take k).map VCall.op)).totalSupply ≠ 0) →
        (assetsAt crypto w₀ vault asset : ℚ) / supplyAt w₀ vault ≤
          (assetsAt crypto w vault asset : ℚ) / supplyAt w vault) := by
  obtain ⟨-, -, cs, hcs, ha⟩ := lift_nested hmin hk hs hdep hinv htr
  refine ⟨cs, hcs, fun hS => ?_⟩
  have hmodel := price_exec_mono (s := abs crypto w₀ vault asset) hinv
    (ops := cs.map VCall.op) (fun op hop => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hop
      exact (hcs c hc).2) (fun k hk' => by
        have := hS k (by simpa using hk')
        rw [exec_eq, List.map_take] at this
        exact this)
  rw [exec_eq] at ha
  have hp := ha.price
  unfold State.price at hp hmodel
  rw [abs_totalAssets', abs_totalSupply'] at hp hmodel
  rw [hp]; exact hmodel

/-- **`totalSupply` = Σ `balanceOf` after one arbitrary covered transaction.** -/
theorem supply_eq_sum_any_tx (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOk vault asset minGas Act K ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) :
    (r.world.sload vault 2#256).toNat = ∑ a : Address,
        (r.world.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (r.world.sload asset 2#256).toNat = ∑ a : Address,
        (r.world.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat := by
  obtain ⟨-, hi, -⟩ := lift_any_tx hmin hk hs hdep hinv hcr hdeleg hmsg hgas hok hr
  exact ⟨supply_eq_sum_of_wf hi.2, supply_eq_sum_of_wf hi.1⟩

/-- **Solvency after one arbitrary covered transaction.** -/
theorem solvent_any_tx (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOk vault asset minGas Act K ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) :
    ∑ a : Address, sharesAt crypto r.world vault a * assetsAt crypto r.world vault asset /
        supplyAt r.world vault ≤ assetsAt crypto r.world vault asset := by
  obtain ⟨-, hi, -⟩ := lift_any_tx hmin hk hs hdep hinv hcr hdeleg hmsg hgas hok hr
  have := Solmate.solvent _ hi
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)] at this
  simpa only [abs_sharesOf, abs_totalAssets', abs_totalSupply'] using this

theorem txTrace_single {w : World} {ctx : Context} {tr : TransientStorage} {msg : Message}
    {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOk vault asset minGas Act K ctx w tr msg)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    TxTrace crypto vault asset minGas Act K w r.world :=
  Relation.ReflTransGen.single (.call hcr hdeleg hmsg hgas hok hr)

/-- **Invariants transfer, after one arbitrary covered transaction.** -/
theorem invariant_any_tx (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {I : State Address → Prop}
    (hI : ∀ s op s', Solmate.Inv s → I s → step s op = some s' → I s')
    (hIa : ∀ s t, AgreeOn (ActorPairs Act) s t → I s → I t)
    {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOk vault asset minGas Act K ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) (hI₀ : I (abs crypto w₀ vault asset)) :
    I (abs crypto r.world vault asset) :=
  invariant_nested hmin hk hs hI hIa hdep hinv (txTrace_single hcr hdeleg hmsg hgas hok hr) hI₀

/-- **Price monotonicity, after one arbitrary covered transaction** whose committed calls are
user operations: unless a prefix of them empties the vault, `T/S` did not decrease. -/
theorem price_mono_any_tx (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOk vault asset minGas Act (fun c => UserOp vault c.op) ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) :
    ∃ cs : List VCall, (∀ c ∈ cs, (∀ a ∈ c.actors, a ∈ Act) ∧ UserOp vault c.op) ∧
      ((∀ k ≤ cs.length,
          (Solmate.exec (abs crypto w₀ vault asset) ((cs.take k).map VCall.op)).totalSupply ≠ 0) →
        (assetsAt crypto w₀ vault asset : ℚ) / supplyAt w₀ vault ≤
          (assetsAt crypto r.world vault asset : ℚ) / supplyAt r.world vault) :=
  price_mono_nested hmin hk hs hdep hinv (txTrace_single hcr hdeleg hmsg hgas hok hr)

end Examples.Solmate.ERC4626.Nested
