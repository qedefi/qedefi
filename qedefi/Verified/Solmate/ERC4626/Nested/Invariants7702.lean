import Verified.Solmate.ERC4626.Nested.Invariants
import EvmLogic.Program.Nested.Deleg

/-!
# The vault invariants for any transaction, EIP-7702 included

`Verified.Solmate.ERC4626.Nested.Invariants` assumes every transaction is before Prague or
carries no EIP-7702 authorization (`hdeleg`, and the `call` step of `TxStep`). Mainnet runs
Prague, where a type-4 transaction applies authorizations before its top-level message. They
only rewrite the code and nonce of accounts holding empty code or a delegation designator
(`EvmLogic.Program.Delegation`), never the vault's or the asset's, so `Follows` survives them and
a call to the vault or the asset still runs its own code (`processMessageCall_good_7702`).

This module restates the headline theorems without that hypothesis (suffix `_7702`), with the
same other hypotheses; `TxStep7702`/`TxTrace7702` are `TxStep`/`TxTrace` with any transaction,
and contain them (`TxTrace.to7702`).
-/

namespace Verified.Solmate.ERC4626.Nested
open Verified.Solmate.ERC20 QEDefi.ERC4626 QEDefi.Trace
open EvmLean Verified.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Verified.Solmate.Contracts
open QEDefi.Math QEDefi.ERC20 QEDefi.ERC4626.Solmate QEDefi.Trace.Lift
open Verified.Solmate.ERC4626.Invariants
open EvmLogic.Program.Nested (Keep KeepP GoodOk DangerStart Danger TopOk Reaches bottom)

variable {crypto : Crypto} {vault asset : Address} {Act : List Address} {K : VCall → Prop}
  {minGas : Nat}

/-- **Any top-level message call of any transaction keeps `Follows`**, given `FrameOk` for every
dangerous frame started by unprotected code: `processMessageCall_follows` without
`ctx.fork < .prague ∨ ctx.tx.authorizations = []`. -/
theorem processMessageCall_follows_7702 (hs : SlotsOk crypto vault Act) {w₀ : World}
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {G fuel : Nat} {ctx : Context} {w : World}
    {tr : TransientStorage} {msg : Message} {r : MessageResult}
    (hw : Follows crypto vault asset Act K w₀ w)
    (hmsg : TopOk (Prot vault asset) w msg) (hG : msg.gas ≤ G)
    (hsum : ∀ m, Reaches ctx w tr msg m →
      DangerStart (Prot vault asset) (Follows crypto vault asset Act K w₀) G m →
      (∀ f ∈ m.parents, ¬ Danger (Prot vault asset) f) → FrameOk crypto vault asset Act K m)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    Follows crypto vault asset Act K w₀ r.world :=
  EvmLogic.Program.Nested.processMessageCall_good_7702 goodOk hw hmsg hG
    (fun m hm hd hp => follows_of_frameOk hs hinv hd (hsum m hm hd hp)) hr

/-- **One transaction, with the uncovered frames' summaries as a hypothesis** (`PendingFrames`
instead of `TxOk`'s coverage) keeps `Follows`.
Any fork, EIP-7702 authorizations included: `follows_tx_pending` without `hdeleg`. -/
theorem follows_tx_pending_7702 (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) (hpend : PendingFrames crypto vault asset minGas Act K)
    {w₀ w : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hw : Follows crypto vault asset Act K w₀ w) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hmsg : TopOk (Prot vault asset) w msg) (hgas : msg.gas < 2 ^ 64)
    (hadm : ∀ m, Reaches ctx w tr msg m → VaultStart vault asset m →
      (∀ f ∈ m.parents, ¬ Danger (Prot vault asset) f) →
      FrameAdmitted ctx.crypto vault asset Act K m)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    Follows crypto vault asset Act K w₀ r.world := by
  refine processMessageCall_follows_7702 hs hinv hw hmsg (le_refl _) (fun m hm hd hp => ?_) hr
  have hv := DangerStart.vaultStart hd
  have hwm : Follows crypto vault asset Act K w₀ m.world := goodOk.keep _ _ hd.snapshot hd.keep
  have hcr' : m.ctx.crypto = crypto := by rw [hm.ctx]; exact hcr
  have hlt := DangerStart.gasLt hd hgas
  by_cases hc : Covered vault asset minGas m
  · exact frameOk_of_covered hmin hk hs hv hwm.1 (hwm.inv hs hinv) hcr' hlt hc
      (hcr ▸ hadm m hm hv hp)
  · exact hpend m hv hwm.1 (hwm.inv hs hinv) hcr' hlt hc

/-- **One covered transaction keeps `Follows`.**
Any fork, EIP-7702 authorizations included: `follows_tx` without `hdeleg`. -/
theorem follows_tx_7702 (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hw : Follows crypto vault asset Act K w₀ w) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hmsg : TopOk (Prot vault asset) w msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOk vault asset minGas Act K ctx w tr msg)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    Follows crypto vault asset Act K w₀ r.world := by
  refine processMessageCall_follows_7702 hs hinv hw hmsg (le_refl _) (fun m hm hd hp => ?_) hr
  have hv := DangerStart.vaultStart hd
  have hwm : Follows crypto vault asset Act K w₀ m.world := goodOk.keep _ _ hd.snapshot hd.keep
  have hcr' : m.ctx.crypto = crypto := by rw [hm.ctx]; exact hcr
  exact frameOk_of_covered hmin hk hs hv hwm.1 (hwm.inv hs hinv) hcr' (DangerStart.gasLt hd hgas)
    (hok m hm hv hp).1 (hcr ▸ (hok m hm hv hp).2)

/-! ## Sequences of transactions -/

/-- **One step of a sequence of arbitrary transactions**: a covered top-level message call (any
fork, EIP-7702 authorizations included), or any transition that keeps the storage and code of the
vault and the asset. `TxStep` without `hdeleg`. -/
inductive TxStep7702 (crypto : Crypto) (vault asset : Address) (minGas : Nat)
    (Act : List Address) (K : VCall → Prop) : World → World → Prop
  | call {w : World} {ctx : Context} {tr : TransientStorage} {msg : Message} {fuel : Nat}
      {r : MessageResult} : ctx.crypto = crypto → TopOk (Prot vault asset) w msg →
      msg.gas < 2 ^ 64 → TxOk vault asset minGas Act K ctx w tr msg →
      processMessageCall fuel ctx w tr msg = .ok r →
      TxStep7702 crypto vault asset minGas Act K w r.world
  | env {w w' : World} : EnvStep vault asset w w' → TxStep7702 crypto vault asset minGas Act K w w'

/-- **Sequences of arbitrary transactions**, EIP-7702 included. -/
def TxTrace7702 (crypto : Crypto) (vault asset : Address) (minGas : Nat) (Act : List Address)
    (K : VCall → Prop) : World → World → Prop :=
  Relation.ReflTransGen (TxStep7702 crypto vault asset minGas Act K)

/-- **Every sequence of covered transactions keeps `Follows`.**
Any fork, EIP-7702 authorizations included: `follows_trace` without `hdeleg`. -/
theorem follows_trace_7702 (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTrace7702 crypto vault asset minGas Act K w₀ w) :
    Follows crypto vault asset Act K w₀ w := by
  induction htr with
  | refl => exact follows_refl hdep
  | tail _ hst ih =>
    cases hst with
    | call hcr hmsg hgas hok hr => exact follows_tx_7702 hmin hk hs hinv ih hcr hmsg hgas hok hr
    | env he => exact ih.env he

/-! ## Headline theorems -/

/-- **The lifting theorem for arbitrary transactions.** After any covered transaction from a
deployed world with well-formed ledgers: deployed, well formed, and `abs` agrees (up to
non-actor allowances) with the model's execution of the admitted calls it committed.
Any fork, EIP-7702 authorizations included: `lift_any_tx` without `hdeleg`. -/
theorem lift_any_tx_7702 (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOk vault asset minGas Act K ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) :
    Deployed r.world vault asset ∧ Solmate.Inv (abs crypto r.world vault asset) ∧
      ∃ cs : List VCall, (∀ c ∈ cs, Admitted Act K c) ∧
        AgreeOn (ActorPairs Act) (abs crypto r.world vault asset)
          (Solmate.exec (abs crypto w₀ vault asset) (cs.map VCall.op)) := by
  have h := follows_tx_7702 hmin hk hs hinv (follows_refl hdep) hcr hmsg hgas hok hr
  exact ⟨h.1, h.inv hs hinv, h.2⟩

/-- **The lifting theorem for sequences of arbitrary transactions.**
Any fork, EIP-7702 authorizations included: `lift_nested` without `hdeleg`. -/
theorem lift_nested_7702 (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTrace7702 crypto vault asset minGas Act K w₀ w) :
    Deployed w vault asset ∧ Solmate.Inv (abs crypto w vault asset) ∧
      ∃ cs : List VCall, (∀ c ∈ cs, Admitted Act K c) ∧
        AgreeOn (ActorPairs Act) (abs crypto w vault asset)
          (Solmate.exec (abs crypto w₀ vault asset) (cs.map VCall.op)) := by
  have h := follows_trace_7702 hmin hk hs hdep hinv htr
  exact ⟨h.1, h.inv hs hinv, h.2⟩

/-- **Invariants transfer, for sequences of arbitrary transactions**: every model invariant
preserved by every successful step and insensitive to non-actor allowances holds.
Any fork, EIP-7702 authorizations included: `invariant_nested` without `hdeleg`. -/
theorem invariant_nested_7702 (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {I : State Address → Prop}
    (hI : ∀ s op s', Solmate.Inv s → I s → step s op = some s' → I s')
    (hIa : ∀ s t, AgreeOn (ActorPairs Act) s t → I s → I t)
    {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTrace7702 crypto vault asset minGas Act K w₀ w) (hI₀ : I (abs crypto w₀ vault asset)) :
    I (abs crypto w vault asset) := by
  obtain ⟨-, -, cs, -, ha⟩ := lift_nested_7702 hmin hk hs hdep hinv htr
  have := (exec_induction (step := step) (Inv := Solmate.Inv) (fun _ _ _ hi h => Inv_step hi h)
    hI hinv hI₀ (cs.map VCall.op)).2
  rw [← exec_eq] at this
  exact hIa _ _ ha.symm this

/-- **`totalSupply` = Σ `balanceOf`, for sequences of arbitrary transactions**, for the
shares and for the asset, read from storage.
Any fork, EIP-7702 authorizations included: `supply_eq_sum_nested` without `hdeleg`. -/
theorem supply_eq_sum_nested_7702 (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTrace7702 crypto vault asset minGas Act K w₀ w) :
    (w.sload vault 2#256).toNat =
        ∑ a : Address, (w.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (w.sload asset 2#256).toNat =
        ∑ a : Address, (w.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat := by
  obtain ⟨-, hi, -⟩ := lift_nested_7702 hmin hk hs hdep hinv htr
  exact ⟨supply_eq_sum_of_wf hi.2, supply_eq_sum_of_wf hi.1⟩

/-- **Solvency, for sequences of arbitrary transactions**: `Σₐ ⌊shares[a]·T/S⌋ ≤ T`, read from
storage.
Any fork, EIP-7702 authorizations included: `solvent_nested` without `hdeleg`. -/
theorem solvent_nested_7702 (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTrace7702 crypto vault asset minGas Act K w₀ w) :
    ∑ a : Address, sharesAt crypto w vault a * assetsAt crypto w vault asset / supplyAt w vault ≤
      assetsAt crypto w vault asset := by
  obtain ⟨-, hi, -⟩ := lift_nested_7702 hmin hk hs hdep hinv htr
  have := Solmate.solvent _ hi
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)] at this
  simpa only [abs_sharesOf, abs_totalAssets', abs_totalSupply'] using this

/-- **Price monotonicity, for sequences of arbitrary transactions** whose committed calls `cs`
are user operations: unless a prefix of `cs` empties the vault, `T/S` never decreased.
Any fork, EIP-7702 authorizations included: `price_mono_nested` without `hdeleg`. -/
theorem price_mono_nested_7702 (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ w : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (htr : TxTrace7702 crypto vault asset minGas Act (fun c => UserOp vault c.op) w₀ w) :
    ∃ cs : List VCall, (∀ c ∈ cs, (∀ a ∈ c.actors, a ∈ Act) ∧ UserOp vault c.op) ∧
      ((∀ k ≤ cs.length,
          (Solmate.exec (abs crypto w₀ vault asset) ((cs.take k).map VCall.op)).totalSupply ≠ 0) →
        (assetsAt crypto w₀ vault asset : ℚ) / supplyAt w₀ vault ≤
          (assetsAt crypto w vault asset : ℚ) / supplyAt w vault) := by
  obtain ⟨-, -, cs, hcs, ha⟩ := lift_nested_7702 hmin hk hs hdep hinv htr
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

/-- **`totalSupply` = Σ `balanceOf` after one arbitrary covered transaction.**
Any fork, EIP-7702 authorizations included: `supply_eq_sum_any_tx` without `hdeleg`. -/
theorem supply_eq_sum_any_tx_7702 (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOk vault asset minGas Act K ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) :
    (r.world.sload vault 2#256).toNat = ∑ a : Address,
        (r.world.sload vault (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat ∧
      (r.world.sload asset 2#256).toNat = ∑ a : Address,
        (r.world.sload asset (ERC20.balanceSlot crypto ERC20.Layout.solmate a)).toNat := by
  obtain ⟨-, hi, -⟩ := lift_any_tx_7702 hmin hk hs hdep hinv hcr hmsg hgas hok hr
  exact ⟨supply_eq_sum_of_wf hi.2, supply_eq_sum_of_wf hi.1⟩

/-- **Solvency after one arbitrary covered transaction.**
Any fork, EIP-7702 authorizations included: `solvent_any_tx` without `hdeleg`. -/
theorem solvent_any_tx_7702 (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOk vault asset minGas Act K ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) :
    ∑ a : Address, sharesAt crypto r.world vault a * assetsAt crypto r.world vault asset /
        supplyAt r.world vault ≤ assetsAt crypto r.world vault asset := by
  obtain ⟨-, hi, -⟩ := lift_any_tx_7702 hmin hk hs hdep hinv hcr hmsg hgas hok hr
  have := Solmate.solvent _ hi
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)] at this
  simpa only [abs_sharesOf, abs_totalAssets', abs_totalSupply'] using this

theorem txTrace_single_7702 {w : World} {ctx : Context} {tr : TransientStorage} {msg : Message}
    {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hmsg : TopOk (Prot vault asset) w msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOk vault asset minGas Act K ctx w tr msg)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    TxTrace7702 crypto vault asset minGas Act K w r.world :=
  Relation.ReflTransGen.single (.call hcr hmsg hgas hok hr)

/-- **Invariants transfer, after one arbitrary covered transaction.**
Any fork, EIP-7702 authorizations included: `invariant_any_tx` without `hdeleg`. -/
theorem invariant_any_tx_7702 (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {I : State Address → Prop}
    (hI : ∀ s op s', Solmate.Inv s → I s → step s op = some s' → I s')
    (hIa : ∀ s t, AgreeOn (ActorPairs Act) s t → I s → I t)
    {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOk vault asset minGas Act K ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) (hI₀ : I (abs crypto w₀ vault asset)) :
    I (abs crypto r.world vault asset) :=
  invariant_nested_7702 hmin hk hs hI hIa hdep hinv (txTrace_single_7702 hcr hmsg hgas hok hr) hI₀

/-- **Price monotonicity, after one arbitrary covered transaction** whose committed calls are
user operations: unless a prefix of them empties the vault, `T/S` did not decrease.
Any fork, EIP-7702 authorizations included: `price_mono_any_tx` without `hdeleg`. -/
theorem price_mono_any_tx_7702 (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {w₀ : World} (hdep : Deployed w₀ vault asset)
    (hinv : Solmate.Inv (abs crypto w₀ vault asset)) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hmsg : TopOk (Prot vault asset) w₀ msg) (hgas : msg.gas < 2 ^ 64)
    (hok : TxOk vault asset minGas Act (fun c => UserOp vault c.op) ctx w₀ tr msg)
    (hr : processMessageCall fuel ctx w₀ tr msg = .ok r) :
    ∃ cs : List VCall, (∀ c ∈ cs, (∀ a ∈ c.actors, a ∈ Act) ∧ UserOp vault c.op) ∧
      ((∀ k ≤ cs.length,
          (Solmate.exec (abs crypto w₀ vault asset) ((cs.take k).map VCall.op)).totalSupply ≠ 0) →
        (assetsAt crypto w₀ vault asset : ℚ) / supplyAt w₀ vault ≤
          (assetsAt crypto r.world vault asset : ℚ) / supplyAt r.world vault) :=
  price_mono_nested_7702 hmin hk hs hdep hinv (txTrace_single_7702 hcr hmsg hgas hok hr)

/-- Every `TxStep` is a `TxStep7702`. -/
theorem TxStep.to7702 {w w' : World} (h : TxStep crypto vault asset minGas Act K w w') :
    TxStep7702 crypto vault asset minGas Act K w w' := by
  cases h with
  | call hcr _ hmsg hgas hok hr => exact .call hcr hmsg hgas hok hr
  | env he => exact .env he

/-- Every `TxTrace` is a `TxTrace7702`. -/
theorem TxTrace.to7702 {w w' : World} (h : TxTrace crypto vault asset minGas Act K w w') :
    TxTrace7702 crypto vault asset minGas Act K w w' := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail hst.to7702

end Verified.Solmate.ERC4626.Nested
