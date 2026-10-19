import EvmLeanSpecs.Refinement.NestedViews

/-!
# The invariants for arbitrary transactions

The headline theorems of `InvariantsFinal.lean` hold for traces of top-level calls to the
vault or the asset. This file proves them for **arbitrary transactions**: a top-level message
call from any externally owned account to **any code** — a router, an attacker contract,
another protocol — that calls the vault and the asset any number of times, at any depth, with
any calldata assembled in memory, with or without value, and that may revert (or run out of
gas) after calling them, in which case the EVM's rollback restores the earlier state. And for
sequences of such transactions interleaved with anything that leaves the vault's and the
asset's storage and code alone (`TxTrace`).

## What a transaction must satisfy

`TxOk vault asset minGas Act K ctx w tr msg`: every non-static frame of the vault's or the
asset's code that the transaction starts (`Reaches`, `VaultStart` — a `STATICCALL` frame cannot
write and needs nothing) is **covered** (`Covered`) and the modelled call it executes is
**admitted** (`Admitted Act K`: its actors are in `Act`, its kind admitted by `K`). Covered
frames are those with a proved frame summary:

* calls carrying value (they revert), with at least 100 gas;
* funded calls (no value, at least `minGas` gas, room for one more call level, calldata below
  `2⁶⁴` bytes) executing a modelled state-changing function (`Executes`: deposit, mint, withdraw,
  redeem, the share and asset transfers, approvals, the asset's mint and burn) or one of the
  covered views (`ViewData`).

The uncovered frames — less than `minGas` gas, depth 1024, other selectors (`permit`, `name`,
`symbol`, `nonces`, `DOMAIN_SEPARATOR`, the hook counters, the asset's other views), malformed
calldata — are the pending obligations (`PendingFrames`); `follows_tx_pending` takes them as a
hypothesis instead of `TxOk`'s coverage.

## Hash hypotheses

`SlotsOk crypto vault Act` (fresh balance and allowance slots of the finitely many actors) and
`hk` (no balance slot is slot 2, 6 or 7), as before. The actors are now the addresses
appearing in the vault/asset calls **the transaction executes** (callers — routers included —
receivers, owners, spenders, sources), required by `TxOk` per frame: there is no need to fix
them before knowing the transaction, only to have `Act` contain them.

## Results

* `follows_tx`: one covered transaction from a world following `w₀` ends in a world following
  `w₀` (`Follows`: deployed, abstraction `≈ Solmate.exec (abs w₀)` of admitted calls);
* `follows_trace`: the same for any `TxTrace`;
* `lift_any_tx`, `invariant_any_tx`, `supply_eq_sum_any_tx`, `solvent_any_tx`,
  `price_mono_any_tx` (one transaction) and `lift_nested`, `supply_eq_sum_nested`,
  `solvent_nested`, `price_mono_nested` (sequences of transactions).
-/

namespace EvmLeanSpecs.Refinement.Nested

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift
open EvmLeanSpecs.Refinement.Invariants
open EvmLean.Program.Nested (Keep KeepP GoodOk DangerStart TopOk Reaches)

variable {crypto : Crypto} {vault asset : Address} {Act : List Address} {K : VCall → Prop}
  {minGas : Nat}

/-! ## Covered frames -/

/-- A funded call: no value, at least `minGas` gas, room for one more call level, calldata
below `2⁶⁴` bytes. -/
structure FundedCall (minGas : Nat) (m : Machine) : Prop where
  /-- No value. -/
  value : m.frame.msg.value = 0
  /-- Enough gas. -/
  gas : minGas ≤ m.frame.gasLeft
  /-- Room for one more call level. -/
  depth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit
  /-- Calldata length fits 64 bits. -/
  size : m.frame.msg.data.size < 2 ^ 64

/-- **The frames of the vault and the asset with a proved frame summary**: a call carrying
value (it reverts), or a funded call executing a modelled function or a covered view. -/
def Covered (vault asset : Address) (minGas : Nat) (m : Machine) : Prop :=
  (m.frame.msg.value ≠ 0 ∧ 100 ≤ m.frame.gasLeft) ∨
  (FundedCall minGas m ∧ ((∃ c, Executes vault asset m c) ∨ ViewData vault asset m))

/-- **A covered transaction**: every non-static frame of the vault's or the asset's code it
starts is covered, and the modelled calls they execute are admitted. -/
def TxOk (vault asset : Address) (minGas : Nat) (Act : List Address) (K : VCall → Prop)
    (ctx : Context) (w : World) (tr : TransientStorage) (msg : Message) : Prop :=
  ∀ m, Reaches ctx w tr msg m → VaultStart vault asset m →
    Covered vault asset minGas m ∧ ∀ c, Executes vault asset m c → Admitted Act K c

/-- **The pending obligations**: frame summaries of the frames of the vault and the asset
that are not covered (low gas, depth 1024, `permit`, `name`, `symbol`, `nonces`,
`DOMAIN_SEPARATOR`, the remaining views, malformed calldata), from a deployed world with
well-formed ledgers. -/
def PendingFrames (crypto : Crypto) (vault asset : Address) (minGas : Nat) (Act : List Address)
    (K : VCall → Prop) : Prop :=
  ∀ m, VaultStart vault asset m → Deployed m.world vault asset →
    Solmate.Inv (abs crypto m.world vault asset) → m.ctx.crypto = crypto →
    m.frame.gasLeft < 2 ^ 64 → ¬ Covered vault asset minGas m →
    FrameOk crypto vault asset Act K m

/-- Covered frames satisfy their frame summary. -/
theorem frameOk_of_covered (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) {m : Machine} (hv : VaultStart vault asset m)
    (hdep : Deployed m.world vault asset) (hinv : Solmate.Inv (abs crypto m.world vault asset))
    (hcr : m.ctx.crypto = crypto) (hlt : m.frame.gasLeft < 2 ^ 64)
    (hc : Covered vault asset minGas m) (hadm : ∀ c, Executes vault asset m c → Admitted Act K c) :
    FrameOk crypto vault asset Act K m := by
  rcases hc with ⟨hval, hg⟩ | ⟨hf, hx⟩
  · exact frameOk_value hv hdep hval hg
  · have h : FrameHyp crypto vault asset Act minGas m :=
      ⟨hv, hdep, hinv, hcr, ⟨hf.value, hf.gas, hlt, hf.depth, hf.size⟩, hs⟩
    rcases hx with ⟨c, hx⟩ | hx
    · exact frameOk_of_executes hmin hk h hx (hadm c hx)
    · exact frameOk_view (by omega) h hx

/-- The gas of a dangerous frame is below `2⁶⁴` when the transaction's is. -/
theorem DangerStart.gasLt {Good : World → Prop} {G : Nat} {m : Machine}
    (h : DangerStart (Prot vault asset) Good G m) (hG : G < 2 ^ 64) : m.frame.gasLeft < 2 ^ 64 := by
  obtain ⟨o, s, hf⟩ := h.fresh
  have : m.frame.gasLeft = m.frame.msg.gas := by rw [hf]; rfl
  rw [this]; exact Nat.lt_of_le_of_lt h.gas hG

/-! ## One transaction -/

/-- **One transaction, with the pending obligations as hypotheses.** From a world following
`w₀`, a top-level message call (`TopOk`: any caller other than the vault and the asset, any
target and code, any value and calldata, gas below `2⁶⁴`) whose covered frames execute
admitted calls ends in a world following `w₀`, given summaries of the uncovered frames. -/
theorem follows_tx_pending (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hs : SlotsOk crypto vault Act) (hpend : PendingFrames crypto vault asset minGas Act K)
    {w₀ w : World} (hinv : Solmate.Inv (abs crypto w₀ vault asset))
    (hw : Follows crypto vault asset Act K w₀ w) {ctx : Context} {tr : TransientStorage}
    {msg : Message} {fuel : Nat} {r : MessageResult} (hcr : ctx.crypto = crypto)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hmsg : TopOk (Prot vault asset) w msg) (hgas : msg.gas < 2 ^ 64)
    (hadm : ∀ m, Reaches ctx w tr msg m → VaultStart vault asset m →
      ∀ c, Executes vault asset m c → Admitted Act K c)
    (hr : processMessageCall fuel ctx w tr msg = .ok r) :
    Follows crypto vault asset Act K w₀ r.world := by
  refine processMessageCall_follows hs hinv hw hdeleg hmsg (le_refl _) (fun m hm hd => ?_) hr
  have hv := DangerStart.vaultStart hd
  have hwm : Follows crypto vault asset Act K w₀ m.world := goodOk.keep _ _ hd.snapshot hd.keep
  have hcr' : m.ctx.crypto = crypto := by rw [hm.ctx]; exact hcr
  have hlt := DangerStart.gasLt hd hgas
  by_cases hc : Covered vault asset minGas m
  · exact frameOk_of_covered hmin hk hs hv hwm.1 (hwm.inv hs hinv) hcr' hlt hc (hadm m hm hv)
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
  refine processMessageCall_follows hs hinv hw hdeleg hmsg (le_refl _) (fun m hm hd => ?_) hr
  have hv := DangerStart.vaultStart hd
  have hwm : Follows crypto vault asset Act K w₀ m.world := goodOk.keep _ _ hd.snapshot hd.keep
  have hcr' : m.ctx.crypto = crypto := by rw [hm.ctx]; exact hcr
  exact frameOk_of_covered hmin hk hs hv hwm.1 (hwm.inv hs hinv) hcr' (DangerStart.gasLt hd hgas)
    (hok m hm hv).1 (hok m hm hv).2

/-! ## Sequences of transactions -/

/-- **One step of a sequence of arbitrary transactions**: a covered top-level message call
from a non-contract sender (any code at the target), or any transition that keeps the storage
and code of the vault and the asset (the transaction layer's bookkeeping, block rewards,
transactions that do not reach them). -/
inductive TxStep (crypto : Crypto) (vault asset : Address) (minGas : Nat) (Act : List Address)
    (K : VCall → Prop) : World → World → Prop
  /-- A covered top-level message call. -/
  | call {w : World} {ctx : Context} {tr : TransientStorage} {msg : Message} {fuel : Nat}
      {r : MessageResult} : ctx.crypto = crypto →
      (ctx.fork < .prague ∨ ctx.tx.authorizations = []) → TopOk (Prot vault asset) w msg →
      msg.gas < 2 ^ 64 → TxOk vault asset minGas Act K ctx w tr msg →
      processMessageCall fuel ctx w tr msg = .ok r → TxStep crypto vault asset minGas Act K w r.world
  /-- Anything else that keeps the vault's and the asset's storage and code. -/
  | env {w w' : World} : EnvStep vault asset w w' → TxStep crypto vault asset minGas Act K w w'

/-- **Sequences of arbitrary transactions.** -/
def TxTrace (crypto : Crypto) (vault asset : Address) (minGas : Nat) (Act : List Address)
    (K : VCall → Prop) : World → World → Prop :=
  Relation.ReflTransGen (TxStep crypto vault asset minGas Act K)

/-- Environment steps keep `Follows`. -/
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
deployed world with well-formed ledgers, the vault and the asset are deployed, the ledgers are
well formed, and the abstraction agrees (up to non-actor allowances) with the model's execution
of some list of admitted calls — the calls the transaction committed. -/
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
        ∑ a : Address, (w.sload vault (Erc20.balanceSlot crypto Erc20.Layout.solmate a)).toNat ∧
      (w.sload asset 2#256).toNat =
        ∑ a : Address, (w.sload asset (Erc20.balanceSlot crypto Erc20.Layout.solmate a)).toNat := by
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

/-- **Price monotonicity, for sequences of arbitrary transactions.** If every vault/asset call
the transactions commit is a user operation (`K = UserOp`), then for the committed calls `cs`
(in order): unless the vault was emptied at some point (a prefix of `cs` leading to zero
supply), the share price `T/S` read from storage never decreased. -/
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
        (r.world.sload vault (Erc20.balanceSlot crypto Erc20.Layout.solmate a)).toNat ∧
      (r.world.sload asset 2#256).toNat = ∑ a : Address,
        (r.world.sload asset (Erc20.balanceSlot crypto Erc20.Layout.solmate a)).toNat := by
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

end EvmLeanSpecs.Refinement.Nested
