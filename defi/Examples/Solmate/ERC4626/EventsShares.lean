import Examples.Solmate.ERC4626.EventsSharesCode
import Examples.Solmate.ERC4626.Events
import Examples.Solmate.ERC4626.Shares

/-!
# Events of the vault's share-token functions against the model

For the compiled vault (any immutables), a top-level call of `transfer`, `approve` or
`transferFrom` returns a result whose logs are the encoding of the model's events
(`Solmate.Events.transfer` / `approve` / `transferFrom` of the share ledger `t` that the vault's
storage represents): the vault's `Transfer` / `Approval` on success, nothing on revert
(`run_logs_of_fail`). Same hypotheses as `Shares.transfer_refines`, … (fewer: no hash or
well-formedness hypothesis is needed to know the events, except `AllowanceSlotOk` of the spent
entry for `transferFrom`).

* `transfer_events`, `approve_events`, `transferFrom_events`: in the form of the refinement
  theorems (`vaultCall i …`, a ledger `t` with `Rep`);
* `transfer_events_call`, `approve_events_call`, `transferFrom_events_call`: for the
  `Deployed` vault, against `events (abs ctx.crypto w vault asset) op`, the form of the other
  call kinds (`EventsAsset`, `EventsEntry`).
-/

namespace EvmLeanSpecs.Refinement.Shares

open EvmLean Interpreter Solidity Contracts Erc20 EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate

variable {i : SolmateVault.Immutables} {ctx : Context} {w : World} {tr : TransientStorage}
  {vault caller : Address} {gas : Nat} {warmAddrs : AddressSet} {warmKeys : StorageKeySet}

/-- The logs of one event. -/
theorem encode_single (vault asset : Address) (e : Event Address) :
    encode vault asset [e] = #[e.toLog vault asset] := rfl

set_option maxHeartbeats 1000000 in
/-- **`transfer(dst, amount)` emits the model's events**: the result's logs are
`Events.transfer .vault t caller dst amount`, encoded. -/
theorem transfer_events {dst : Address} {amount : Word}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false) (hgas : 100000 ≤ gas)
    {t : Token Address} (hr : Rep (view ctx.crypto Layout.solmate w vault) t)
    (fuel : Nat) (hfuel : 400 ≤ fuel) (asset : Address) :
    ∃ r, processMessageCall fuel ctx w tr
        (vaultCall i vault caller (transferData dst amount) gas warmAddrs warmKeys) = .ok r ∧
      r.logs = encode vault asset (Events.transfer .vault t caller dst amount.toNat) := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 400 := ⟨fuel - 400, by omega⟩
  rw [processMessageCall_vaultCall hdeleg hpre]
  cases hT : t.transfer caller dst amount.toNat with
  | some t' =>
    have hbal :
        amount.toNat ≤ ((view ctx.crypto Layout.solmate w vault).balanceOf caller).toNat := by
      rw [hr.balanceOf caller]; exact (Token.transfer_eq_some.1 hT).1
    obtain ⟨r, hrun, -, -, -, hl⟩ := transfer_ok_events (i := i) (tr := tr) (dst := dst)
      (warmAddrs := warmAddrs) (warmKeys := warmKeys) hgas hbal k
    refine ⟨r, hrun, ?_⟩
    simp only [Events.transfer, hT, Option.isSome_some, ↓reduceIte, encode_single,
      toLog_transfer, Emitter.addr, hl]
  | none =>
    have hlt :
        ((view ctx.crypto Layout.solmate w vault).balanceOf caller).toNat < amount.toNat := by
      rw [hr.balanceOf caller]
      unfold Token.transfer at hT
      split at hT
      · assumption
      · cases hT
    obtain ⟨r, hrun, hs, -⟩ := transfer_revert (i := i) (tr := tr) (dst := dst)
      (warmAddrs := warmAddrs) (warmKeys := warmKeys) hgas hlt k
    refine ⟨r, hrun, ?_⟩
    simp only [Events.transfer, hT, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      encode_nil]
    exact run_logs_of_fail hrun hs

set_option maxHeartbeats 1000000 in
/-- **`approve(spender, amount)` emits the model's event**: `Approval(caller, spender,
amount)` of the vault. -/
theorem approve_events {spender : Address} {amount : Word}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false) (hgas : 100000 ≤ gas)
    (fuel : Nat) (hfuel : 300 ≤ fuel) (asset : Address) :
    ∃ r, processMessageCall fuel ctx w tr
        (vaultCall i vault caller (approveData spender amount) gas warmAddrs warmKeys) = .ok r ∧
      r.logs = encode vault asset (Events.approve .vault caller spender amount.toNat) := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 300 := ⟨fuel - 300, by omega⟩
  rw [processMessageCall_vaultCall hdeleg hpre]
  obtain ⟨r, hrun, -, -, -, hl⟩ := approve_ok_events (i := i) (tr := tr) (spender := spender)
    (amount := amount) (warmAddrs := warmAddrs) (warmKeys := warmKeys) (vault := vault)
    (caller := caller) (w := w) (ctx := ctx) hgas k
  refine ⟨r, hrun, ?_⟩
  simp only [Events.approve, encode_single, toLog_approval, Emitter.addr, hl]

set_option maxHeartbeats 1000000 in
/-- **`transferFrom(src, dst, amount)` emits the model's events**: `Transfer(src, dst,
amount)` of the vault on success (no `Approval`), nothing on revert. -/
theorem transferFrom_events {src dst : Address} {amount : Word}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = [])
    (hpre : Precompile.isPrecompile ctx.fork vault = false) (hgas : 100000 ≤ gas)
    (ha : AllowanceSlotOk ctx.crypto Layout.solmate src caller)
    {t : Token Address} (hr : Rep (view ctx.crypto Layout.solmate w vault) t)
    (fuel : Nat) (hfuel : 500 ≤ fuel) (asset : Address) :
    ∃ r, processMessageCall fuel ctx w tr
        (vaultCall i vault caller (transferFromData src dst amount) gas warmAddrs warmKeys) =
        .ok r ∧
      r.logs = encode vault asset (Events.transferFrom .vault t caller src dst amount.toNat) := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 500 := ⟨fuel - 500, by omega⟩
  rw [processMessageCall_vaultCall hdeleg hpre]
  cases hT : t.transferFrom caller src dst amount.toNat with
  | some t' =>
    obtain ⟨t₁, hsp, htr⟩ := Option.bind_eq_some_iff.1 hT
    obtain ⟨s₁, hm₁⟩ := Option.isSome_iff_exists.1
      ((spend_isSome_iff hr src caller amount).2 (by simp [hsp]))
    have hal := allowance_cond_of_spend hr hsp
    have hbal : amount.toNat ≤ ((spendWorld ctx.crypto w vault src caller amount).sload vault
        (balanceSlot ctx.crypto Layout.solmate src)).toNat := by
      rw [balance_spendWorld ha hm₁, hr.balanceOf src, ← (Token.spend_eq_some hsp).1]
      exact (Token.transfer_eq_some.1 htr).1
    obtain ⟨r, hrun, -, -, -, hl⟩ := transferFrom_ok_events (i := i) (tr := tr) (dst := dst)
      (warmAddrs := warmAddrs) (warmKeys := warmKeys) hgas hal hbal k
    refine ⟨r, hrun, ?_⟩
    simp only [Events.transferFrom, hT, Option.isSome_some, ↓reduceIte, encode_single,
      toLog_transfer, Emitter.addr, hl]
  | none =>
    simp only [Events.transferFrom, hT, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      encode_nil]
    cases hsp : t.spend src caller amount.toNat with
    | none =>
      unfold Token.spend at hsp
      have ha' := hr.allowance src caller trivial
      split at hsp
      · cases hsp
      · rename_i hmax
        split at hsp
        · rename_i hlt
          have hmax' : (view ctx.crypto Layout.solmate w vault).allowance src caller ≠ maxWord :=
            fun h => hmax (by rw [← ha', (eq_maxWord_iff _).1 h])
          have hlt' : ((view ctx.crypto Layout.solmate w vault).allowance src caller).toNat <
              amount.toNat := by rw [ha']; exact hlt
          obtain ⟨r, hrun, hs, -⟩ := transferFrom_revert_allowance (i := i) (tr := tr)
            (dst := dst) (warmAddrs := warmAddrs) (warmKeys := warmKeys) hgas hmax' hlt' k
          exact ⟨r, hrun, run_logs_of_fail hrun hs⟩
        · cases hsp
    | some t₁ =>
      have htr : t₁.transfer src dst amount.toNat = none := by
        unfold Token.transferFrom at hT
        rw [hsp] at hT
        simpa using hT
      obtain ⟨s₁, hm₁⟩ := Option.isSome_iff_exists.1
        ((spend_isSome_iff hr src caller amount).2 (by simp [hsp]))
      have hal := allowance_cond_of_spend hr hsp
      have hbal : ((spendWorld ctx.crypto w vault src caller amount).sload vault
          (balanceSlot ctx.crypto Layout.solmate src)).toNat < amount.toNat := by
        rw [balance_spendWorld ha hm₁, hr.balanceOf src, ← (Token.spend_eq_some hsp).1]
        unfold Token.transfer at htr
        split at htr
        · assumption
        · cases htr
      obtain ⟨r, hrun, hs, -⟩ := transferFrom_revert_balance (i := i) (tr := tr) (dst := dst)
        (warmAddrs := warmAddrs) (warmKeys := warmKeys) hgas hal hbal k
      exact ⟨r, hrun, run_logs_of_fail hrun hs⟩

/-! ## For the deployed vault, against `abs` -/

variable {asset : Address} {wa : AddressSet} {wk : StorageKeySet}

/-- **`vault.transfer(dst, amount)` at the top level**: the result's logs are the model's
events, encoded. -/
theorem transfer_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 100000 ≤ gas)
    (dst : Address) (amount : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (transferData dst amount) gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.transfer caller dst amount.toNat)) := by
  obtain ⟨i, -, hcode⟩ := hdep.vaultCode
  rw [hcode]
  exact ⟨400, fun fuel hle => transfer_events (i := i) hdeleg (hdep.vaultNotPrecompile _) hgas
    (rep_toToken _) fuel hle asset⟩

/-- **`vault.approve(spender, amount)` at the top level**: the result's logs are the model's
event, encoded. -/
theorem approve_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 100000 ≤ gas)
    (spender : Address) (amount : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (approveData spender amount) gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.approve caller spender amount.toNat)) := by
  obtain ⟨i, -, hcode⟩ := hdep.vaultCode
  rw [hcode]
  exact ⟨300, fun fuel hle => approve_events (i := i) hdeleg (hdep.vaultNotPrecompile _) hgas
    fuel hle asset⟩

/-- **`vault.transferFrom(src, dst, amount)` at the top level**: the result's logs are the
model's events, encoded. -/
theorem transferFrom_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 100000 ≤ gas)
    {src : Address} (ha : AllowanceSlotOk ctx.crypto Layout.solmate src caller)
    (dst : Address) (amount : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller (transferFromData src dst amount) gas wa wk) =
        .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.transferFrom caller src dst amount.toNat)) := by
  obtain ⟨i, -, hcode⟩ := hdep.vaultCode
  rw [hcode]
  exact ⟨500, fun fuel hle => transferFrom_events (i := i) hdeleg (hdep.vaultNotPrecompile _)
    hgas ha (rep_toToken _) fuel hle asset⟩

end EvmLeanSpecs.Refinement.Shares
