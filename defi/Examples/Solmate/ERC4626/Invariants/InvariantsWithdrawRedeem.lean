import Examples.Solmate.ERC4626.Invariants.Deployed
import Examples.Solmate.ERC4626.WithdrawRefines

/-!
# `vault.withdraw` and `vault.redeem` at the top level: the invariants layer's obligations

`opRefines_withdraw`, `opRefines_redeem`: the `withdraw` and `redeem` fields of
`Invariants.Pending` (`OpRefinesAt` for every caller and arguments), from the top-level
refinement theorems `withdraw_call` / `redeem_call`. The trace-level hash hypothesis `SlotsOk`
gives the per-call `Out.OutSlots` for actors (`outSlots_of`), except the fixed-slot rows, which are
the hypothesis `KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256]` (no balance row is the
`totalSupply` slot or the `beforeWithdraw` counter: both are written). `withdraw` / `redeem`
need `200000 ≤ minGas` (four storage writes and a call into the asset).
-/

namespace EvmLeanSpecs.Refinement.Invariants

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift
open EvmLeanSpecs.Refinement.Out

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

/-- The per-call hash hypotheses of `withdraw` / `redeem` for actors. -/
theorem outSlots_of (hs : SlotsOk crypto vault Act)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256]) {c r o : Address}
    (hc : c ∈ Act) (hr : r ∈ Act) (ho : o ∈ Act) : OutSlots crypto vault c o r where
  rows := hk
  ownerOk := hs.bal o ho
  owner7 := (hs.balFixed o ho).2
  allowOk := fun _ => hs.allow o ho c hc
  allow67 := fun _ => hs.allowFixed o ho c hc
  vaultOk := hs.bal vault hs.vault_mem
  receiverOk := hs.bal r hr

/-- Actor pairs are among the share allowances known after `withdraw` / `redeem`. -/
theorem outAllowances_of (hs : SlotsOk crypto vault Act) {c o : Address} (hc : c ∈ Act)
    (ho : o ∈ Act) {a b : Address} (h : ActorPairs Act a b) : OutAllowances crypto c o a b := by
  obtain ⟨ha, hb⟩ := h
  refine ⟨?_, (hs.allowFixed a ha b hb).1,
    (Erc20.balanceSlot_ne_allowanceSlot (hs.allow a ha b hb) o).symm, (hs.allow a ha b hb).2.2⟩
  rcases hs.allowP ha hb ho hc with h | h
  · exact .inr (.inl h)
  · exact .inr (.inr h)

/-- Actor pairs are among the asset allowances known after the payout. -/
theorem transferAllowances_of (hs : SlotsOk crypto vault Act) {r : Address} {a b : Address}
    (h : ActorPairs Act a b) : TransferAllowances crypto vault r a b :=
  ⟨(Erc20.balanceSlot_ne_allowanceSlot (hs.allow a h.1 b h.2) _).symm,
    (Erc20.balanceSlot_ne_allowanceSlot (hs.allow a h.1 b h.2) _).symm⟩

/-- `RefinesOn` with the actor pairs inside both predicates gives `AgreeOn`. -/
theorem agree_of_refinesOn (hs : SlotsOk crypto vault Act) {c r o : Address} (hc : c ∈ Act)
    (ho : o ∈ Act) {w' : World} {s' : State Address}
    (h : RefinesOn (OutAllowances crypto c o) (TransferAllowances crypto vault r) crypto w' vault
      asset s') :
    AgreeOn (ActorPairs Act) (abs crypto w' vault asset) s' :=
  agree_of_reps h.self h.shares h.asset (fun _ _ hp => outAllowances_of hs hc ho hp)
    (fun _ _ hp => transferAllowances_of hs hp) h.afterDeposit h.beforeWithdraw

set_option maxHeartbeats 1000000 in
/-- **`vault.withdraw`** refines `Op.withdraw`. -/
theorem opRefines_withdraw (hmin : 200000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256]) (caller : Address)
    (assets : Word) (receiver owner : Address) :
    OpRefinesAt crypto vault asset minGas Act (.withdraw caller assets receiver owner) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, hg', -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, Bool.false_eq_true,
    ite_false] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hr : receiver ∈ Act := hact receiver (by simp [VCall.actors])
  have ho : owner ∈ Act := hact owner (by simp [VCall.actors])
  obtain ⟨n', hn'⟩ := withdraw_call (tr := tr) (wa := wa) (wk := wk) hdep hdeleg (by omega) hg'
    (outSlots_of hs hk hc hr ho) hinv assets
  obtain ⟨res, hrun, hres⟩ := hn' (max n n') (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hrun
  unfold OutResult at hres
  split at hres
  · rename_i s' v hW
    obtain ⟨-, -, hR, hC⟩ := hres
    refine ⟨hdep.of_code (hC vault) (hC asset), callRefines_some ?_ (agree_of_refinesOn hs hc ho hR)⟩
    show Option.map Prod.fst (Solmate.withdraw _ _ _ _ _) = _
    rw [hW]; rfl
  · rename_i hW
    obtain ⟨-, -, hwld⟩ := hres
    refine ⟨hwld ▸ hdep, callRefines_none ?_ hwld⟩
    show Option.map Prod.fst (Solmate.withdraw _ _ _ _ _) = _
    rw [hW]; rfl

set_option maxHeartbeats 1000000 in
/-- **`vault.redeem`** refines `Op.redeem`. -/
theorem opRefines_redeem (hmin : 200000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256]) (caller : Address)
    (shares : Word) (receiver owner : Address) :
    OpRefinesAt crypto vault asset minGas Act (.redeem caller shares receiver owner) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, hg', -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, Bool.false_eq_true,
    ite_false] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hr : receiver ∈ Act := hact receiver (by simp [VCall.actors])
  have ho : owner ∈ Act := hact owner (by simp [VCall.actors])
  obtain ⟨n', hn'⟩ := redeem_call (tr := tr) (wa := wa) (wk := wk) hdep hdeleg (by omega) hg'
    (outSlots_of hs hk hc hr ho) hinv shares
  obtain ⟨res, hrun, hres⟩ := hn' (max n n') (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hrun
  unfold OutResult at hres
  split at hres
  · rename_i s' v hW
    obtain ⟨-, -, hR, hC⟩ := hres
    refine ⟨hdep.of_code (hC vault) (hC asset), callRefines_some ?_ (agree_of_refinesOn hs hc ho hR)⟩
    show Option.map Prod.fst (Solmate.redeem _ _ _ _ _) = _
    rw [hW]; rfl
  · rename_i hW
    obtain ⟨-, -, hwld⟩ := hres
    refine ⟨hwld ▸ hdep, callRefines_none ?_ hwld⟩
    show Option.map Prod.fst (Solmate.redeem _ _ _ _ _) = _
    rw [hW]; rfl

end EvmLeanSpecs.Refinement.Invariants
