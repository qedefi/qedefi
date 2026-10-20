import Examples.Solmate.ERC4626.Invariants.Deployed
import Examples.Solmate.ERC4626.DepositCall
import Examples.Solmate.ERC4626.Invariants.InvariantsWithdrawRedeem

/-!
# `vault.deposit` and `vault.mint` at the top level: the invariants layer's obligations

`opRefines_deposit`, `opRefines_mint`: the `deposit` and `mint` fields of
`Invariants.Pending` (`OpRefinesAt` for every caller and arguments), from the top-level
refinement theorems `deposit_call` / `mint_call`. The trace-level hash hypothesis `SlotsOk`
gives the per-call hypotheses for actors (balance slots of caller, receiver and vault, the
allowance `allowance[caller][vault]` of the asset, the actor allowance pairs avoiding the
written slots), except the fixed-slot rows, which are the hypothesis
`KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256]` (no balance row is the
`totalSupply` slot or a hook counter: slots 2 and 7 are written, and the receiver's balance
write must not touch counter 6). `deposit` / `mint` need `250000 ≤ minGas` (four storage
writes in the vault, three in the asset, and the `transferFrom` call).
-/

namespace EvmLeanSpecs.Refinement.Invariants

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

/-- Actor pairs are among the share allowances known after `deposit` / `mint`. -/
theorem depositAllowances_of (hs : SlotsOk crypto vault Act) {r : Address} {a b : Address}
    (h : ActorPairs Act a b) : DepositAllowances crypto r a b :=
  ⟨⟨(hs.allow a h.1 b h.2).2.2, hs.balP h.1 h.2 r⟩, (hs.allowFixed a h.1 b h.2).2⟩

/-- Actor pairs are among the asset allowances known after the asset's `transferFrom`. -/
theorem transferFromAllowances_of (hs : SlotsOk crypto vault Act) {c : Address} (hc : c ∈ Act)
    {a b : Address} (h : ActorPairs Act a b) : TransferFromAllowances crypto vault c vault a b :=
  ⟨⟨hs.balP h.1 h.2 c, hs.balP h.1 h.2 vault⟩, hs.allowP h.1 h.2 hc hs.vault_mem⟩

/-- `Out.RefinesOn` with the actor pairs inside both predicates gives `AgreeOn`. -/
theorem agree_of_entry (hs : SlotsOk crypto vault Act) {c r : Address} (hc : c ∈ Act)
    {w' : World} {s' : State Address}
    (h : Out.RefinesOn (DepositAllowances crypto r) (TransferFromAllowances crypto vault c vault)
      crypto w' vault asset s') :
    AgreeOn (ActorPairs Act) (abs crypto w' vault asset) s' :=
  agree_of_reps h.self h.shares h.asset (fun _ _ hp => depositAllowances_of hs hp)
    (fun _ _ hp => transferFromAllowances_of hs hc hp) h.afterDeposit h.beforeWithdraw

set_option maxHeartbeats 1000000 in
/-- **`vault.deposit`** refines `Op.deposit`. -/
theorem opRefines_deposit (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256]) (caller : Address)
    (assets : Word) (receiver : Address) :
    OpRefinesAt crypto vault asset minGas Act (.deposit caller assets receiver) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, hg', -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, Bool.false_eq_true,
    ite_false] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hr : receiver ∈ Act := hact receiver (by simp [VCall.actors])
  obtain ⟨n', hn'⟩ := deposit_call (tr := tr) (wa := wa) (wk := wk) hdep hdeleg (by omega) hg'
    hk (hs.bal caller hc) (hs.bal vault hs.vault_mem) (hs.bal receiver hr)
    (hs.allow caller hc vault hs.vault_mem) hinv assets
  obtain ⟨res, hrun, hres⟩ := hn' (max n n') (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hrun
  unfold EntryResult at hres
  split at hres
  · rename_i s' v hW
    obtain ⟨-, -, hwld, hR⟩ := hres
    refine ⟨hdep.of_code (by rw [hwld]; exact code_depositWorld ..)
      (by rw [hwld]; exact code_depositWorld ..), callRefines_some ?_ (agree_of_entry hs hc hR)⟩
    show Option.map Prod.fst (Solmate.deposit _ _ _ _) = _
    rw [hW]; rfl
  · rename_i hW
    obtain ⟨-, -, hwld⟩ := hres
    refine ⟨hwld ▸ hdep, callRefines_none ?_ hwld⟩
    show Option.map Prod.fst (Solmate.deposit _ _ _ _) = _
    rw [hW]; rfl

set_option maxHeartbeats 1000000 in
/-- **`vault.mint`** refines `Op.mint`. -/
theorem opRefines_mint (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256]) (caller : Address)
    (shares : Word) (receiver : Address) :
    OpRefinesAt crypto vault asset minGas Act (.mint caller shares receiver) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, hg', -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, Bool.false_eq_true,
    ite_false] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hr : receiver ∈ Act := hact receiver (by simp [VCall.actors])
  obtain ⟨n', hn'⟩ := mint_call (tr := tr) (wa := wa) (wk := wk) hdep hdeleg (by omega) hg'
    hk (hs.bal caller hc) (hs.bal vault hs.vault_mem) (hs.bal receiver hr)
    (hs.allow caller hc vault hs.vault_mem) hinv shares
  obtain ⟨res, hrun, hres⟩ := hn' (max n n') (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hrun
  unfold EntryResult at hres
  split at hres
  · rename_i s' v hW
    obtain ⟨-, -, hwld, hR⟩ := hres
    refine ⟨hdep.of_code (by rw [hwld]; exact code_depositWorld ..)
      (by rw [hwld]; exact code_depositWorld ..), callRefines_some ?_ (agree_of_entry hs hc hR)⟩
    show Option.map Prod.fst (Solmate.mint _ _ _ _) = _
    rw [hW]; rfl
  · rename_i hW
    obtain ⟨-, -, hwld⟩ := hres
    refine ⟨hwld ▸ hdep, callRefines_none ?_ hwld⟩
    show Option.map Prod.fst (Solmate.mint _ _ _ _) = _
    rw [hW]; rfl

/-- **All four pending obligations**, from `opRefines_deposit` / `opRefines_mint` here and
`opRefines_withdraw` / `opRefines_redeem` (`InvariantsWithdrawRedeem`), under the one fixed-slot
hypothesis `[2, 6, 7]`. With `refinesFor_all` every call kind is refined. -/
theorem pending_of (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256]) :
    Pending crypto vault asset minGas Act where
  deposit c a r := opRefines_deposit hmin hk c a r
  mint c n r := opRefines_mint hmin hk c n r
  withdraw c a r o := opRefines_withdraw (by omega) (KeccakAvoids.sub hk (by simp)) c a r o
  redeem c n r o := opRefines_redeem (by omega) (KeccakAvoids.sub hk (by simp)) c n r o

/-- **Every call kind refines its operation** under `SlotsOk` and the fixed-slot hypothesis. -/
theorem refinesFor_all_of (hmin : 250000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256]) :
    RefinesFor crypto vault asset minGas Act (fun _ => True) :=
  refinesFor_all (by omega) (KeccakAvoids.sub hk (by simp)) (pending_of hmin hk)

end EvmLeanSpecs.Refinement.Invariants
