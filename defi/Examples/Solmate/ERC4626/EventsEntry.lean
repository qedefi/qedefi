import Examples.Solmate.ERC4626.EventsDeposit
import Examples.Solmate.ERC4626.EventsMint
import Examples.Solmate.ERC4626.EventsWithdraw
import Examples.Solmate.ERC4626.EventsRedeem
import Examples.Solmate.ERC4626.DepositCall

/-!
# Events of the ERC-4626 entry points against the model

For the compiled vault (any immutables, any asset address):

* **Frame form.** `deposit_events`, `mint_events` (`EventsDeposit`, `EventsMint`) and
  `withdraw_events`, `redeem_events` (here, from the bytecode-level `withdraw_halts_events` /
  `redeem_halts_events` and the model-level `Out.withdrawWorld?_refines` /
  `Out.redeemWorld?_refines`): in any frame (top level or called by another contract), with the
  hypotheses of `deposit_refines` / `withdraw_refines`, the frame ends as the refinement
  theorem says **and** as `EventsPost` with the encoded events of the model (`Events.deposit`,
  …): on success it appended exactly the asset's and the vault's logs, in emission order —
  for `deposit` / `mint` the asset's `Transfer(caller, vault, assets)` (emitted by the asset's
  frame, inside `safeTransferFrom`, and merged into the vault's on return), the shares'
  `Transfer(0, receiver, shares)`, `Deposit(caller, receiver, assets, shares)`; for `withdraw` /
  `redeem` the shares' `Transfer(owner, 0, shares)`, `Withdraw(caller, receiver, owner, assets,
  shares)`, the asset's `Transfer(vault, receiver, assets)`; on revert the model emits nothing
  (and the caller drops the frame's logs, `resumeAfter_eventsPost`).
* **Top-level form.** `deposit_events_call`, …: a top-level call of the `Deployed` vault returns a
  result whose `logs` are `encode vault asset (events (abs ctx.crypto w vault asset) op)`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Out

/-- **`withdraw(assets, receiver, owner)` emits the model's events**, in any frame: as
`withdraw_refines`, and the frame ends as `EventsPost` with the encoded `Events.withdraw`. -/
theorem withdraw_events {i : SolmateVault.Immutables} (m : Machine) (h : OutPre i m)
    {assets : Word} {receiver owner : Address}
    (hd : ThreeWordCall m.frame.msg.data 0xb460af94 assets (Word.ofAddress receiver)
      (Word.ofAddress owner))
    (hk : OutSlots m.ctx.crypto m.frame.msg.currentTarget m.frame.msg.caller owner receiver)
    (hinv : Solmate.Inv (absOf i.asset m)) :
    Halts m (fun mf o => OutRefPost m.ctx.crypto m.world m.frame.msg.currentTarget i.asset
      m.frame.msg.caller receiver owner (Solmate.withdraw (absOf i.asset m) m.frame.msg.caller
        assets.toNat receiver owner) mf o ∧
      EventsPost m (encode m.frame.msg.currentTarget i.asset
        (Events.withdraw m.frame.msg.currentTarget m.frame.msg.caller receiver owner assets.toNat
          (Solmate.withdraw (absOf i.asset m) m.frame.msg.caller assets.toNat receiver owner)))
        mf o) := by
  have hW := withdrawWorld?_refines (refines_iff.2 rfl) hinv h.assetNe hk assets
  refine (withdraw_halts_events m h hd).mono fun mf o _ hp => ?_
  revert hW
  generalize Solmate.withdraw (absOf i.asset m) m.frame.msg.caller assets.toNat receiver owner = r
  intro hW
  rcases r with _ | ⟨s', v⟩
  · simp only at hW
    rw [hW] at hp
    exact ⟨hp, eventsPost_revert hp⟩
  · obtain ⟨w', hrw, hR⟩ := hW
    rw [hrw] at hp
    obtain ⟨ho, hw, hl⟩ := hp
    refine ⟨⟨ho, hw ▸ hR, hw ▸ fun b => code_of_withdrawWorld? hrw b⟩, ?_⟩
    rw [ho]
    exact eventsPost_success (by rw [hl, encode_withdraw, append_three])

/-- **`redeem(shares, receiver, owner)` emits the model's events**, in any frame: as
`redeem_refines`, and the frame ends as `EventsPost` with the encoded `Events.redeem`. -/
theorem redeem_events {i : SolmateVault.Immutables} (m : Machine) (h : OutPre i m)
    {shares : Word} {receiver owner : Address}
    (hd : ThreeWordCall m.frame.msg.data 0xba087652 shares (Word.ofAddress receiver)
      (Word.ofAddress owner))
    (hk : OutSlots m.ctx.crypto m.frame.msg.currentTarget m.frame.msg.caller owner receiver)
    (hinv : Solmate.Inv (absOf i.asset m)) :
    Halts m (fun mf o => OutRefPost m.ctx.crypto m.world m.frame.msg.currentTarget i.asset
      m.frame.msg.caller receiver owner (Solmate.redeem (absOf i.asset m) m.frame.msg.caller
        shares.toNat receiver owner) mf o ∧
      EventsPost m (encode m.frame.msg.currentTarget i.asset
        (Events.redeem m.frame.msg.currentTarget m.frame.msg.caller receiver owner shares.toNat
          (Solmate.redeem (absOf i.asset m) m.frame.msg.caller shares.toNat receiver owner)))
        mf o) := by
  have hW := redeemWorld?_refines (refines_iff.2 rfl) hinv h.assetNe hk shares
  refine (redeem_halts_events m h hd).mono fun mf o _ hp => ?_
  revert hW
  generalize Solmate.redeem (absOf i.asset m) m.frame.msg.caller shares.toNat receiver owner = r
  intro hW
  rcases r with _ | ⟨s', v⟩
  · simp only at hW
    rw [hW] at hp
    exact ⟨hp, eventsPost_revert hp⟩
  · obtain ⟨w', hrw, hR⟩ := hW
    rw [hrw] at hp
    obtain ⟨ho, hw, hl⟩ := hp
    refine ⟨⟨ho, hw ▸ hR, hw ▸ fun b => code_of_redeemWorld? hrw b⟩, ?_⟩
    rw [ho]
    exact eventsPost_success (by rw [hl, encode_redeem, append_three])

/-! ## Top-level transactions -/

variable {ctx : Context} {w : World} {tr : TransientStorage} {vault asset caller : Address}
  {gas : Nat} {wa : AddressSet} {wk : StorageKeySet}

/-- **`deposit(assets, receiver)` at the top level**: the result's logs are the model's events,
encoded. Hypotheses of `deposit_call`. -/
theorem deposit_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 250000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver : Address}
    (hk : KeccakAvoids ctx.crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate caller)
    (hbv : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate vault)
    (hbr : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate receiver)
    (ha : Erc20.AllowanceSlotOk ctx.crypto Erc20.Layout.solmate caller vault)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (assets : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0x6e553f65 [assets, Word.ofAddress receiver]) gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.deposit caller assets.toNat receiver)) := by
  have hne := hdep.asset_ne
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := deposit_events _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile (by omega) hgas' (by rw [Abi.size_encodeCall]; simp))
    rfl hgas (twoWordCall_encodeCall' (by decide) assets _) hne.symm hk hbc hbv hbr ha hinv
  exact events_call hdeleg (Shares.delegatedAddress?_code i) (hdep.vaultNotPrecompile _)
    (hm.mono fun _ _ _ h => h.2)

/-- **`mint(shares, receiver)` at the top level**: the result's logs are the model's events,
encoded. Hypotheses of `mint_call`. -/
theorem mint_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 250000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver : Address}
    (hk : KeccakAvoids ctx.crypto (AddressKeyed [3#256]) [2#256, 6#256, 7#256])
    (hbc : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate caller)
    (hbv : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate vault)
    (hbr : Erc20.BalanceSlotOk ctx.crypto Erc20.Layout.solmate receiver)
    (ha : Erc20.AllowanceSlotOk ctx.crypto Erc20.Layout.solmate caller vault)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (shares : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0x94bf804d [shares, Word.ofAddress receiver]) gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.mint caller shares.toNat receiver)) := by
  have hne := hdep.asset_ne
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := mint_events _ (viewPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep.assetCode
    hdep.assetNotPrecompile (by omega) hgas' (by rw [Abi.size_encodeCall]; simp))
    rfl hgas (twoWordCall_encodeCall' (by decide) shares _) hne.symm hk hbc hbv hbr ha hinv
  exact events_call hdeleg (Shares.delegatedAddress?_code i) (hdep.vaultNotPrecompile _)
    (hm.mono fun _ _ _ h => h.2)

/-- **`withdraw(assets, receiver, owner)` at the top level**: the result's logs are the model's
events, encoded. Hypotheses of `withdraw_call`. -/
theorem withdraw_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 200000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver owner : Address}
    (hk : OutSlots ctx.crypto vault caller owner receiver)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (assets : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0xb460af94 [assets, Word.ofAddress receiver, Word.ofAddress owner])
          gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.withdraw caller assets.toNat receiver owner)) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := withdraw_events _ (outPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas'
    (by rw [Abi.size_encodeCall]; simp))
    (threeWordCall_encodeCall' (by decide) assets _ _) hk hinv
  exact events_call hdeleg (Shares.delegatedAddress?_code i) (hdep.vaultNotPrecompile _)
    (hm.mono fun _ _ _ h => h.2)

/-- **`redeem(shares, receiver, owner)` at the top level**: the result's logs are the model's
events, encoded. Hypotheses of `redeem_call`. -/
theorem redeem_events_call (hdep : Deployed w vault asset)
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (hgas : 200000 ≤ gas)
    (hgas' : gas < 2 ^ 64) {receiver owner : Address}
    (hk : OutSlots ctx.crypto vault caller owner receiver)
    (hinv : Solmate.Inv (abs ctx.crypto w vault asset)) (shares : Word) :
    ∃ n, ∀ fuel, n ≤ fuel → ∃ res, processMessageCall fuel ctx w tr
        (callMsg (w.code vault) vault caller
          (Abi.encodeCall 0xba087652 [shares, Word.ofAddress receiver, Word.ofAddress owner])
          gas wa wk) = .ok res ∧
      res.logs = encode vault asset
        (events (abs ctx.crypto w vault asset) (.redeem caller shares.toNat receiver owner)) := by
  obtain ⟨i, rfl, hcode⟩ := hdep.vaultCode
  rw [hcode]
  have hm := redeem_events _ (outPre_start (ctx := ctx) (tr := tr) (vault := vault)
    (caller := caller) (wa := wa) (wk := wk) (data := Abi.encodeCall _ _) hdep hgas hgas'
    (by rw [Abi.size_encodeCall]; simp))
    (threeWordCall_encodeCall' (by decide) shares _ _) hk hinv
  exact events_call hdeleg (Shares.delegatedAddress?_code i) (hdep.vaultNotPrecompile _)
    (hm.mono fun _ _ _ h => h.2)

end EvmLeanSpecs.Refinement
