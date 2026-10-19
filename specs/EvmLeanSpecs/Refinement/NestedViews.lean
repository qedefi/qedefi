import EvmLeanSpecs.Refinement.NestedCalls
import EvmLeanSpecs.Refinement.SharesFrameViews
import EvmLeanSpecs.Refinement.VaultViewsSpec

/-!
# Frame summaries of views and of calls carrying value

`FrameOk` (`NestedSystem.lean`) holds with **no** model call for every dangerous frame whose
world is unchanged on success:

* `frameOk_view`: a funded frame (`Funded`, at least 60000 gas) calling one of the covered views
  (`ViewData`): the vault's twelve ERC-4626 views (`VaultViews*.lean`), its share-token views
  `totalSupply`, `balanceOf`, `allowance`, `decimals` (`SharesFrameViews.lean`), and the asset's
  `balanceOf` (`AssetBalanceOf.lean`) — called with a non-static `CALL` (a `STATICCALL` frame
  is not dangerous and needs no summary);
* `frameOk_value`: any call with non-zero value to the vault or the asset: both are compiled
  with every function non-payable, so the dispatcher's first instructions revert
  (`CALLVALUE ISZERO JUMPI … REVERT`), with at least 100 gas.
-/

namespace EvmLeanSpecs.Refinement.Nested

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift
open EvmLeanSpecs.Refinement.Invariants

variable {crypto : Crypto} {vault asset : Address} {Act : List Address} {K : VCall → Prop}

/-- `FrameOk` of a frame that, on success, leaves the world unchanged. -/
theorem frameOk_of_world {m : Machine} (hdep : Deployed m.world vault asset)
    (h : Halts m (fun mf o => ∀ out, o = .success out → mf.world = m.world)) :
    FrameOk crypto vault asset Act K m :=
  h.mono fun mf o _ hp out ho => by
    rw [hp out ho]
    exact ⟨hdep, [], fun _ hc => absurd hc List.not_mem_nil, AgreeOn.refl _⟩

/-! ## Views -/

/-- Calldata selecting one of the vault's views with a frame summary. -/
def VaultViewData (d : ByteArray) : Prop :=
  (∃ x, WordCall d 0xc6e6f592 x) ∨ (∃ x, WordCall d 0x07a2d13a x) ∨
  (∃ x, WordCall d 0xef8b30f7 x) ∨ (∃ x, WordCall d 0xb3d7f6b9 x) ∨
  (∃ x, WordCall d 0x0a28a477 x) ∨ (∃ x, WordCall d 0x4cdad506 x) ∨
  (∃ a, AddrCall d 0x402d267d a) ∨ (∃ a, AddrCall d 0xc63d75b6 a) ∨
  (∃ a, AddrCall d 0xce96cb77 a) ∨ (∃ a, AddrCall d 0xd905777e a) ∨
  NoArgCall d 0x01e1d114 ∨ NoArgCall d 0x38d52e0f ∨
  NoArgCall d 0x18160ddd ∨ (∃ a, AddrCall d 0x70a08231 a) ∨
  (∃ o s, TwoWordCall d 0xdd62ed3e (Word.ofAddress o) (Word.ofAddress s)) ∨
  NoArgCall d 0x313ce567

/-- The frame calls one of the views with a frame summary: a view of the vault, or the
asset's `balanceOf`. -/
def ViewData (vault asset : Address) (m : Machine) : Prop :=
  (m.frame.msg.currentTarget = vault ∧ VaultViewData m.frame.msg.data) ∨
  (m.frame.msg.currentTarget = asset ∧
    ∃ a, AddrCall m.frame.msg.data balanceOfSelector a)

/-- A view post leaves the world unchanged. -/
theorem viewPost_world {m mf : Machine} {r : Option ℕ} {o : Outcome} (h : ViewPost m r mf o) :
    mf.world = m.world := h.1

set_option maxHeartbeats 1000000 in
/-- **The covered views, in any frame**: on success the world is unchanged. -/
theorem frameOk_view {minGas : Nat} {m : Machine} (hmin : 60000 ≤ minGas)
    (h : FrameHyp crypto vault asset Act minGas m) (hv : ViewData vault asset m) :
    FrameOk crypto vault asset Act K m := by
  refine frameOk_of_world h.dep ?_
  have hval := h.funded.value
  have hsz := h.funded.size
  have hg := h.funded.gas
  rcases hv with ⟨ht, hd⟩ | ⟨ht, a, hd⟩
  · obtain ⟨i, hia, hf⟩ := vault_fresh h.start h.dep ht
    have hp := viewPre_of hmin h hia ht hf
    have w : ∀ {H : Machine → Outcome → Prop}, Halts m H →
        (∀ mf o, H mf o → mf.world = m.world) →
        Halts m (fun mf o => ∀ out, o = .success out → mf.world = m.world) :=
      fun hH hw => hH.mono fun mf o _ hp _ _ => hw mf o hp
    rcases hd with ⟨x, hd⟩ | ⟨x, hd⟩ | ⟨x, hd⟩ | ⟨x, hd⟩ | ⟨x, hd⟩ | ⟨x, hd⟩ | ⟨a, hd⟩ |
      ⟨a, hd⟩ | ⟨a, hd⟩ | ⟨a, hd⟩ | hd | hd | hd | ⟨a, hd⟩ | ⟨o, s, hd⟩ | hd
    · exact w (convertToShares_halts m hp hd) fun _ _ h => h.1
    · exact w (convertToAssets_halts m hp hd) fun _ _ h => h.1
    · exact w (previewDeposit_halts m hp hd) fun _ _ h => h.1
    · exact w (previewMint_halts m hp hd) fun _ _ h => h.1
    · exact w (previewWithdraw_halts m hp hd) fun _ _ h => h.1
    · exact w (previewRedeem_halts m hp hd) fun _ _ h => h.1
    · exact w (maxDeposit_halts m hp hd) fun _ _ h => h.1
    · exact w (maxMint_halts m hp hd) fun _ _ h => h.1
    · exact w (maxWithdraw_halts m hp hd) fun _ _ h => h.1
    · exact w (maxRedeem_halts m hp hd) fun _ _ h => h.1
    · exact w (totalAssets_halts m hp hd) fun _ _ h => h.1
    · exact w (asset_halts m hp hd) fun _ _ h => h.1
    · exact w (sharesTotalSupply_halts m hf hval hd hsz (by omega)) fun _ _ h => h.2
    · exact w (sharesBalanceOf_halts m hf hval hd hsz (by omega)) fun _ _ h => h.2
    · exact w (sharesAllowance_halts m hf hval hd hsz (by omega)) fun _ _ h => h.2
    · exact w (sharesDecimals_halts m hf hval hd hsz (by omega)) fun _ _ h => h.2
  · obtain ⟨ia, hf⟩ := asset_fresh h.start h.dep ht
    exact (balanceOf_halts m hf a hval hd.selector hd.size hsz hd.arg (by omega)).mono
      fun mf o _ hp _ _ => hp.2.1

/-! ## Calls carrying value -/

/-- `ISZERO` of a non-zero word. -/
theorem iszero_of_ne {v : Word} (h : v ≠ 0) : Word.iszero v = 0#256 := by
  unfold Word.iszero
  have : (v == 0) = false := by simpa using h
  rw [this]; rfl

set_option maxHeartbeats 0 in
/-- **The vault rejects value**: every function is non-payable; the dispatcher's first check
reverts. -/
theorem vault_value_reverts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value ≠ 0)
    (hg : 100 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hz := iszero_of_ne hval
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hz]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 0 in
/-- **The asset rejects value.** -/
theorem asset_value_reverts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value ≠ 0)
    (hg : 100 ≤ m.frame.gasLeft) :
    Halts m (fun _ o => ∃ out, o = .revert out) := by
  apply WP.halts_of_false
  have hz := iszero_of_ne hval
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hz]
  exact ⟨_, rfl⟩

/-- **A call with value to the vault or the asset**, in any frame, reverts (at least 100 gas). -/
theorem frameOk_value {m : Machine} (hv : VaultStart vault asset m)
    (hdep : Deployed m.world vault asset) (hval : m.frame.msg.value ≠ 0)
    (hg : 100 ≤ m.frame.gasLeft) : FrameOk crypto vault asset Act K m := by
  have hrev : Halts m (fun _ o => ∃ out, o = .revert out) := by
    rcases hv.prot with ht | ht
    · obtain ⟨i, -, hf⟩ := vault_fresh hv hdep ht
      exact vault_value_reverts m hf hval hg
    · obtain ⟨ia, hf⟩ := asset_fresh hv hdep ht
      exact asset_value_reverts m hf hval hg
  exact hrev.mono fun _ _ _ ⟨out, ho⟩ out' ho' => by rw [ho] at ho'; cases ho'

end EvmLeanSpecs.Refinement.Nested
