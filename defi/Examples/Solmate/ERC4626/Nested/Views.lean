import Examples.Solmate.ERC4626.Nested.Calls
import Examples.Solmate.ERC4626.SharesFrame
import Examples.Solmate.ERC4626.ViewsSpec
import Examples.Solmate.ERC20.Strings
import Examples.Solmate.ERC4626.Strings
import Examples.Solmate.ERC4626.PermitSpec
import Examples.Solmate.ERC4626.Malformed

/-!
# Frame summaries of views and of calls carrying value

`FrameOk` with no model call for frames that leave the world unchanged on success:
`frameOk_view` (the covered views of both tokens, called with a non-static `CALL`),
`frameOk_value` (every function is non-payable), `frameOk_unknown` (no function selected) and
`frameOk_malformed` (the ABI decoder reverts). See `docs/erc4626/details.md` §4–5.
-/

namespace Examples.Solmate.ERC4626.Nested
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.Math Defi.ERC20 Defi.ERC4626.Solmate Defi.Trace.Lift
open Examples.Solmate.ERC4626.Invariants

variable {crypto : Crypto} {vault asset : Address} {Act : List Address} {K : VCall → Prop}

theorem frameOk_of_world {m : Machine} (hdep : Deployed m.world vault asset)
    (h : Halts m (fun mf o => ∀ out, o = .success out → mf.world = m.world)) :
    FrameOk crypto vault asset Act K m :=
  h.mono fun mf o _ hp out ho => by
    rw [hp out ho]
    exact ⟨hdep, [], fun _ hc => absurd hc List.not_mem_nil, AgreeOn.refl _⟩

/-! ## Views -/

/-- Calldata selecting one of the vault's views with a frame summary (selector and ABI-clean
arguments): the twelve ERC-4626 views, the share-token views, the hook counters, `nonces`. -/
def VaultViewData (d : ByteArray) : Prop :=
  (∃ x, WordCall d 0xc6e6f592 x) ∨ (∃ x, WordCall d 0x07a2d13a x) ∨
  (∃ x, WordCall d 0xef8b30f7 x) ∨ (∃ x, WordCall d 0xb3d7f6b9 x) ∨
  (∃ x, WordCall d 0x0a28a477 x) ∨ (∃ x, WordCall d 0x4cdad506 x) ∨
  (∃ a, AddrCall d 0x402d267d a) ∨ (∃ a, AddrCall d 0xc63d75b6 a) ∨
  (∃ a, AddrCall d 0xce96cb77 a) ∨ (∃ a, AddrCall d 0xd905777e a) ∨
  NoArgCall d 0x01e1d114 ∨ NoArgCall d 0x38d52e0f ∨
  NoArgCall d 0x18160ddd ∨ (∃ a, AddrCall d 0x70a08231 a) ∨
  (∃ o s, TwoWordCall d 0xdd62ed3e (Word.ofAddress o) (Word.ofAddress s)) ∨
  NoArgCall d 0x313ce567 ∨ NoArgCall d 0xbc368a8a ∨ NoArgCall d 0xfc407ae7 ∨
  (∃ a, AddrCall d 0x7ecebe00 a)

/-- Calldata selecting one of the asset's views with a frame summary: `balanceOf`,
`totalSupply`, `allowance`, `decimals`, `nonces`. -/
def AssetViewData (d : ByteArray) : Prop :=
  (∃ a, AddrCall d balanceOfSelector a) ∨ NoArgCall d 0x18160ddd ∨
  (∃ o s, TwoWordCall d 0xdd62ed3e (Word.ofAddress o) (Word.ofAddress s)) ∨
  NoArgCall d 0x313ce567 ∨ (∃ a, AddrCall d 0x7ecebe00 a)

/-- The cases `DOMAIN_SEPARATOR()` and `permit` are proved for (`Permit.DomainCase`): the
deployment chain, or a name in slot 0 shorter than 32 bytes. A long name on another chain is not
covered (the out-of-place string encoder is not verified). -/
def DomainOk (m : Machine) : Prop :=
  (∀ i : SolmateVault.Immutables,
    m.world.code m.frame.msg.currentTarget = SolmateVault.runtimeCodeWith i →
    Permit.DomainCase i.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256)) ∧
  (∀ ia : SolmateAsset.Immutables,
    m.world.code m.frame.msg.currentTarget = SolmateAsset.runtimeCodeWith ia →
    Permit.DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256))

/-- The views both tokens share whose summaries need more than the calldata: `name()` and
`symbol()` with the gas the stored string needs (`Str.getterGas` of its length), and
`DOMAIN_SEPARATOR()` in the covered cases (`DomainOk`). -/
def TokenViewData (m : Machine) : Prop :=
  (NoArgCall m.frame.msg.data 0x06fdde03 ∧ Str.getterGas (Str.slotLen
    (m.world.sload m.frame.msg.currentTarget 0#256)) ≤ m.frame.gasLeft) ∨
  (NoArgCall m.frame.msg.data 0x95d89b41 ∧ Str.getterGas (Str.slotLen
    (m.world.sload m.frame.msg.currentTarget 1#256)) ≤ m.frame.gasLeft) ∨
  (NoArgCall m.frame.msg.data 0x3644e515 ∧ DomainOk m)

/-- The frame calls one of the views with a frame summary: a view of the vault, a view of the
asset, or a string / domain-separator view of either. -/
def ViewData (vault asset : Address) (m : Machine) : Prop :=
  (m.frame.msg.currentTarget = vault ∧ VaultViewData m.frame.msg.data) ∨
  (m.frame.msg.currentTarget = asset ∧ AssetViewData m.frame.msg.data) ∨
  ((m.frame.msg.currentTarget = vault ∨ m.frame.msg.currentTarget = asset) ∧ TokenViewData m)

theorem viewPost_world {m mf : Machine} {r : Option ℕ} {o : Outcome} (h : ViewPost m r mf o) :
    mf.world = m.world := h.1

theorem halts_world {m : Machine} {H : Machine → Outcome → Prop} (hH : Halts m H)
    (hw : ∀ mf o, H mf o → mf.world = m.world) :
    Halts m (fun mf o => ∀ out, o = .success out → mf.world = m.world) :=
  hH.mono fun mf o _ hp _ _ => hw mf o hp

set_option maxHeartbeats 1000000 in
theorem vaultView_world {minGas : Nat} {m : Machine} (hmin : 60000 ≤ minGas)
    (h : FrameHyp crypto vault asset Act minGas m) (ht : m.frame.msg.currentTarget = vault)
    (hd : VaultViewData m.frame.msg.data) :
    Halts m (fun mf o => ∀ out, o = .success out → mf.world = m.world) := by
  have hval := h.funded.value
  have hsz := h.funded.size
  have hg := h.funded.gas
  obtain ⟨i, hia, hf⟩ := vault_fresh h.start h.dep ht
  have hp := viewPre_of hmin h hia ht hf
  rcases hd with ⟨x, hd⟩ | ⟨x, hd⟩ | ⟨x, hd⟩ | ⟨x, hd⟩ | ⟨x, hd⟩ | ⟨x, hd⟩ | ⟨a, hd⟩ |
    ⟨a, hd⟩ | ⟨a, hd⟩ | ⟨a, hd⟩ | hd | hd | hd | ⟨a, hd⟩ | ⟨o, s, hd⟩ | hd | hd | hd | ⟨a, hd⟩
  · exact halts_world (convertToShares_halts m hp hd) fun _ _ h => h.1
  · exact halts_world (convertToAssets_halts m hp hd) fun _ _ h => h.1
  · exact halts_world (previewDeposit_halts m hp hd) fun _ _ h => h.1
  · exact halts_world (previewMint_halts m hp hd) fun _ _ h => h.1
  · exact halts_world (previewWithdraw_halts m hp hd) fun _ _ h => h.1
  · exact halts_world (previewRedeem_halts m hp hd) fun _ _ h => h.1
  · exact halts_world (maxDeposit_halts m hp hd) fun _ _ h => h.1
  · exact halts_world (maxMint_halts m hp hd) fun _ _ h => h.1
  · exact halts_world (maxWithdraw_halts m hp hd) fun _ _ h => h.1
  · exact halts_world (maxRedeem_halts m hp hd) fun _ _ h => h.1
  · exact halts_world (totalAssets_halts m hp hd) fun _ _ h => h.1
  · exact halts_world (asset_halts m hp hd) fun _ _ h => h.1
  · exact halts_world (sharesTotalSupply_halts m hf hval hd hsz (by omega)) fun _ _ h => h.2
  · exact halts_world (sharesBalanceOf_halts m hf hval hd hsz (by omega)) fun _ _ h => h.2
  · exact halts_world (sharesAllowance_halts m hf hval hd hsz (by omega)) fun _ _ h => h.2
  · exact halts_world (sharesDecimals_halts m hf hval hd hsz (by omega)) fun _ _ h => h.2
  · exact halts_world (vaultBeforeWithdrawCounter_halts m hf hval hd hsz (by omega))
      fun _ _ h => h.2
  · exact halts_world (vaultAfterDepositCounter_halts m hf hval hd hsz (by omega))
      fun _ _ h => h.2
  · exact halts_world (Permit.vault_nonces_halts m hf a hval hd.selector hd.size hsz hd.arg
      (by omega)) fun _ _ h => h.2.1

set_option maxHeartbeats 1000000 in
theorem assetView_world {minGas : Nat} {m : Machine} (hmin : 60000 ≤ minGas)
    (h : FrameHyp crypto vault asset Act minGas m) (ht : m.frame.msg.currentTarget = asset)
    (hd : AssetViewData m.frame.msg.data) :
    Halts m (fun mf o => ∀ out, o = .success out → mf.world = m.world) := by
  have hval := h.funded.value
  have hsz := h.funded.size
  have hg := h.funded.gas
  obtain ⟨ia, hf⟩ := asset_fresh h.start h.dep ht
  rcases hd with ⟨a, hd⟩ | hd | ⟨o, s, hd⟩ | hd | ⟨a, hd⟩
  · exact halts_world (balanceOf_halts m hf a hval hd.selector hd.size hsz hd.arg (by omega))
      fun _ _ h => h.2.1
  · exact halts_world (assetTotalSupply_halts m hf hval hd hsz (by omega)) fun _ _ h => h.2
  · exact halts_world (assetAllowance_halts m hf hval hd hsz (by omega)) fun _ _ h => h.2
  · exact halts_world (assetDecimals_halts m hf hval hd hsz (by omega)) fun _ _ h => h.2
  · exact halts_world (Permit.asset_nonces_halts m hf a hval hd.selector hd.size hsz hd.arg
      (by omega)) fun _ _ h => h.2.1

set_option maxHeartbeats 1000000 in
theorem tokenView_world {minGas : Nat} {m : Machine} (hmin : 60000 ≤ minGas)
    (h : FrameHyp crypto vault asset Act minGas m)
    (ht : m.frame.msg.currentTarget = vault ∨ m.frame.msg.currentTarget = asset)
    (hd : TokenViewData m) :
    Halts m (fun mf o => ∀ out, o = .success out → mf.world = m.world) := by
  have hval := h.funded.value
  have hsz := h.funded.size
  have hg := h.funded.gas
  have hlt := h.funded.gasLt
  rcases ht with ht | ht
  · obtain ⟨i, -, hc⟩ := h.dep.vaultCode
    have hf : Fresh (SolmateVault.runtimeCodeWith i) m := by
      have := h.start.fresh; rw [ht, hc] at this; exact this
    rcases hd with ⟨hd, hgs⟩ | ⟨hd, hgs⟩ | ⟨hd, hdom⟩
    · exact halts_world (vaultName_refines m ⟨hf, hval, hgs, hlt, hsz⟩ hd) fun _ _ h => h.1
    · exact halts_world (vaultSymbol_refines m ⟨hf, hval, hgs, hlt, hsz⟩ hd) fun _ _ h => h.1
    · exact halts_world (Permit.vault_domainSeparator_halts m hf hval hd.selector hd.size hsz
        (hdom.1 i (by rw [ht, hc])) (by omega) hlt) fun _ _ h => h.2.1
  · obtain ⟨ia, hc⟩ := h.dep.assetCode
    have hf : Fresh (SolmateAsset.runtimeCodeWith ia) m := by
      have := h.start.fresh; rw [ht, hc] at this; exact this
    rcases hd with ⟨hd, hgs⟩ | ⟨hd, hgs⟩ | ⟨hd, hdom⟩
    · exact halts_world (assetName_refines m ⟨hf, hval, hgs, hlt, hsz⟩ hd) fun _ _ h => h.1
    · exact halts_world (assetSymbol_refines m ⟨hf, hval, hgs, hlt, hsz⟩ hd) fun _ _ h => h.1
    · exact halts_world (Permit.asset_domainSeparator_halts m hf hval hd.selector hd.size hsz
        (hdom.2 ia (by rw [ht, hc])) (by omega) hlt) fun _ _ h => h.2.1

/-- **The covered views, in any frame**: on success the world is unchanged. -/
theorem frameOk_view {minGas : Nat} {m : Machine} (hmin : 60000 ≤ minGas)
    (h : FrameHyp crypto vault asset Act minGas m) (hv : ViewData vault asset m) :
    FrameOk crypto vault asset Act K m := by
  refine frameOk_of_world h.dep ?_
  rcases hv with ⟨ht, hd⟩ | ⟨ht, hd⟩ | ⟨ht, hd⟩
  · exact vaultView_world hmin h ht hd
  · exact assetView_world hmin h ht hd
  · exact tokenView_world hmin h ht hd

/-! ## Calls carrying value -/

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

/-! ## Unknown selectors and short calldata -/

/-- The calldata selects no function of the called contract: shorter than four bytes, or a
selector outside `vaultSelectors` / `assetSelectors`. -/
def UnknownData (vault asset : Address) (m : Machine) : Prop :=
  m.frame.msg.data.size < 4 ∨
  (4 ≤ m.frame.msg.data.size ∧
    (m.frame.msg.currentTarget = vault → Abi.selectorOf m.frame.msg.data ∉ vaultSelectors) ∧
    (m.frame.msg.currentTarget = asset → Abi.selectorOf m.frame.msg.data ∉ assetSelectors))

/-- **Calldata selecting no function**, in any frame without value: the dispatcher reverts
(at least 1000 gas). -/
theorem frameOk_unknown {m : Machine} (hv : VaultStart vault asset m)
    (hdep : Deployed m.world vault asset) (hval : m.frame.msg.value = 0)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 1000 ≤ m.frame.gasLeft)
    (hu : UnknownData vault asset m) : FrameOk crypto vault asset Act K m := by
  have hrev : Halts m (fun _ o => ∃ out, o = .revert out) := by
    rcases hv.prot with ht | ht
    · obtain ⟨i, -, hf⟩ := vault_fresh hv hdep ht
      rcases hu with hu | ⟨h4, hu, -⟩
      · exact vault_short_reverts m hf hval hu hg
      · exact vault_unknown_reverts m hf hval h4 hsz hg (hu ht)
    · obtain ⟨ia, hf⟩ := asset_fresh hv hdep ht
      rcases hu with hu | ⟨h4, -, hu⟩
      · exact asset_short_reverts m hf hval hu hg
      · exact asset_unknown_reverts m hf hval h4 hsz hg (hu ht)
  exact hrev.mono fun _ _ _ ⟨out, ho⟩ out' ho' => by rw [ho] at ho'; cases ho'

/-! ## Malformed calldata -/

/-- The calldata selects a function of the called contract that takes arguments, but is
malformed for its ABI decoder (`Malformed`: too few argument words, or a dirty `address`
argument after clean ones). -/
def MalformedData (vault asset : Address) (m : Machine) : Prop :=
  4 ≤ m.frame.msg.data.size ∧ ∃ k addrs,
    ((m.frame.msg.currentTarget = vault ∧
        (Abi.selectorOf m.frame.msg.data, k, addrs) ∈ vaultArgShapes) ∨
      (m.frame.msg.currentTarget = asset ∧
        (Abi.selectorOf m.frame.msg.data, k, addrs) ∈ assetArgShapes)) ∧
    Malformed m.frame.msg.data k addrs

/-- **Malformed calldata**, in any frame without value: the ABI decoder reverts (at least 2000
gas). -/
theorem frameOk_malformed {m : Machine} (hv : VaultStart vault asset m)
    (hdep : Deployed m.world vault asset) (hval : m.frame.msg.value = 0)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 2000 ≤ m.frame.gasLeft)
    (hu : MalformedData vault asset m) : FrameOk crypto vault asset Act K m := by
  obtain ⟨h4, k, addrs, ht, hbad⟩ := hu
  have hrev : Halts m (fun _ o => ∃ out, o = .revert out) := by
    rcases ht with ⟨ht, hmem⟩ | ⟨ht, hmem⟩
    · obtain ⟨i, -, hf⟩ := vault_fresh hv hdep ht
      exact vault_malformed_reverts m hf hval hsz hg hmem rfl h4 hbad
    · obtain ⟨ia, hf⟩ := asset_fresh hv hdep ht
      exact asset_malformed_reverts m hf hval hsz hg hmem rfl h4 hbad
  exact hrev.mono fun _ _ _ ⟨out, ho⟩ out' ho' => by rw [ho] at ho'; cases ho'

end Examples.Solmate.ERC4626.Nested
