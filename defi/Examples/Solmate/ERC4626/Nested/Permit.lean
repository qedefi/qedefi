import Examples.Solmate.ERC4626.Nested.Views

/-!
# `permit` in any frame, as a modelled call

`abs` has no nonces: under `NonceSlotOk` the nonce write of `permitWorld` is invisible to it
(`agree_permitWorld_vault`, `agree_permitWorld_asset`), so a successful `permit` frame commits the
owner's approval (`.approve`/`.assetApprove` with the owner as `caller`): `frameOk_permit`.
Top-level traces have no `permit` call. See `docs/erc4626/details.md` §7.
-/

namespace Examples.Solmate.ERC4626.Nested
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.Math Defi.ERC20 Defi.ERC4626.Solmate Defi.Trace.Lift
open Examples.Solmate.ERC4626.Invariants Examples.Solmate.ERC20.Permit
open Examples.Solmate.ERC4626.Permit

variable {crypto : Crypto} {vault asset : Address} {Act : List Address} {K : VCall → Prop}

/-! ## Frames running `permit` -/

/-- The frame runs `permit(owner, spender, value, …)` at the vault or the asset, and `c` is the
call it commits on success: the owner's approval of `spender` for `value` on that token. -/
def PermitData (vault asset : Address) (m : Machine) : VCall → Prop
  | .approve o sp v => m.frame.msg.currentTarget = vault ∧
      ∃ dl v' r s, PermitCall m.frame.msg.data o sp v dl v' r s
  | .assetApprove o sp v => m.frame.msg.currentTarget = asset ∧
      ∃ dl v' r s, PermitCall m.frame.msg.data o sp v dl v' r s
  | _ => False

/-- The frame conditions of the `permit` theorems beyond `Funded`: `DomainOk`, `0x01` not
EIP-7702-delegated (always true before Prague, and unless someone holds the key of `0x01`), and
room for the precompile call. -/
structure PermitFrame (m : Machine) : Prop where
  domain : DomainOk m
  ecrecover : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none
  depth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit

/-- **The hash hypothesis of a permit's owner `a`**: its nonce slot `keccak(a ‖ 5)` is fresh
among the address-keyed preimages of slots 3, 4, 5, is none of the fixed slots 2, 6, 7, and is
no actor pair's allowance slot. -/
structure NonceSlotOk (crypto : Crypto) (Act : List Address) (a : Address) : Prop where
  /-- One target against `3 · 2¹⁶⁰` candidates; in particular no balance slot. -/
  fresh : KeccakFresh crypto (AddressKeyed [3#256, 4#256, 5#256])
    (slotPreimage (Word.ofAddress a) 5#256)
  total : nonceSlot crypto a ≠ 2#256
  hook6 : nonceSlot crypto a ≠ 6#256
  hook7 : nonceSlot crypto a ≠ 7#256
  allow : ∀ o ∈ Act, ∀ sp ∈ Act,
    ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp ≠ nonceSlot crypto a

theorem permitSlotsOk_of (hs : SlotsOk crypto vault Act) {o sp : Address} (ho : o ∈ Act)
    (hsp : sp ∈ Act) (hn : NonceSlotOk crypto Act o) : PermitSlotsOk crypto o sp :=
  ⟨hs.allow o ho sp hsp, hn.fresh, hn.total, hn.allow o ho sp hsp⟩

theorem permitAllowances_of (hs : SlotsOk crypto vault Act) {o sp : Address} (ho : o ∈ Act)
    (hsp : sp ∈ Act) (hn : NonceSlotOk crypto Act o) :
    ∀ o' sp', ActorPairs Act o' sp' → PermitAllowances crypto o sp o' sp' := by
  intro o' sp' ⟨ho', hsp'⟩
  refine ⟨?_, hn.allow o' ho' sp' hsp'⟩
  by_cases he : o' = o ∧ sp' = sp
  · exact .inl he
  · exact .inr fun h => he (hs.allowInj o' ho' sp' hsp' o ho sp hsp h)

theorem permit_true (t : PermitToken Address) (o sp : Address) (v : ℕ) :
    t.permit o sp v (fun _ => True) =
      some ⟨t.token.approve o sp v, t.nonces.update o ((t.nonces o + 1) % U256)⟩ := rfl

/-! ## The nonce write is invisible to the abstraction -/

/-- **`permit` of the vault's shares, in the abstraction**: `permitWorld` agrees (up to
non-actor allowances) with the model's `approve(o → sp, value)` on the shares. -/
theorem agree_permitWorld_vault (hs : SlotsOk crypto vault Act) (hne : vault ≠ asset)
    {w : World} {o sp : Address} {v : Word} (ho : o ∈ Act) (hsp : sp ∈ Act)
    (hn : NonceSlotOk crypto Act o) :
    AgreeOn (ActorPairs Act) (abs crypto (permitWorld crypto w vault o sp v) vault asset)
      { abs crypto w vault asset with
        shares := (abs crypto w vault asset).shares.approve o sp v.toNat } := by
  have hrep := (rep_permitWorld (permitSlotsOk_of hs ho hsp hn)
    (permit_true (permitView crypto w vault) o sp v.toNat)).ledger
  have hf := hs.allowFixed o ho sp hsp
  exact agree_of_shares hrep (permitAllowances_of hs ho hsp hn)
    (fun k => sload_permitWorld (.inl hne.symm))
    (sload_permitWorld (.inr ⟨hn.hook6.symm, hf.1.symm⟩))
    (sload_permitWorld (.inr ⟨hn.hook7.symm, hf.2.symm⟩))

/-- **`permit` of the asset, in the abstraction**: `permitWorld` agrees (up to non-actor
allowances) with the model's `approve(o → sp, value)` on the asset. -/
theorem agree_permitWorld_asset (hs : SlotsOk crypto vault Act) (hne : vault ≠ asset)
    {w : World} {o sp : Address} {v : Word} (ho : o ∈ Act) (hsp : sp ∈ Act)
    (hn : NonceSlotOk crypto Act o) :
    AgreeOn (ActorPairs Act) (abs crypto (permitWorld crypto w asset o sp v) vault asset)
      { abs crypto w vault asset with
        asset := (abs crypto w vault asset).asset.approve o sp v.toNat } := by
  have hrep := (rep_permitWorld (permitSlotsOk_of hs ho hsp hn)
    (permit_true (permitView crypto w asset) o sp v.toNat)).ledger
  exact agree_of_asset hrep (permitAllowances_of hs ho hsp hn)
    (fun k => sload_permitWorld (.inl hne))

/-! ## The frame summary -/

theorem permitPost_success {ds : Word} {o sp : Address} {v dl v' r s : Word} {m mf : Machine}
    {out : ByteArray} (h : PermitPost ds o sp v dl v' r s m mf (.success out)) :
    mf.world = permitWorld m.ctx.crypto m.world m.frame.msg.currentTarget o sp v := by
  obtain ⟨h1, h2, -⟩ := h
  by_cases hv : PermitValid m.ctx.crypto ds m.ctx.block.timestamp o sp v dl v' r s
      (m.world.sload m.frame.msg.currentTarget (nonceSlot m.ctx.crypto o))
  · exact (h1 hv).2.1
  · obtain ⟨_, he⟩ := h2 hv; cases he

set_option maxHeartbeats 1000000 in
/-- **`permit` of either token, in any frame**: a funded frame running `permit` (`PermitData`)
under `PermitFrame` satisfies `FrameOk`, committing the owner's approval `c` (admitted), under
the owner's `NonceSlotOk`. -/
theorem frameOk_permit {minGas : Nat} {m : Machine} (hmin : 100000 ≤ minGas)
    (h : FrameHyp crypto vault asset Act minGas m) (hp : PermitFrame m) {c : VCall}
    (hx : PermitData vault asset m c) (hadm : Admitted Act K c)
    (hn : NonceSlotOk crypto Act c.caller) :
    FrameOk crypto vault asset Act K m := by
  have hcr := h.hash
  have hdep := h.dep
  have hne := hdep.vault_ne_asset
  have hs := h.slots
  have hg : 100000 ≤ m.frame.gasLeft := Nat.le_trans hmin h.funded.gas
  cases c with
  | approve o sp v =>
    obtain ⟨ht, dl, v', r, s, hd⟩ := hx
    have ho : o ∈ Act := hadm.1 o (by simp [VCall.actors])
    have hsp : sp ∈ Act := hadm.1 sp (by simp [VCall.actors])
    obtain ⟨i, -, hc⟩ := hdep.vaultCode
    have hf : Fresh (SolmateVault.runtimeCodeWith i) m := by
      have := h.start.fresh; rw [ht, hc] at this; exact this
    have H := vault_permit_halts m hf h.funded.value h.start.static hd h.funded.size
      (hp.domain.1 i (by rw [ht, hc])) hg h.funded.gasLt h.start.pre hp.ecrecover hp.depth
    refine frameOk_one hadm (H.mono fun mf o' _ hpost out ho' => ?_)
    subst ho'
    have hw := permitPost_success hpost
    rw [hcr, ht] at hw
    rw [hw]
    refine ⟨hdep.of_code (code_permitWorld ..) (code_permitWorld ..), ?_⟩
    rw [stepD_of_some (s' := { abs crypto m.world vault asset with
      shares := (abs crypto m.world vault asset).shares.approve o sp v.toNat }) rfl]
    exact agree_permitWorld_vault hs hne ho hsp hn
  | assetApprove o sp v =>
    obtain ⟨ht, dl, v', r, s, hd⟩ := hx
    have ho : o ∈ Act := hadm.1 o (by simp [VCall.actors])
    have hsp : sp ∈ Act := hadm.1 sp (by simp [VCall.actors])
    obtain ⟨ia, hc⟩ := hdep.assetCode
    have hf : Fresh (SolmateAsset.runtimeCodeWith ia) m := by
      have := h.start.fresh; rw [ht, hc] at this; exact this
    have H := asset_permit_halts m hf h.funded.value h.start.static hd h.funded.size
      (hp.domain.2 ia (by rw [ht, hc])) hg h.funded.gasLt h.start.pre hp.ecrecover hp.depth
    refine frameOk_one hadm (H.mono fun mf o' _ hpost out ho' => ?_)
    subst ho'
    have hw := permitPost_success hpost
    rw [hcr, ht] at hw
    rw [hw]
    refine ⟨hdep.of_code (code_permitWorld ..) (code_permitWorld ..), ?_⟩
    rw [stepD_of_some (s' := { abs crypto m.world vault asset with
      asset := (abs crypto m.world vault asset).asset.approve o sp v.toNat }) rfl]
    exact agree_permitWorld_asset hs hne ho hsp hn
  | _ => exact hx.elim

end Examples.Solmate.ERC4626.Nested
