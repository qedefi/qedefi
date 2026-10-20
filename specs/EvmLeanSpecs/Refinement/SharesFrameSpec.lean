import EvmLeanSpecs.Refinement.SharesFrame

/-!
# The vault's share-token functions refine `Token`, in any frame

Model-level versions of `SharesFrame.lean`, in the shape of `AssetSpec.lean`: from a fresh frame
of the vault's code (any parents) whose share storage represents a well-formed ledger `t`
(`Shares.Rep`, `Token.WF`):

* `sharesTransfer_refines`: `match t.transfer caller dst amount` — `some t'`: `TransferOk` and
  the new share storage represents `t'` on the allowances whose slot is not a written balance
  slot; `none`: a revert;
* `sharesTransferFrom_refines`: likewise for `Token.transferFrom`;
* `sharesApprove_refines`: always succeeds; the new storage represents `Token.approve`.

Hash hypotheses as in the asset's versions: `BalanceSlotOk` for the balances written,
`AllowanceSlotOk` for the allowance written.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLean.Solidity.Examples.SolmateAssetTransfer (transferWorld view_transferWorld)
open Vault Shares

/-- **`transfer(dst, amount)` of the vault's shares refines `Token.transfer`**, in any
non-static frame. -/
theorem sharesTransfer_refines {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {dst : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hs : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller)
    (hdst : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate dst)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    match t.transfer m.frame.msg.caller dst amount.toNat with
    | some t' => Halts m (fun mf o => TransferOk dst amount m mf o ∧
        RepOn (TransferAllowances m.ctx.crypto m.frame.msg.caller dst)
          (Erc20.view m.ctx.crypto Erc20.Layout.solmate mf.world m.frame.msg.currentTarget) t')
    | none => Halts m (Reverts 10000 m) := by
  split
  · rename_i t' hT
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1
      ((transfer_isSome_iff hr m.frame.msg.caller dst amount).2 (by simp [hT]))
    have hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
        (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller)).toNat := by
      unfold Erc20.Model.transfer at hm
      split at hm
      · assumption
      · cases hm
    obtain ⟨h1, h2, h3, -⟩ := view_transferWorld (token := m.frame.msg.currentTarget) hs hdst hm
    have hrep := rep_transfer hr hw hm hT
    refine (sharesTransfer_halts_ok m hf hval hstatic hd hsz hg hbal).mono
      fun mf o _ hok => ⟨hok, ?_⟩
    rw [hok.2.1]
    exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1 hp.2) hrep
  · rename_i hT
    have hbal : (m.world.sload m.frame.msg.currentTarget
        (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller)).toNat <
          amount.toNat := by
      have := hr.balanceOf m.frame.msg.caller
      simp only [Erc20.view] at this
      rw [this]
      unfold Token.transfer at hT
      split at hT
      · assumption
      · cases hT
    exact sharesTransfer_halts_revert m hf hval hd hsz (by omega) hbal

/-- **`transferFrom(src, dst, amount)` of the vault's shares refines `Token.transferFrom`**,
in any non-static frame. -/
theorem sharesTransferFrom_refines {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {src dst : Address} {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (hs : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate src)
    (hdst : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate dst)
    (ha : Erc20.AllowanceSlotOk m.ctx.crypto Erc20.Layout.solmate src m.frame.msg.caller)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    match t.transferFrom m.frame.msg.caller src dst amount.toNat with
    | some t' => Halts m (fun mf o => TransferFromOk src dst amount m mf o ∧
        RepOn (TransferFromAllowances m.ctx.crypto m.frame.msg.caller src dst)
          (Erc20.view m.ctx.crypto Erc20.Layout.solmate mf.world m.frame.msg.currentTarget) t')
    | none => Halts m (Reverts 80000 m) := by
  split
  · rename_i t' hT
    obtain ⟨t₁, hsp, htr⟩ := Option.bind_eq_some_iff.1 hT
    obtain ⟨s₁, hm₁⟩ := Option.isSome_iff_exists.1
      ((spend_isSome_iff hr src m.frame.msg.caller amount).2 (by simp [hsp]))
    have hal := allowance_cond_of_spend hr hsp
    have hbal : amount.toNat ≤ ((Erc20.spendWorld m.ctx.crypto m.world m.frame.msg.currentTarget
        src m.frame.msg.caller amount).sload m.frame.msg.currentTarget
          (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate src)).toNat := by
      rw [balance_spendWorld ha hm₁, hr.balanceOf src, ← (Token.spend_eq_some hsp).1]
      exact (Token.transfer_eq_some.1 htr).1
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1
      ((transferFrom_isSome_iff hr m.frame.msg.caller src dst amount).2 (by simp [hT]))
    obtain ⟨h1, h2, h3, -⟩ := Erc20.view_transferFromWorld hs hdst ha hm
    have hrep := rep_transferFrom hr hw hm hT
    refine (sharesTransferFrom_halts_ok m hf hval hstatic hd hsz hg hal hbal).mono
      fun mf o _ hok => ⟨hok, ?_⟩
    rw [hok.2.1]
    exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1.1 hp.1.2 hp.2) hrep
  · rename_i hT
    refine sharesTransferFrom_halts_revert m hf hval hstatic hd hsz hg ?_
    rintro ⟨hal, hbal⟩
    cases hsp : t.spend src m.frame.msg.caller amount.toNat with
    | none =>
      have ha' := hr.allowance src m.frame.msg.caller trivial
      unfold Token.spend at hsp
      split at hsp
      · cases hsp
      · rename_i hmax
        split at hsp
        · rename_i hlt
          rcases hal with h | h
          · exact hmax (by rw [← ha']; exact (eq_maxWord_iff _).1 h)
          · simp only [Erc20.view] at ha'; omega
        · cases hsp
    | some t₁ =>
      have htr : t₁.transfer src dst amount.toNat = none := by
        unfold Token.transferFrom at hT
        rw [hsp] at hT
        simpa using hT
      obtain ⟨s₁, hm₁⟩ := Option.isSome_iff_exists.1
        ((spend_isSome_iff hr src m.frame.msg.caller amount).2 (by simp [hsp]))
      rw [balance_spendWorld ha hm₁, hr.balanceOf src, ← (Token.spend_eq_some hsp).1] at hbal
      unfold Token.transfer at htr
      split at htr
      · omega
      · cases htr

/-- **`approve(spender, amount)` of the vault's shares refines `Token.approve`**, in any
non-static frame. -/
theorem sharesApprove_refines {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {spender : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0x095ea7b3 (Word.ofAddress spender) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 40000 ≤ m.frame.gasLeft)
    (ha : Erc20.AllowanceSlotOk m.ctx.crypto Erc20.Layout.solmate m.frame.msg.caller spender)
    {t : Token Address} (hr : Rep (assetView m) t) :
    Halts m (fun mf o => ApproveOk spender amount m mf o ∧
      RepOn (ApproveAllowances m.ctx.crypto m.frame.msg.caller spender)
        (Erc20.view m.ctx.crypto Erc20.Layout.solmate mf.world m.frame.msg.currentTarget)
        (t.approve m.frame.msg.caller spender amount.toNat)) := by
  obtain ⟨h1, h2, h3, -⟩ := Erc20.view_approveWorld (w := m.world)
    (token := m.frame.msg.currentTarget) (amount := amount) ha
  refine (sharesApprove_halts m hf hval hstatic hd hsz hg).mono fun mf o _ hok => ⟨hok, ?_⟩
  rw [hok.2.1]
  exact RepOn.of_eq h1 h2 h3 (rep_approve hr m.frame.msg.caller spender amount)

end EvmLeanSpecs.Refinement
