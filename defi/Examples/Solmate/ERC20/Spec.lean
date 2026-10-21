import Examples.Solmate.ERC20.SpecView
import Examples.Solmate.ERC20.Transfer
import Examples.Solmate.ERC20.TransferFrom

/-!
# The asset's functions refine the model's `Token` operations, in any frame

The asset's callee summaries stated against the model ledger (`Shares.Rep`/`Shares.RepOn`):
`assetTransfer_refines`, `assetTransferFrom_refines` (success with a represented `t'` when the
model returns `some t'`, revert on `none`); `assetBalanceOf_refines` is in `SpecView`. Hypotheses:
`BalanceSlotOk`/`AllowanceSlotOk` for the written entries and `Token.WF` (the unchecked
`balanceOf[to] += amount` does not wrap). See `docs/erc4626/details.md` §2.
-/

namespace Examples.Solmate.ERC20
open Examples.Solmate.ERC4626 Defi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open EvmLogic.Solidity.ERC20 (transferWorld view_transferWorld)
open Defi.Math Defi.ERC20 Examples.Solmate.ERC4626.Shares

/-- Allowance entries represented after `transfer`: those in neither written balance slot. -/
def TransferAllowances (crypto : Crypto) (src dst : Address) (o sp : Address) : Prop :=
  ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp ≠
      ERC20.balanceSlot crypto ERC20.Layout.solmate src ∧
    ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp ≠
      ERC20.balanceSlot crypto ERC20.Layout.solmate dst

/-- **The asset's `transfer` refines `Token.transfer`**, in any non-static frame. -/
theorem assetTransfer_refines {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {dst : Address} {amount : Word}
    (hd : TwoWordCall m.frame.msg.data 0xa9059cbb (Word.ofAddress dst) amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 60000 ≤ m.frame.gasLeft)
    (hs : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)
    (hdst : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate dst)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    match t.transfer m.frame.msg.caller dst amount.toNat with
    | some t' => Halts m (fun mf o => TransferOk dst amount m mf o ∧
        RepOn (TransferAllowances m.ctx.crypto m.frame.msg.caller dst)
          (ERC20.view m.ctx.crypto ERC20.Layout.solmate mf.world m.frame.msg.currentTarget) t')
    | none => Halts m (Reverts 10000 m) := by
  split
  · rename_i t' hT
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1
      ((transfer_isSome_iff hr m.frame.msg.caller dst amount).2 (by simp [hT]))
    have hbal : amount.toNat ≤ (m.world.sload m.frame.msg.currentTarget
        (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)).toNat := by
      unfold ERC20.Model.transfer at hm
      split at hm
      · assumption
      · cases hm
    obtain ⟨h1, h2, h3, -⟩ := view_transferWorld (token := m.frame.msg.currentTarget) hs hdst hm
    have hrep := rep_transfer hr hw hm hT
    refine (transfer_halts_ok m hf hval hstatic hd hsz hg hbal).mono fun mf o _ hok => ⟨hok, ?_⟩
    rw [hok.2.1]
    exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1 hp.2) hrep
  · rename_i hT
    have hbal : (m.world.sload m.frame.msg.currentTarget
        (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate m.frame.msg.caller)).toNat <
          amount.toNat := by
      have := hr.balanceOf m.frame.msg.caller
      simp only [ERC20.view] at this
      rw [this]
      unfold Token.transfer at hT
      split at hT
      · assumption
      · cases hT
    exact transfer_halts_revert m hf hval hd hsz (by omega) hbal

/-- Allowance entries represented after `transferFrom`. -/
def TransferFromAllowances (crypto : Crypto) (spender src dst : Address) (o sp : Address) :
    Prop :=
  TransferAllowances crypto src dst o sp ∧
    ((o = src ∧ sp = spender) ∨ ERC20.allowanceSlot crypto ERC20.Layout.solmate o sp ≠
      ERC20.allowanceSlot crypto ERC20.Layout.solmate src spender)

/-- **The asset's `transferFrom` refines `Token.transferFrom`**, in any non-static frame. -/
theorem assetTransferFrom_refines {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {src dst : Address} {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (hs : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate src)
    (hdst : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate dst)
    (ha : ERC20.AllowanceSlotOk m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.caller)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    match t.transferFrom m.frame.msg.caller src dst amount.toNat with
    | some t' => Halts m (fun mf o => TransferFromOk src dst amount m mf o ∧
        RepOn (TransferFromAllowances m.ctx.crypto m.frame.msg.caller src dst)
          (ERC20.view m.ctx.crypto ERC20.Layout.solmate mf.world m.frame.msg.currentTarget) t')
    | none => Halts m (Reverts 80000 m) := by
  split
  · rename_i t' hT
    obtain ⟨t₁, hsp, htr⟩ := Option.bind_eq_some_iff.1 hT
    obtain ⟨s₁, hm₁⟩ := Option.isSome_iff_exists.1
      ((spend_isSome_iff hr src m.frame.msg.caller amount).2 (by simp [hsp]))
    have hal := allowance_cond_of_spend hr hsp
    have hbal : amount.toNat ≤ ((ERC20.spendWorld m.ctx.crypto m.world m.frame.msg.currentTarget
        src m.frame.msg.caller amount).sload m.frame.msg.currentTarget
          (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate src)).toNat := by
      rw [balance_spendWorld ha hm₁, hr.balanceOf src, ← (Token.spend_eq_some hsp).1]
      exact (Token.transfer_eq_some.1 htr).1
    obtain ⟨s', hm⟩ := Option.isSome_iff_exists.1
      ((transferFrom_isSome_iff hr m.frame.msg.caller src dst amount).2 (by simp [hT]))
    obtain ⟨h1, h2, h3, -⟩ := ERC20.view_transferFromWorld hs hdst ha hm
    have hrep := rep_transferFrom hr hw hm hT
    refine (transferFrom_halts_ok m hf hval hstatic hd hsz hg hal hbal).mono
      fun mf o _ hok => ⟨hok, ?_⟩
    rw [hok.2.1]
    exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1.1 hp.1.2 hp.2) hrep
  · rename_i hT
    refine transferFrom_halts_revert m hf hval hstatic hd hsz hg ?_
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
          · simp only [ERC20.view] at ha'; omega
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

end Examples.Solmate.ERC20
