import EvmLeanSpecs.Refinement.DepositInternal
import EvmLeanSpecs.Refinement.EventsAssetTransferFrom
import EvmLeanSpecs.Refinement.EventsTactic

/-!
# Logs of `deposit` / `mint`'s internal functions

Companions of `safeTransferFrom_wp` (`AssetCallIn.lean`), `mintShares_wp` and
`afterDeposit_wp` (`DepositInternal.lean`) that also determine the logs of the substate each
returns with:

* `assetTransferFrom_halts_logs`: the asset's `transferFrom` as a callee summary
  (`assetTransferFrom_halts`), with the child frame's logs on success (its `Transfer`);
* `safeTransferFrom_wp_logs`: on success the vault frame's logs gain the asset's
  `Transfer(src, dst, amount)` (the child's logs, merged on return);
* `mintShares_wp_logs`: `_mint` appends the vault's `Transfer(0, to, amount)`;
* `afterDeposit_wp_logs`: the hook emits nothing.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault Shares

/-- `assetTransferFrom_halts` with the child frame's logs on success: the callee summary of
the asset's `transferFrom` that `safeTransferFrom_wp_logs` uses. -/
theorem assetTransferFrom_halts_logs {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {src dst : Address} {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (hs : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate src)
    (hdst : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate dst)
    (ha : Erc20.AllowanceSlotOk m.ctx.crypto Erc20.Layout.solmate src m.frame.msg.caller)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    Halts m (fun mf o =>
      (∃ t', t.transferFrom m.frame.msg.caller src dst amount.toNat = some t' ∧
        TransferFromOk src dst amount m mf o ∧
        RepOn (TransferFromAllowances m.ctx.crypto m.frame.msg.caller src dst)
          (Erc20.view m.ctx.crypto Erc20.Layout.solmate mf.world m.frame.msg.currentTarget) t' ∧
        mf.frame.sub.logs = m.frame.sub.logs.push
          (transferLog m.frame.msg.currentTarget src dst amount)) ∨
      (t.transferFrom m.frame.msg.caller src dst amount.toNat = none ∧ Reverts 80000 m mf o)) := by
  cases hT : t.transferFrom m.frame.msg.caller src dst amount.toNat with
  | some t' =>
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
    refine (transferFrom_halts_ok_events m hf hval hstatic hd hsz hg hal hbal).mono
      fun mf o _ ⟨hok, hl⟩ => .inl ⟨t', rfl, hok, ?_, hl⟩
    rw [hok.2.1]
    exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1.1 hp.1.2 hp.2) hrep
  | none =>
    have h := assetTransferFrom_refines m hf hval hstatic hd hsz hg hs hdst ha hr hw
    rw [hT] at h
    exact h.mono fun _ _ _ h => .inr ⟨rfl, h⟩

set_option maxHeartbeats 0 in
/-- **With its log** (`safeTransferFrom_wp`, and on success the frame's logs gain the asset's
`Transfer(src, dst, amount)`, emitted in the child frame and kept by the merge): **`safeTransferFrom(asset, src, dst, amount)` (internal, entry `0x0f38`, stack
`amount :: dst :: src :: asset :: r :: rest`)**: Solmate's `SafeTransferLib.safeTransferFrom`
in the vault (immutables `i`). It writes the calldata of `transferFrom(src, dst, amount)` at the
free pointer, `CALL`s the asset with all remaining gas and no value (`WP.call0`, the asset's
callee summary `assetTransferFrom_halts`), and checks `success && (returndata == 1 ||
(returndatasize == 0 && extcodesize(asset) > 0))`. When the model's
`Token.transferFrom` of the asset ledger (spender: the vault) succeeds, the call returns
`true`, the check passes and the function returns to `r` with the asset's `transferFrom`
writes applied to the world (`Erc20.transferFromWorld`), whose asset view represents the
model's ledger; otherwise the asset reverts and so does the vault
(`TRANSFER_FROM_FAILED`). -/
theorem safeTransferFrom_wp_logs {i : SolmateVault.Immutables} (m : Machine) {amount r : Word}
    {src dst : Address} {rest : List Word}
    (hv : VaultFrame i m) (hstatic : m.frame.msg.isStatic = false)
    (hpc : m.frame.pc = 0xf38)
    (hs : m.frame.stack = amount :: Word.ofAddress dst :: Word.ofAddress src ::
      Word.ofAddress i.asset :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpOk m.frame.memory)
    (hg : 100000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hbs : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate src)
    (hbd : Erc20.BalanceSlotOk m.ctx.crypto Erc20.Layout.solmate dst)
    (ha : Erc20.AllowanceSlotOk m.ctx.crypto Erc20.Layout.solmate src m.frame.msg.currentTarget)
    (hwf : (tokenView m.ctx.crypto m.world i.asset).WF) :
    WP m (fun m' => ∃ t', (tokenView m.ctx.crypto m.world i.asset).transferFrom
          m.frame.msg.currentTarget src dst amount.toNat = some t' ∧
        RepOn (TransferFromAllowances m.ctx.crypto m.frame.msg.currentTarget src dst)
          (Erc20.view m.ctx.crypto Erc20.Layout.solmate (Erc20.transferFromWorld m.ctx.crypto
            m.world i.asset m.frame.msg.currentTarget src dst amount) i.asset) t' ∧
        ∃ mem g rd sub,
          m' = { m.resumeWith r.toNat rest mem g rd sub with
            world := Erc20.transferFromWorld m.ctx.crypto m.world i.asset
              m.frame.msg.currentTarget src dst amount } ∧
          FmpAfterTransfer mem ∧ m.frame.gasLeft ≤ g + 90000 ∧
          sub.logs = m.frame.sub.logs.push (transferLog i.asset src dst amount))
      (fun _ o => (tokenView m.ctx.crypto m.world i.asset).transferFrom
          m.frame.msg.currentTarget src dst amount.toNat = none ∧ ∃ out, o = .revert out) := by
  obtain ⟨hc, hj, ⟨ia, hcode⟩, hpre, hdepth⟩ := hv
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  have hacc := accessCost_le (m_sub.accessedAddresses.contains i.asset)
  have hmod : ∀ k, (m_gasLeft - k) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      m_gasLeft - k := fun k => Nat.mod_eq_of_lt (by omega)
  have hto : Word.toAddress (Word.ofAddress i.asset) = i.asset := Word.toAddress_ofAddress _
  have hdel := delegatedAddress?_assetCode ia
  rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩ <;>
  · pwp_steps [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress]
    refine WP.call0 (by pcode_fact) rfl ?_ ?_ hdepth ?_
      (assetTransferFrom_halts_logs (ia := ia) (t := tokenView m_ctx.crypto m_world i.asset)
        (src := src) (dst := dst) (amount := amount) _ ?_ ?_ ?_
        ?_ ?_ ?_ hbs hbd ha ?_ hwf) ?_
    · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
    · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod, hmod]
      rw [messageCallGas_zero (by evm_gas)]
      simp only [Gas.maxMessageCallGas]
      evm_gas
    · rw [hto]; exact hpre
    · exact ⟨_, _, _, rfl, by dsimp only [childMsg]; rw [hto, hcode]⟩
    · rfl
    · dsimp only [Frame.init, childMsg]; simp [hstatic]
    · dsimp only [call0Child, Frame.init, childMsg, callMemory]
      simp only [BitVec.reduceToNat, readBytes_bytes]
      refine ⟨?_, by simp, ?_, ?_, ?_⟩
      · simp only [Abi.selectorOf]
        rw [Memory.readBytes_read _ _ 100 0 4 (by decide)]
        simp (disch := decide) only [Memory.read_expand, Nat.add_zero,
          Memory.read_storeWord_of_disjoint, Memory.read_storeWord_prefix]
        decide +kernel
      all_goals
        rw [Memory.readBytes_read _ _ 100 _ 32 (by decide)]
        simp (disch := decide) only [Memory.read_expand, Nat.reduceAdd,
          Memory.read_storeWord_of_disjoint, Memory.read_storeWord, Bytes.toWord_ofWord]
    · dsimp only [call0Child, Frame.init, childMsg]
      simp
    · dsimp only [call0Child, Frame.init, childMsg]
      simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod, hmod]
      rw [messageCallGas_zero (by evm_gas)]
      simp only [Gas.maxMessageCallGas]
      evm_gas
    · dsimp only [assetView, call0Child, Frame.init, childMsg]; rw [hto]; exact rep_toToken _
    · intro mf o hc hsame
      have hk : mf.frame.kind = .call 0 32 := hsame.kind
      have hs1 : mf.ctx = m_ctx := hsame.ctx
      have hs2 : mf.precompiles = m_pre := hsame.precompiles
      have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
      rcases hc with ⟨t', hT, ⟨ho, hw, ht, hca, hgasB⟩, hrep, hlogs⟩ | ⟨hT, ⟨out, ho⟩, hgasB⟩
      · subst ho
        rw [resumeAfter_success hk]
        dsimp only at hw ht hca hgasB hT hrep hlogs
        rw [hto] at hlogs
        simp only [hw, ht, hca, hs1, hs2, hs3]
        dsimp only [call0Caller, callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
        simp only [hto, returnMemory_ofWord, callCost, callGas, callExt, ofNat,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hmod] at hgasB ⊢
        rw [messageCallGas_zero (by evm_gas)] at hgasB ⊢
        simp only [Gas.maxMessageCallGas] at hgasB ⊢
        wp_generalize_gas g1 hg1
        have hg1' : m_gasLeft ≤ g1 + 84000 := by
          subst hg1
          generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses i.asset) = acc
            at hacc hgasB ⊢
          evm_gas
        dsimp only [call0Child, Frame.init, childMsg] at hT hrep
        rw [hw, hto] at hrep
        clear hg1 hgasB hdel hto hcode hpre hw ht hca hsame hs1 hs2 hs3 hk hmod hacc
        pwp_steps [hfmp, hsize]
        refine WP.ret ⟨t', hT, hrep, _, _, _, _, rfl, ?_, ?_, ?_⟩
        · unfold FmpAfterTransfer
          simp (disch := decide) only [Memory.loadWord_storeWord_of_disjoint,
            Memory.loadWord_expand, hfmp, Memory.size_storeWord, Memory.size_expand, hsize,
            Memory.wordsAfter, Memory.words, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
            Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.max_def, ↓reduceIte]
          decide
        · omega
        · logs_simp [hlogs]
          try rfl
      · subst ho
        rw [resumeAfter_revert hk]
        have hsnap : mf.frame.snapshot = (m_world, m_transient) := hsame.snapshot
        simp only [hsnap, hs1, hs2, hs3]
        dsimp only [call0Caller, callerFrame, callMemory, Frame.init, childMsg] at hgasB hT ⊢
        simp only [hto, callCost, callGas, callExt, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod, hmod] at hgasB ⊢
        rw [messageCallGas_zero (by evm_gas)] at hgasB ⊢
        simp only [Gas.maxMessageCallGas] at hgasB ⊢
        wp_generalize_gas g1 hg1
        have hg1' : m_gasLeft ≤ g1 + 84000 := by
          subst hg1
          generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses i.asset) = acc
            at hacc hgasB ⊢
          evm_gas
        clear hg1 hgasB hdel hto hcode hpre hsame hs1 hs2 hs3 hk hmod hacc hsnap
        generalize hM : returnMemory _ 0 32 out = M
        obtain ⟨hMs, hMl⟩ := returnMemory_zero_facts hM
        have hM64 := hMl 64 (by decide)
        simp (disch := decide) only [Memory.loadWord_storeWord_of_disjoint,
          Memory.loadWord_expand, hfmp] at hM64
        simp only [Memory.size_storeWord, Memory.size_expand, hsize, Memory.wordsAfter,
          Memory.words, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
          Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.max_def, ↓reduceIte] at hMs
        clear hM hMl
        pwp_steps [hM64, hMs, word_and_zero, iszero_zero]
        exact ⟨hT, _, rfl⟩

set_option maxHeartbeats 0 in
/-- **With its log** (`mintShares_wp`, and the frame's logs gain `Transfer(0, to, amount)`):
**`_mint(to, amount)` (internal, entry `0x0fdc`)**: without supply overflow it returns to
`r` with the world `mintWorld` (at most 55000 gas); on overflow it reverts. -/
theorem mintShares_wp_logs {i : SolmateVault.Immutables} (m : Machine) {amount r : Word}
    {dst : Address} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hstatic : m.frame.msg.isStatic = false)
    (hpc : m.frame.pc = 0xfdc)
    (hs : m.frame.stack = amount :: Word.ofAddress dst :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpAfterTransfer m.frame.memory)
    (hg : 60000 ≤ m.frame.gasLeft) :
    WP m (fun m' => (m.world.sload m.frame.msg.currentTarget 2#256).toNat + amount.toNat < 2 ^ 256 ∧
        ∃ mem g rd sub,
          m' = { m.resumeWith r.toNat rest mem g rd sub with
            world := mintWorld m.ctx.crypto m.world m.frame.msg.currentTarget dst amount } ∧
          FmpAfterTransfer mem ∧ m.frame.gasLeft ≤ g + 55000 ∧
          sub.logs = m.frame.sub.logs.push (transferLog m.frame.msg.currentTarget 0 dst amount))
      (fun _ o => 2 ^ 256 ≤ (m.world.sload m.frame.msg.currentTarget 2#256).toNat + amount.toNat ∧
        ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩ <;>
  · pwp_steps [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress]
    by_cases hov : (m_world.sload m_msg.currentTarget 2#256).toNat + amount.toNat < 2 ^ 256
    · simp only [gt_add_self_of_lt hov, iszero_zero]
      pwp_steps [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      pwp_codecopy
      pwp_steps [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress, Memory.read_64]
      refine WP.ret ⟨hov, _, _, _, _, rfl, ?_, ?_, ?_⟩
      · unfold FmpAfterTransfer
        simp (disch := decide) only [Memory.loadWord_storeWord_of_disjoint,
          Memory.loadWord_expand, hfmp, Memory.size_storeWord, Memory.size_expand, hsize,
          Memory.wordsAfter, Memory.words, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
          Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.max_def, ↓reduceIte]
        decide
      · evm_gas
      · event_log [amount]
    · simp only [gt_add_self_of_le (Nat.le_of_not_lt hov), iszero_one]
      pwp_steps [hfmp, hsize]
      exact ⟨Nat.le_of_not_lt hov, _, rfl⟩

set_option maxHeartbeats 0 in
/-- **Without logs** (`afterDeposit_wp`, and the frame's logs are unchanged):
**`afterDeposit(assets, shares)` (internal, entry `0x1033`)**: without counter overflow it
returns to `r` with the world `bumpWorld` (at most 30000 gas); at `type(uint256).max` it
reverts. -/
theorem afterDeposit_wp_logs {i : SolmateVault.Immutables} (m : Machine) {x y r : Word}
    {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hstatic : m.frame.msg.isStatic = false)
    (hpc : m.frame.pc = 0x1033)
    (hs : m.frame.stack = x :: y :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpAfterTransfer m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) :
    WP m (fun m' => (m.world.sload m.frame.msg.currentTarget 7#256).toNat + 1 < 2 ^ 256 ∧
        ∃ g sub,
          m' = { m.resumeWith r.toNat rest m.frame.memory g m.frame.returnData sub with
            world := bumpWorld m.world m.frame.msg.currentTarget } ∧
          m.frame.gasLeft ≤ g + 30000 ∧ sub.logs = m.frame.sub.logs)
      (fun _ o => (m.world.sload m.frame.msg.currentTarget 7#256).toNat + 1 = 2 ^ 256 ∧
        ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  pwp_steps
  by_cases hov : (m_world.sload m_msg.currentTarget 7#256).toNat + 1 < 2 ^ 256
  · have hne := add_one_ne_zero_of_lt hov
    pwp_steps
    exact WP.ret ⟨hov, _, _, rfl, by evm_gas, by rfl⟩
  · have he : (m_world.sload m_msg.currentTarget 7#256).toNat + 1 = 2 ^ 256 := by
      have := (m_world.sload m_msg.currentTarget 7#256).isLt; omega
    simp only [add_one_eq_zero_of_eq he]
    rcases hmem with ⟨-, hsize⟩ | ⟨-, hsize⟩ <;>
    · pwp_steps [hsize]
      exact ⟨he, _, rfl⟩

end EvmLeanSpecs.Refinement
