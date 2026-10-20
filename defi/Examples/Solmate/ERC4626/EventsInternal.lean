import Examples.Solmate.ERC4626.Deposit
import Examples.Solmate.ERC20.Events
import Defi.ERC4626.Logs
import Examples.Solmate.ERC4626.WithdrawInternal

/-!
# Logs of the vault's internal functions

Companions of the internal summaries of `deposit`/`mint` (`safeTransferFrom_wp`, `mintShares_wp`,
`afterDeposit_wp`) and `withdraw`/`redeem` (`bump_wp`, `burn_wp`, `*Spend_wp`, `safeTransfer_wp`)
that also fix the logs: `_mint`/`_burn` append the vault's `Transfer`, the safe transfers the
asset's (the callee's log, merged on return); the hooks and allowance spending emit nothing.
-/

section

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.Math Defi.ERC20 Examples.Solmate.ERC4626.Shares

theorem assetTransferFrom_halts_logs {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hstatic : m.frame.msg.isStatic = false) {src dst : Address} {amount : Word}
    (hd : ThreeWordCall m.frame.msg.data 0x23b872dd (Word.ofAddress src) (Word.ofAddress dst)
      amount)
    (hsz : m.frame.msg.data.size < 2 ^ 64) (hg : 90000 ≤ m.frame.gasLeft)
    (hs : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate src)
    (hdst : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate dst)
    (ha : ERC20.AllowanceSlotOk m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.caller)
    {t : Token Address} (hr : Rep (assetView m) t) (hw : t.WF) :
    Halts m (fun mf o =>
      (∃ t', t.transferFrom m.frame.msg.caller src dst amount.toNat = some t' ∧
        TransferFromOk src dst amount m mf o ∧
        RepOn (TransferFromAllowances m.ctx.crypto m.frame.msg.caller src dst)
          (ERC20.view m.ctx.crypto ERC20.Layout.solmate mf.world m.frame.msg.currentTarget) t' ∧
        mf.frame.sub.logs = m.frame.sub.logs.push
          (transferLog m.frame.msg.currentTarget src dst amount)) ∨
      (t.transferFrom m.frame.msg.caller src dst amount.toNat = none ∧ Reverts 80000 m mf o)) := by
  cases hT : t.transferFrom m.frame.msg.caller src dst amount.toNat with
  | some t' =>
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
    refine (transferFrom_halts_ok_events m hf hval hstatic hd hsz hg hal hbal).mono
      fun mf o _ ⟨hok, hl⟩ => .inl ⟨t', rfl, hok, ?_, hl⟩
    rw [hok.2.1]
    exact RepOn.of_eq h1 h2 (fun o sp hp => h3 o sp hp.1.1 hp.1.2 hp.2) hrep
  | none =>
    have h := assetTransferFrom_refines m hf hval hstatic hd hsz hg hs hdst ha hr hw
    rw [hT] at h
    exact h.mono fun _ _ _ h => .inr ⟨rfl, h⟩

set_option maxHeartbeats 0 in
theorem safeTransferFrom_wp_logs {i : SolmateVault.Immutables} (m : Machine) {amount r : Word}
    {src dst : Address} {rest : List Word}
    (hv : VaultFrame i m) (hstatic : m.frame.msg.isStatic = false)
    (hpc : m.frame.pc = 0xf38)
    (hs : m.frame.stack = amount :: Word.ofAddress dst :: Word.ofAddress src ::
      Word.ofAddress i.asset :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpOk m.frame.memory)
    (hg : 100000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hbs : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate src)
    (hbd : ERC20.BalanceSlotOk m.ctx.crypto ERC20.Layout.solmate dst)
    (ha : ERC20.AllowanceSlotOk m.ctx.crypto ERC20.Layout.solmate src m.frame.msg.currentTarget)
    (hwf : (tokenView m.ctx.crypto m.world i.asset).WF) :
    WP m (fun m' => ∃ t', (tokenView m.ctx.crypto m.world i.asset).transferFrom
          m.frame.msg.currentTarget src dst amount.toNat = some t' ∧
        RepOn (TransferFromAllowances m.ctx.crypto m.frame.msg.currentTarget src dst)
          (ERC20.view m.ctx.crypto ERC20.Layout.solmate (ERC20.transferFromWorld m.ctx.crypto
            m.world i.asset m.frame.msg.currentTarget src dst amount) i.asset) t' ∧
        ∃ mem g rd sub,
          m' = { m.resumeWith r.toNat rest mem g rd sub with
            world := ERC20.transferFromWorld m.ctx.crypto m.world i.asset
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
        kernel_decide
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

end Examples.Solmate.ERC4626

end

section

/-! ## Logs of `withdraw` / `redeem`'s internal functions -/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626 Defi.Trace

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open Examples.Solmate.ERC4626.Out
open EvmLogic.Solidity.ERC20 (transferWorld)

/-- `OutPost` with the frame's final logs: on `some (w', v)` the call returns the word `v` with
world `w'` and logs `L v`; on `none` it reverts. -/
def OutPostLogs (L : Word → Array Log) (r : Option (World × Word)) (mf : Machine) (o : Outcome) :
    Prop :=
  match r with
  | some (w', v) => o = .success (Bytes.ofWord v) ∧ mf.world = w' ∧ mf.frame.sub.logs = L v
  | none => ∃ out, o = .revert out

set_option maxHeartbeats 0 in
theorem bump_wp_logs {i : SolmateVault.Immutables} (m : Machine) {a b r : Word} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0x104b) (hs : m.frame.stack = a :: b :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hstatic : m.frame.msg.isStatic = false) (hmem : FmpOk m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) :
    WP m (fun m' => ∃ w', bumpStep m.world m.frame.msg.currentTarget = some w' ∧ ∃ g sub,
        m' = resumeWorld m r.toNat rest m.frame.memory g m.frame.returnData sub w' ∧
        m.frame.gasLeft ≤ g + 25000 ∧ g ≤ m.frame.gasLeft ∧ sub.logs = m.frame.sub.logs)
      (fun _ o => bumpStep m.world m.frame.msg.currentTarget = none ∧ ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  by_cases hmax : m_world.sload m_msg.currentTarget 6#256 = MAXW
  · have hz : m_world.sload m_msg.currentTarget 6#256 + 1#256 = 0#256 := by rw [hmax]; decide
    rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, hz]
      exact ⟨by simp [bumpStep, hmax], _, rfl⟩
  · have hnz : m_world.sload m_msg.currentTarget 6#256 + 1#256 ≠ 0#256 := by
      intro h; apply hmax
      have := congrArg (· - 1#256) h
      simpa [MAXW] using this
    have hnz' : m_world.sload m_msg.currentTarget 6#256 + 1#256 ≠ 0 := hnz
    pwp_steps
    apply WP.ret
    exact ⟨_, by simp [bumpStep, hmax], _, _, rfl, by evm_gas, by evm_gas, by rfl⟩

set_option maxHeartbeats 0 in
theorem burn_wp_logs {i : SolmateVault.Immutables} (m : Machine) {amount r : Word} {src : Address}
    {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0x105a) (hs : m.frame.stack = amount :: Word.ofAddress src :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hstatic : m.frame.msg.isStatic = false) (hmem : FmpOk m.frame.memory)
    (hg : 60000 ≤ m.frame.gasLeft) :
    WP m (fun m' => ∃ w', burnStep m.ctx.crypto m.world m.frame.msg.currentTarget src amount =
          some w' ∧ ∃ mem g rd sub,
        m' = resumeWorld m r.toNat rest mem g rd sub w' ∧ FmpBurnt mem ∧
        m.frame.gasLeft ≤ g + 55000 ∧ g ≤ m.frame.gasLeft ∧
        sub.logs = m.frame.sub.logs.push (transferLog m.frame.msg.currentTarget src 0 amount))
      (fun _ o => burnStep m.ctx.crypto m.world m.frame.msg.currentTarget src amount = none ∧
        ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [burnStep, balanceSlot_solmate]
  by_cases hbal : amount.toNat ≤ (m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress src) ++ Bytes.ofWord 3#256))).toNat
  · rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, hfmp, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Memory.read_64]
      simp only [gt_sub_self_of_le hbal, iszero_zero]
      pwp_steps [hsize, hfmp, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Memory.read_64]
      pwp_codecopy
      pwp_steps [hsize, hfmp, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Memory.read_64]
      apply WP.ret
      refine ⟨_, by simp only [Nat.not_lt.2 hbal, ↓reduceIte], _, _, _, _, rfl, ?_, by evm_gas,
        by evm_gas, ?_⟩
      first
        | refine .inl ⟨?_, ?_⟩
          · simp only [Memory.loadWord_expand,
              Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 128 64 _ (by decide), hfmp]
          · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
              hsize]
            decide
        | refine .inr ⟨?_, ?_⟩
          · simp only [Memory.loadWord_expand,
              Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 160 64 _ (by decide), hfmp]
          · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
              hsize]
            decide
      event_log [amount]
  · rw [Nat.not_le] at hbal
    rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, hfmp, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Memory.read_64]
      simp only [gt_sub_self_of_lt hbal, iszero_one]
      pwp_steps [hsize, hfmp]
      exact ⟨by simp only [hbal, ↓reduceIte], _, rfl⟩

set_option maxHeartbeats 0 in
theorem withdrawSpend_wp_logs {i : SolmateVault.Immutables} (m : Machine) {v x : Word}
    {owner : Address} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0x993) (hs : m.frame.stack = v :: x :: Word.ofAddress owner :: rest)
    (hlen : rest.length ≤ 1000) (hstatic : m.frame.msg.isStatic = false)
    (hmem : FmpOk m.frame.memory) (hg : 30000 ≤ m.frame.gasLeft) :
    WP m (fun m' => ∃ w₁, spendStep m.ctx.crypto m.world m.frame.msg.currentTarget owner
          m.frame.msg.caller v = some w₁ ∧ ∃ mem g sub,
        m' = resumeWorld m 0xa00 (v :: Word.ofAddress owner :: rest) mem g m.frame.returnData sub
          w₁ ∧
        mem.loadWord 64 = m.frame.memory.loadWord 64 ∧ mem.size = m.frame.memory.size ∧
        m.frame.gasLeft ≤ g + 26000 ∧ g ≤ m.frame.gasLeft ∧ sub.logs = m.frame.sub.logs)
      (fun _ o => spendStep m.ctx.crypto m.world m.frame.msg.currentTarget owner
          m.frame.msg.caller v = none ∧ ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  by_cases hco : m_msg.caller = owner
  · subst hco
    pwp_run_to 0xa00 [ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    apply WP.ret
    exact ⟨_, by simp [spendStep], _, _, _, rfl, rfl, rfl, by evm_gas, by evm_gas, by rfl⟩
  · have hne1 := eq_ofAddress_of_ne hco
    have hne2 := eq_ofAddress_of_ne (Ne.symm hco)
    have hsp : spendStep m_ctx.crypto m_world m_msg.currentTarget owner m_msg.caller v =
        let a := m_world.sload m_msg.currentTarget
          (ERC20.allowanceSlot m_ctx.crypto ERC20.Layout.solmate owner m_msg.caller)
        if a ≠ ERC20.maxWord ∧ a.toNat < v.toNat then none
        else some (ERC20.spendWorld m_ctx.crypto m_world m_msg.currentTarget owner m_msg.caller v) := by
      simp only [spendStep, hco, ↓reduceIte]
    rw [hsp]
    simp only [ERC20.spendWorld, allowanceSlot_solmate, maxWord_eq_MAXW]
    rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, ofAddress_and_addressMask, addressMask_and_ofAddress, hne1, hne2,
        Memory.read_64]
      by_cases hmax : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
          (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 4#256)))) = MAXW
      · simp only [hmax, Solidity.eq_self]
        pwp_run_to 0xa00 [hsize]
        apply WP.ret
        refine ⟨_, by simp, _, _, _, rfl, ?_, ?_, by evm_gas, by evm_gas, by rfl⟩
        · simp only [Memory.loadWord_expand,
            Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide)]
        · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
            hsize]
          decide
      · simp only [eq_of_ne hmax, hmax]
        pwp_steps [hsize]
        by_cases hle : v.toNat ≤ (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
              (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 4#256))))).toNat
        · simp only [gt_sub_self_of_le hle, iszero_zero]
          pwp_run_to 0xa00 [hsize, ofAddress_and_addressMask, addressMask_and_ofAddress,
            Memory.read_64]
          apply WP.ret
          refine ⟨_, by simp [Nat.not_lt.2 hle], _, _, _, rfl, ?_, ?_, by evm_gas, by evm_gas, by rfl⟩
          · simp only [Memory.loadWord_expand,
              Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide)]
          · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter,
              Memory.words, hsize]
            decide
        · rw [Nat.not_le] at hle
          simp only [gt_sub_self_of_lt hle, iszero_one]
          pwp_steps [hsize]
          exact ⟨by simp [hmax, hle], _, rfl⟩

set_option maxHeartbeats 0 in
theorem redeemSpend_wp_logs {i : SolmateVault.Immutables} (m : Machine) {v y : Word}
    {owner : Address} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 0xa93) (hs : m.frame.stack = Word.ofAddress owner :: y :: v :: rest)
    (hlen : rest.length ≤ 1000) (hstatic : m.frame.msg.isStatic = false)
    (hmem : FmpOk m.frame.memory) (hg : 30000 ≤ m.frame.gasLeft) :
    WP m (fun m' => ∃ w₁, spendStep m.ctx.crypto m.world m.frame.msg.currentTarget owner
          m.frame.msg.caller v = some w₁ ∧ ∃ mem g sub,
        m' = resumeWorld m 0xaff (0#256 :: Word.ofAddress owner :: y :: v :: rest) mem g
          m.frame.returnData sub w₁ ∧
        mem.loadWord 64 = m.frame.memory.loadWord 64 ∧ mem.size = m.frame.memory.size ∧
        m.frame.gasLeft ≤ g + 26000 ∧ g ≤ m.frame.gasLeft ∧ sub.logs = m.frame.sub.logs)
      (fun _ o => spendStep m.ctx.crypto m.world m.frame.msg.currentTarget owner
          m.frame.msg.caller v = none ∧ ∃ out, o = .revert out) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  by_cases hco : m_msg.caller = owner
  · subst hco
    pwp_run_to 0xaff [ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    apply WP.ret
    exact ⟨_, by simp [spendStep], _, _, _, rfl, rfl, rfl, by evm_gas, by evm_gas, by rfl⟩
  · have hne1 := eq_ofAddress_of_ne hco
    have hne2 := eq_ofAddress_of_ne (Ne.symm hco)
    have hsp : spendStep m_ctx.crypto m_world m_msg.currentTarget owner m_msg.caller v =
        let a := m_world.sload m_msg.currentTarget
          (ERC20.allowanceSlot m_ctx.crypto ERC20.Layout.solmate owner m_msg.caller)
        if a ≠ ERC20.maxWord ∧ a.toNat < v.toNat then none
        else some (ERC20.spendWorld m_ctx.crypto m_world m_msg.currentTarget owner m_msg.caller v) := by
      simp only [spendStep, hco, ↓reduceIte]
    rw [hsp]
    simp only [ERC20.spendWorld, allowanceSlot_solmate, maxWord_eq_MAXW]
    rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
    all_goals
      pwp_steps [hsize, ofAddress_and_addressMask, addressMask_and_ofAddress, hne1, hne2,
        Memory.read_64]
      by_cases hmax : m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
          (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 4#256)))) = MAXW
      · simp only [hmax, Solidity.eq_self]
        pwp_run_to 0xaff [hsize]
        apply WP.ret
        refine ⟨_, by simp, _, _, _, rfl, ?_, ?_, by evm_gas, by evm_gas, by rfl⟩
        · simp only [Memory.loadWord_expand,
            Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide)]
        · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
            hsize]
          decide
      · simp only [eq_of_ne hmax, hmax]
        pwp_steps [hsize]
        by_cases hle : v.toNat ≤ (m_world.sload m_msg.currentTarget (m_ctx.crypto.keccak256
            (Bytes.ofWord (Word.ofAddress m_msg.caller) ++ Bytes.ofWord (m_ctx.crypto.keccak256
              (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 4#256))))).toNat
        · simp only [gt_sub_self_of_le hle, iszero_zero]
          pwp_run_to 0xaff [hsize, ofAddress_and_addressMask, addressMask_and_ofAddress,
            Memory.read_64]
          apply WP.ret
          refine ⟨_, by simp [Nat.not_lt.2 hle], _, _, _, rfl, ?_, ?_, by evm_gas, by evm_gas, by rfl⟩
          · simp only [Memory.loadWord_expand,
              Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
              Memory.loadWord_storeWord_of_disjoint _ 32 64 _ (by decide)]
          · simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter,
              Memory.words, hsize]
            decide
        · rw [Nat.not_le] at hle
          simp only [gt_sub_self_of_lt hle, iszero_one]
          pwp_steps [hsize]
          exact ⟨by simp [hmax, hle], _, rfl⟩

set_option maxHeartbeats 0 in
theorem safeTransfer_wp_logs {i : SolmateVault.Immutables} (m : Machine) {amount r : Word}
    {rcv : Address} {rest : List Word} (hv : VaultFrame i m) (hpc : m.frame.pc = 0x10b9)
    (hs : m.frame.stack = amount :: Word.ofAddress rcv :: Word.ofAddress i.asset :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hstatic : m.frame.msg.isStatic = false) (hne : i.asset ≠ m.frame.msg.currentTarget)
    (hmem : FmpCall m.frame.memory)
    (hg : 70000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => amount.toNat ≤ (assetsOf i.asset m).toNat ∧ ∃ mem g rd sub,
        m' = resumeWorld m r.toNat rest mem g rd sub
          (transferWorld m.ctx.crypto m.world i.asset m.frame.msg.currentTarget rcv amount) ∧
        mem.loadWord 64 = m.frame.memory.loadWord 64 ∧ mem.size = m.frame.memory.size + 32 ∧
        m.frame.gasLeft ≤ g + 60000 ∧
        sub.logs = m.frame.sub.logs.push (transferLog i.asset m.frame.msg.currentTarget rcv amount))
      (fun _ o => (assetsOf i.asset m).toNat < amount.toNat ∧ ∃ out, o = .revert out) := by
  obtain ⟨hc, hj, ⟨ia, hcode⟩, hpre, hdepth⟩ := hv
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [assetsOf]
  have hto : Word.toAddress (Word.ofAddress i.asset) = i.asset := Word.toAddress_ofAddress _
  have hdel := delegatedAddress?_assetCode ia
  have hacc := accessCost_le (m_sub.accessedAddresses.contains i.asset)
  rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
  · pwp_run_to 0x10e6 [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress]
    by_cases hbal : amount.toNat ≤ (m_world.sload i.asset
        (ERC20.balanceSlot m_ctx.crypto ERC20.Layout.solmate m_msg.currentTarget)).toNat
    · refine WP.callNoValue (by pcode_fact) rfl ?_ ?_ hdepth ?_
        (transfer_halts_ok_events (ia := ia) (dst := rcv) (amount := amount) _ ?_ rfl ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_) ?_
      · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
      · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat,
          Nat.reducePow, Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · rw [hto]; exact hpre
      · exact ⟨_, _, _, rfl, by dsimp only [childMsg]; rw [hto, hcode]⟩
      · simp [Frame.init, childMsg, hstatic]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Abi.selectorOf]
        rw [Memory.readBytes_read _ 128 68 0 4 (by decide)]
        simp only [Memory.read_expand, Nat.add_zero,
          Memory.read_storeWord_of_disjoint _ 164 128 4 _ (by decide),
          Memory.read_storeWord_of_disjoint _ 132 128 4 _ (by decide),
          Memory.read_storeWord_prefix _ _ 4 _ (by decide)]
        kernel_decide
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 128 68 4 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand,
          Memory.read_storeWord_of_disjoint _ 164 132 32 _ (by decide), Memory.read_storeWord,
          Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 128 68 36 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand, Memory.read_storeWord, Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg]
        simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · dsimp only [Frame.init, childMsg]
        rw [hto]
        exact hbal
      · intro mf o ⟨⟨ho, hw, ht, hca, hgasB⟩, hlogs⟩ hsame
        have hk : mf.frame.kind = .call 0 32 := hsame.kind
        subst ho
        rw [resumeAfter_success hk]
        dsimp only [Frame.init, childMsg] at hw ht hca hgasB hlogs
        rw [hto] at hw hlogs
        have hs1 : mf.ctx = m_ctx := hsame.ctx
        have hs2 : mf.precompiles = m_pre := hsame.precompiles
        have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
        clear hsame
        simp only [hw, ht, hca, hs1, hs2, hs3, hto]
        dsimp only [callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
        simp only [hto, returnMemory_ofWord, callCost, callGas, callExt, ofNat,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
        rw [messageCallGas_zero (by evm_gas)] at hgasB ⊢
        simp only [Gas.maxMessageCallGas] at hgasB ⊢
        wp_generalize_gas g1 hg1
        have hg1' : m_gasLeft ≤ g1 + 58000 := by
          subst hg1
          generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses i.asset) = acc
            at hacc hgasB ⊢
          evm_gas
        clear hg1 hgasB hdel hto hcode hpre
        pwp_steps [Bytes.size_ofWord]
        apply WP.ret
        refine ⟨hbal, _, _, _, _, rfl, ?_, ?_, ?_, ?_⟩
        · simp only [Memory.loadWord_expand,
            Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 164 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 132 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 128 64 _ (by decide), hfmp]
        · evm_gas_norm
          rw_mem_sizes
          evm_gas_norm
        · evm_gas
        · logs_simp [hlogs]
    · rw [Nat.not_le] at hbal
      refine WP.callNoValue (by pcode_fact) rfl ?_ ?_ hdepth ?_
        (transfer_halts_revert (ia := ia) («to» := rcv) (amount := amount) _ ?_ rfl
          ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_) ?_
      · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
      · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat,
          Nat.reducePow, Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · rw [hto]; exact hpre
      · exact ⟨_, _, _, rfl, by dsimp only [childMsg]; rw [hto, hcode]⟩
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Abi.selectorOf]
        rw [Memory.readBytes_read _ 128 68 0 4 (by decide)]
        simp only [Memory.read_expand, Nat.add_zero,
          Memory.read_storeWord_of_disjoint _ 164 128 4 _ (by decide),
          Memory.read_storeWord_of_disjoint _ 132 128 4 _ (by decide),
          Memory.read_storeWord_prefix _ _ 4 _ (by decide)]
        kernel_decide
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 128 68 4 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand,
          Memory.read_storeWord_of_disjoint _ 164 132 32 _ (by decide), Memory.read_storeWord,
          Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 128 68 36 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand, Memory.read_storeWord, Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg]
        simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · dsimp only [Frame.init, childMsg]
        rw [hto]
        exact hbal
      · intro mf o ⟨⟨out, ho⟩, hgasB⟩ hsame
        have hk : mf.frame.kind = .call 0 32 := hsame.kind
        have hsnap : mf.frame.snapshot = (m_world, m_transient) := hsame.snapshot
        subst ho
        rw [resumeAfter_revert hk]
        have hs1 : mf.ctx = m_ctx := hsame.ctx
        have hs2 : mf.precompiles = m_pre := hsame.precompiles
        have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
        clear hsame
        simp only [hs1, hs2, hs3, hsnap]
        dsimp only [callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
        simp only [hto, callCost, callGas, callExt, ofNat,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
        rw [messageCallGas_zero (by evm_gas)] at hgasB ⊢
        simp only [Gas.maxMessageCallGas] at hgasB ⊢
        generalize hM : returnMemory _ 0 32 out = M
        obtain ⟨hm1, hm2⟩ := returnMemory_zero_word_eq hM (by clear hgasB; simp only [Memory.size_storeWord, Memory.size_expand]; omega)
        simp only [Memory.loadWord_expand,
          Memory.loadWord_storeWord_of_disjoint _ 164 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 132 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 128 64 _ (by decide), hfmp] at hm1
        have hm2' : M.size = 224 := by
          rw [hm2]
          simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
            hsize]
          decide
        clear hM hm2
        wp_generalize_gas g1 hg1
        have hg1' : m_gasLeft ≤ g1 + 15000 := by
          subst hg1
          generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses i.asset) = acc
            at hacc hgasB ⊢
          evm_gas
        clear hg1 hgasB hdel hto hcode hpre
        pwp_steps [hm1, hm2', and_zero_word]
        exact ⟨hbal, _, rfl⟩
  · pwp_run_to 0x10e6 [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress]
    by_cases hbal : amount.toNat ≤ (m_world.sload i.asset
        (ERC20.balanceSlot m_ctx.crypto ERC20.Layout.solmate m_msg.currentTarget)).toNat
    · refine WP.callNoValue (by pcode_fact) rfl ?_ ?_ hdepth ?_
        (transfer_halts_ok_events (ia := ia) (dst := rcv) (amount := amount) _ ?_ rfl ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_) ?_
      · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
      · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat,
          Nat.reducePow, Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · rw [hto]; exact hpre
      · exact ⟨_, _, _, rfl, by dsimp only [childMsg]; rw [hto, hcode]⟩
      · simp [Frame.init, childMsg, hstatic]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Abi.selectorOf]
        rw [Memory.readBytes_read _ 160 68 0 4 (by decide)]
        simp only [Memory.read_expand, Nat.add_zero,
          Memory.read_storeWord_of_disjoint _ 196 160 4 _ (by decide),
          Memory.read_storeWord_of_disjoint _ 164 160 4 _ (by decide),
          Memory.read_storeWord_prefix _ _ 4 _ (by decide)]
        kernel_decide
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 160 68 4 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand,
          Memory.read_storeWord_of_disjoint _ 196 164 32 _ (by decide), Memory.read_storeWord,
          Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 160 68 36 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand, Memory.read_storeWord, Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg]
        simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · dsimp only [Frame.init, childMsg]
        rw [hto]
        exact hbal
      · intro mf o ⟨⟨ho, hw, ht, hca, hgasB⟩, hlogs⟩ hsame
        have hk : mf.frame.kind = .call 0 32 := hsame.kind
        subst ho
        rw [resumeAfter_success hk]
        dsimp only [Frame.init, childMsg] at hw ht hca hgasB hlogs
        rw [hto] at hw hlogs
        have hs1 : mf.ctx = m_ctx := hsame.ctx
        have hs2 : mf.precompiles = m_pre := hsame.precompiles
        have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
        clear hsame
        simp only [hw, ht, hca, hs1, hs2, hs3, hto]
        dsimp only [callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
        simp only [hto, returnMemory_ofWord, callCost, callGas, callExt, ofNat,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
        rw [messageCallGas_zero (by evm_gas)] at hgasB ⊢
        simp only [Gas.maxMessageCallGas] at hgasB ⊢
        wp_generalize_gas g1 hg1
        have hg1' : m_gasLeft ≤ g1 + 58000 := by
          subst hg1
          generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses i.asset) = acc
            at hacc hgasB ⊢
          evm_gas
        clear hg1 hgasB hdel hto hcode hpre
        pwp_steps [Bytes.size_ofWord]
        apply WP.ret
        refine ⟨hbal, _, _, _, _, rfl, ?_, ?_, ?_, ?_⟩
        · simp only [Memory.loadWord_expand,
            Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 196 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 164 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 160 64 _ (by decide), hfmp]
        · evm_gas_norm
          rw_mem_sizes
          evm_gas_norm
        · evm_gas
        · logs_simp [hlogs]
    · rw [Nat.not_le] at hbal
      refine WP.callNoValue (by pcode_fact) rfl ?_ ?_ hdepth ?_
        (transfer_halts_revert (ia := ia) («to» := rcv) (amount := amount) _ ?_ rfl
          ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_) ?_
      · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
      · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat,
          Nat.reducePow, Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · rw [hto]; exact hpre
      · exact ⟨_, _, _, rfl, by dsimp only [childMsg]; rw [hto, hcode]⟩
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Abi.selectorOf]
        rw [Memory.readBytes_read _ 160 68 0 4 (by decide)]
        simp only [Memory.read_expand, Nat.add_zero,
          Memory.read_storeWord_of_disjoint _ 196 160 4 _ (by decide),
          Memory.read_storeWord_of_disjoint _ 164 160 4 _ (by decide),
          Memory.read_storeWord_prefix _ _ 4 _ (by decide)]
        kernel_decide
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 160 68 4 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand,
          Memory.read_storeWord_of_disjoint _ 196 164 32 _ (by decide), Memory.read_storeWord,
          Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes]
        rw [Memory.readBytes_read _ 160 68 36 32 (by decide)]
        simp only [Nat.reduceAdd, Memory.read_expand, Memory.read_storeWord, Bytes.toWord_ofWord]
      · dsimp only [Frame.init, childMsg, callMemory]
        simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
        decide
      · dsimp only [Frame.init, childMsg]
        simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · dsimp only [Frame.init, childMsg]
        rw [hto]
        exact hbal
      · intro mf o ⟨⟨out, ho⟩, hgasB⟩ hsame
        have hk : mf.frame.kind = .call 0 32 := hsame.kind
        have hsnap : mf.frame.snapshot = (m_world, m_transient) := hsame.snapshot
        subst ho
        rw [resumeAfter_revert hk]
        have hs1 : mf.ctx = m_ctx := hsame.ctx
        have hs2 : mf.precompiles = m_pre := hsame.precompiles
        have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
        clear hsame
        simp only [hs1, hs2, hs3, hsnap]
        dsimp only [callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
        simp only [hto, callCost, callGas, callExt, ofNat,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
        rw [messageCallGas_zero (by evm_gas)] at hgasB ⊢
        simp only [Gas.maxMessageCallGas] at hgasB ⊢
        generalize hM : returnMemory _ 0 32 out = M
        obtain ⟨hm1, hm2⟩ := returnMemory_zero_word_eq hM (by clear hgasB; simp only [Memory.size_storeWord, Memory.size_expand]; omega)
        simp only [Memory.loadWord_expand,
          Memory.loadWord_storeWord_of_disjoint _ 196 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 164 64 _ (by decide),
          Memory.loadWord_storeWord_of_disjoint _ 160 64 _ (by decide), hfmp] at hm1
        have hm2' : M.size = 256 := by
          rw [hm2]
          simp only [Memory.size_storeWord, Memory.size_expand, Memory.wordsAfter, Memory.words,
            hsize]
          decide
        clear hM hm2
        wp_generalize_gas g1 hg1
        have hg1' : m_gasLeft ≤ g1 + 15000 := by
          subst hg1
          generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses i.asset) = acc
            at hacc hgasB ⊢
          evm_gas
        clear hg1 hgasB hdel hto hcode hpre
        pwp_steps [hm1, hm2', and_zero_word]
        exact ⟨hbal, _, rfl⟩

end Examples.Solmate.ERC4626

end
