import Examples.Solmate.ERC20.Spec
import EvmLogic.Program.Call

/-!
# The vault's `safeTransferFrom` into the asset

`safeTransferFrom_wp`: the internal `SafeTransferLib.safeTransferFrom` (entry `0x0f38`, used by
`deposit` / `mint`) `CALL`s the asset, whose effect is the model's `Token.transferFrom` (spender
= the vault); it returns with the asset's writes applied, or reverts exactly when the model
does. The asset (`MockERC20`) makes no calls, so its callee summary is exact.
-/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20 Defi.ERC4626

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open Defi.Math Defi.ERC20 Examples.Solmate.ERC4626.Shares

/-- Memory after `safeTransferFrom`: free pointer unchanged (`0x80` or `0xa0`), the call's input
window `[fmp, fmp + 100)` allocated. -/
def FmpAfterTransfer (mem : Memory) : Prop :=
  (mem.loadWord 64 = 128#256 ∧ mem.size = 256) ∨ (mem.loadWord 64 = 160#256 ∧ mem.size = 288)

theorem assetTransferFrom_halts {ia : SolmateAsset.Immutables} (m : Machine)
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
          (ERC20.view m.ctx.crypto ERC20.Layout.solmate mf.world m.frame.msg.currentTarget) t') ∨
      (t.transferFrom m.frame.msg.caller src dst amount.toNat = none ∧ Reverts 80000 m mf o)) := by
  have h := assetTransferFrom_refines m hf hval hstatic hd hsz hg hs hdst ha hr hw
  revert h
  cases hT : t.transferFrom m.frame.msg.caller src dst amount.toNat with
  | some t' => exact fun h => h.mono fun _ _ _ h => .inl ⟨t', rfl, h⟩
  | none => exact fun h => h.mono fun _ _ _ h => .inr ⟨rfl, h⟩

theorem word_and_zero (x : Word) : x &&& (0 : Word) = 0#256 := BitVec.and_zero

set_option maxHeartbeats 0 in
/-- **`safeTransferFrom(asset, src, dst, amount)`** (internal, entry `0x0f38`, stack
`amount :: dst :: src :: asset :: r :: rest`): when the model's asset `transferFrom` (spender: the
vault) succeeds, returns to `r` with `ERC20.transferFromWorld` applied; otherwise reverts. -/
theorem safeTransferFrom_wp {i : SolmateVault.Immutables} (m : Machine) {amount r : Word}
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
          FmpAfterTransfer mem ∧ m.frame.gasLeft ≤ g + 90000)
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
      (assetTransferFrom_halts (ia := ia) (t := tokenView m_ctx.crypto m_world i.asset)
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
      rcases hc with ⟨t', hT, ⟨ho, hw, ht, hca, hgasB⟩, hrep⟩ | ⟨hT, ⟨out, ho⟩, hgasB⟩
      · subst ho
        rw [resumeAfter_success hk]
        dsimp only at hw ht hca hgasB hT hrep
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
        refine WP.ret ⟨t', hT, hrep, _, _, _, _, rfl, ?_, ?_⟩
        · unfold FmpAfterTransfer
          simp (disch := decide) only [Memory.loadWord_storeWord_of_disjoint,
            Memory.loadWord_expand, hfmp, Memory.size_storeWord, Memory.size_expand, hsize,
            Memory.wordsAfter, Memory.words, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
            Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.max_def, ↓reduceIte]
          decide
        · omega
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

end Examples.Solmate.ERC4626
