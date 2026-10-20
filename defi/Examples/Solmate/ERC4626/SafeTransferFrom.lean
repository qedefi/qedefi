import Examples.Solmate.ERC20.Spec
import EvmLogic.Program.Call

/-!
# The vault's `safeTransferFrom` into the asset

`deposit` and `mint` pull the assets with Solmate's `SafeTransferLib.safeTransferFrom(asset,
msg.sender, address(this), assets)`, compiled once as an internal function of the vault (entry
`0x0f38`). It is the only external call of the two functions:

```
mstore(fmp, 0x23b872dd…); mstore(fmp+4, from); mstore(fmp+36, to); mstore(fmp+68, amount)
success := call(gas(), token, 0, fmp, 100, 0, 32)
if and(iszero(and(eq(mload(0), 1), gt(returndatasize(), 31))), success) {
  success := iszero(or(iszero(extcodesize(token)), returndatasize())) }
require(success, "TRANSFER_FROM_FAILED")
```

`safeTransferFrom_wp` summarises it, for the vault deployed with any immutables `i`, in any
non-static frame with solc's memory discipline (`FmpOk`), against the model's
`Token.transferFrom` of the asset ledger (`tokenView`, spender = the vault):

* the `CALL` (no value) is handled by the callee-summary rule `WP.call0`
  (`EvmLeanProofs.Program.InExtraCall`) with the asset's model-level summary
  `assetTransferFrom_halts` (from `assetTransferFrom_refines`) on the child frame: the
  calldata the vault assembled in memory is a `ThreeWordCall`;
* **success** (the model returns `some t'`): the asset returns the ABI word `1` (32 bytes), so
  the return-data check passes without `EXTCODESIZE`; the function returns to its caller with
  the world `Erc20.transferFromWorld` (the asset's exact writes), whose asset view represents
  `t'` (`RepOn`), memory `FmpAfterTransfer`, and at most 90000 gas used;
* **failure** (`none`): the asset reverts (`success = 0`, whatever the revert data copied to
  the scratch word), and the vault reverts.

The asset is `MockERC20` (it makes no calls), so there is no reentrancy into the vault; this
is what makes the callee summary exact.

Hypotheses: `BalanceSlotOk` of `src` and `dst`, `AllowanceSlotOk` of `allowance[src][vault]`
(the written entries, pointwise Keccak freshness) and `Token.WF` of the asset ledger, as in
`assetTransferFrom_refines`; `100000 ≤ gas < 2⁶⁴` (the asset needs 90000 of the forwarded
63/64).
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open Vault Shares

/-- Memory after `safeTransferFrom`: the free pointer unchanged (`0x80` or `0xa0`), the call's
input window `[fmp, fmp + 100)` allocated. -/
def FmpAfterTransfer (mem : Memory) : Prop :=
  (mem.loadWord 64 = 128#256 ∧ mem.size = 256) ∨ (mem.loadWord 64 = 160#256 ∧ mem.size = 288)

/-- `assetTransferFrom_refines` with the model's result as a disjunction (for `WP.call0`). -/
theorem assetTransferFrom_halts {ia : SolmateAsset.Immutables} (m : Machine)
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
          (Erc20.view m.ctx.crypto Erc20.Layout.solmate mf.world m.frame.msg.currentTarget) t') ∨
      (t.transferFrom m.frame.msg.caller src dst amount.toNat = none ∧ Reverts 80000 m mf o)) := by
  have h := assetTransferFrom_refines m hf hval hstatic hd hsz hg hs hdst ha hr hw
  revert h
  cases hT : t.transferFrom m.frame.msg.caller src dst amount.toNat with
  | some t' => exact fun h => h.mono fun _ _ _ h => .inl ⟨t', rfl, h⟩
  | none => exact fun h => h.mono fun _ _ _ h => .inr ⟨rfl, h⟩

/-- `x AND 0 = 0` for the literal `0` that a failed call pushes. -/
theorem word_and_zero (x : Word) : x &&& (0 : Word) = 0#256 := BitVec.and_zero

set_option maxHeartbeats 0 in
/-- **`safeTransferFrom(asset, src, dst, amount)` (internal, entry `0x0f38`, stack
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
theorem safeTransferFrom_wp {i : SolmateVault.Immutables} (m : Machine) {amount r : Word}
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

end EvmLeanSpecs.Refinement
