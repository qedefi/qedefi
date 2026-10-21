import Examples.Solmate.ERC4626.Convert
import Examples.Solmate.ERC20.Transfer
import EvmLogic.Program.Call

/-!
# The vault's `safeTransfer` into the asset

`safeTransfer_wp`: the internal `SafeTransferLib.safeTransfer` (entry `0x10b9`, used by
`withdraw` / `redeem`) `CALL`s the asset's `transfer`; it returns with the asset's two balance
writes applied when the vault's balance covers the amount, and reverts otherwise. The asset's
code enters only through its callee summaries `transfer_halts_ok` / `transfer_halts_revert`.
-/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts
open EvmLogic.Solidity.ERC20 (transferWorld)

-- The `asset` immutable as read by the `PUSH32` at `0x0a6b` (in `withdraw`).
theorem readBytes_code_asset2668 (i : SolmateVault.Immutables) :
    readBytes (SolmateVault.runtimeCodeWith i) 2668 32 = Bytes.ofWord (Word.ofAddress i.asset) := by
  have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
      (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset),
      (2014, Word.ofAddress i.asset), (2169, Word.ofAddress i.asset)] ++
      (2668, Word.ofAddress i.asset) :: [(2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
  simp only [SolmateVault.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateVault.size_runtimeCode]; decide)
    (by simp)

-- The `asset` immutable as read by the `PUSH32` at `0x0bb2` (in `redeem`).
theorem readBytes_code_asset2995 (i : SolmateVault.Immutables) :
    readBytes (SolmateVault.runtimeCodeWith i) 2995 32 = Bytes.ofWord (Word.ofAddress i.asset) := by
  have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
      (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset),
      (2014, Word.ofAddress i.asset), (2169, Word.ofAddress i.asset),
      (2668, Word.ofAddress i.asset)] ++ (2995, Word.ofAddress i.asset) :: [(623, i.decimals)] :=
    rfl
  simp only [SolmateVault.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateVault.size_runtimeCode]; decide)
    (by simp)

/-- solc's memory at the `safeTransfer` call site of `withdraw` / `redeem`: the free pointer at
`0x80` with six words of memory, or at `0xa0` (after a `totalAssets()` call) with seven. -/
def FmpCall (mem : Memory) : Prop :=
  (mem.loadWord 64 = 128#256 ∧ mem.size = 192) ∨ (mem.loadWord 64 = 160#256 ∧ mem.size = 224)

theorem loadWord_64_storeWord {mem : Memory} {off : Nat} (w : Word) (h : 96 ≤ off) :
    (mem.storeWord off w).loadWord 64 = mem.loadWord 64 :=
  Memory.loadWord_storeWord_of_disjoint _ _ _ _ (.inl h)

theorem and_zero_word (x : Word) : x &&& 0 = 0 := by simp

/-- `m` with the world and the mutable fields of its frame replaced: where an internal function
that writes storage (or makes a call that does) returns to. -/
abbrev resumeWorld (m : Machine) (pc : Nat) (stack : List Word) (mem : Memory) (gas : Nat)
    (rd : ByteArray) (sub : Substate) (w : World) : Machine :=
  { m.resumeWith pc stack mem gas rd sub with world := w }

set_option maxHeartbeats 0 in
/-- **`safeTransfer(asset, to, amount)`** (internal, entry `0x10b9`, stack
`amount :: to :: asset :: r :: rest`): when the vault's asset balance covers `amount`, returns
to `r` with the asset's `transfer` applied to the world; otherwise reverts. -/
theorem safeTransfer_wp {i : SolmateVault.Immutables} (m : Machine) {amount r : Word}
    {to : Address} {rest : List Word} (hv : VaultFrame i m) (hpc : m.frame.pc = 0x10b9)
    (hs : m.frame.stack = amount :: Word.ofAddress to :: Word.ofAddress i.asset :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hstatic : m.frame.msg.isStatic = false) (hne : i.asset ≠ m.frame.msg.currentTarget)
    (hmem : FmpCall m.frame.memory)
    (hg : 70000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => amount.toNat ≤ (assetsOf i.asset m).toNat ∧ ∃ mem g rd sub,
        m' = resumeWorld m r.toNat rest mem g rd sub
          (transferWorld m.ctx.crypto m.world i.asset m.frame.msg.currentTarget to amount) ∧
        mem.loadWord 64 = m.frame.memory.loadWord 64 ∧ mem.size = m.frame.memory.size + 32 ∧
        m.frame.gasLeft ≤ g + 60000)
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
  have hmod : (m_gasLeft - 93) % 2 ^ 256 = m_gasLeft - 93 := Nat.mod_eq_of_lt (by omega)
  rcases hmem with ⟨hfmp, hsize⟩ | ⟨hfmp, hsize⟩
  · pwp_run_to 0x10e6 [hfmp, hsize, ofAddress_and_addressMask, addressMask_and_ofAddress]
    by_cases hbal : amount.toNat ≤ (m_world.sload i.asset
        (ERC20.balanceSlot m_ctx.crypto ERC20.Layout.solmate m_msg.currentTarget)).toNat
    · refine WP.callNoValue (by pcode_fact) rfl ?_ ?_ hdepth ?_
        (transfer_halts_ok (ia := ia) (to := to) (amount := amount) _ ?_ rfl ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_) ?_
      · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
      · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, hmod,
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
        simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, hmod, Nat.reducePow,
          Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · dsimp only [Frame.init, childMsg]
        rw [hto]
        exact hbal
      · intro mf o ⟨ho, hw, ht, hca, hgasB⟩ hsame
        have hk : mf.frame.kind = .call 0 32 := hsame.kind
        subst ho
        rw [resumeAfter_success hk]
        dsimp only [Frame.init, childMsg] at hw ht hca hgasB
        rw [hto] at hw
        have hs1 : mf.ctx = m_ctx := hsame.ctx
        have hs2 : mf.precompiles = m_pre := hsame.precompiles
        have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
        clear hsame
        simp only [hw, ht, hca, hs1, hs2, hs3, hto]
        dsimp only [callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
        simp only [hto, returnMemory_ofWord, callCost, callGas, callExt, ofNat,
          BitVec.toNat_ofNat, hmod, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
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
        refine ⟨hbal, _, _, _, _, rfl, ?_, ?_, ?_⟩
        · simp only [Memory.loadWord_expand,
            Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 164 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 132 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 128 64 _ (by decide), hfmp]
        · rw_mem_sizes
          evm_gas_norm
          rw_mem_sizes
          evm_gas_norm
        · evm_gas
    · rw [Nat.not_le] at hbal
      refine WP.callNoValue (by pcode_fact) rfl ?_ ?_ hdepth ?_
        (transfer_halts_revert (ia := ia) (to := to) (amount := amount) _ ?_ rfl
          ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_) ?_
      · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
      · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, hmod,
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
        simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, hmod, Nat.reducePow,
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
          BitVec.toNat_ofNat, hmod, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
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
        (transfer_halts_ok (ia := ia) (to := to) (amount := amount) _ ?_ rfl ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_) ?_
      · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
      · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, hmod,
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
        simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, hmod, Nat.reducePow,
          Nat.reduceMod]
        rw [messageCallGas_zero (by evm_gas)]
        simp only [Gas.maxMessageCallGas]
        evm_gas
      · dsimp only [Frame.init, childMsg]
        rw [hto]
        exact hbal
      · intro mf o ⟨ho, hw, ht, hca, hgasB⟩ hsame
        have hk : mf.frame.kind = .call 0 32 := hsame.kind
        subst ho
        rw [resumeAfter_success hk]
        dsimp only [Frame.init, childMsg] at hw ht hca hgasB
        rw [hto] at hw
        have hs1 : mf.ctx = m_ctx := hsame.ctx
        have hs2 : mf.precompiles = m_pre := hsame.precompiles
        have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
        clear hsame
        simp only [hw, ht, hca, hs1, hs2, hs3, hto]
        dsimp only [callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
        simp only [hto, returnMemory_ofWord, callCost, callGas, callExt, ofNat,
          BitVec.toNat_ofNat, hmod, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
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
        refine ⟨hbal, _, _, _, _, rfl, ?_, ?_, ?_⟩
        · simp only [Memory.loadWord_expand,
            Memory.loadWord_storeWord_of_disjoint _ 0 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 196 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 164 64 _ (by decide),
            Memory.loadWord_storeWord_of_disjoint _ 160 64 _ (by decide), hfmp]
        · rw_mem_sizes
          evm_gas_norm
          rw_mem_sizes
          evm_gas_norm
        · evm_gas
    · rw [Nat.not_le] at hbal
      refine WP.callNoValue (by pcode_fact) rfl ?_ ?_ hdepth ?_
        (transfer_halts_revert (ia := ia) (to := to) (amount := amount) _ ?_ rfl
          ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_) ?_
      · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
      · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, hmod,
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
        simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, hmod, Nat.reducePow,
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
          BitVec.toNat_ofNat, hmod, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
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
