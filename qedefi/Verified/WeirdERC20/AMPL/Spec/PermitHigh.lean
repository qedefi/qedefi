import Verified.WeirdERC20.AMPL.Spec.PermitBridge

/-!
# AMPL's `permit` from enough gas, for a short name: the tails

The runs of `permit_high` (`PermitFull`) from `pc = 2689`, where `DOMAIN_SEPARATOR()`'s name
bytes are in memory, to the end: `tail_high_empty` (an empty name, free pointer `384`) and
`tail_high_short` (1 to 31 bytes, free pointer `416`). Below the call-depth limit, with the
signature recovered as the owner and the nonce below `2²⁵⁶ - 1`, the frame succeeds with the
nonce incremented, the allowance set and `Approval`; otherwise it reverts. A long name moves
the free memory pointer by a symbolic amount, which these runs do not cover; `amplGp` is `2⁶⁴`
there.

`wp_staticcall_one_high`: the call to `ecrecover` below the depth limit with the gas the code
forwards (all of it, `GAS`): it succeeds, and at most `5600` gas is spent on it.
-/

set_option linter.unusedSimpArgs false

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open EvmLogic.Program.Nested
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC4626 Verified.WeirdERC20.AMPL.Contracts
open Verified.WeirdERC20.AMPL.Spec Verified.Solady.Spec.AnyGas

variable {H : Machine → Outcome → Prop} {Q : Machine → Prop} {m : Machine}
  {inOff outOff : Word} {rest : List Word}

/-- **solc's call to `ecrecover` with all the gas, below the depth limit.** -/
theorem wp_staticcall_one_high {hash v r s : Word}
    (hcode : m.frame.code[m.frame.pc]? = some 0xfa)
    (hstk : m.frame.stack =
      ofNat m.frame.gasLeft :: 1#256 :: inOff :: 128#256 :: outOff :: 32#256 :: rest)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hin : m.frame.memory.read inOff.toNat 128 =
      Bytes.ofWord hash ++ (Bytes.ofWord v ++ (Bytes.ofWord r ++ Bytes.ofWord s)))
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hmem : (callExt m inOff 128#256 outOff 32#256).cost = 0)
    (hg : 10000 ≤ m.frame.gasLeft) (hgl : m.frame.gasLeft < 2 ^ 64)
    (kok : ∀ (gl : Nat) (sb : Substate), sb.logs = m.frame.sub.logs →
      m.frame.gasLeft ≤ gl + 5600 →
      WP { m with frame := { m.frame with
        stack := 1 :: rest
        memory := returnMemory (callMemory m inOff 128#256 outOff 32#256) outOff.toNat 32
          (ecrecoverOutput m.ctx.crypto hash v r s)
        gasLeft := gl
        sub := sb
        returnData := ecrecoverOutput m.ctx.crypto hash v r s
        pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  have hacc := accessCost_le (m.frame.sub.accessedAddresses.contains 1)
  have hgw : (ofNat m.frame.gasLeft : Word).toNat = m.frame.gasLeft := by
    simp only [ofNat, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hto : Word.toAddress (1#256) = 1 := by decide
  have hcg : callGas m (ofNat m.frame.gasLeft) 0 1 0 0 inOff 128#256 outOff 32#256 =
      { cost := Gas.maxMessageCallGas (m.frame.gasLeft - Gas.accessCost
            (m.frame.sub.accessedAddresses.contains 1)) +
          Gas.accessCost (m.frame.sub.accessedAddresses.contains 1),
        subCall := Gas.maxMessageCallGas (m.frame.gasLeft - Gas.accessCost
            (m.frame.sub.accessedAddresses.contains 1)) } := by
    simp only [callGas]
    rw [hmem, hgw]
    simp only [Nat.add_zero]
    rw [messageCallGas_zero (by omega)]
    simp only [Gas.maxMessageCallGas, Nat.sub_zero]
    congr 1 <;> omega
  refine WP.staticcall_ecrecover hcode hstk hstd hdel ?_ hdepth hin ?_ ?_
  · simp only [callCost, hcg, hmem, Gas.maxMessageCallGas]; omega
  · simp only [hcg, Gas.maxMessageCallGas]; omega
  · refine kok _ _ (by simp [mergeSub, Substate.warmAddr, Substate.ofMessage, callerFrame]) ?_
    simp only [callCost, hcg, hmem, Gas.maxMessageCallGas]
    omega

end Verified.WeirdERC20.AMPL.Spec.Malformed

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter EvmLogic.Tactic
open EvmLogic.Program.Nested
open QEDefi.ERC20 QEDefi.ERC20.Spec QEDefi.ERC4626 Verified.WeirdERC20.AMPL.Contracts
open Verified.WeirdERC20.AMPL.Spec Verified.Solady.Spec.AnyGas

variable {H : Machine → Outcome → Prop} {Q : Machine → Prop} {m : Machine}
  {inOff outOff : Word} {rest : List Word}

theorem add_one_lt_iszero {n : Word} (h : n.toNat + 1 < 2 ^ 256) :
    (Word.lt (1#256 + n) n).iszero = 1 := by
  have : BitVec.ult (1#256 + n) n = false := by
    simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp
  simp [Word.lt, Word.ofBool, this, Word.iszero]

theorem add_one_lt_iszero_zero {n : Word} (h : ¬ n.toNat + 1 < 2 ^ 256) :
    (Word.lt (1#256 + n) n).iszero = 0 := by
  have hn := n.isLt
  have he : n.toNat = 2 ^ 256 - 1 := by omega
  have h0 : 1#256 + n = 0#256 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, he]; norm_num
  rw [h0]
  have : BitVec.ult 0#256 n = true := by simp [BitVec.ult, he]
  simp [Word.lt, Word.ofBool, this, Word.iszero]

theorem eq_addr_zero {a b : Address} (h : a ≠ b) :
    (Word.ofAddress a).eq (Word.ofAddress b) = 0 := by
  have : Word.ofAddress a ≠ Word.ofAddress b := fun e => h (Word.ofAddress_injective e)
  have h' : (Word.ofAddress a == Word.ofAddress b) = false := by simpa using this
  simp [Word.eq, Word.ofBool, h']

/-- **`STATICCALL` at the depth limit** with the gas the code forwards: it pushes `0`. -/
theorem staticcall_limit_high
    (hcode : m.frame.code[m.frame.pc]? = some 0xfa)
    (hstk : m.frame.stack =
      ofNat m.frame.gasLeft :: 1#256 :: inOff :: 128#256 :: outOff :: 32#256 :: rest)
    (hlen : rest.length < 1024)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : Gas.stackDepthLimit < m.frame.msg.depth + 1)
    (hmem : (callExt m inOff 128#256 outOff 32#256).cost = 0)
    (hg : 10000 ≤ m.frame.gasLeft) (hgl : m.frame.gasLeft < 2 ^ 64)
    (k : ∀ (gl : Nat) (sb : Substate), m.frame.gasLeft ≤ gl + 2600 →
      WP { m with frame := { m.frame with
        stack := 0 :: rest
        memory := callMemory m inOff 128#256 outOff 32#256
        gasLeft := gl
        sub := sb
        returnData := ByteArray.empty
        pc := m.frame.pc + 1 } } Q H) :
    WP m Q H := by
  have hacc := accessCost_le (m.frame.sub.accessedAddresses.contains 1)
  have hgw : (ofNat m.frame.gasLeft : Word).toNat = m.frame.gasLeft := by
    simp only [ofNat, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hto : Word.toAddress (1#256) = 1 := by decide
  have hcg : callGas m (ofNat m.frame.gasLeft) 0 1 0 0 inOff 128#256 outOff 32#256 =
      { cost := Gas.maxMessageCallGas (m.frame.gasLeft - Gas.accessCost
            (m.frame.sub.accessedAddresses.contains 1)) +
          Gas.accessCost (m.frame.sub.accessedAddresses.contains 1),
        subCall := Gas.maxMessageCallGas (m.frame.gasLeft - Gas.accessCost
            (m.frame.sub.accessedAddresses.contains 1)) } := by
    simp only [callGas]
    rw [hmem, hgw]
    simp only [Nat.add_zero]
    rw [messageCallGas_zero (by omega)]
    simp only [Gas.maxMessageCallGas, Nat.sub_zero]
    congr 1 <;> omega
  have hdel' : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code (Word.toAddress 1#256)) =
      none := by rw [hto]; exact hdel
  have hgas : callCost m (ofNat m.frame.gasLeft) 0 (Word.toAddress 1#256) 0 0 inOff 128#256 outOff
      32#256 ≤ m.frame.gasLeft := by
    rw [hto]; simp only [callCost, hcg, hmem, Gas.maxMessageCallGas]; omega
  refine WP.of_step (step_staticcall_limit hcode hstk hdel' hgas hdepth hlen)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
  refine k _ _ ?_
  rw [hto]
  simp only [callCost, hcg, hmem, Gas.maxMessageCallGas]
  omega

set_option maxHeartbeats 0 in
/-- `permit` from the return of `name()` with enough gas, the name has 1 to 31 bytes. -/
theorem tail_high_short {H : Machine → Outcome → Prop} (m : Machine) (L : Nat)
    (sh nonce s r v dl val : Word) (o sp : Address)
    (hc : m.frame.code = AMPL.runtimeCode) (hj : JumpTable m.frame.jumpDests AMPL.runtimeCode)
    (hpc : m.frame.pc = 2689)
    (hs : m.frame.stack = [352#256, DOMAIN_TYPEHASH, ofNat m.ctx.block.chainId, 0#256,
      5041#256, 0#256, sh, nonce, s, r, v, dl, val, Word.ofAddress sp, Word.ofAddress o, 974#256,
      3573918927#256])
    (hM352 : m.frame.memory.loadWord 352 = BitVec.ofNat 256 L)
    (hM64 : m.frame.memory.loadWord 64 = 416#256)
    (hMs : m.frame.memory.size = 416) (hL0 : 0 < L) (hL31 : L ≤ 31)
    (hst : m.frame.msg.isStatic = false) (hg : 100000 ≤ m.frame.gasLeft)
    (hgl : m.frame.gasLeft < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hsucc : ∀ (mf : Machine),
      m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit →
      (ecrecoverAddress? m.ctx.crypto (digest m.ctx.crypto (dsOfMem m (BitVec.ofNat 256 L)) sh)
        (255#256 &&& v) r s).getD 0 = o →
      nonce.toNat + 1 < 2 ^ 256 →
      mf.world = (m.world.sstore m.frame.msg.currentTarget
          (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress o) ++ Bytes.ofWord 160#256))
          (1#256 + nonce)).sstore m.frame.msg.currentTarget
        (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress sp) ++
          Bytes.ofWord (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress o) ++
            Bytes.ofWord 159#256)))) val →
      mf.transient = m.transient → mf.createdAccounts = m.createdAccounts →
      mf.frame.sub.logs = m.frame.sub.logs.push (approvalLog m.frame.msg.currentTarget o sp val) →
      H mf (.success .empty))
    (hrev : ∀ (mf : Machine) (out : ByteArray),
      ¬ (m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit ∧
        (ecrecoverAddress? m.ctx.crypto (digest m.ctx.crypto (dsOfMem m (BitVec.ofNat 256 L)) sh)
          (255#256 &&& v) r s).getD 0 = o ∧ nonce.toNat + 1 < 2 ^ 256) →
      H mf (.revert out)) :
    WP m (fun _ => False) H := by
  have hLm : L % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = L :=
    Nat.mod_eq_of_lt (by omega)
  have hext : Gas.extendMemory 416 [(384, L)] = { cost := 0, newSize := 416 } :=
    Gas.extendMemory_one_of_le (by omega) (by decide)
  have hkc : Gas.keccak256Cost L = 36 := by
    simp only [Gas.keccak256Cost, Gas.keccak256Base, Gas.keccak256PerWord, Gas.words]; omega
  have hexp : ∀ a b, a + b ≤ 416 → m.frame.memory.expand a b = m.frame.memory :=
    fun a b h => Memory.expand_eq_self_of_le (by omega) (by omega)
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only [dsOfMem] at *
  subst hc hpc hs hstd
  pwp_run_to 2697 [hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH, mask_lit_and, and_mask_lit,
      Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
  refine WP.of_step (step_keccak256 (by pcode_fact) rfl (by simp) ?_)
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ ?_
  · simp (disch := omega) only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hLm, hexp, hMs,
      hext, hkc]
    omega
  simp (disch := omega) only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hLm, hexp, hMs,
    hext, hkc, Nat.reduceAdd]
  pwp_run_to 5175 [hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH, mask_lit_and, and_mask_lit,
      Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
  have hmem : ∀ mm : Machine, mm.frame.memory.size = 960 →
      (callExt mm 802#256 128#256 770#256 32#256).cost = 0 := fun mm h => by
    simp only [callExt, h]; decide
  by_cases hdep : m_msg.depth + 1 ≤ Gas.stackDepthLimit
  swap
  · refine staticcall_limit_high (by pcode_fact) rfl (by simp) hdel (Nat.lt_of_not_le hdep)
      (hmem _ ?_) (by dsimp only; omega) (by dsimp only; omega) fun gl sb hgl' => ?_
    · dsimp only
      simp [Memory.size_storeWord, Memory.size_expand, hMs, Memory.wordsAfter, Memory.words,
        Nat.max_def]
    dsimp only
    pwp_xsteps [hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH, mask_lit_and, and_mask_lit,
      Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
    exact hrev _ _ fun h => hdep h.1
  refine wp_staticcall_one_high (by pcode_fact) rfl rfl hdel (read_128_loadWords _ _) hdep
    (hmem _ ?_) (by dsimp only; omega) (by dsimp only; omega) fun gl sb hsb hgl' => ?_
  · dsimp only
    simp [Memory.size_storeWord, Memory.size_expand, hMs, Memory.wordsAfter, Memory.words,
      Nat.max_def]
  dsimp only
  rw [returnMemory_ecrecoverOutput]
  split
  · rename_i a hrec
    simp (disch := omega) only [Memory.loadWord_expand, Memory.read_expand,
          loadWord_storeWord_eq, Memory.loadWord_storeWord_of_disjoint, read32_storeWord_eq,
          Memory.read_storeWord_of_disjoint, Memory.read_66, Memory.read_160,
          read_storeWord_prefix_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, callMemory,
          extract_ofWord_32, prefix_eq, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, hexp] at hrec
    by_cases hao : o = a
    · subst hao
      have hr : (ecrecoverAddress? m_ctx.crypto (digest m_ctx.crypto (m_ctx.crypto.keccak256
          (Bytes.ofWord DOMAIN_TYPEHASH ++ (Bytes.ofWord (m_ctx.crypto.keccak256
            (m_memory.read 384 ((BitVec.ofNat 256 L).toNat))) ++ (Bytes.ofWord VERSION_HASH ++
              (Bytes.ofWord (ofNat m_ctx.block.chainId) ++
                Bytes.ofWord (Word.ofAddress m_msg.currentTarget)))))) sh)
          (255#256 &&& v) r s).getD 0 = o := by
        simp only [digest, DOMAIN_TYPEHASH, VERSION_HASH, BitVec.toNat_ofNat, hLm]
        rw [hrec]; rfl
      by_cases hno : nonce.toNat + 1 < 2 ^ 256
      · have hn1 := add_one_lt_iszero hno
        pwp_xsteps [hn1, hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH,
          mask_lit_and, and_mask_lit, Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
        exact WP.halt_of_step (step_stop (by pcode_fact)) (SameFrame.refl _)
          (hsucc _ hdep hr hno rfl rfl rfl (by
              logs_simp [hsb]
              rw [logEntry_eq_eventLog (data := [val])]
              · rfl
              · simp (disch := omega) only [Memory.read_expand, read32_storeWord_eq,
                  Memory.read_storeWord_of_disjoint, encodeArgs_one, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt, Nat.reducePow, Nat.reduceMod]))
      · have hn0 := add_one_lt_iszero_zero hno
        pwp_xsteps [hn0, hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH,
          mask_lit_and, and_mask_lit, Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
        exact hrev _ _ fun h => hno h.2.2
    · have hne := eq_addr_zero hao
      pwp_xsteps [hne, hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH,
        mask_lit_and, and_mask_lit, Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
      refine hrev _ _ fun h => hao ?_
      have h2 := h.2.1
      simp only [digest, DOMAIN_TYPEHASH, VERSION_HASH, BitVec.toNat_ofNat, hLm] at h2
      rw [hrec] at h2
      exact h2.symm
  · rename_i hrec
    simp (disch := omega) only [Memory.loadWord_expand, Memory.read_expand,
          loadWord_storeWord_eq, Memory.loadWord_storeWord_of_disjoint, read32_storeWord_eq,
          Memory.read_storeWord_of_disjoint, Memory.read_66, Memory.read_160,
          read_storeWord_prefix_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, callMemory,
          extract_ofWord_32, prefix_eq, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, hexp] at hrec
    by_cases ho0 : o = 0
    · subst ho0
      have hr : (ecrecoverAddress? m_ctx.crypto (digest m_ctx.crypto (m_ctx.crypto.keccak256
          (Bytes.ofWord DOMAIN_TYPEHASH ++ (Bytes.ofWord (m_ctx.crypto.keccak256
            (m_memory.read 384 ((BitVec.ofNat 256 L).toNat))) ++ (Bytes.ofWord VERSION_HASH ++
              (Bytes.ofWord (ofNat m_ctx.block.chainId) ++
                Bytes.ofWord (Word.ofAddress m_msg.currentTarget)))))) sh)
          (255#256 &&& v) r s).getD 0 = 0 := by
        simp only [digest, DOMAIN_TYPEHASH, VERSION_HASH, BitVec.toNat_ofNat, hLm]
        rw [hrec]; rfl
      by_cases hno : nonce.toNat + 1 < 2 ^ 256
      · have hn1 := add_one_lt_iszero hno
        pwp_xsteps [hn1, hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH,
          mask_lit_and, and_mask_lit, Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
        exact WP.halt_of_step (step_stop (by pcode_fact)) (SameFrame.refl _)
          (hsucc _ hdep hr hno rfl rfl rfl (by
              logs_simp [hsb]
              rw [logEntry_eq_eventLog (data := [val])]
              · rfl
              · simp (disch := omega) only [Memory.read_expand, read32_storeWord_eq,
                  Memory.read_storeWord_of_disjoint, encodeArgs_one, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt, Nat.reducePow, Nat.reduceMod]))
      · have hn0 := add_one_lt_iszero_zero hno
        pwp_xsteps [hn0, hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH,
          mask_lit_and, and_mask_lit, Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
        exact hrev _ _ fun h => hno h.2.2
    · have hne : (Word.ofAddress o).eq 0#256 = 0 := eq_addr_zero (b := 0) ho0
      pwp_xsteps [hne, hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH,
        mask_lit_and, and_mask_lit, Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
      refine hrev _ _ fun h => ho0 ?_
      have h2 := h.2.1
      simp only [digest, DOMAIN_TYPEHASH, VERSION_HASH, BitVec.toNat_ofNat, hLm] at h2
      rw [hrec] at h2
      exact h2.symm

set_option maxHeartbeats 0 in
/-- `permit` from the return of `name()` with enough gas, the name is empty. -/
theorem tail_high_empty {H : Machine → Outcome → Prop} (m : Machine) (L : Nat)
    (sh nonce s r v dl val : Word) (o sp : Address)
    (hc : m.frame.code = AMPL.runtimeCode) (hj : JumpTable m.frame.jumpDests AMPL.runtimeCode)
    (hpc : m.frame.pc = 2689)
    (hs : m.frame.stack = [352#256, DOMAIN_TYPEHASH, ofNat m.ctx.block.chainId, 0#256,
      5041#256, 0#256, sh, nonce, s, r, v, dl, val, Word.ofAddress sp, Word.ofAddress o, 974#256,
      3573918927#256])
    (hM352 : m.frame.memory.loadWord 352 = BitVec.ofNat 256 L)
    (hM64 : m.frame.memory.loadWord 64 = 384#256)
    (hMs : m.frame.memory.size = 384) (hL0 : L = 0)
    (hst : m.frame.msg.isStatic = false) (hg : 100000 ≤ m.frame.gasLeft)
    (hgl : m.frame.gasLeft < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hsucc : ∀ (mf : Machine),
      m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit →
      (ecrecoverAddress? m.ctx.crypto (digest m.ctx.crypto (dsOfMem m (BitVec.ofNat 256 L)) sh)
        (255#256 &&& v) r s).getD 0 = o →
      nonce.toNat + 1 < 2 ^ 256 →
      mf.world = (m.world.sstore m.frame.msg.currentTarget
          (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress o) ++ Bytes.ofWord 160#256))
          (1#256 + nonce)).sstore m.frame.msg.currentTarget
        (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress sp) ++
          Bytes.ofWord (m.ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress o) ++
            Bytes.ofWord 159#256)))) val →
      mf.transient = m.transient → mf.createdAccounts = m.createdAccounts →
      mf.frame.sub.logs = m.frame.sub.logs.push (approvalLog m.frame.msg.currentTarget o sp val) →
      H mf (.success .empty))
    (hrev : ∀ (mf : Machine) (out : ByteArray),
      ¬ (m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit ∧
        (ecrecoverAddress? m.ctx.crypto (digest m.ctx.crypto (dsOfMem m (BitVec.ofNat 256 L)) sh)
          (255#256 &&& v) r s).getD 0 = o ∧ nonce.toNat + 1 < 2 ^ 256) →
      H mf (.revert out)) :
    WP m (fun _ => False) H := by
  have hLm : L % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = L :=
    by rw [hL0]
  have hext : Gas.extendMemory 384 [(384, L)] = { cost := 0, newSize := 384 } := by
    rw [hL0]; exact Gas.extendMemory_one_of_le (by omega) (by decide)
  have hkc : Gas.keccak256Cost L = 30 := by rw [hL0]; rfl
  have hexp : ∀ a b, a + b ≤ 384 → m.frame.memory.expand a b = m.frame.memory :=
    fun a b h => Memory.expand_eq_self_of_le (by omega) (by omega)
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only [dsOfMem] at *
  subst hc hpc hs hstd
  pwp_run_to 2697 [hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH, mask_lit_and, and_mask_lit,
      Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
  refine WP.of_step (step_keccak256 (by pcode_fact) rfl (by simp) ?_)
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ ?_
  · simp (disch := omega) only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hLm, hexp, hMs,
      hext, hkc]
    omega
  simp (disch := omega) only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hLm, hexp, hMs,
    hext, hkc, Nat.reduceAdd]
  pwp_run_to 5175 [hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH, mask_lit_and, and_mask_lit,
      Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
  have hmem : ∀ mm : Machine, mm.frame.memory.size = 928 →
      (callExt mm 770#256 128#256 738#256 32#256).cost = 0 := fun mm h => by
    simp only [callExt, h]; decide
  by_cases hdep : m_msg.depth + 1 ≤ Gas.stackDepthLimit
  swap
  · refine staticcall_limit_high (by pcode_fact) rfl (by simp) hdel (Nat.lt_of_not_le hdep)
      (hmem _ ?_) (by dsimp only; omega) (by dsimp only; omega) fun gl sb hgl' => ?_
    · dsimp only
      simp [Memory.size_storeWord, Memory.size_expand, hMs, Memory.wordsAfter, Memory.words,
        Nat.max_def]
    dsimp only
    pwp_xsteps [hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH, mask_lit_and, and_mask_lit,
      Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
    exact hrev _ _ fun h => hdep h.1
  refine wp_staticcall_one_high (by pcode_fact) rfl rfl hdel (read_128_loadWords _ _) hdep
    (hmem _ ?_) (by dsimp only; omega) (by dsimp only; omega) fun gl sb hsb hgl' => ?_
  · dsimp only
    simp [Memory.size_storeWord, Memory.size_expand, hMs, Memory.wordsAfter, Memory.words,
      Nat.max_def]
  dsimp only
  rw [returnMemory_ecrecoverOutput]
  split
  · rename_i a hrec
    simp (disch := omega) only [Memory.loadWord_expand, Memory.read_expand,
          loadWord_storeWord_eq, Memory.loadWord_storeWord_of_disjoint, read32_storeWord_eq,
          Memory.read_storeWord_of_disjoint, Memory.read_66, Memory.read_160,
          read_storeWord_prefix_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, callMemory,
          extract_ofWord_32, prefix_eq, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, hexp] at hrec
    by_cases hao : o = a
    · subst hao
      have hr : (ecrecoverAddress? m_ctx.crypto (digest m_ctx.crypto (m_ctx.crypto.keccak256
          (Bytes.ofWord DOMAIN_TYPEHASH ++ (Bytes.ofWord (m_ctx.crypto.keccak256
            (m_memory.read 384 ((BitVec.ofNat 256 L).toNat))) ++ (Bytes.ofWord VERSION_HASH ++
              (Bytes.ofWord (ofNat m_ctx.block.chainId) ++
                Bytes.ofWord (Word.ofAddress m_msg.currentTarget)))))) sh)
          (255#256 &&& v) r s).getD 0 = o := by
        simp only [digest, DOMAIN_TYPEHASH, VERSION_HASH, BitVec.toNat_ofNat, hLm]
        rw [hrec]; rfl
      by_cases hno : nonce.toNat + 1 < 2 ^ 256
      · have hn1 := add_one_lt_iszero hno
        pwp_xsteps [hn1, hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH,
          mask_lit_and, and_mask_lit, Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
        exact WP.halt_of_step (step_stop (by pcode_fact)) (SameFrame.refl _)
          (hsucc _ hdep hr hno rfl rfl rfl (by
              logs_simp [hsb]
              rw [logEntry_eq_eventLog (data := [val])]
              · rfl
              · simp (disch := omega) only [Memory.read_expand, read32_storeWord_eq,
                  Memory.read_storeWord_of_disjoint, encodeArgs_one, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt, Nat.reducePow, Nat.reduceMod]))
      · have hn0 := add_one_lt_iszero_zero hno
        pwp_xsteps [hn0, hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH,
          mask_lit_and, and_mask_lit, Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
        exact hrev _ _ fun h => hno h.2.2
    · have hne := eq_addr_zero hao
      pwp_xsteps [hne, hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH,
        mask_lit_and, and_mask_lit, Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
      refine hrev _ _ fun h => hao ?_
      have h2 := h.2.1
      simp only [digest, DOMAIN_TYPEHASH, VERSION_HASH, BitVec.toNat_ofNat, hLm] at h2
      rw [hrec] at h2
      exact h2.symm
  · rename_i hrec
    simp (disch := omega) only [Memory.loadWord_expand, Memory.read_expand,
          loadWord_storeWord_eq, Memory.loadWord_storeWord_of_disjoint, read32_storeWord_eq,
          Memory.read_storeWord_of_disjoint, Memory.read_66, Memory.read_160,
          read_storeWord_prefix_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, callMemory,
          extract_ofWord_32, prefix_eq, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, hexp] at hrec
    by_cases ho0 : o = 0
    · subst ho0
      have hr : (ecrecoverAddress? m_ctx.crypto (digest m_ctx.crypto (m_ctx.crypto.keccak256
          (Bytes.ofWord DOMAIN_TYPEHASH ++ (Bytes.ofWord (m_ctx.crypto.keccak256
            (m_memory.read 384 ((BitVec.ofNat 256 L).toNat))) ++ (Bytes.ofWord VERSION_HASH ++
              (Bytes.ofWord (ofNat m_ctx.block.chainId) ++
                Bytes.ofWord (Word.ofAddress m_msg.currentTarget)))))) sh)
          (255#256 &&& v) r s).getD 0 = 0 := by
        simp only [digest, DOMAIN_TYPEHASH, VERSION_HASH, BitVec.toNat_ofNat, hLm]
        rw [hrec]; rfl
      by_cases hno : nonce.toNat + 1 < 2 ^ 256
      · have hn1 := add_one_lt_iszero hno
        pwp_xsteps [hn1, hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH,
          mask_lit_and, and_mask_lit, Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
        exact WP.halt_of_step (step_stop (by pcode_fact)) (SameFrame.refl _)
          (hsucc _ hdep hr hno rfl rfl rfl (by
              logs_simp [hsb]
              rw [logEntry_eq_eventLog (data := [val])]
              · rfl
              · simp (disch := omega) only [Memory.read_expand, read32_storeWord_eq,
                  Memory.read_storeWord_of_disjoint, encodeArgs_one, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt, Nat.reducePow, Nat.reduceMod]))
      · have hn0 := add_one_lt_iszero_zero hno
        pwp_xsteps [hn0, hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH,
          mask_lit_and, and_mask_lit, Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
        exact hrev _ _ fun h => hno h.2.2
    · have hne : (Word.ofAddress o).eq 0#256 = 0 := eq_addr_zero (b := 0) ho0
      pwp_xsteps [hne, hM352, hM64, hMs, hLm, hext, hkc, hexp, hst, DOMAIN_TYPEHASH,
        mask_lit_and, and_mask_lit, Word.toAddress_ofAddress, callMemory, Solidity.eq_self, Memory.read_64]
      refine hrev _ _ fun h => ho0 ?_
      have h2 := h.2.1
      simp only [digest, DOMAIN_TYPEHASH, VERSION_HASH, BitVec.toNat_ofNat, hLm] at h2
      rw [hrec] at h2
      exact h2.symm

end Verified.WeirdERC20.AMPL.Spec.Malformed
