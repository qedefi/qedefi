import EvmLeanSpecs.Refinement.PermitVaultTail
import EvmLeanSpecs.Refinement.PermitAssetBody

/-!
# The vault's `permit`: the body after `DOMAIN_SEPARATOR()`

`vault_permit_body` is `asset_permit_body` for the vault's code (pc `0x0c75`).
-/

namespace EvmLeanSpecs.Refinement.Permit

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

set_option maxHeartbeats 0 in
/-- **The body of the vault's `permit`** (pc `0x0c75` to the end), for both memory layouts that
`DOMAIN_SEPARATOR()` leaves. -/
theorem vault_permit_body {i : SolmateVault.Immutables} (m : Machine) {M : Memory} {F S : Nat}
    {ds deadline value v r s : Word} {owner spender : Address}
    (hFS : (F = 128 ∧ S = 96) ∨ (F = 320 ∧ S = 320))
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 3189)
    (hs : m.frame.stack = [ds, 1#256, 0#256, s, r, v, deadline, value, Word.ofAddress spender,
      Word.ofAddress owner, 1035#256, 3573918927#256])
    (hmem : m.frame.memory = M) (hM64 : M.loadWord 64 = BitVec.ofNat 256 F) (hMs : M.size = S)
    (hv : v &&& 255#256 = v)
    (hg : 90000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hstatic : m.frame.msg.isStatic = false) :
    WP m (fun _ => False) (BodyPost ds owner spender value deadline v r s m) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs hmem hstd
  rcases hFS with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · pwp_run_to 3227 [hM64, hMs, permit_norm, ofAddress_and_addressMask, addressMask_and_ofAddress,
      Memory.read_64, hstatic]
    generalize hN : m_world.sload m_msg.currentTarget
      (m_ctx.crypto.keccak256 (Bytes.ofWord (Word.ofAddress owner) ++ Bytes.ofWord 5#256)) = nonce
    wp_generalize_gas g1 hg1
    have hg1' : m_gasLeft ≤ g1 + 30000 := by subst hg1; evm_gas
    have hg1'' : 60000 ≤ g1 := by subst hg1; evm_gas
    have hg1u : g1 ≤ m_gasLeft := by subst hg1; omega
    clear hg1
    -- the struct hash
    wp_generalize_mem M1 hM1
    have hM1a := congrArg (Memory.loadWord · 64) hM1
    have hM1b := congrArg Memory.size hM1
    simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
      hM64] at hM1a
    simp only [permit_norm, hMs] at hM1b
    clear hM1
    replace hM1a := hM1a.symm
    replace hM1b := hM1b.symm
    pwp_run_to 3329 [hM1a, hM1b, permit_norm, ofAddress_and_addressMask,
      addressMask_and_ofAddress, Memory.read_192]
    -- the digest
    wp_generalize_mem M2 hM2
    have hM2a := congrArg (Memory.loadWord · 64) hM2
    have hM2b := congrArg Memory.size hM2
    simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord] at hM2a
    simp only [permit_norm, hM1b] at hM2b
    clear hM2
    replace hM2a := hM2a.symm
    replace hM2b := hM2b.symm
    pwp_run_to 3387 [hM2a, hM2b, permit_norm, Memory.read_66, Memory.read_storeWord_two,
      prefix_eq]
    -- the input of `ecrecover`
    wp_generalize_mem M3 hM3
    have hM3a := congrArg (Memory.loadWord · 64) hM3
    have hM3b := congrArg Memory.size hM3
    simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord] at hM3a
    simp only [permit_norm, hM2b] at hM3b
    clear hM3
    replace hM3a := hM3a.symm
    replace hM3b := hM3b.symm
    pwp_run_to 3438 [hM3a, hM3b, permit_norm, hv]
    refine WP.mono (vault_permit_tail _
      (dg := digest m_ctx.crypto ds (structHash m_ctx.crypto owner spender value nonce deadline))
      (by decide) rfl hj rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl
      (by dsimp only; rw [World.code_sstore]; exact hdel1) hdepth hstatic) (fun _ _ h => h) ?_
    · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
        Memory.loadWord_storeWord]
    · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
        Memory.loadWord_storeWord]
    · simp (disch := decide) only [Memory.read_128, Memory.read_expand, Memory.read_storeWord,
        Memory.read_storeWord_of_disjoint]
      rfl
    · simp only [permit_norm, hM3b]
    · dsimp only; omega
    · dsimp only; omega
    intro mf o _ ht
    obtain ⟨h1, h2, h3⟩ := ht
    subst hN
    refine ⟨fun hr => h1 hr, fun hr => h2 hr, ?_⟩
    dsimp only at h3 ⊢
    omega

end EvmLeanSpecs.Refinement.Permit
