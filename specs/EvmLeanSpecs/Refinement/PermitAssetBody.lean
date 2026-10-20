import EvmLeanSpecs.Refinement.PermitAssetTail

/-!
# The asset's `permit`: the body after `DOMAIN_SEPARATOR()`

`asset_permit_body`: from pc `0x0566` (back from the internal `DOMAIN_SEPARATOR()`, the
separator on the stack) to the end of the frame. The code increments `nonces[owner]`
(`SSTORE`, unchecked), hashes the EIP-712 struct (`structHash`) at the free pointer, hashes
`"\x19\x01" ‖ separator ‖ structHash` (`digest`), lays out `digest ‖ v ‖ r ‖ s` for
`ecrecover` with a zero in the output word, and continues with `asset_permit_tail`. Memory is
as `DOMAIN_SEPARATOR()` left it (`DsMem`: free pointer `0x80` or `0x140`).
-/

namespace EvmLeanSpecs.Refinement.Permit

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-- What the body of `permit` does, from a machine `m` back from `DOMAIN_SEPARATOR()` with
separator `ds`, at the owner's nonce `nonce` read from `m.world`: if the signature recovers
`owner ≠ 0` for the permit digest, success with `permitWorld`, transient storage and created
accounts unchanged, `Approval(owner, spender, value)` logged; otherwise a revert; at most `80000` gas. -/
def BodyPost (ds : Word) (owner spender : Address) (value deadline v r s : Word) (m mf : Machine)
    (o : Outcome) : Prop :=
  (RecoversTo m.ctx.crypto (digest m.ctx.crypto ds (structHash m.ctx.crypto owner spender value
      (m.world.sload m.frame.msg.currentTarget (nonceSlot m.ctx.crypto owner)) deadline)) v r s
      owner →
    o = .success .empty ∧
    mf.world = permitWorld m.ctx.crypto m.world m.frame.msg.currentTarget owner spender value ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (approvalLog m.frame.msg.currentTarget owner spender value)) ∧
  (¬ RecoversTo m.ctx.crypto (digest m.ctx.crypto ds (structHash m.ctx.crypto owner spender value
      (m.world.sload m.frame.msg.currentTarget (nonceSlot m.ctx.crypto owner)) deadline)) v r s
      owner → ∃ out, o = .revert out) ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 80000

/-- The two-byte prefix the code stores (`shl(240, 0x1901)`), as the digest reads it. -/
theorem prefix_eq :
    (Bytes.ofWord 11309588061646438093662687302255421419811724423900836950936401294474059186176#256).extract
      0 2 = eip712Prefix := by
  decide +kernel

set_option maxHeartbeats 0 in
/-- **The body of the asset's `permit`** (pc `0x0566` to the end), for both memory layouts that
`DOMAIN_SEPARATOR()` leaves. -/
theorem asset_permit_body {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {F S : Nat}
    {ds deadline value v r s : Word} {owner spender : Address}
    (hFS : (F = 128 ∧ S = 96) ∨ (F = 320 ∧ S = 320))
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1382)
    (hs : m.frame.stack = [ds, 1#256, 0#256, s, r, v, deadline, value, Word.ofAddress spender,
      Word.ofAddress owner, 424#256, 3573918927#256])
    (hmem : m.frame.memory = M) (hM64 : M.loadWord 64 = BitVec.ofNat 256 F) (hMs : M.size = S)
    (hv : v &&& 255#256 = v)
    (hg : 90000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hstatic : m.frame.msg.isStatic = false) :
    WP m (fun _ => False) (BodyPost ds owner spender value deadline v r s m) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs hmem hstd
  rcases hFS with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · pwp_run_to 1420 [hM64, hMs, permit_norm, ofAddress_and_addressMask, addressMask_and_ofAddress,
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
    pwp_run_to 1522 [hM1a, hM1b, permit_norm, ofAddress_and_addressMask,
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
    pwp_run_to 1580 [hM2a, hM2b, permit_norm, Memory.read_66, Memory.read_storeWord_two,
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
    pwp_run_to 1631 [hM3a, hM3b, permit_norm, hv]
    refine WP.mono (asset_permit_tail _
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
    refine ⟨fun hr => ?_, fun hr => h2 hr, ?_⟩
    · obtain ⟨ho, hw, ht, hc, hl⟩ := h1 hr
      exact ⟨ho, hw, ht, hc, hl⟩
    dsimp only at h3 ⊢
    omega

end EvmLeanSpecs.Refinement.Permit
