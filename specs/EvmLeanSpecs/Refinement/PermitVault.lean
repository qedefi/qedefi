import EvmLeanSpecs.Refinement.PermitVaultBody
import EvmLeanSpecs.Refinement.PermitAsset

/-!
# The vault's `permit`, in any frame

`vault_permit_halts` is `asset_permit_halts` for the share token of the compiled vault
(`SolmateVault.runtimeCodeWith i`, any immutables): same statement (`PermitPost`), same
assumptions.
-/

namespace EvmLeanSpecs.Refinement.Permit

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

set_option maxHeartbeats 0 in
/-- **`permit` of the vault, in any frame** (see the module docstring). -/
theorem vault_permit_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    {owner spender : Address} {value deadline v r s : Word}
    (hd : PermitCall m.frame.msg.data owner spender value deadline v r s)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hcase : DomainCase i.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256))
    (hg : 100000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit) :
    Halts m (PermitPost (dsOf i.initialChainId i.initialDomainSeparator m) owner spender value
      deadline v r s m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2, harg3, harg4, harg5, harg6⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  subst hstd
  unfold PermitPost PermitValid
  by_cases hv : v.toNat < 256
  swap
  · -- `v` is not a `uint8`: the decoder reverts
    have hne := eq_of_ne (Ne.symm (and_255_ne (x := v) (by omega)))
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hne, ofAddress_and_addressMask, addressMask_and_ofAddress, Solidity.eq_self]
    refine ⟨fun h => absurd h.1 hv, fun _ => ⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]; evm_gas
  have hv' := and_255_of_lt hv
  by_cases hdl : (ofNat m_ctx.block.timestamp).toNat ≤ deadline.toNat
  swap
  · -- the deadline has passed
    have hlt' : Word.lt deadline (ofNat m_ctx.block.timestamp) = 1 :=
      (Word.lt_eq_one_iff _ _).2 (by omega)
    pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3, harg4,
      harg5, harg6, hv', hlt', ofAddress_and_addressMask, addressMask_and_ofAddress,
      Solidity.eq_self, iszero_one]
    refine ⟨fun h => absurd h.2.1 hdl, fun _ => ⟨_, rfl⟩, ?_⟩
    dsimp only [outputMachine]; evm_gas
  have hge : Word.lt deadline (ofNat m_ctx.block.timestamp) = 0 := (Word.lt_eq_zero_iff _ _).2 hdl
  pwp_run_to 1828 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3,
    harg4, harg5, harg6, hv', hge, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Solidity.eq_self, iszero_zero]
  refine WP.bind_mono (vault_ds_wp _ rfl hj rfl rfl (by simp) (by pjumpdest_disch)
    (Memory.loadWord_storeWord _ _ _) (by simp [Memory.size_storeWord, Memory.size_expand,
      Memory.wordsAfter, Memory.words]) hcase (by dsimp only; omega) (by dsimp only; omega))
    (fun _ _ _ h => h.elim) ?_
  rintro _ - ⟨mem, g, sub, rfl, hmem, hgb, hgu⟩
  dsimp only [Machine.resumeWith] at hgb hgu ⊢
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, dsOf]
  generalize domainSeparator m_ctx.crypto _ _ _ _ _ = ds
  rcases hmem with ⟨h64, hs⟩ | ⟨h64, hs⟩
  · refine WP.mono (vault_permit_body _ (F := 128) (S := 96) (.inl ⟨rfl, rfl⟩) rfl hj rfl rfl rfl
      h64 hs hv' (by dsimp only; omega) (by dsimp only; omega) rfl hdel1 hdepth hstatic)
      (fun _ _ h => h) ?_
    intro mf o _ ⟨h1, h2, h3⟩
    refine ⟨fun h => h1 h.2.2, fun h => h2 fun h' => h ⟨hv, hdl, h'⟩, ?_⟩
    dsimp only at h3 ⊢
    omega
  · refine WP.mono (vault_permit_body _ (F := 320) (S := 320) (.inr ⟨rfl, rfl⟩) rfl hj rfl rfl rfl
      h64 hs hv' (by dsimp only; omega) (by dsimp only; omega) rfl hdel1 hdepth hstatic)
      (fun _ _ h => h) ?_
    intro mf o _ ⟨h1, h2, h3⟩
    refine ⟨fun h => h1 h.2.2, fun h => h2 fun h' => h ⟨hv, hdl, h'⟩, ?_⟩
    dsimp only at h3 ⊢
    omega

end EvmLeanSpecs.Refinement.Permit
