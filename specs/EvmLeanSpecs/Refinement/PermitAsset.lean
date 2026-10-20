import EvmLeanSpecs.Refinement.PermitAssetBody

/-!
# The asset's `permit`, in any frame

`asset_permit_halts`: `permit(owner, spender, value, deadline, v, r, s)` of the compiled asset
(Solmate `MockERC20`, any immutables), run in any fresh non-static frame (a top-level call or a
callee frame), for every `Crypto`:

* it **succeeds** (empty output) exactly when `PermitValid` holds at the owner's current nonce:
  `v < 256`, the deadline is not before the block timestamp, and `SigOk` (the `ECRECOVER`
  precompile, for this `crypto`, recovers `owner ≠ 0` from the EIP-712 digest under the
  domain separator `dsOf …` that `DOMAIN_SEPARATOR()` computes); the world is then
  `permitWorld` (`nonces[owner] += 1`, `allowance[owner][spender] = value`);
* otherwise it **reverts** (so the world is rolled back to the snapshot);
* on success it appends `Approval(owner, spender, value)` to the frame's logs;
* it uses at most 100000 gas.

Assumptions: a call of the standard precompiles of the context (`hstd`), address `0x01` not
delegated (before Prague, or no EIP-7702 designator there), room for one more call frame,
`100000 ≤ gas < 2⁶⁴`, and `DomainCase` (the deployment chain, or a short `name`).
-/

namespace EvmLeanSpecs.Refinement.Permit

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-- What `permit` ends with, relative to the start machine `m`, for the domain separator `ds`:
success with `permitWorld` exactly when `PermitValid` holds at the owner's current nonce, a
revert otherwise, at most `100000` gas. -/
def PermitPost (ds : Word) (owner spender : Address) (value deadline v r s : Word) (m mf : Machine)
    (o : Outcome) : Prop :=
  (PermitValid m.ctx.crypto ds m.ctx.block.timestamp owner spender value deadline v r s
      (m.world.sload m.frame.msg.currentTarget (nonceSlot m.ctx.crypto owner)) →
    o = .success .empty ∧
    mf.world = permitWorld m.ctx.crypto m.world m.frame.msg.currentTarget owner spender value ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (approvalLog m.frame.msg.currentTarget owner spender value)) ∧
  (¬ PermitValid m.ctx.crypto ds m.ctx.block.timestamp owner spender value deadline v r s
      (m.world.sload m.frame.msg.currentTarget (nonceSlot m.ctx.crypto owner)) →
    ∃ out, o = .revert out) ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 100000

/-- Masking to `uint8` keeps a value below 256. -/
theorem and_255_of_lt {x : Word} (h : x.toNat < 256) : x &&& 255#256 = x := by
  apply BitVec.eq_of_toNat_eq
  have h255 : (255#256).toNat = 2 ^ 8 - 1 := by simp
  rw [BitVec.toNat_and, h255, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by simpa using h)]

/-- Masking to `uint8` changes a value of at least 256. -/
theorem and_255_ne {x : Word} (h : 256 ≤ x.toNat) : x &&& 255#256 ≠ x := by
  intro he
  have := congrArg BitVec.toNat he
  have h255 : (255#256).toNat = 2 ^ 8 - 1 := by simp
  rw [BitVec.toNat_and, h255, Nat.and_two_pow_sub_one_eq_mod] at this
  have := Nat.mod_lt x.toNat (show 2 ^ 8 > 0 by decide)
  omega

set_option maxHeartbeats 0 in
/-- **`permit` of the asset, in any frame** (see the module docstring). -/
theorem asset_permit_halts {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    {owner spender : Address} {value deadline v r s : Word}
    (hd : PermitCall m.frame.msg.data owner spender value deadline v r s)
    (hsz : m.frame.msg.data.size < 2 ^ 64)
    (hcase : DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256))
    (hg : 100000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit) :
    Halts m (PermitPost (dsOf ia.initialChainId ia.initialDomainSeparator m) owner spender value
      deadline v r s m) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize, harg0, harg1, harg2, harg3, harg4, harg5, harg6⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 224))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := assetJumpDestsAgree ia
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
  pwp_run_to 1060 [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg0, harg1, harg2, harg3,
    harg4, harg5, harg6, hv', hge, ofAddress_and_addressMask, addressMask_and_ofAddress,
    Solidity.eq_self, iszero_zero]
  refine WP.bind_mono (asset_ds_wp _ rfl hj rfl rfl (by simp) (by pjumpdest_disch)
    (Memory.loadWord_storeWord _ _ _) (by simp [Memory.size_storeWord, Memory.size_expand,
      Memory.wordsAfter, Memory.words]) hcase (by dsimp only; omega) (by dsimp only; omega))
    (fun _ _ _ h => h.elim) ?_
  rintro _ - ⟨mem, g, sub, rfl, hmem, hgb, hgu, hlog⟩
  dsimp only [Machine.resumeWith] at hgb hgu hlog ⊢
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, dsOf]
  generalize domainSeparator m_ctx.crypto _ _ _ _ _ = ds
  rcases hmem with ⟨h64, hs⟩ | ⟨h64, hs⟩
  · refine WP.mono (asset_permit_body _ (F := 128) (S := 96) (.inl ⟨rfl, rfl⟩) rfl hj rfl rfl rfl
      h64 hs hv' (by dsimp only; omega) (by dsimp only; omega) rfl hdel1 hdepth hstatic)
      (fun _ _ h => h) ?_
    intro mf o _ ⟨h1, h2, h3⟩
    refine ⟨fun h => ?_, fun h => h2 fun h' => h ⟨hv, hdl, h'⟩, ?_⟩
    · obtain ⟨ho, hw, ht, hc, hl⟩ := h1 h.2.2
      exact ⟨ho, hw, ht, hc, hl.trans (by rw [hlog])⟩
    dsimp only at h3 ⊢
    omega
  · refine WP.mono (asset_permit_body _ (F := 320) (S := 320) (.inr ⟨rfl, rfl⟩) rfl hj rfl rfl rfl
      h64 hs hv' (by dsimp only; omega) (by dsimp only; omega) rfl hdel1 hdepth hstatic)
      (fun _ _ h => h) ?_
    intro mf o _ ⟨h1, h2, h3⟩
    refine ⟨fun h => ?_, fun h => h2 fun h' => h ⟨hv, hdl, h'⟩, ?_⟩
    · obtain ⟨ho, hw, ht, hc, hl⟩ := h1 h.2.2
      exact ⟨ho, hw, ht, hc, hl.trans (by rw [hlog])⟩
    dsimp only at h3 ⊢
    omega

end EvmLeanSpecs.Refinement.Permit
