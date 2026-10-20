import EvmLeanSpecs.Refinement.PermitAssetDS
import EvmLeanProofs.Program.PrecompileCallEcrecover
import EvmLeanSpecs.Refinement.EventsTactic

/-!
# The asset's `permit`: from the `ECRECOVER` call to the end

`asset_permit_tail`: the last part of the compiled `permit` of the asset (pc `0x065f`, the
`STATICCALL` to `ecrecover`, to the end of the frame). The machine there is described by its
stack (the call's arguments, the decoded `permit` arguments below them) and by what its memory
holds: the four input words `digest ‖ v ‖ r ‖ s`, a zero in the output word, the free pointer.
The free pointer `F` at the start of the `permit` body is `0x80` or, after
`computeDomainSeparator()`, `0x140` (`Permit.DsMem`); every offset is `F` plus a constant.

* `ECRECOVER` runs through `WP.staticcall_ecrecover` (any `Crypto`);
* if it recovers `owner ≠ 0`, the code writes `allowance[owner][spender] = value`, emits
  `Approval` and stops (success, empty output);
* otherwise (`none`, another address, or the zero address) it reverts with
  `INVALID_SIGNER`.
-/

namespace EvmLeanSpecs.Refinement.Permit

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-- The signature part of `SigOk`, for a given digest. -/
def RecoversTo (crypto : Crypto) (dg v r s : Word) (owner : Address) : Prop :=
  owner ≠ 0 ∧ ecrecoverAddress? crypto dg v r s = some owner

/-- What the end of `permit` does, from a machine `m` at the `ECRECOVER` call: on a signature
recovering `owner ≠ 0`, success with the allowance written (in `m.world`), transient storage and
created accounts unchanged, `Approval(owner, spender, value)` appended to the logs; otherwise a revert; at most `40000` gas in both cases. -/
def TailPost (owner spender : Address) (value dg v r s : Word) (m mf : Machine) (o : Outcome) :
    Prop :=
  (RecoversTo m.ctx.crypto dg v r s owner →
    o = .success .empty ∧
    mf.world = m.world.sstore m.frame.msg.currentTarget
      (Erc20.allowanceSlot m.ctx.crypto Erc20.Layout.solmate owner spender) value ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (approvalLog m.frame.msg.currentTarget owner spender value)) ∧
  (¬ RecoversTo m.ctx.crypto dg v r s owner → ∃ out, o = .revert out) ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 40000

/-- `iszero` of a nonzero address word. -/
theorem iszero_ofAddress {a : Address} (h : a ≠ 0) : Word.iszero (Word.ofAddress a) = 0#256 := by
  apply iszero_of_ne
  intro he; apply h
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat he
  simp only [Word.ofAddress, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  have hlt := a.isLt
  rw [Nat.mod_eq_of_lt (by omega)] at this
  exact this

/-- `EQ` of two different address words. -/
theorem eq_ofAddress_ne {a b : Address} (h : a ≠ b) :
    Word.eq (Word.ofAddress a) (Word.ofAddress b) = 0#256 :=
  eq_of_ne fun he => h (Word.ofAddress_injective he)

set_option maxHeartbeats 0 in
/-- **The end of the asset's `permit`**, from the `ECRECOVER` call (pc `0x065f`), for the free
pointer `F ∈ {0x80, 0x140}` at the start of the body. -/
theorem asset_permit_tail {ia : SolmateAsset.Immutables} (m : Machine) {M : Memory} {F : Nat}
    {dg v r s deadline value : Word} {owner spender : Address}
    (hF : F = 128 ∨ F = 320)
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1631)
    (hs : m.frame.stack = [ofNat m.frame.gasLeft, 1#256, BitVec.ofNat 256 (F + 354), 128#256,
      BitVec.ofNat 256 (F + 322), 32#256, BitVec.ofNat 256 (F + 482), 1#256, 0#256,
      s, r, v, deadline, value, Word.ofAddress spender, Word.ofAddress owner, 424#256,
      3573918927#256])
    (hmem : m.frame.memory = M) (hM64 : M.loadWord 64 = BitVec.ofNat 256 (F + 354))
    (hMout : M.loadWord (F + 322) = 0#256)
    (hMin : M.read (F + 354) 128 =
      Bytes.ofWord dg ++ (Bytes.ofWord v ++ (Bytes.ofWord r ++ Bytes.ofWord s)))
    (hMs : M.size = F + 512)
    (hg : 40000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64)
    (hstd : m.precompiles = PrecompileImpl.standard m.ctx)
    (hdel1 : m.ctx.fork < .prague ∨ delegatedAddress? (m.world.code 1) = none)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hstatic : m.frame.msg.isStatic = false) :
    WP m (fun _ => False) (TailPost owner spender value dg v r s m) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs hmem hstd
  have hmod : m_gasLeft % 2 ^ 256 = m_gasLeft := Nat.mod_eq_of_lt (by omega)
  have hacc := accessCost_le (m_sub.accessedAddresses.contains 1)
  rcases hF with rfl | rfl <;>
  · simp only [Nat.reduceAdd] at hM64 hMout hMin hMs ⊢
    refine WP.staticcall_ecrecover (hash := dg) (v := v) (r := r) (s := s) (by pcode_fact) rfl rfl
      hdel1 ?_ hdepth hMin ?_ ?_
    · simp only [callCost, callGas, callExt, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod]
      rw [messageCallGas_zero (by evm_gas)]
      simp only [Gas.maxMessageCallGas]
      evm_gas
    · simp only [callGas, callExt, ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      rw [messageCallGas_zero (by evm_gas)]
      simp only [Gas.maxMessageCallGas]
      evm_gas
    simp only [returnMemory_ecrecoverOutput, callMemory, callCost, callGas, callExt, ofNat,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, callerFrame]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    wp_generalize_gas g1 hg1
    have hg1' : m_gasLeft ≤ g1 + 6000 := by
      subst hg1
      generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses 1) = acc at hacc ⊢
      evm_gas
    have hg1'' : 30000 ≤ g1 := by
      subst hg1
      generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses 1) = acc at hacc ⊢
      evm_gas
    clear hg1
    generalize ecrecoverOutput m_ctx.crypto dg v r s = rd
    cases hrec : ecrecoverAddress? m_ctx.crypto dg v r s with
    | none =>
      -- invalid signature: the pre-stored zero is read back
      pwp_steps [hM64, hMout, ofAddress_and_addressMask, addressMask_and_ofAddress,
        Solidity.eq_self, iszero_zero, iszero_one, permit_norm, hMs, Memory.read_64, hstatic]
      unfold TailPost RecoversTo
      refine ⟨fun h => absurd h.2 (by rw [hrec]; simp), fun _ => ⟨_, rfl⟩, ?_⟩
      dsimp only [outputMachine]; evm_gas
    | some a =>
      by_cases ha0 : a = 0
      · subst ha0
        pwp_steps [hM64, hMout, ofAddress_and_addressMask, addressMask_and_ofAddress,
          Solidity.eq_self, iszero_zero, iszero_one, permit_norm, hMs, Memory.read_64, hstatic]
        unfold TailPost RecoversTo
        refine ⟨fun h => (h.1 (Option.some.inj (h.2.symm.trans hrec))).elim, fun _ => ⟨_, rfl⟩,
          ?_⟩
        dsimp only [outputMachine]; evm_gas
      · have hz := iszero_ofAddress ha0
        by_cases hao : a = owner
        · subst hao
          pwp_steps [hM64, hz, ofAddress_and_addressMask, addressMask_and_ofAddress,
            Solidity.eq_self, iszero_zero, iszero_one, permit_norm, hMs, Memory.read_64, hstatic]
          apply WP.halt_of_step (step_stop (by pcode_fact)) (SameFrame.refl _)
          unfold TailPost RecoversTo
          refine ⟨fun _ => ⟨rfl, ?_, rfl, rfl, ?_⟩, fun h => absurd ⟨ha0, hrec⟩ h, ?_⟩
          · rfl
          · dsimp only
            logs_simp []
            event_log [value]
          · evm_gas
        · have hne := eq_ofAddress_ne hao
          pwp_steps [hM64, hz, hne, ofAddress_and_addressMask, addressMask_and_ofAddress,
            Solidity.eq_self, iszero_zero, iszero_one, permit_norm, hMs, Memory.read_64, hstatic]
          unfold TailPost RecoversTo
          refine ⟨fun h => (hao (Option.some.inj (hrec.symm.trans h.2))).elim, fun _ => ⟨_, rfl⟩,
            ?_⟩
          dsimp only [outputMachine]; evm_gas

end EvmLeanSpecs.Refinement.Permit
