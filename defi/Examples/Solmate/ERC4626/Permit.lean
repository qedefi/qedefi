import Examples.Solmate.ERC20.Permit
import Examples.Solmate.ERC4626.SharesBase

/-!
# The vault's `permit`, `DOMAIN_SEPARATOR()` and `nonces(owner)`

The share token of the vault has the same Solmate `ERC20` code as the asset at other offsets, so
these are the asset's theorems (`Examples.Solmate.ERC20.Permit`) with the same proof scripts.
-/

section

namespace Examples.Solmate.ERC4626.Permit
open Examples.Solmate.ERC20 Defi.ERC4626 Examples.Solmate.ERC20.Permit

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

theorem readBytes_vault_chainId (i : SolmateVault.Immutables) :
    readBytes (SolmateVault.runtimeCodeWith i) 1831 32 = Bytes.ofWord i.initialChainId := by
  have hp : i.patches = [] ++ (1831, i.initialChainId) :: [(1879, i.initialDomainSeparator),
      (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset),
      (2014, Word.ofAddress i.asset), (2169, Word.ofAddress i.asset),
      (2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
  simp only [SolmateVault.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateVault.size_runtimeCode]; decide)
    (by simp)

theorem readBytes_vault_ds (i : SolmateVault.Immutables) :
    readBytes (SolmateVault.runtimeCodeWith i) 1879 32 = Bytes.ofWord i.initialDomainSeparator := by
  have hp : i.patches = [(1831, i.initialChainId)] ++ (1879, i.initialDomainSeparator) ::
      [(688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset),
      (2014, Word.ofAddress i.asset), (2169, Word.ofAddress i.asset),
      (2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
  simp only [SolmateVault.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateVault.size_runtimeCode]; decide)
    (by simp)

set_option maxHeartbeats 0 in
/-- **`DOMAIN_SEPARATOR()` of the vault, internal (entry `0x0724`)**: returns to `r` with
`dsOf …` on the stack, at most 6000 gas, under `DomainCase`. -/
theorem vault_ds_wp {i : SolmateVault.Immutables} (m : Machine) {r : Word} {rest : List Word}
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 1828) (hs : m.frame.stack = r :: rest) (hlen : rest.length ≤ 1000)
    (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hfmp : m.frame.memory.loadWord 64 = 128#256) (hsize : m.frame.memory.size = 96)
    (hcase : DomainCase i.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256))
    (hg : 10000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ mem g sub, m' = m.resumeWith r.toNat
        (dsOf i.initialChainId i.initialDomainSeparator m :: rest) mem g m.frame.returnData sub ∧
        DsMem mem ∧ m.frame.gasLeft ≤ g + 6000 ∧ g ≤ m.frame.gasLeft ∧
        sub.logs = m.frame.sub.logs)
      (fun _ _ => False) := by
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs
  simp only [dsOf, domainSeparator]
  by_cases hceq : ofNat m_ctx.block.chainId = i.initialChainId
  · -- the deployment chain: the immutable
    have he : Word.eq (ofNat m_ctx.block.chainId) i.initialChainId = 1#256 := by
      rw [hceq]; exact Solidity.eq_self _
    simp only [hceq, ↓reduceIte]
    pwp_steps [he, readBytes_vault_chainId, readBytes_vault_ds]
    apply WP.ret
    exact ⟨_, _, _, rfl, .inl ⟨hfmp, hsize⟩, by omega, by omega, rfl⟩
  · -- another chain: `computeDomainSeparator()`
    have hne : Word.eq (ofNat m_ctx.block.chainId) i.initialChainId = 0#256 := eq_of_ne hceq
    have hshort := hcase.resolve_left hceq
    simp only [hceq, ↓reduceIte, computedDomainSeparator, shortStringBytes]
    generalize hns : m_world.sload m_msg.currentTarget 0#256 = ns at hshort ⊢
    obtain ⟨h1, hl⟩ := hshort
    have hl1 : (shortLength ns).lt 32#256 = 1#256 := (Word.lt_eq_one_iff _ _).2 hl
    simp only [shortLength] at hl1 hl ⊢
    have hle : (Word.shr 1#256 ns &&& 127#256).toNat ≤ 32 := by omega
    pwp_steps [hne, readBytes_vault_chainId, readBytes_vault_ds, hfmp, hsize, permit_norm, hns, h1,
      hl1, Word.mul_iszero_iszero, Word.add_sub_cancel_left']
    generalize hL : (Word.shr (1#256) ns &&& 127#256) = L at hle ⊢
    wp_generalize_mem M hM
    have hMs : M.size = 160 := by subst hM; simp only [permit_norm, hsize]
    have hMr : M.read 128 L.toNat = (Bytes.ofWord (ns &&& ~~~255#256)).extract 0 L.toNat := by
      subst hM; simp only [Memory.read_expand, Memory.read_storeWord_prefix _ _ _ _ hle, not_255]
    have hM64 : M.loadWord 64 = 128#256 := by
      subst hM
      simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
        hfmp]
    clear hM
    refine WP.of_step (step_keccak256 (by pcode_fact) rfl (by simp; omega) ?hg) (by same_frame) ?hw
    case hg =>
      dsimp only
      rw [hMs, BitVec.toNat_ofNat, show 128 % 2 ^ 256 = 128 by decide,
        Gas.extendMemory_one_of_le (by omega) (by decide)]
      simp only [Gas.keccak256Cost, Gas.keccak256Base, Gas.keccak256PerWord, Gas.words]
      evm_gas
    dsimp only
    rw [BitVec.toNat_ofNat, show 128 % 2 ^ 256 = 128 by decide,
      Memory.expand_eq_self_of_le (by omega) (by rw [hMs]), readBytes_bytes, hMr, hMs,
      Gas.extendMemory_one_of_le (by omega) (by decide)]
    wp_generalize_gas g1 hg1
    have hg1' : m_gasLeft ≤ g1 + 3000 := by subst hg1; evm_gas
    have hg1'' : 5000 ≤ g1 := by subst hg1; evm_gas
    have hg1u : g1 ≤ m_gasLeft := by subst hg1; omega
    clear hg1
    pwp_steps [hM64, hMs, permit_norm, Memory.read_160]
    apply WP.ret
    refine ⟨_, _, _, rfl, .inr ⟨?_, ?_⟩, by omega, by omega, rfl⟩
    · simp only [Memory.loadWord_expand, Memory.loadWord_storeWord]
    · simp only [permit_norm, hMs]

set_option maxHeartbeats 0 in
/-- **`DOMAIN_SEPARATOR()` of the vault**, in any fresh frame: returns
`Permit.domainSeparator …` (the immutable on the deployment chain, else recomputed from the
short name in slot 0) as one word; the world is unchanged. -/
theorem vault_domainSeparator_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m)
    (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x3644e515)
    (hsize : 4 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hcase : DomainCase i.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256))
    (hg : 20000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    Halts m (fun mf o =>
      o = .success (Bytes.ofWord (dsOf i.initialChainId i.initialDomainSeparator m)) ∧
      mf.world = m.world ∧ m.frame.gasLeft ≤ mf.frame.gasLeft + 10000) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_run_to 1828 [hval, hsel', hlt, Abi.shr_calldataload_zero]
  refine WP.bind_mono (vault_ds_wp _ rfl hj rfl rfl (by simp) (by pjumpdest_disch)
    (Memory.loadWord_storeWord _ _ _) (by simp [Memory.size_storeWord, Memory.size_expand,
      Memory.wordsAfter, Memory.words]) hcase (by dsimp only; omega) (by dsimp only; omega))
    (fun _ _ _ h => h.elim) ?_
  rintro _ - ⟨mem, g, sub, rfl, hmem, hgb, -, -⟩
  dsimp only [Machine.resumeWith] at hgb ⊢
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  simp only [dsOf]
  rcases hmem with ⟨h64, hs⟩ | ⟨h64, hs⟩
  · pwp_steps [h64, hs, permit_norm]
    refine ⟨trivial, by dsimp only [outputMachine], ?_⟩
    dsimp only [outputMachine]; evm_gas
  · pwp_steps [h64, hs, permit_norm]
    refine ⟨trivial, by dsimp only [outputMachine], ?_⟩
    dsimp only [outputMachine]; evm_gas

set_option maxHeartbeats 0 in
/-- **`nonces(owner)` of the vault**, in any fresh frame: returns the word in `nonces[owner]`
(slot `keccak(owner ‖ 5)`); the world is unchanged. -/
theorem vault_nonces_halts {i : SolmateVault.Immutables} (m : Machine)
    (hf : Fresh (SolmateVault.runtimeCodeWith i) m) (owner : Address)
    (hval : m.frame.msg.value = 0)
    (hsel : Abi.selectorOf m.frame.msg.data = 0x7ecebe00)
    (hsize : 36 ≤ m.frame.msg.data.size) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (harg : Bytes.toWord (readBytes m.frame.msg.data 4 32) = Word.ofAddress owner)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (fun mf o =>
      o = .success (Bytes.ofWord (m.world.sload m.frame.msg.currentTarget
        (nonceSlot m.ctx.crypto owner))) ∧
      mf.world = m.world ∧ m.frame.gasLeft ≤ mf.frame.gasLeft + 3000) := by
  apply WP.halts_of_false
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hok : Word.iszero (Word.slt (ofNat m.frame.msg.data.size - 4#256) (BitVec.ofNat 256 32))
      = 1 := iszero_slt_calldatasize hsize (by omega)
  have hagree := Shares.jumpDestsAgree i
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, hok, harg,
    ofAddress_and_addressMask, Solidity.eq_self, Memory.read_64]
  refine ⟨rfl, by dsimp only [outputMachine], ?_⟩
  dsimp only [outputMachine]
  evm_gas


end Examples.Solmate.ERC4626.Permit

end

section

/-! ## The vault's `permit`: from the `ECRECOVER` call (`0x0d6e`) to the end -/

namespace Examples.Solmate.ERC4626.Permit
open Examples.Solmate.ERC20 Defi.ERC4626 Examples.Solmate.ERC20.Permit

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

set_option maxHeartbeats 0 in
/-- The end of the vault's `permit`, from the `ECRECOVER` call (pc `0x0d6e`). -/
theorem vault_permit_tail {i : SolmateVault.Immutables} (m : Machine) {M : Memory} {F : Nat}
    {dg v r s deadline value : Word} {owner spender : Address}
    (hF : F = 128 ∨ F = 320)
    (hc : m.frame.code = SolmateVault.runtimeCodeWith i)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i))
    (hpc : m.frame.pc = 3438)
    (hs : m.frame.stack = [ofNat m.frame.gasLeft, 1#256, BitVec.ofNat 256 (F + 354), 128#256,
      BitVec.ofNat 256 (F + 322), 32#256, BitVec.ofNat 256 (F + 482), 1#256, 0#256,
      s, r, v, deadline, value, Word.ofAddress spender, Word.ofAddress owner, 1035#256,
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
  have hagree := Shares.jumpDestsAgree i
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

end Examples.Solmate.ERC4626.Permit

end

section

/-! ## The vault's `permit`: the body after `DOMAIN_SEPARATOR()` (pc `0x0c75`) -/

namespace Examples.Solmate.ERC4626.Permit
open Examples.Solmate.ERC20 Defi.ERC4626 Examples.Solmate.ERC20.Permit

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

set_option maxHeartbeats 0 in
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
    refine ⟨fun hr => ?_, fun hr => h2 hr, ?_⟩
    · obtain ⟨ho, hw, ht, hc, hl⟩ := h1 hr
      exact ⟨ho, hw, ht, hc, hl⟩
    dsimp only at h3 ⊢
    omega

end Examples.Solmate.ERC4626.Permit

end

section

/-! ## The vault's `permit`, in any frame -/

namespace Examples.Solmate.ERC4626.Permit
open Examples.Solmate.ERC20 Defi.ERC4626 Examples.Solmate.ERC20.Permit

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

set_option maxHeartbeats 0 in
/-- **`permit` of the vault, in any frame**: as `asset_permit_halts` (`PermitPost`). -/
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
  rintro _ - ⟨mem, g, sub, rfl, hmem, hgb, hgu, hlog⟩
  dsimp only [Machine.resumeWith] at hgb hgu hlog ⊢
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, dsOf]
  generalize domainSeparator m_ctx.crypto _ _ _ _ _ = ds
  rcases hmem with ⟨h64, hs⟩ | ⟨h64, hs⟩
  · refine WP.mono (vault_permit_body _ (F := 128) (S := 96) (.inl ⟨rfl, rfl⟩) rfl hj rfl rfl rfl
      h64 hs hv' (by dsimp only; omega) (by dsimp only; omega) rfl hdel1 hdepth hstatic)
      (fun _ _ h => h) ?_
    intro mf o _ ⟨h1, h2, h3⟩
    refine ⟨fun h => ?_, fun h => h2 fun h' => h ⟨hv, hdl, h'⟩, ?_⟩
    · obtain ⟨ho, hw, ht, hc, hl⟩ := h1 h.2.2
      exact ⟨ho, hw, ht, hc, hl.trans (by rw [hlog])⟩
    dsimp only at h3 ⊢
    omega
  · refine WP.mono (vault_permit_body _ (F := 320) (S := 320) (.inr ⟨rfl, rfl⟩) rfl hj rfl rfl rfl
      h64 hs hv' (by dsimp only; omega) (by dsimp only; omega) rfl hdel1 hdepth hstatic)
      (fun _ _ h => h) ?_
    intro mf o _ ⟨h1, h2, h3⟩
    refine ⟨fun h => ?_, fun h => h2 fun h' => h ⟨hv, hdl, h'⟩, ?_⟩
    · obtain ⟨ho, hw, ht, hc, hl⟩ := h1 h.2.2
      exact ⟨ho, hw, ht, hc, hl.trans (by rw [hlog])⟩
    dsimp only at h3 ⊢
    omega

end Examples.Solmate.ERC4626.Permit

end
