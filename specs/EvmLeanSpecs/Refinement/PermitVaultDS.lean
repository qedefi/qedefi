import EvmLeanSpecs.Refinement.PermitAssetDS
import EvmLeanSpecs.Refinement.SharesCode

/-!
# The vault's `DOMAIN_SEPARATOR()` and `nonces(owner)`

The share token of the compiled vault (`SolmateVault.runtimeCodeWith i`, any immutables) has
the same Solmate `ERC20` code as the asset at other offsets (internal `DOMAIN_SEPARATOR()` at
`0x0724`, `computeDomainSeparator()` at `0x0ea0`): `vault_ds_wp`,
`vault_domainSeparator_halts`, `vault_nonces_halts` are `asset_ds_wp`, … for the vault (same
proof scripts, see `PermitAssetDS`).
-/

namespace EvmLeanSpecs.Refinement.Permit

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-- The `INITIAL_CHAIN_ID` immutable of the vault, as the `PUSH32` at `0x0726` reads it. -/
theorem readBytes_vault_chainId (i : SolmateVault.Immutables) :
    readBytes (SolmateVault.runtimeCodeWith i) 1831 32 = Bytes.ofWord i.initialChainId := by
  have hp : i.patches = [] ++ (1831, i.initialChainId) :: [(1879, i.initialDomainSeparator),
      (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset),
      (2014, Word.ofAddress i.asset), (2169, Word.ofAddress i.asset),
      (2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
  simp only [SolmateVault.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateVault.size_runtimeCode]; decide)
    (by simp)

/-- The `INITIAL_DOMAIN_SEPARATOR` immutable of the vault, as the `PUSH32` at `0x0756` reads
it. -/
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
/-- **`DOMAIN_SEPARATOR()` of the vault, internal (entry `0x0724`, stack `r :: rest`)**: returns
to `r` with `Permit.domainSeparator …` on the stack. Entered with solc's initial memory
(`FmpInit`); the world, transient storage and return data are unchanged; memory as in
`DsMem`; no logs; at most 6000 gas. Covers the deployment chain (any name) and other chains for a
short name (`DomainCase`). -/
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


end EvmLeanSpecs.Refinement.Permit
