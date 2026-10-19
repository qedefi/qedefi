import EvmLeanSpecs.Refinement.AssetBalanceOf
import EvmLeanSpecs.Refinement.PermitDefs
import EvmLeanProofs.Program.ExtraTactic
import EvmLeanProofs.Program.ExtraLogic
import EvmLeanProofs.Solidity.ExtraTactic
import EvmLeanProofs.Solidity.PermitExtraMemory
import EvmLeanProofs.Solidity.PermitExtraTactic
import EvmLeanProofs.Solidity.PermitExtraWord

/-!
# The asset's `DOMAIN_SEPARATOR()`, internal and external

Solmate's `DOMAIN_SEPARATOR()` in the compiled asset (`MockERC20`, any immutables `ia`) is an
internal function at pc `0x0424` (called by `permit` and by the external
`DOMAIN_SEPARATOR()`): if `block.chainid` is the `INITIAL_CHAIN_ID` immutable it pushes the
`INITIAL_DOMAIN_SEPARATOR` immutable; otherwise it calls `computeDomainSeparator()` (`0x0749`),
which encodes the `name` from storage slot 0 (`abi_encode_t_string_storage`, `0x0a66`) at the
free-memory pointer, hashes it, and hashes the `abi.encode` of the EIP-712 domain.

* `asset_ds_wp`: the internal function, both branches (the second for a name in short-string
  form, `Permit.ShortString`): it returns `Permit.domainSeparator …` to its return address;
  the memory either is unchanged or has the free pointer at `0x140` and ten words
  (`DsMem`); at most 6000 gas.
* `asset_domainSeparator_halts`: the external `DOMAIN_SEPARATOR()` in any fresh frame.
-/

namespace EvmLeanSpecs.Refinement.Permit

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-- The `INITIAL_CHAIN_ID` immutable, as the `PUSH32` at `0x0426` reads it. -/
theorem readBytes_asset_chainId (ia : SolmateAsset.Immutables) :
    readBytes (SolmateAsset.runtimeCodeWith ia) 1063 32 = Bytes.ofWord ia.initialChainId := by
  have hp : ia.patches = [] ++ (1063, ia.initialChainId) ::
      [(1116, ia.initialDomainSeparator), (345, ia.decimals)] := rfl
  simp only [SolmateAsset.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateAsset.size_runtimeCode]; decide)
    (by simp)

/-- The `INITIAL_DOMAIN_SEPARATOR` immutable, as the `PUSH32` at `0x045b` reads it. -/
theorem readBytes_asset_ds (ia : SolmateAsset.Immutables) :
    readBytes (SolmateAsset.runtimeCodeWith ia) 1116 32 = Bytes.ofWord ia.initialDomainSeparator := by
  have hp : ia.patches = [(1063, ia.initialChainId)] ++ (1116, ia.initialDomainSeparator) ::
      [(345, ia.decimals)] := rfl
  simp only [SolmateAsset.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateAsset.size_runtimeCode]; decide)
    (by simp)

/-- The memory after `DOMAIN_SEPARATOR()` (entered with solc's initial memory): unchanged (free
pointer `0x80`, three words), or, after `computeDomainSeparator()`, free pointer `0x140` and ten
words. -/
def DsMem (mem : Memory) : Prop :=
  (mem.loadWord 64 = 128#256 ∧ mem.size = 96) ∨ (mem.loadWord 64 = 320#256 ∧ mem.size = 320)

/-- The cleared-low-byte mask `~0xff` as a literal (how symbolic execution shows it). -/
theorem not_255 : (~~~255#256 : Word) =
    115792089237316195423570985008687907853269984665640564039457584007913129639680#256 := by
  decide

/-- The domain separator the code of a frame computes. -/
def dsOf (initialChainId initialDomainSeparator : Word) (m : Machine) : Word :=
  domainSeparator m.ctx.crypto initialChainId initialDomainSeparator (ofNat m.ctx.block.chainId)
    (m.world.sload m.frame.msg.currentTarget 0#256) m.frame.msg.currentTarget

set_option maxHeartbeats 0 in
/-- **`DOMAIN_SEPARATOR()` of the asset, internal (entry `0x0424`, stack `r :: rest`)**: returns
to `r` with `Permit.domainSeparator …` on the stack. Entered with solc's initial memory
(`FmpInit`); the world, transient storage and return data are unchanged; memory as in
`DsMem`; at most 6000 gas. Covers the deployment chain (any name) and other chains for a
short name (`DomainCase`). -/
theorem asset_ds_wp {ia : SolmateAsset.Immutables} (m : Machine) {r : Word} {rest : List Word}
    (hc : m.frame.code = SolmateAsset.runtimeCodeWith ia)
    (hj : JumpTable m.frame.jumpDests (SolmateAsset.runtimeCodeWith ia))
    (hpc : m.frame.pc = 1060) (hs : m.frame.stack = r :: rest) (hlen : rest.length ≤ 1000)
    (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hfmp : m.frame.memory.loadWord 64 = 128#256) (hsize : m.frame.memory.size = 96)
    (hcase : DomainCase ia.initialChainId (ofNat m.ctx.block.chainId)
      (m.world.sload m.frame.msg.currentTarget 0#256))
    (hg : 10000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ mem g sub, m' = m.resumeWith r.toNat
        (dsOf ia.initialChainId ia.initialDomainSeparator m :: rest) mem g m.frame.returnData sub ∧
        DsMem mem ∧ m.frame.gasLeft ≤ g + 6000)
      (fun _ _ => False) := by
  have hagree := assetJumpDestsAgree ia
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs
  simp only [dsOf, domainSeparator]
  by_cases hceq : ofNat m_ctx.block.chainId = ia.initialChainId
  · -- the deployment chain: the immutable
    have he : Word.eq (ofNat m_ctx.block.chainId) ia.initialChainId = 1#256 := by
      rw [hceq]; exact Solidity.eq_self _
    simp only [hceq, ↓reduceIte]
    pwp_steps [he, readBytes_asset_chainId, readBytes_asset_ds]
    apply WP.ret
    exact ⟨_, _, _, rfl, .inl ⟨hfmp, hsize⟩, by omega⟩
  · -- another chain: `computeDomainSeparator()`
    have hne : Word.eq (ofNat m_ctx.block.chainId) ia.initialChainId = 0#256 := eq_of_ne hceq
    have hshort := hcase.resolve_left hceq
    simp only [hceq, ↓reduceIte, computedDomainSeparator, shortStringBytes]
    generalize hns : m_world.sload m_msg.currentTarget 0#256 = ns at hshort ⊢
    obtain ⟨h1, hl⟩ := hshort
    have hl1 : (shortLength ns).lt 32#256 = 1#256 := (Word.lt_eq_one_iff _ _).2 hl
    simp only [shortLength] at hl1 hl ⊢
    have hle : (Word.shr 1#256 ns &&& 127#256).toNat ≤ 32 := by omega
    pwp_steps [hne, readBytes_asset_chainId, readBytes_asset_ds, hfmp, hsize, permit_norm, hns, h1,
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
    clear hg1
    pwp_steps [hM64, hMs, permit_norm, Memory.read_160]
    apply WP.ret
    refine ⟨_, _, _, rfl, .inr ⟨?_, ?_⟩, by omega⟩
    · simp (disch := decide) only [Memory.loadWord_expand, Memory.loadWord_storeWord_of_disjoint,
        Memory.loadWord_storeWord]
    · simp only [permit_norm, hMs]

end EvmLeanSpecs.Refinement.Permit
