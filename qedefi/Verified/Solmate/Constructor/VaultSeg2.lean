import Verified.Solmate.Constructor.VaultDefs
import Verified.Solmate.Constructor.VaultCode
import Verified.Solmate.ERC4626.ViewsSpec
import Verified.Solmate.ERC4626.Convert
import EvmLogic.Tactic.StepExt

/-!
# The `MockERC4626` constructor, second segment

From `0x0068` to the `RETURN`: the `STATICCALL` of `asset.decimals()` (callee summary
`assetDecimals_halts_gas`, the asset holding the Solmate asset's code), the decoding of its
result, the storage of the name and symbol, `computeDomainSeparator()`, the `CODECOPY` of the
runtime code and the stores of its immutables (`Vault.output_eq`).
-/

namespace Verified.Solmate.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Tactic
open Verified.Solmate.Contracts Verified.Solmate.ERC4626 Verified.Solmate.ERC20

set_option maxHeartbeats 0 in
/-- `decimals()` of the asset (`assetDecimals_halts`), with the gas it uses: under 3000. -/
theorem assetDecimals_halts_gas {ia : SolmateAsset.Immutables} (m : Machine)
    (hf : Fresh (SolmateAsset.runtimeCodeWith ia) m) (hval : m.frame.msg.value = 0)
    (hd : NoArgCall m.frame.msg.data 0x313ce567) (hsize' : m.frame.msg.data.size < 2 ^ 64)
    (hg : 3000 ≤ m.frame.gasLeft) :
    Halts m (fun mf o => SharesViewPost (ia.decimals &&& 255#256) m mf o ∧
      m.frame.gasLeft ≤ mf.frame.gasLeft + 3000) := by
  apply WP.halts_of_false
  obtain ⟨hsel, hsize⟩ := hd
  have hlt := lt_size_four (n := m.frame.msg.data.size) (by omega) (by omega)
  have hsel' := Dispatch.selector_eq hsel
  have hagree := assetJumpDestsAgree ia
  fresh_intro
  pwp_steps [hval, hsel', hlt, Abi.shr_calldataload_zero, Solidity.eq_self, Memory.read_64,
    readBytes_assetCode_decimals]
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  dsimp only [outputMachine]
  evm_gas

set_option maxHeartbeats 0 in
/-- **The second segment**: from `0x0068`, over an asset holding the Solmate asset's code, the
constructor returns the runtime code with `Vault.immutables` (decimals: the asset's, as a
`uint8`) and writes the name and symbol slots. -/
theorem vault_seg2 (asset : Address) (ia : SolmateAsset.Immutables) (m : Machine)
    (hc : m.frame.code = SolmateVault.initCodeFor asset)
    (hj : JumpTable m.frame.jumpDests (SolmateVault.initCodeFor asset)) (hpc : m.frame.pc = 104)
    (hs : m.frame.stack = [Word.ofAddress asset, 608#256, 4#256, 608#256, 32#256, 612#256,
      826074471#256, Word.ofAddress asset, 544#256, 480#256, 544#256, 480#256,
      Word.ofAddress asset, 544#256, 480#256, Word.ofAddress asset])
    (hA : Vault.MemA m.frame.memory) (hstatic : m.frame.msg.isStatic = false)
    (hcode : m.world.code asset = SolmateAsset.runtimeCodeWith ia)
    (hpre : m.precompiles.isPrecompile asset = false)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hs0 : m.world.sload m.frame.msg.currentTarget 0#256 = 0#256)
    (hs1 : m.world.sload m.frame.msg.currentTarget 1#256 = 0#256)
    (hg : 1900000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun _ => False) (fun mf o =>
      o = .success (SolmateVault.runtimeCodeWith (Vault.immutables m.ctx.crypto
        m.ctx.block.chainId m.frame.msg.currentTarget asset (ia.decimals &&& 255#256))) ∧
      mf.world = (m.world.sstore m.frame.msg.currentTarget 0#256 Vault.nameSlot).sstore
        m.frame.msg.currentTarget 1#256 Vault.symbolSlot ∧
      m.frame.gasLeft ≤ mf.frame.gasLeft + 150000) := by
  have hJ := SolmateVault.jumpTable_initCodeFor hj
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, M, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hc hpc hs
  obtain ⟨M_size, M_fp, h480, h512, h544, h576, h608, h608'⟩ := hA
  pwp_xsteps 1 [M_size]
  have hacc := accessCost_le (m_sub.accessedAddresses.contains asset)
  have hto : Word.toAddress (Word.ofAddress asset) = asset := Word.toAddress_ofAddress _
  have hdel := delegatedAddress?_assetCode ia
  refine WP.staticcall (by pcode_fact) rfl ?_ ?_ ?_ ?_
    (assetDecimals_halts_gas (ia := ia) _ ?_ rfl ?_ ?_ ?_) ?_
  · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
  · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    evm_gas
  · exact hdepth
  · rw [hto]; exact hpre
  · exact ⟨_, _, _, rfl, by dsimp only [childMsg]; rw [hto, hcode]⟩
  · dsimp only [Frame.init, childMsg, callMemory]
    simp only [BitVec.reduceToNat, readBytes_bytes, Memory.read_expand, h608']
    exact ⟨Vault.selectorOf_decimals, by simp [Bytes.size_ofWord]⟩
  · dsimp only [Frame.init, childMsg, callMemory]
    simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
    decide
  · dsimp only [Frame.init, childMsg]
    simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    evm_gas
  · intro mf o ⟨⟨ho, hw⟩, hgasB⟩ hsame
    have hk : mf.frame.kind = .call 608 32 := hsame.kind
    subst ho
    rw [resumeAfter_success hk]
    dsimp only at hw hgasB
    have hs1' : mf.ctx = m_ctx := hsame.ctx
    have hs2 : mf.precompiles = m_pre := hsame.precompiles
    have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
    simp only [hw, hs1', hs2, hs3]
    dsimp only [callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
    simp only [hto, returnMemory_ofWord, callCost, callGas, callExt, ofNat,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
    rw [messageCallGas_zero (by evm_gas)] at hgasB ⊢
    simp only [Gas.maxMessageCallGas] at hgasB ⊢
    wp_generalize_gas g1 hg1
    have hg1' : m_gasLeft ≤ g1 + 6000 := by
      subst hg1
      generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses asset) = acc
        at hacc hgasB ⊢
      evm_gas
    clear hg1 hgasB hdel hto hcode hpre
    have hs1' : ∀ v, (m_world.sstore m_msg.currentTarget 0#256 v).sload m_msg.currentTarget 1#256 =
        0#256 := fun v => by rw [World.sload_sstore_ne_key _ _ _ (by decide), hs1]
    have hs0' : ∀ v v', ((m_world.sstore m_msg.currentTarget 0#256 v).sstore m_msg.currentTarget
        1#256 v').sload m_msg.currentTarget 0#256 = v := fun v v' => by
      rw [World.sload_sstore_ne_key _ _ _ (by decide), World.sload_sstore_self]
    have hdec : ia.decimals &&& 255#256 &&& 255#256 = ia.decimals &&& 255#256 := by
      rw [BitVec.and_assoc, BitVec.and_self]
    pwp_xsteps 400 [M_size, M_fp, h480, h512, h544, h576, hs0, hs1', hs0', Bytes.size_ofWord,
      hdec, Solidity.eq_self,
      Memory.loadWord_storeWord_zero_tail', Memory.read_write_extract, Memory.read_storeWord_prefix,
      Memory.read_write_of_disjoint, Memory.loadWord_write_of_disjoint, ByteArray.size_extract,
      Memory.size_write, Bytes.size_zeros]
    wp_abstract_mem M1 with hM1
    have h128 : M1.loadWord 128 = ia.decimals &&& 255#256 := by subst hM1; mem_fact
    have h160 : M1.loadWord 160 = ofNat m_ctx.block.chainId := by subst hM1; mem_fact
    have h64 : M1.loadWord 64 = 640#256 := by subst hM1; mem_fact
    have h640 : M1.read 640 13 = (Bytes.ofWord SolmateVault.nameWord).extract 0 13 := by
      subst hM1; mem_fact; rfl
    clear hM1
    pwp_xrun_to 382 [h64, h128, h160, h640, Memory.read_160]
    wp_abstract_mem M2 with hM2
    have h128' : M2.loadWord 128 = ia.decimals &&& 255#256 := by subst hM2; mem_fact [h128]
    have h160' : M2.loadWord 160 = ofNat m_ctx.block.chainId := by subst hM2; mem_fact [h160]
    clear hM2
    pwp_xsteps 30 [h128', h160', ofAddress_and_addressMask]
    pwp_xsteps 1
    pwp_xsteps 1
    pwp_xsteps 1
    pwp_xsteps 1
    wp_abstract_mem M3 with hM3
    pwp_xsteps 100 [M3_size]
    wp_abstract_mem M4 with hM4
    simp only [EvmLean.Interpreter.size_readBytes] at M4_size
    pwp_xsteps 100 [M4_size]
    have hM : ∀ j < 5248, Bytes.getD M4.bytes j =
        Bytes.getD (readBytes SolmateVault.initCode 1226 5248) j := fun j hj => by
      rw [← hM4, Memory.getD_bytes_write, size_readBytes]
      simp only [show 0 ≤ j ∧ j < 0 + 5248 from ⟨Nat.zero_le _, by omega⟩, and_self, ↓reduceIte,
        Nat.sub_zero]
    refine ⟨congrArg Outcome.success (Vault.output_eq M4 hM _ _ asset _), rfl, ?_⟩
    dsimp only [outputMachine]
    evm_gas

end Verified.Solmate.Constructor
