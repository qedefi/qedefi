import EvmLeanSpecs.Refinement.AssetBalanceOf
import EvmLeanSpecs.Refinement.MulDiv
import EvmLeanProofs.Program.Call
import EvmLeanProofs.Program.ExtraTactic
import EvmLeanProofs.Solidity.Call
import EvmLeanProofs.Solidity.ExtraMemory

/-!
# The vault's `totalAssets()` as an internal function

`MockERC4626.totalAssets()` is `asset.balanceOf(address(this))`. solc compiles it as an
internal function at pc `0x047b` (called by `totalAssets()`, the conversions and the
previews): it writes the calldata of `balanceOf(address(this))` at the free-memory pointer,
`STATICCALL`s the asset with all remaining gas, checks success, re-aligns the free-memory
pointer to the returned data and ABI-decodes one word.

`totalAssets_wp` summarises it once. The asset's code enters only through its callee summary
`balanceOf_halts`, plugged into the callee-summary rule `WP.staticcall`: the result is the
asset's balance slot of the vault (`assetsOf m`), the world is unchanged, the free-memory
pointer moves from `0x80` to `0xa0` and memory grows to six words (`FmpAfterCall`).

## Assumptions

* the frame runs the canonical vault code (`VaultFrame`): the vault's `asset` immutable is
  `assetAddr`, which holds the asset's runtime code, is not a precompile, and the call depth
  leaves room for one more frame;
* solc's memory discipline at entry (`FmpInit`: free pointer `0x80`, three words of memory);
* `20000 ≤ gas < 2⁶⁴`.
-/

namespace EvmLeanSpecs.Refinement

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts

/-- The asset address of the canonical vault deployment (the vault's `asset` immutable in
`SolmateVault.runtimeCode`). -/
abbrev assetAddr : Address := SolmateVault.deployment.asset

/-- A frame executing the canonical vault: its code and jump table, the asset's code at
`assetAddr`, `assetAddr` not a precompile, and room for one more call frame. -/
structure VaultFrame (m : Machine) : Prop where
  /-- The frame runs the vault's runtime code. -/
  code : m.frame.code = SolmateVault.runtimeCode
  /-- Its jump table. -/
  jumpTable : JumpTable m.frame.jumpDests SolmateVault.runtimeCode
  /-- The asset is deployed. -/
  assetCode : m.world.code assetAddr = SolmateAsset.runtimeCode
  /-- The asset is not a precompile. -/
  assetNotPrecompile : m.precompiles.isPrecompile assetAddr = false
  /-- A call from this frame does not exceed the depth limit. -/
  depth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit

/-- The vault's `totalSupply` word (slot 2 of the executing account). -/
def supplyOf (m : Machine) : Word := m.world.sload m.frame.msg.currentTarget 2

/-- The asset balance word of the executing account: what `totalAssets()` returns. -/
def assetsOf (m : Machine) : Word :=
  m.world.sload assetAddr (Erc20.balanceSlot m.ctx.crypto Erc20.Layout.solmate
    m.frame.msg.currentTarget)

/-- solc's memory at the start of a function body: free pointer `0x80`, three words. -/
def FmpInit (mem : Memory) : Prop := mem.loadWord 64 = 128#256 ∧ mem.size = 96

/-- Memory after one external call through the free pointer: free pointer `0xa0`, six words. -/
def FmpAfterCall (mem : Memory) : Prop := mem.loadWord 64 = 160#256 ∧ mem.size = 192

set_option maxHeartbeats 0 in
/-- **`totalAssets()` (internal, entry `0x047b`, stack `r :: rest`)**: returns to `r` with
`assetsOf m` on the stack; memory, gas, return data and substate change as described by
`FmpAfterCall` and the gas bound, nothing else (in particular not the world). -/
theorem totalAssets_wp (m : Machine) {r : Word} {rest : List Word} (hv : VaultFrame m)
    (hpc : m.frame.pc = 0x47b) (hs : m.frame.stack = r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hfmp : m.frame.memory.loadWord 64 = 128#256) (hsize : m.frame.memory.size = 96)
    (hg : 20000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ mem g rd sub,
        m' = m.resumeWith r.toNat (assetsOf m :: rest) mem g rd sub ∧
        FmpAfterCall mem ∧ m.frame.gasLeft ≤ g + 8000)
      (fun _ _ => False) := by
  obtain ⟨hc, hj, hcode, hpre, hdepth⟩ := hv
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  wp_run_to 0x4d0 [hfmp, hsize]
  have hacc := accessCost_le (m_sub.accessedAddresses.contains assetAddr)
  have hmod : (m_gasLeft - 112) % 2 ^ 256 = m_gasLeft - 112 := Nat.mod_eq_of_lt (by omega)
  have hto : Word.toAddress (108902904548468084633759432717356981306078134798#256) = assetAddr := by
    decide
  have hdel : delegatedAddress? SolmateAsset.runtimeCode = none :=
    delegatedAddress?_of_size (by rw [SolmateAsset.size_runtimeCode]; decide)
  refine WP.staticcall (by code_fact) rfl ?_ ?_ ?_ ?_
    (balanceOf_halts _ ?_ m_msg.currentTarget rfl ?_ ?_ ?_ ?_ ?_) ?_
  · exact .inr (by dsimp only; rw [hto, hcode]; exact hdel)
  · simp only [callCost, callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, hmod,
      Nat.reducePow, Nat.reduceMod]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    evm_gas
  · exact hdepth
  · rw [hto]; exact hpre
  · exact ⟨_, _, _, rfl, by dsimp only [childMsg]; rw [hto, hcode]⟩
  · dsimp only [Frame.init, childMsg, callMemory]
    simp only [BitVec.reduceToNat, readBytes_bytes, Abi.selectorOf]
    rw [Memory.readBytes_read _ 128 36 0 4 (by decide)]
    simp only [Memory.read_expand, Nat.add_zero,
      Memory.read_storeWord_of_disjoint _ 132 128 4 _ (by decide),
      Memory.read_storeWord_prefix _ _ 4 _ (by decide)]
    decide +kernel
  · dsimp only [Frame.init, childMsg, callMemory]
    simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
    decide
  · dsimp only [Frame.init, childMsg, callMemory]
    simp only [BitVec.reduceToNat, readBytes_bytes, Memory.size_read]
    decide
  · dsimp only [Frame.init, childMsg, callMemory]
    simp only [BitVec.reduceToNat, readBytes_bytes]
    rw [Memory.readBytes_read _ 128 36 4 32 (by decide), Memory.read_expand, Memory.read_expand,
      Memory.read_expand, Memory.read_storeWord, Bytes.toWord_ofWord]
  · dsimp only [Frame.init, childMsg]
    simp only [callGas, callExt, hto, ofNat, BitVec.toNat_ofNat, hmod, Nat.reducePow,
      Nat.reduceMod]
    rw [messageCallGas_zero (by evm_gas)]
    simp only [Gas.maxMessageCallGas]
    evm_gas
  · intro mf o ⟨ho, hw, ht, hca, hlogs, hgasB⟩ hsame
    have hk : mf.frame.kind = .call 128 32 := hsame.kind
    subst ho
    rw [resumeAfter_success hk]
    dsimp only at hw ht hca hgasB hlogs
    have hs1 : mf.ctx = m_ctx := hsame.ctx
    have hs2 : mf.precompiles = m_pre := hsame.precompiles
    have hs3 : mf.originalWorld = m_originalWorld := hsame.originalWorld
    simp only [hw, ht, hca, hs1, hs2, hs3]
    dsimp only [callerFrame, callMemory, Frame.init, childMsg] at hgasB ⊢
    simp only [hto, returnMemory_ofWord, callCost, callGas, callExt, ofNat,
      BitVec.toNat_ofNat, hmod, Nat.reducePow, Nat.reduceMod] at hgasB ⊢
    rw [messageCallGas_zero (by evm_gas)] at hgasB ⊢
    simp only [Gas.maxMessageCallGas] at hgasB ⊢
    wp_generalize_gas g1 hg1
    have hg1' : m_gasLeft ≤ g1 + 6000 := by
      subst hg1
      generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses assetAddr) = acc
        at hacc hgasB ⊢
      evm_gas
    clear hg1 hgasB hdel hto hcode hpre
    wp_steps [hfmp, hsize, Bytes.size_ofWord]
    apply WP.ret
    refine ⟨_, _, _, _, by simp only [Machine.resumeWith, assetsOf]; rfl, ⟨?_, ?_⟩, ?_⟩
    · simp only [Memory.loadWord_expand, Memory.loadWord_storeWord]
    · rw_mem_sizes
      evm_gas_norm
      rw_mem_sizes
      evm_gas_norm
    · omega


end EvmLeanSpecs.Refinement
