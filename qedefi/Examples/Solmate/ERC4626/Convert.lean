import Examples.Solmate.ERC20.BalanceOf
import Examples.Solmate.ERC4626.MulDiv
import EvmLogic.Tactic.Patched
import EvmLogic.Program.Call
import EvmLogic.Tactic.WpStep
import EvmLogic.Solidity.Call
import EvmLogic.Solidity.Memory

/-!
# The vault's internal `totalAssets()` and conversions

Summaries, for any immutables, of the internal `totalAssets()` (`0x047b`: `STATICCALL` to the
asset, plugged in through its callee summary `balanceOf_halts`) and of the four internal
conversions (`convertToShares`, `convertToAssets`, `previewMint`, `previewWithdraw`), each
returning the `Nat`-level specification (`convertToSharesN` …) at `supplyOf`/`assetsOf`.
-/

section

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

/-- A frame executing the vault (immutables `i`): its code and jump table, the asset's code at
`i.asset` (not a precompile), and room for one more call frame. -/
structure VaultFrame (i : SolmateVault.Immutables) (m : Machine) : Prop where
  code : m.frame.code = SolmateVault.runtimeCodeWith i
  jumpTable : JumpTable m.frame.jumpDests (SolmateVault.runtimeCodeWith i)
  assetCode : ∃ ia, m.world.code i.asset = SolmateAsset.runtimeCodeWith ia
  assetNotPrecompile : m.precompiles.isPrecompile i.asset = false
  depth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit

theorem readBytes_code_asset1170 (i : SolmateVault.Immutables) :
    readBytes (SolmateVault.runtimeCodeWith i) 1170 32 = Bytes.ofWord (Word.ofAddress i.asset) := by
  have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
      (688, Word.ofAddress i.asset)] ++ (1170, Word.ofAddress i.asset) ::
      [(2014, Word.ofAddress i.asset), (2169, Word.ofAddress i.asset),
      (2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
  simp only [SolmateVault.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateVault.size_runtimeCode]; decide)
    (by simp)

theorem readBytes_code_asset688 (i : SolmateVault.Immutables) :
    readBytes (SolmateVault.runtimeCodeWith i) 688 32 = Bytes.ofWord (Word.ofAddress i.asset) := by
  have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator)] ++
      (688, Word.ofAddress i.asset) :: [(1170, Word.ofAddress i.asset),
      (2014, Word.ofAddress i.asset), (2169, Word.ofAddress i.asset),
      (2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
  simp only [SolmateVault.runtimeCodeWith, hp]
  exact readBytes_patchWords_last _ _ _ _ _ (by rw [SolmateVault.size_runtimeCode]; decide)
    (by simp)

theorem delegatedAddress?_assetCode (ia : SolmateAsset.Immutables) :
    delegatedAddress? (SolmateAsset.runtimeCodeWith ia) = none :=
  delegatedAddress?_of_size (by
    rw [SolmateAsset.runtimeCodeWith, size_patchWords, SolmateAsset.size_runtimeCode]; decide)

/-- The vault's `totalSupply` word (slot 2 of the executing account). -/
def supplyOf (m : Machine) : Word := m.world.sload m.frame.msg.currentTarget (2#256)

/-- The executing account's balance word in the asset at `asset` (what `totalAssets()` returns). -/
def assetsOf (asset : Address) (m : Machine) : Word :=
  m.world.sload asset (ERC20.balanceSlot m.ctx.crypto ERC20.Layout.solmate
    m.frame.msg.currentTarget)

/-- solc's memory at the start of a function body: free pointer `0x80`, three words. -/
def FmpInit (mem : Memory) : Prop := mem.loadWord 64 = 128#256 ∧ mem.size = 96

/-- Memory after one external call through the free pointer: free pointer `0xa0`, six words. -/
def FmpAfterCall (mem : Memory) : Prop := mem.loadWord 64 = 160#256 ∧ mem.size = 192

set_option maxHeartbeats 0 in
/-- **`totalAssets()` (internal, entry `0x047b`, stack `r :: rest`)**: returns to `r` with
`assetsOf i.asset m`; the world is unchanged and memory ends as `FmpAfterCall`. -/
theorem totalAssets_wp {i : SolmateVault.Immutables} (m : Machine) {r : Word} {rest : List Word}
    (hv : VaultFrame i m)
    (hpc : m.frame.pc = 0x47b) (hs : m.frame.stack = r :: rest)
    (hlen : rest.length ≤ 1010) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hfmp : m.frame.memory.loadWord 64 = 128#256) (hsize : m.frame.memory.size = 96)
    (hg : 20000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ mem g rd sub,
        m' = m.resumeWith r.toNat (assetsOf i.asset m :: rest) mem g rd sub ∧
        FmpAfterCall mem ∧ m.frame.gasLeft ≤ g + 8000)
      (fun _ _ => False) := by
  obtain ⟨hc, hj, ⟨ia, hcode⟩, hpre, hdepth⟩ := hv
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  pwp_run_to 0x4d0 [hfmp, hsize, readBytes_code_asset1170, ofAddress_and_addressMask,
    addressMask_and_ofAddress]
  have hacc := accessCost_le (m_sub.accessedAddresses.contains i.asset)
  have hmod : (m_gasLeft - 112) % 2 ^ 256 = m_gasLeft - 112 := Nat.mod_eq_of_lt (by omega)
  have hto : Word.toAddress (Word.ofAddress i.asset) = i.asset := Word.toAddress_ofAddress _
  have hdel := delegatedAddress?_assetCode ia
  refine WP.staticcall (by pcode_fact) rfl ?_ ?_ ?_ ?_
    (balanceOf_halts (ia := ia) _ ?_ m_msg.currentTarget rfl ?_ ?_ ?_ ?_ ?_) ?_
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
    kernel_decide
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
      generalize Gas.accessCost (Std.ExtTreeSet.contains m_sub.accessedAddresses i.asset) = acc
        at hacc hgasB ⊢
      evm_gas
    clear hg1 hgasB hdel hto hcode hpre
    pwp_steps [hfmp, hsize, Bytes.size_ofWord]
    apply WP.ret
    refine ⟨_, _, _, _, by simp only [Machine.resumeWith, assetsOf]; rfl, ⟨?_, ?_⟩, ?_⟩
    · simp only [Memory.loadWord_expand, Memory.loadWord_storeWord]
    · rw_mem_sizes
      evm_gas_norm
      rw_mem_sizes
      evm_gas_norm
    · omega


end Examples.Solmate.ERC4626

end

section

/-!
## The conversions as internal functions

With `supply = 0` each returns its argument without calling the asset. (`previewDeposit` and
`previewRedeem` are `convertToShares` and `convertToAssets`.)
-/

namespace Examples.Solmate.ERC4626
open Examples.Solmate.ERC20

open EvmLean Examples.Solmate EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open EvmLogic.Tactic Examples.Solmate.Contracts

/-- `convertToShares(x)`: `supply == 0 ? x : x.mulDivDown(supply, totalAssets())`. -/
def convertToSharesN (S T x : Nat) : Option Nat := if S = 0 then some x else mulDivDownN x S T

/-- `convertToAssets(x)`: `supply == 0 ? x : x.mulDivDown(totalAssets(), supply)`. -/
def convertToAssetsN (S T x : Nat) : Option Nat := if S = 0 then some x else mulDivDownN x T S

/-- `previewMint(x)`: `supply == 0 ? x : x.mulDivUp(totalAssets(), supply)`. -/
def previewMintN (S T x : Nat) : Option Nat := if S = 0 then some x else mulDivUpN x T S

/-- `previewWithdraw(x)`: `supply == 0 ? x : x.mulDivUp(supply, totalAssets())`. -/
def previewWithdrawN (S T x : Nat) : Option Nat := if S = 0 then some x else mulDivUpN x S T

/-- Memory at the end of a conversion: `FmpInit` (no call made) or `FmpAfterCall`. -/
def FmpOk (mem : Memory) : Prop := FmpInit mem ∨ FmpAfterCall mem

set_option maxHeartbeats 0 in
/-- **`convertToShares(x)` (internal, entry `0xbda`, stack `x :: r :: rest`)**: returns to `r`
with the specification's value, or reverts as `mulDiv` does. -/
theorem convertToShares_wp {i : SolmateVault.Immutables} (m : Machine) {x r : Word} {rest : List Word}
    (hv : VaultFrame i m)
    (hpc : m.frame.pc = 0xbda) (hs : m.frame.stack = x :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpInit m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ v mem g rd sub,
        convertToSharesN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = some v ∧
        m' = m.resumeWith r.toNat (BitVec.ofNat 256 v :: rest) mem g rd sub ∧
        FmpOk mem ∧ m.frame.gasLeft ≤ g + 12000)
      (fun mf o => convertToSharesN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = none ∧
        MulDivRevert m mf o) := by
  obtain ⟨hc, hj, hcode, hpre, hdepth⟩ := hv
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨hfmp, hsize⟩ := hmem
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [supplyOf, assetsOf]
  pwp_steps
  by_cases hS : m_world.sload m_msg.currentTarget 2#256 = 0#256
  · simp only [hS, iszero_zero]
    pwp_steps
    refine WP.ret ⟨x.toNat, m_memory, _, m_returnData, _,
      by simp only [convertToSharesN]; rfl,
      by rw [Machine.resumeWith, ofNat_toNat_word], .inl ⟨hfmp, hsize⟩, ?_⟩
    evm_gas
  · have hS' : (m_world.sload m_msg.currentTarget 2#256).toNat ≠ 0 :=
      fun h => hS (BitVec.eq_of_toNat_eq (by simpa using h))
    simp only [iszero_of_ne hS]
    pwp_run_to 0x47b
    wp_generalize_gas g0 hg0
    have hg0' : m_gasLeft ≤ g0 + 2300 := by subst hg0; evm_gas
    have hg0'' : g0 ≤ m_gasLeft := by subst hg0; omega
    clear hg0
    refine WP.bind_mono (totalAssets_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl
      (by simp only [List.length_cons]; omega) (by pjumpdest_disch) hfmp hsize (by dsimp only; omega)
      (by dsimp only; omega)) (fun _ _ _ h => h.elim) ?_
    rintro m1 - ⟨mem, g, rd, sub, rfl, ⟨hfmp1, hsize1⟩, hg1⟩
    simp only [Machine.resumeWith, assetsOf, BitVec.reduceToNat] at hg1 ⊢
    pwp_run_to 0xe62
    refine WP.bind_mono (mulDivDown_wp _ rfl hj rfl rfl (by simp only [List.length_cons]; omega)
      (by pjumpdest_disch) (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hnone, hrev⟩
      exact ⟨by simp only [convertToSharesN, hS', ↓reduceIte]; exact hnone, hrev⟩
    rintro m2 - ⟨v, hv, rfl⟩
    simp only [Machine.resumeAt, BitVec.reduceToNat]
    pwp_steps
    exact WP.ret ⟨v, mem, _, rd, sub, by simp only [convertToSharesN, hS', ↓reduceIte, hv], rfl,
      .inr ⟨hfmp1, hsize1⟩, by omega⟩

set_option maxHeartbeats 0 in
/-- **`convertToAssets(x)` (internal, entry `0x593`, stack `x :: r :: rest`)**: returns to `r`
with the specification's value, or reverts as `mulDiv` does. -/
theorem convertToAssets_wp {i : SolmateVault.Immutables} (m : Machine) {x r : Word} {rest : List Word}
    (hv : VaultFrame i m)
    (hpc : m.frame.pc = 0x593) (hs : m.frame.stack = x :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpInit m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ v mem g rd sub,
        convertToAssetsN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = some v ∧
        m' = m.resumeWith r.toNat (BitVec.ofNat 256 v :: rest) mem g rd sub ∧
        FmpOk mem ∧ m.frame.gasLeft ≤ g + 12000)
      (fun mf o => convertToAssetsN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = none ∧
        MulDivRevert m mf o) := by
  obtain ⟨hc, hj, hcode, hpre, hdepth⟩ := hv
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨hfmp, hsize⟩ := hmem
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [supplyOf, assetsOf]
  pwp_steps
  by_cases hS : m_world.sload m_msg.currentTarget 2#256 = 0#256
  · simp only [hS, iszero_zero]
    pwp_steps
    refine WP.ret ⟨x.toNat, m_memory, _, m_returnData, _,
      by simp only [convertToAssetsN]; rfl,
      by rw [Machine.resumeWith, ofNat_toNat_word], .inl ⟨hfmp, hsize⟩, ?_⟩
    evm_gas
  · have hS' : (m_world.sload m_msg.currentTarget 2#256).toNat ≠ 0 :=
      fun h => hS (BitVec.eq_of_toNat_eq (by simpa using h))
    simp only [iszero_of_ne hS]
    pwp_run_to 0x47b
    wp_generalize_gas g0 hg0
    have hg0' : m_gasLeft ≤ g0 + 2300 := by subst hg0; evm_gas
    have hg0'' : g0 ≤ m_gasLeft := by subst hg0; omega
    clear hg0
    refine WP.bind_mono (totalAssets_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl
      (by simp only [List.length_cons]; omega) (by pjumpdest_disch) hfmp hsize (by dsimp only; omega)
      (by dsimp only; omega)) (fun _ _ _ h => h.elim) ?_
    rintro m1 - ⟨mem, g, rd, sub, rfl, ⟨hfmp1, hsize1⟩, hg1⟩
    simp only [Machine.resumeWith, assetsOf, BitVec.reduceToNat] at hg1 ⊢
    pwp_run_to 0xe62
    refine WP.bind_mono (mulDivDown_wp _ rfl hj rfl rfl (by simp only [List.length_cons]; omega)
      (by pjumpdest_disch) (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hnone, hrev⟩
      exact ⟨by simp only [convertToAssetsN, hS', ↓reduceIte]; exact hnone, hrev⟩
    rintro m2 - ⟨v, hv, rfl⟩
    simp only [Machine.resumeAt, BitVec.reduceToNat]
    pwp_steps
    exact WP.ret ⟨v, mem, _, rd, sub, by simp only [convertToAssetsN, hS', ↓reduceIte, hv], rfl,
      .inr ⟨hfmp1, hsize1⟩, by omega⟩

set_option maxHeartbeats 0 in
/-- **`previewMint(x)` (internal, entry `0x96b`, stack `x :: r :: rest`)**: returns to `r`
with the specification's value, or reverts as `mulDiv` does. -/
theorem previewMint_wp {i : SolmateVault.Immutables} (m : Machine) {x r : Word} {rest : List Word}
    (hv : VaultFrame i m)
    (hpc : m.frame.pc = 0x96b) (hs : m.frame.stack = x :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpInit m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ v mem g rd sub,
        previewMintN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = some v ∧
        m' = m.resumeWith r.toNat (BitVec.ofNat 256 v :: rest) mem g rd sub ∧
        FmpOk mem ∧ m.frame.gasLeft ≤ g + 12000)
      (fun mf o => previewMintN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = none ∧
        MulDivRevert m mf o) := by
  obtain ⟨hc, hj, hcode, hpre, hdepth⟩ := hv
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨hfmp, hsize⟩ := hmem
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [supplyOf, assetsOf]
  pwp_steps
  by_cases hS : m_world.sload m_msg.currentTarget 2#256 = 0#256
  · simp only [hS, iszero_zero]
    pwp_steps
    refine WP.ret ⟨x.toNat, m_memory, _, m_returnData, _,
      by simp only [previewMintN]; rfl,
      by rw [Machine.resumeWith, ofNat_toNat_word], .inl ⟨hfmp, hsize⟩, ?_⟩
    evm_gas
  · have hS' : (m_world.sload m_msg.currentTarget 2#256).toNat ≠ 0 :=
      fun h => hS (BitVec.eq_of_toNat_eq (by simpa using h))
    simp only [iszero_of_ne hS]
    pwp_run_to 0x47b
    wp_generalize_gas g0 hg0
    have hg0' : m_gasLeft ≤ g0 + 2300 := by subst hg0; evm_gas
    have hg0'' : g0 ≤ m_gasLeft := by subst hg0; omega
    clear hg0
    refine WP.bind_mono (totalAssets_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl
      (by simp only [List.length_cons]; omega) (by pjumpdest_disch) hfmp hsize (by dsimp only; omega)
      (by dsimp only; omega)) (fun _ _ _ h => h.elim) ?_
    rintro m1 - ⟨mem, g, rd, sub, rfl, ⟨hfmp1, hsize1⟩, hg1⟩
    simp only [Machine.resumeWith, assetsOf, BitVec.reduceToNat] at hg1 ⊢
    pwp_run_to 0xe7d
    refine WP.bind_mono (mulDivUp_wp _ rfl hj rfl rfl (by simp only [List.length_cons]; omega)
      (by pjumpdest_disch) (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hnone, hrev⟩
      exact ⟨by simp only [previewMintN, hS', ↓reduceIte]; exact hnone, hrev⟩
    rintro m2 - ⟨v, hv, rfl⟩
    simp only [Machine.resumeAt, BitVec.reduceToNat]
    pwp_steps
    exact WP.ret ⟨v, mem, _, rd, sub, by simp only [previewMintN, hS', ↓reduceIte, hv], rfl,
      .inr ⟨hfmp1, hsize1⟩, by omega⟩

set_option maxHeartbeats 0 in
/-- **`previewWithdraw(x)` (internal, entry `0x62b`, stack `x :: r :: rest`)**: returns to `r`
with the specification's value, or reverts as `mulDiv` does. -/
theorem previewWithdraw_wp {i : SolmateVault.Immutables} (m : Machine) {x r : Word} {rest : List Word}
    (hv : VaultFrame i m)
    (hpc : m.frame.pc = 0x62b) (hs : m.frame.stack = x :: r :: rest)
    (hlen : rest.length ≤ 1000) (hr : isValidJumpDest m.frame.jumpDests r.toNat = true)
    (hmem : FmpInit m.frame.memory)
    (hg : 30000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    WP m (fun m' => ∃ v mem g rd sub,
        previewWithdrawN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = some v ∧
        m' = m.resumeWith r.toNat (BitVec.ofNat 256 v :: rest) mem g rd sub ∧
        FmpOk mem ∧ m.frame.gasLeft ≤ g + 12000)
      (fun mf o => previewWithdrawN (supplyOf m).toNat (assetsOf i.asset m).toNat x.toNat = none ∧
        MulDivRevert m mf o) := by
  obtain ⟨hc, hj, hcode, hpre, hdepth⟩ := hv
  have hagree := Shares.jumpDestsAgree i
  obtain ⟨hfmp, hsize⟩ := hmem
  obtain ⟨m_ctx, m_pre, m_world, m_transient, m_originalWorld, m_created,
    ⟨m_msg, m_code, m_jumpDests, m_pc, m_stack, m_memory, m_gasLeft, m_returnData, m_sub,
      m_snapshot, m_kind⟩, m_parents⟩ := m
  dsimp only at *
  subst hs hpc hc
  simp only [supplyOf, assetsOf]
  pwp_steps
  by_cases hS : m_world.sload m_msg.currentTarget 2#256 = 0#256
  · simp only [hS, iszero_zero]
    pwp_steps
    refine WP.ret ⟨x.toNat, m_memory, _, m_returnData, _,
      by simp only [previewWithdrawN]; rfl,
      by rw [Machine.resumeWith, ofNat_toNat_word], .inl ⟨hfmp, hsize⟩, ?_⟩
    evm_gas
  · have hS' : (m_world.sload m_msg.currentTarget 2#256).toNat ≠ 0 :=
      fun h => hS (BitVec.eq_of_toNat_eq (by simpa using h))
    simp only [iszero_of_ne hS]
    pwp_run_to 0x47b
    wp_generalize_gas g0 hg0
    have hg0' : m_gasLeft ≤ g0 + 2300 := by subst hg0; evm_gas
    have hg0'' : g0 ≤ m_gasLeft := by subst hg0; omega
    clear hg0
    refine WP.bind_mono (totalAssets_wp _ ⟨rfl, hj, hcode, hpre, hdepth⟩ rfl rfl
      (by simp only [List.length_cons]; omega) (by pjumpdest_disch) hfmp hsize (by dsimp only; omega)
      (by dsimp only; omega)) (fun _ _ _ h => h.elim) ?_
    rintro m1 - ⟨mem, g, rd, sub, rfl, ⟨hfmp1, hsize1⟩, hg1⟩
    simp only [Machine.resumeWith, assetsOf, BitVec.reduceToNat] at hg1 ⊢
    pwp_run_to 0xe7d
    refine WP.bind_mono (mulDivUp_wp _ rfl hj rfl rfl (by simp only [List.length_cons]; omega)
      (by pjumpdest_disch) (by dsimp only; omega)) ?_ ?_
    · rintro mf o - ⟨hnone, hrev⟩
      exact ⟨by simp only [previewWithdrawN, hS', ↓reduceIte]; exact hnone, hrev⟩
    rintro m2 - ⟨v, hv, rfl⟩
    simp only [Machine.resumeAt, BitVec.reduceToNat]
    pwp_steps
    exact WP.ret ⟨v, mem, _, rd, sub, by simp only [previewWithdrawN, hS', ↓reduceIte, hv], rfl,
      .inr ⟨hfmp1, hsize1⟩, by omega⟩

end Examples.Solmate.ERC4626

end
