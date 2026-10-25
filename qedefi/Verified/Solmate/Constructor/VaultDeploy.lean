import Verified.Solmate.Constructor.VaultSeg1
import Verified.Solmate.Constructor.VaultSeg2
import Verified.Solmate.Constructor.AssetDeploy

/-!
# Deploying the Solmate vault (`MockERC4626`) over a deployed asset

`vault_ctor_halts`: the constructor frame, run from its first instruction over an `asset`
holding the Solmate asset's code (any immutables), calls `asset.decimals()`, returns the runtime
code with the immutables it computed (`Vault.immutables`, the asset among them) and writes the
name and symbol into slots 0 and 1 (and zero into the hook counters, slots 6 and 7).

`vault_create`: a top-level creation running `creationCode ++ constructorArgsFor asset` at a
deployable address succeeds, and its world is `vaultWorld`.
-/

namespace Verified.Solmate.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Tactic
open Verified.Solmate.Contracts

/-- What the vault's constructor frame does. -/
def VaultCtorPost (asset : Address) (dec : Word) (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (SolmateVault.runtimeCodeWith (Vault.immutables m.ctx.crypto m.ctx.block.chainId
    m.frame.msg.currentTarget asset dec)) ∧
  mf.world = ((((m.world.sstore m.frame.msg.currentTarget 6#256 0#256).sstore
    m.frame.msg.currentTarget 7#256 0#256).sstore m.frame.msg.currentTarget 0#256
      Vault.nameSlot).sstore m.frame.msg.currentTarget 1#256 Vault.symbolSlot) ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 200000

/-- **The `MockERC4626` constructor**, for any frame that starts running the init code of a
vault over `asset` (which holds the Solmate asset's code, is not a precompile, and is reached
below the depth limit) with no value, not static, slots 0 and 1 of its account empty and
enough gas. -/
theorem vault_ctor_halts (asset : Address) (ia : SolmateAsset.Immutables) (m : Machine)
    (hf : Fresh (SolmateVault.initCodeFor asset) m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    (hcode : m.world.code asset = SolmateAsset.runtimeCodeWith ia)
    (hpre : m.precompiles.isPrecompile asset = false)
    (hdepth : m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit)
    (hs0 : m.world.sload m.frame.msg.currentTarget 0#256 = 0#256)
    (hs1 : m.world.sload m.frame.msg.currentTarget 1#256 = 0#256)
    (hg : 2000000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    Halts m (VaultCtorPost asset (ia.decimals &&& 255#256) m) := by
  apply WP.halts_of_false
  refine WP.bind ((vault_seg1 asset m hf hval hstatic (by omega) hg').mono (fun _ _ h => h)
    (fun _ _ _ h => h.elim)) ?_
  rintro m' hsf ⟨hc, hj, hpc, hs, hA, hw, hg1, hg2⟩
  have hmsg := hsf.msg
  have hctx := hsf.ctx
  have hpre' : m'.precompiles = m.precompiles := hsf.precompiles
  refine (vault_seg2 asset ia m' hc hj hpc hs hA (by rw [hmsg]; exact hstatic)
    (by rw [hw]; simp only [World.code_sstore]; exact hcode) (by rw [hpre']; exact hpre)
    (by rw [hmsg]; exact hdepth)
    (by rw [hw, hmsg, World.sload_sstore_ne_key _ _ _ (by decide),
      World.sload_sstore_ne_key _ _ _ (by decide)]; exact hs0)
    (by rw [hw, hmsg, World.sload_sstore_ne_key _ _ _ (by decide),
      World.sload_sstore_ne_key _ _ _ (by decide)]; exact hs1)
    (by omega) (by omega)).mono (fun _ _ h => h) ?_
  rintro mf o - ⟨ho, hwf, hgf⟩
  refine ⟨?_, ?_, by omega⟩
  · rw [ho, hctx, hmsg]
  · rw [hwf, hw, hmsg]

/-- The world after deploying a vault over `asset` at `self` on chain `chainId`, the asset's
`decimals()` having returned `dec`. -/
def vaultWorld (crypto : Crypto) (chainId : Nat) (w : World) (self asset : Address) (dec : Word) :
    World :=
  setCode (((((incrementNonce w self).sstore self 6#256 0#256).sstore self 7#256 0#256).sstore
    self 0#256 Vault.nameSlot).sstore self 1#256 Vault.symbolSlot) self
    (SolmateVault.runtimeCodeWith (Vault.immutables crypto chainId self asset dec))

theorem code_incrementNonce' (w : World) (a b : Address) :
    (incrementNonce w a).code b = w.code b := by
  simp only [World.code, incrementNonce, account_modifyState w a
    (fun acc => { acc with nonce := acc.nonce + 1 }) b (by simp [Account.isEmpty])]
  split <;> simp_all

theorem delegatedAddress?_vaultInit (asset : Address) :
    delegatedAddress? (SolmateVault.creationCode ++ SolmateVault.constructorArgsFor asset) =
      none := by
  rw [← SolmateVault.initCodeFor_eq]
  simp only [delegatedAddress?, isValidDelegation, SolmateVault.size_initCodeFor]
  rfl

theorem getElem_vaultRuntimeCodeWith_zero (i : SolmateVault.Immutables) :
    (SolmateVault.runtimeCodeWith i)[0]? = some 0x60 := by
  rw [SolmateVault.runtimeCodeWith, getElem?_patchWords_of_offsets _ _ 0
    [1831, 1879, 688, 1170, 2014, 2169, 2668, 2995, 623] rfl (by decide)]
  decide +kernel

theorem size_vaultRuntimeCodeWith (i : SolmateVault.Immutables) :
    (SolmateVault.runtimeCodeWith i).size = 5248 := by
  rw [SolmateVault.runtimeCodeWith, size_patchWords, SolmateVault.size_runtimeCode]

/-- **Deploying the vault.** A top-level creation running the `MockERC4626` init code over
`asset` (`creationCode ++ constructorArgsFor asset`) at an address with no code, nonce 0 and
empty storage, sent with no value, not static, at depth 0, with at least 2 000 000 and fewer than
`2⁶⁴` gas, before Prague or without EIP-7702 authorizations, where `asset` holds the Solmate
asset's code (any immutables `ia`) and is not a precompile, terminates successfully in
`vaultWorld` (its `decimals` from the asset). -/
theorem vault_create {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    {asset : Address} {ia : SolmateAsset.Immutables}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (htarget : msg.target = none)
    (hcode : msg.code = SolmateVault.creationCode ++ SolmateVault.constructorArgsFor asset)
    (hval : msg.value = 0) (hdepth : msg.depth = 0) (hstatic : msg.isStatic = false)
    (hd : accountDeployable w msg.currentTarget = true)
    (hasset : w.code asset = SolmateAsset.runtimeCodeWith ia)
    (hpre : Precompile.isPrecompile ctx.fork asset = false)
    (hg : 2000000 ≤ msg.gas) (hg' : msg.gas < 2 ^ 64) :
    ∃ r : MessageResult, (∃ n, ∀ fuel, n ≤ fuel → processMessageCall fuel ctx w tr msg = .ok r) ∧
      r.success = true ∧ r.world = vaultWorld ctx.crypto ctx.block.chainId w msg.currentTarget
        asset (ia.decimals &&& 255#256) := by
  have hf : Fresh (SolmateVault.initCodeFor asset) (createMachine ctx w tr msg) := by
    have := fresh_createMachine ctx w tr msg
    rwa [hcode, ← SolmateVault.initCodeFor_eq] at this
  have hh := vault_ctor_halts asset ia (createMachine ctx w tr msg) hf hval hstatic
    (by simp only [createMachine]; rw [code_incrementNonce']; exact hasset) hpre
    (by simp only [createMachine, Frame.init, hdepth, Gas.stackDepthLimit]; decide)
    (sload_incrementNonce_of_deployable _ hd) (sload_incrementNonce_of_deployable _ hd) hg hg'
  obtain ⟨n, mf, o, ⟨ho, hwf, hgf⟩, hsf, hr⟩ := processMessageCall_create_of_halts hdeleg
    (hcode ▸ delegatedAddress?_vaultInit asset) htarget hd hval hdepth hh
  have hk : mf.frame.kind = .create := hsf.kind
  have hmsg : mf.frame.msg = msg := hsf.msg
  dsimp only [createMachine, Frame.init] at ho hwf hgf
  subst ho
  have hdep := depositCode_ok (fork := mf.ctx.fork) (g := mf.frame.gasLeft)
    (out := SolmateVault.runtimeCodeWith (Vault.immutables ctx.crypto ctx.block.chainId
      msg.currentTarget asset (ia.decimals &&& 255#256)))
    (by rw [getElem_vaultRuntimeCodeWith_zero]; decide)
    (by rw [size_vaultRuntimeCodeWith]; omega)
    (by rw [size_vaultRuntimeCodeWith]; cases mf.ctx.fork <;> decide)
  obtain ⟨hs, hw⟩ := topLevelResult_create hk hdep
  refine ⟨_, ⟨n, fun fuel hle => (hr fuel hle).trans (by rw [htarget])⟩, hs, ?_⟩
  rw [hw, hwf, hmsg]
  rfl

end Verified.Solmate.Constructor
