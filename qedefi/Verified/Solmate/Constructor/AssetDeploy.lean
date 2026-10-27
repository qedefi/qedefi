import Verified.Solmate.Constructor.AssetSeg1
import Verified.Solmate.Constructor.AssetSeg2

/-!
# Deploying the Solmate asset (`MockERC20`)

`asset_ctor_halts`: the constructor frame, run from its first instruction (any frame running
the canonical init code with no value and slots 0 and 1 empty), returns the runtime code with
the immutables it computed (`Asset.immutables`: chain id, domain separator, 18 decimals) and
writes the name and symbol into slots 0 and 1.

`asset_create`: a top-level creation (`processMessageCall` of a message with `target = none`)
running `creationCode ++ constructorArgs` at a deployable address succeeds, and its world is
`assetWorld`: the new account's nonce incremented, slots 0 and 1 written, the runtime code
deposited.
-/

namespace Verified.Solmate.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Tactic
open Verified.Solmate.Contracts

/-- What the constructor frame does: returns the runtime code with `Asset.immutables`, writes
the name and symbol slots, uses less than 103 000 gas. -/
def AssetCtorPost (m mf : Machine) (o : Outcome) : Prop :=
  o = .success (SolmateAsset.runtimeCodeWith
    (Asset.immutables m.ctx.crypto m.ctx.block.chainId m.frame.msg.currentTarget)) ∧
  mf.world = (m.world.sstore m.frame.msg.currentTarget 0#256 Asset.nameSlot).sstore
    m.frame.msg.currentTarget 1#256 Asset.symbolSlot ∧
  m.frame.gasLeft ≤ mf.frame.gasLeft + 103000

/-- **The `MockERC20` constructor**, for any frame that starts running the canonical init code
with no value, not static, with slots 0 and 1 of its account empty and enough gas. -/
theorem asset_ctor_halts (m : Machine) (hf : Fresh SolmateAsset.initCode m)
    (hval : m.frame.msg.value = 0) (hstatic : m.frame.msg.isStatic = false)
    (hs0 : m.world.sload m.frame.msg.currentTarget 0#256 = 0#256)
    (hs1 : m.world.sload m.frame.msg.currentTarget 1#256 = 0#256)
    (hg : 1000000 ≤ m.frame.gasLeft) (hg' : m.frame.gasLeft < 2 ^ 64) :
    Halts m (AssetCtorPost m) := by
  apply WP.halts_of_false
  refine WP.bind ((asset_seg1 m hf hval (by omega)).mono (fun _ _ h => h)
    (fun _ _ _ h => h.elim)) ?_
  rintro m' hsf ⟨hc, hj, hpc, hs, hA, hw, hg1, hg2⟩
  have hmsg := hsf.msg
  have hctx := hsf.ctx
  refine (asset_seg2 m' hc hj hpc hs hA (by rw [hmsg]; exact hstatic)
    (by rw [hw, hmsg]; exact hs0) (by rw [hw, hmsg]; exact hs1) (by omega) (by omega)).mono
    (fun _ _ h => h) ?_
  rintro mf o - ⟨ho, hwf, hgf⟩
  refine ⟨?_, ?_, by omega⟩
  · rw [ho, hctx, hmsg]
  · rw [hwf, hw, hmsg]

/-- The world after deploying the asset at `self` on chain `chainId`. -/
def assetWorld (crypto : Crypto) (chainId : Nat) (w : World) (self : Address) : World :=
  setCode (((incrementNonce w self).sstore self 0#256 Asset.nameSlot).sstore self 1#256
    Asset.symbolSlot) self (SolmateAsset.runtimeCodeWith (Asset.immutables crypto chainId self))

theorem delegatedAddress?_assetInit :
    delegatedAddress? (SolmateAsset.creationCode ++ SolmateAsset.constructorArgs) = none := by
  rw [← SolmateAsset.initCode_eq]
  simp only [delegatedAddress?, isValidDelegation, SolmateAsset.size_initCode]
  rfl

theorem getElem_runtimeCodeWith_zero (i : SolmateAsset.Immutables) :
    (SolmateAsset.runtimeCodeWith i)[0]? = some 0x60 := by
  rw [SolmateAsset.runtimeCodeWith, getElem?_patchWords_of_offsets _ _ 0 [1063, 1116, 345] rfl
    (by decide)]
  decide +kernel

theorem size_runtimeCodeWith (i : SolmateAsset.Immutables) :
    (SolmateAsset.runtimeCodeWith i).size = 2870 := by
  rw [SolmateAsset.runtimeCodeWith, size_patchWords, SolmateAsset.size_runtimeCode]

/-- **Deploying the asset.** A top-level creation running the canonical `MockERC20` init code
(`creationCode ++ constructorArgs`) at an address with no code, nonce 0 and empty storage
(`accountDeployable`; otherwise it fails with an address collision), sent with no value, not
static, at depth 0, with at least 1 000 000 and fewer than `2⁶⁴` gas, before Prague or without
EIP-7702 authorizations, terminates successfully in `assetWorld`. -/
theorem asset_create {ctx : Context} {w : World} {tr : TransientStorage} {msg : Message}
    (hdeleg : ctx.fork < .prague ∨ ctx.tx.authorizations = []) (htarget : msg.target = none)
    (hcode : msg.code = SolmateAsset.creationCode ++ SolmateAsset.constructorArgs)
    (hval : msg.value = 0) (hdepth : msg.depth = 0) (hstatic : msg.isStatic = false)
    (hd : accountDeployable w msg.currentTarget = true)
    (hg : 1000000 ≤ msg.gas) (hg' : msg.gas < 2 ^ 64) :
    ∃ r : MessageResult, (∃ n, ∀ fuel, n ≤ fuel → processMessageCall fuel ctx w tr msg = .ok r) ∧
      r.success = true ∧ r.world = assetWorld ctx.crypto ctx.block.chainId w msg.currentTarget := by
  have hf : Fresh SolmateAsset.initCode (createMachine ctx w tr msg) := by
    have := fresh_createMachine ctx w tr msg
    rwa [hcode, ← SolmateAsset.initCode_eq] at this
  have hh := asset_ctor_halts (createMachine ctx w tr msg) hf hval hstatic
    (sload_incrementNonce_of_deployable _ hd) (sload_incrementNonce_of_deployable _ hd) hg hg'
  obtain ⟨n, mf, o, ⟨ho, hwf, hgf⟩, hsf, hr⟩ := processMessageCall_create_of_halts hdeleg
    (hcode ▸ delegatedAddress?_assetInit) htarget hd hval hdepth hh
  have hk : mf.frame.kind = .create := hsf.kind
  have hmsg : mf.frame.msg = msg := hsf.msg
  have hctx : mf.ctx = ctx := hsf.ctx
  dsimp only [createMachine, Frame.init] at ho hwf hgf
  subst ho
  have hdep := depositCode_ok (fork := mf.ctx.fork) (g := mf.frame.gasLeft)
    (out := SolmateAsset.runtimeCodeWith (Asset.immutables ctx.crypto ctx.block.chainId
      msg.currentTarget))
    (by rw [getElem_runtimeCodeWith_zero]; decide)
    (by rw [size_runtimeCodeWith]; omega)
    (by rw [size_runtimeCodeWith]; cases mf.ctx.fork <;> decide)
  obtain ⟨hs, hw⟩ := topLevelResult_create hk hdep
  refine ⟨_, ⟨n, fun fuel hle => (hr fuel hle).trans (by rw [htarget])⟩, hs, ?_⟩
  rw [hw, hwf, hmsg]
  rfl

end Verified.Solmate.Constructor
