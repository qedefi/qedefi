import Examples.Solmate.ERC4626.Invariants.InvariantsCalls
import Examples.Solmate.ERC20.MintBurn

/-!
# `asset.mint` at the top level: the invariants layer's obligation

`opRefines_assetMint`: the `OpRefinesAt` obligation of `InvariantsSystem.lean` for a top-level
call of the asset's unrestricted `mint(dst, amount)` (any caller, any arguments), from the
frame-level `assetMint_refines` lifted by `call_of_halts`. On success the asset's storage
represents `Token.mint` (balances and supply exactly, allowances on every actor pair under
`SlotsOk`), the vault's storage is untouched; on overflow the call reverts.

Besides `SlotsOk` it needs the hash hypothesis `KeccakAvoids crypto (AddressKeyed [3]) [2]`
(no balance slot is the `totalSupply` slot; see `AssetMint.lean` for why it is necessary).
-/

namespace EvmLeanSpecs.Refinement.Invariants

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

/-- Actor pairs avoid both slots a `mint` / `burn` of `a` writes. -/
theorem SlotsOk.mintP (hs : SlotsOk crypto vault Act) {o sp : Address} (ho : o ∈ Act)
    (hsp : sp ∈ Act) (a : Address) : MintAllowances crypto a o sp :=
  ⟨(hs.allow o ho sp hsp).2.2, hs.balP ho hsp a⟩

set_option maxHeartbeats 1000000 in
/-- **`asset.mint`** refines `Op.assetMint`. -/
theorem opRefines_assetMint (hmin : 100000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256]) (caller dst : Address)
    (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.assetMint caller dst amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨ia, hcode⟩ := hdep.assetCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, ite_true, hcode] at hn
  have hd : dst ∈ Act := hact dst (by simp [VCall.actors])
  have hm := assetMint_refines (ia := ia) (dst := dst) (amount := amount)
    (startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Abi.encodeCall 0x40c10f19 [Word.ofAddress dst, amount]) gas wa wk))
    (fresh_startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Abi.encodeCall 0x40c10f19 [Word.ofAddress dst, amount]) gas wa wk)) rfl rfl
    (twoWordCall_encodeCall (by decide) _ _)
    (show (Abi.encodeCall 0x40c10f19 [Word.ofAddress dst, amount]).size < 2 ^ 64 by
      rw [Abi.size_encodeCall]; simp)
    (show 60000 ≤ gas by omega) hk (hs.bal dst hd) (rep_toToken _) hinv.1
  split at hm
  · rename_i t' ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨ho, hwld, -⟩, hrep⟩, hrun, hsucc, -⟩ :=
      hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw : r'.world = mintWorld ctx.crypto w asset dst amount := (hsucc _ ho).trans hwld
    rw [← hsucc _ ho] at hrep
    refine ⟨hdep.of_code (by rw [hw]; exact code_mintWorld ..)
      (by rw [hw]; exact code_mintWorld ..),
      callRefines_some (s' := { abs ctx.crypto w vault asset with asset := t' }) ?_ ?_⟩
    · show Option.map _ ((abs ctx.crypto w vault asset).asset.mint _ _) = _
      rw [show (abs ctx.crypto w vault asset).asset.mint dst amount.toNat = some t' from ht]; rfl
    exact agree_of_asset hrep (fun o sp ⟨ho, hsp⟩ => hs.mintP ho hsp dst)
      (fun k => by rw [hw]; exact sload_mintWorld (.inl hne))
  · rename_i ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨out, ho⟩, -⟩, hrun, -, hrev⟩ := hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw := hrev out ho
    refine ⟨hw ▸ hdep, callRefines_none ?_ hw⟩
    show Option.map _ ((abs ctx.crypto w vault asset).asset.mint _ _) = _
    rw [show (abs ctx.crypto w vault asset).asset.mint dst amount.toNat = none from ht]; rfl

end EvmLeanSpecs.Refinement.Invariants
