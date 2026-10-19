import EvmLeanSpecs.Refinement.AssetMintCall
import EvmLeanSpecs.Refinement.AssetBurn

/-!
# `asset.burn` at the top level: the invariants layer's obligation

`opRefines_assetBurn`: the `OpRefinesAt` obligation of `InvariantsSystem.lean` for a top-level
call of the asset's unrestricted `burn(src, amount)` (any caller, any arguments; with
`src = vault` this is the model's "loss"), from the frame-level `assetBurn_refines` lifted by
`call_of_halts`. Same hypotheses as `opRefines_assetMint`.
-/

namespace EvmLeanSpecs.Refinement.Invariants

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

set_option maxHeartbeats 1000000 in
/-- **`asset.burn`** refines `Op.assetBurn`. -/
theorem opRefines_assetBurn (hmin : 100000 ≤ minGas)
    (hk : KeccakAvoids crypto (AddressKeyed [3#256]) [2#256]) (caller src : Address)
    (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.assetBurn caller src amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨ia, hcode⟩ := hdep.assetCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, ite_true, hcode] at hn
  have hsr : src ∈ Act := hact src (by simp [VCall.actors])
  have hm := assetBurn_refines (ia := ia) (src := src) (amount := amount)
    (startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Abi.encodeCall 0x9dc29fac [Word.ofAddress src, amount]) gas wa wk))
    (fresh_startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Abi.encodeCall 0x9dc29fac [Word.ofAddress src, amount]) gas wa wk)) rfl rfl
    (twoWordCall_encodeCall (by decide) _ _)
    (show (Abi.encodeCall 0x9dc29fac [Word.ofAddress src, amount]).size < 2 ^ 64 by
      rw [Abi.size_encodeCall]; simp)
    (show 60000 ≤ gas by omega) hk (hs.bal src hsr) (rep_toToken _) hinv.1
  split at hm
  · rename_i t' ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨ho, hwld, -⟩, hrep⟩, hrun, hsucc, -⟩ :=
      hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw : r'.world = burnWorld ctx.crypto w asset src amount := (hsucc _ ho).trans hwld
    rw [← hsucc _ ho] at hrep
    refine ⟨hdep.of_code (by rw [hw]; exact code_burnWorld ..)
      (by rw [hw]; exact code_burnWorld ..),
      callRefines_some (s' := { abs ctx.crypto w vault asset with asset := t' }) ?_ ?_⟩
    · show Option.map _ ((abs ctx.crypto w vault asset).asset.burn _ _) = _
      rw [show (abs ctx.crypto w vault asset).asset.burn src amount.toNat = some t' from ht]; rfl
    exact agree_of_asset hrep (fun o sp ⟨ho, hsp⟩ => hs.mintP ho hsp src)
      (fun k => by rw [hw]; exact sload_burnWorld (.inl hne))
  · rename_i ht
    obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
      (hdep.assetNotPrecompile _) hm
    obtain ⟨mf, o, r', ⟨⟨out, ho⟩, -⟩, hrun, -, hrev⟩ := hn' (max n n') (le_max_right _ _)
    obtain rfl := terminates_unique hn (le_max_left _ _) hrun
    have hw := hrev out ho
    refine ⟨hw ▸ hdep, callRefines_none ?_ hw⟩
    show Option.map _ ((abs ctx.crypto w vault asset).asset.burn _ _) = _
    rw [show (abs ctx.crypto w vault asset).asset.burn src amount.toNat = none from ht]; rfl

end EvmLeanSpecs.Refinement.Invariants
