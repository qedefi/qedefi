import Examples.Solmate.ERC4626.Invariants.InvariantsCalls
import Examples.Solmate.ERC20.Approve

/-!
# `asset.approve` at the top level: the invariants layer's obligation

`opRefines_assetApprove`: the `OpRefinesAt` obligation of `InvariantsSystem.lean` for a
top-level call of the asset's `approve(spender, amount)` (any caller, any arguments), from the
frame-level `assetApprove_refines` lifted by `call_of_halts`, as for the asset's
`transfer` in `InvariantsCalls.lean`. The call always succeeds; the asset's storage represents
`Token.approve` on every actor pair (`SlotsOk`), the vault's storage is untouched.
-/

namespace EvmLeanSpecs.Refinement.Invariants

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity EvmLean.Contracts
open EvmLeanSpecs.Vault EvmLeanSpecs.Vault.Solmate EvmLeanSpecs.Refinement.Lift

variable {crypto : Crypto} {vault asset : Address} {minGas : Nat} {Act : List Address}

set_option maxHeartbeats 1000000 in
/-- **`asset.approve`** refines `Op.assetApprove`. -/
theorem opRefines_assetApprove (hmin : 100000 ≤ minGas) (caller spender : Address)
    (amount : Word) :
    OpRefinesAt crypto vault asset minGas Act (.assetApprove caller spender amount) := by
  rintro hs hact w w' hdep hinv ⟨ctx, tr, gas, wa, wk, r, hcr, hdeleg, hg, -, -, -, ⟨n, hn⟩, hw'⟩
  subst hcr hw'
  have hne := hdep.vault_ne_asset
  obtain ⟨ia, hcode⟩ := hdep.assetCode
  simp only [VCall.target, VCall.onAsset, VCall.caller, VCall.data, ite_true, hcode] at hn
  have hc : caller ∈ Act := hact caller (by simp [VCall.actors])
  have hsp : spender ∈ Act := hact spender (by simp [VCall.actors])
  have hm := assetApprove_refines (ia := ia) (spender := spender) (amount := amount)
    (startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Shares.approveData spender amount) gas wa wk))
    (fresh_startMachine ctx w tr (callMsg (SolmateAsset.runtimeCodeWith ia) asset caller
      (Shares.approveData spender amount) gas wa wk)) rfl rfl
    (twoWordCall_encodeCall (by decide) _ _)
    (show (Shares.approveData spender amount).size < 2 ^ 64 by
      rw [Shares.approveData, Abi.size_encodeCall]; simp)
    (show 40000 ≤ gas by omega) (hs.allow caller hc spender hsp) (rep_toToken _)
  obtain ⟨n', hn'⟩ := call_of_halts hdeleg (delegatedAddress?_assetCode ia)
    (hdep.assetNotPrecompile _) hm
  obtain ⟨mf, o, r', ⟨⟨ho, hwld, -⟩, hrep⟩, hrun, hsucc, -⟩ := hn' (max n n') (le_max_right _ _)
  obtain rfl := terminates_unique hn (le_max_left _ _) hrun
  have hw : r'.world = Erc20.approveWorld ctx.crypto w asset caller spender amount :=
    (hsucc _ ho).trans hwld
  rw [← hsucc _ ho] at hrep
  refine ⟨hdep.of_code (by rw [hw]; exact code_approveWorld ..)
    (by rw [hw]; exact code_approveWorld ..),
    callRefines_some (s' := { abs ctx.crypto w vault asset with
      asset := (abs ctx.crypto w vault asset).asset.approve caller spender amount.toNat }) rfl ?_⟩
  exact agree_of_asset hrep (fun o sp ⟨ho, hsp'⟩ => hs.allowP ho hsp' hc hsp)
    (fun k => by rw [hw]; exact World.sload_sstore_ne_addr _ _ _ _ hne)

end EvmLeanSpecs.Refinement.Invariants
