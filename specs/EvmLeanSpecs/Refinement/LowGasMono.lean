import EvmLeanSpecs.Refinement.LowGas
import EvmLeanProofs.Program.GasMono.CallsFedScan
import EvmLeanProofs.Program.GasMono.LockstepTop

/-!
# Low gas: `CallsFed` for the Solmate vault and asset

The remaining code-level condition of the gas-lockstep theorem (`GasMono.CodeOk`): every
`CALL`/`CREATE`-family byte at a boundary of the region directly follows a `GAS`. Kernel
evaluations of the one-pass check `callsFedB` over the instruction scan (`insns`), which is the
same for every choice of immutables (`insns_vault`, `insns_asset`).
-/

namespace EvmLeanSpecs.Refinement.LowGas

open EvmLean EvmLean.Program.GasMono EvmLean.Contracts

/-- In the vault, every call byte below 5216 follows a `GAS`. -/
theorem vault_callsFed (i : SolmateVault.Immutables) :
    CallsFed (SolmateVault.runtimeCodeWith i) 5216 := by
  apply callsFed_of_scan
  rw [insns_vault]; decide +kernel

/-- In the asset, every call byte below 2838 follows a `GAS`. -/
theorem asset_callsFed (ia : SolmateAsset.Immutables) :
    CallsFed (SolmateAsset.runtimeCodeWith ia) 2838 := by
  apply callsFed_of_scan
  rw [insns_asset]; decide +kernel

/-- The code-level conditions of the lockstep for the vault. -/
theorem vault_codeOk (i : SolmateVault.Immutables) :
    CodeOk (SolmateVault.runtimeCodeWith i) 5216 :=
  ⟨vault_gasFeedsCall i, vault_regionOk i, vault_callsFed i, vault_failureReverts i⟩

/-- The code-level conditions of the lockstep for the asset. -/
theorem asset_codeOk (ia : SolmateAsset.Immutables) :
    CodeOk (SolmateAsset.runtimeCodeWith ia) 2838 :=
  ⟨asset_gasFeedsCall ia, asset_regionOk ia, asset_callsFed ia, asset_failureReverts ia⟩

end EvmLeanSpecs.Refinement.LowGas
