import EvmLogic.GasMono.CodeScan
import EvmLogic.GasMono.CodeFails
import Examples.Solmate.Contracts.SolmateVault
import Examples.Solmate.Contracts.SolmateAsset
import EvmLogic.Tactic.KernelRfl
import EvmLogic.GasMono.Lockstep

/-!
# Low gas: the code-specific premises of the gas-lockstep theorem

The generic gas-lockstep theorem (`EvmLogic.GasMono`) applies to a frame running
code in which

* every `GAS` feeds the gas argument of the immediately following `CALL`/`STATICCALL`
  (`GasFeedsCall code n`),
* execution stays in the region `[0, n)` (`RegionOk code n`), and
* after each call site, a failed call (success flag `0` on top of the stack) makes the frame
  end without success (`FailureReverts code p` for each `p ∈ callReturnPoints code n`).

This file establishes these premises for the compiled Solmate vault (`SolmateVault`, region
`[0, 5216)`: the final `INVALID` is at 5215, followed by a 32-byte data constant) and its asset
(`SolmateAsset`, region `[0, 2838)`), **for arbitrary immutables** and every `Crypto`, fork and
machine state.

* The scan facts are kernel evaluations of the list-based scan `insns`
  (`GasMono.CodeScan`). Patching immutables only rewrites `PUSH32` immediates, which the scan
  skips, so `insns (runtimeCodeWith i) = insns runtimeCode` (`insns_vault`, `insns_asset`,
  kernel-checked once for symbolic immutables), and the predicates are decided on the canonical
  code.
* The failure paths are run with the `Fails` calculus (`GasMono.CodeFails`), which absorbs every
  exceptional halt (out of gas included) into the rules, so the gas is never case-split.
  `LOWGAS.md` describes each call site and what follows a failed call.
-/

section

namespace Examples.Solmate.ERC4626.LowGas

open EvmLean Examples.Solmate EvmLogic EvmLogic.GasMono EvmLogic.Solidity Examples.Solmate.Contracts

/-! ## The vault -/

/-- The patches leave the vault's instruction scan unchanged. -/
theorem insns_vault (i : SolmateVault.Immutables) :
    insns (SolmateVault.runtimeCodeWith i) = insns SolmateVault.runtimeCode := by
  kernel_decide

/-- In the vault, every `GAS` below 5216 feeds a `CALL` or `STATICCALL`. -/
theorem vault_gasFeedsCall (i : SolmateVault.Immutables) :
    GasFeedsCall (SolmateVault.runtimeCodeWith i) 5216 := by
  rw [gasFeedsCall_iff, insns_vault]; decide +kernel

/-- The vault's execution stays in `[0, 5216)`. -/
theorem vault_regionOk (i : SolmateVault.Immutables) :
    RegionOk (SolmateVault.runtimeCodeWith i) 5216 := by
  rw [regionOk_iff, insns_vault]; decide +kernel

/-- The vault's call sites return to 1233 (`asset.balanceOf`), 3439 (`ecrecover`), 3957
(`safeTransferFrom`) and 4327 (`safeTransfer`). -/
theorem vault_callReturnPoints (i : SolmateVault.Immutables) :
    callReturnPoints (SolmateVault.runtimeCodeWith i) 5216 = [1233, 3439, 3957, 4327] := by
  rw [callReturnPoints_eq, insns_vault]; decide +kernel

/-- After `asset.balanceOf(address(this))` in `totalAssets` (solc: bubble the revert). -/
theorem vault_failureReverts_1233 (i : SolmateVault.Immutables) :
    FailureReverts (SolmateVault.runtimeCodeWith i) 1233 := by
  apply failureReverts_of_fails
  intro rest
  fails_steps

/-- After the `ecrecover` precompile call in `permit` (solc: bubble the revert). -/
theorem vault_failureReverts_3439 (i : SolmateVault.Immutables) :
    FailureReverts (SolmateVault.runtimeCodeWith i) 3439 := by
  apply failureReverts_of_fails
  intro rest
  fails_steps

/-- After the `transferFrom` call of `SafeTransferLib.safeTransferFrom` (in `deposit`/`mint`):
`require(success, "TRANSFER_FROM_FAILED")`. -/
theorem vault_failureReverts_3957 (i : SolmateVault.Immutables) :
    FailureReverts (SolmateVault.runtimeCodeWith i) 3957 := by
  apply failureReverts_of_fails
  intro rest
  -- `SWAP2` first: a stack shorter than three items underflows.
  rcases rest with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact Fails.swap_underflow ⟨1, by decide⟩ (by pcode_fact) rfl
  · exact Fails.swap_underflow ⟨1, by decide⟩ (by pcode_fact) rfl
  fails_steps

/-- After the `transfer` call of `SafeTransferLib.safeTransfer` (in `withdraw`/`redeem`):
`require(success, "TRANSFER_FAILED")`. -/
theorem vault_failureReverts_4327 (i : SolmateVault.Immutables) :
    FailureReverts (SolmateVault.runtimeCodeWith i) 4327 := by
  apply failureReverts_of_fails
  intro rest
  rcases rest with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact Fails.swap_underflow ⟨1, by decide⟩ (by pcode_fact) rfl
  · exact Fails.swap_underflow ⟨1, by decide⟩ (by pcode_fact) rfl
  fails_steps

/-- **Vault: every call site reverts on failure.** -/
theorem vault_failureReverts (i : SolmateVault.Immutables) :
    ∀ p ∈ callReturnPoints (SolmateVault.runtimeCodeWith i) 5216,
      FailureReverts (SolmateVault.runtimeCodeWith i) p := by
  rw [vault_callReturnPoints]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact vault_failureReverts_1233 i
  · exact vault_failureReverts_3439 i
  · exact vault_failureReverts_3957 i
  · exact vault_failureReverts_4327 i

/-! ## The asset -/

/-- The patches leave the asset's instruction scan unchanged. -/
theorem insns_asset (ia : SolmateAsset.Immutables) :
    insns (SolmateAsset.runtimeCodeWith ia) = insns SolmateAsset.runtimeCode := by
  kernel_decide

/-- In the asset, every `GAS` below 2838 feeds a `CALL` or `STATICCALL`. -/
theorem asset_gasFeedsCall (ia : SolmateAsset.Immutables) :
    GasFeedsCall (SolmateAsset.runtimeCodeWith ia) 2838 := by
  rw [gasFeedsCall_iff, insns_asset]; decide +kernel

/-- The asset's execution stays in `[0, 2838)`. -/
theorem asset_regionOk (ia : SolmateAsset.Immutables) :
    RegionOk (SolmateAsset.runtimeCodeWith ia) 2838 := by
  rw [regionOk_iff, insns_asset]; decide +kernel

/-- The asset's only call site returns to 1632 (`ecrecover` in `permit`). -/
theorem asset_callReturnPoints (ia : SolmateAsset.Immutables) :
    callReturnPoints (SolmateAsset.runtimeCodeWith ia) 2838 = [1632] := by
  rw [callReturnPoints_eq, insns_asset]; decide +kernel

/-- After the `ecrecover` precompile call in the asset's `permit` (solc: bubble the revert). -/
theorem asset_failureReverts_1632 (ia : SolmateAsset.Immutables) :
    FailureReverts (SolmateAsset.runtimeCodeWith ia) 1632 := by
  apply failureReverts_of_fails
  intro rest
  fails_steps

/-- **Asset: every call site reverts on failure.** -/
theorem asset_failureReverts (ia : SolmateAsset.Immutables) :
    ∀ p ∈ callReturnPoints (SolmateAsset.runtimeCodeWith ia) 2838,
      FailureReverts (SolmateAsset.runtimeCodeWith ia) p := by
  rw [asset_callReturnPoints]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact asset_failureReverts_1632 ia

end Examples.Solmate.ERC4626.LowGas

end

section

/-!
## Low gas: `CallsFed` for the Solmate vault and asset

The remaining code-level condition of the gas-lockstep theorem (`GasMono.CodeOk`): every
`CALL`/`CREATE`-family byte at a boundary of the region directly follows a `GAS`. Kernel
evaluations of the one-pass check `callsFedB` over the instruction scan (`insns`), which is the
same for every choice of immutables (`insns_vault`, `insns_asset`).
-/

namespace Examples.Solmate.ERC4626.LowGas

open EvmLean Examples.Solmate EvmLogic EvmLogic.GasMono EvmLogic.Solidity Examples.Solmate.Contracts

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

end Examples.Solmate.ERC4626.LowGas

end
