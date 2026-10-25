import EvmLogic.GasMono.CodeScan
import EvmLogic.GasMono.CodeFails
import Verified.Solmate.Contracts.SolmateVault
import Verified.Solmate.Contracts.SolmateAsset
import EvmLogic.Tactic.KernelRfl
import EvmLogic.GasMono.Lockstep

/-!
# Low gas: the code-specific premises of the gas-lockstep theorem

`GasFeedsCall`, `RegionOk`, `FailureReverts` at each call return point, and `CallsFed`, for the
vault (region `[0, 5216)`) and the asset (`[0, 2838)`), for arbitrary immutables. Patching
immutables only rewrites `PUSH32` immediates, which the scan skips, so the scan facts are
decided on the canonical code. See `docs/erc4626/details.md` §9.
-/

section

namespace Verified.Solmate.ERC4626.LowGas

open EvmLean Verified.Solmate EvmLogic EvmLogic.GasMono EvmLogic.Solidity
open Verified.Solmate.Contracts

/-! ## The vault -/

theorem insns_vault (i : SolmateVault.Immutables) :
    insns (SolmateVault.runtimeCodeWith i) = insns SolmateVault.runtimeCode := by
  kernel_decide

theorem vault_gasFeedsCall (i : SolmateVault.Immutables) :
    GasFeedsCall (SolmateVault.runtimeCodeWith i) 5216 := by
  rw [gasFeedsCall_iff, insns_vault]; kernel_decide

theorem vault_regionOk (i : SolmateVault.Immutables) :
    RegionOk (SolmateVault.runtimeCodeWith i) 5216 := by
  rw [regionOk_iff, insns_vault]; kernel_decide

/-- The vault's call sites return to 1233 (`asset.balanceOf`), 3439 (`ecrecover`), 3957
(`safeTransferFrom`, `require`) and 4327 (`safeTransfer`, `require`); the others bubble. -/
theorem vault_callReturnPoints (i : SolmateVault.Immutables) :
    callReturnPoints (SolmateVault.runtimeCodeWith i) 5216 = [1233, 3439, 3957, 4327] := by
  rw [callReturnPoints_eq, insns_vault]; kernel_decide

theorem vault_failureReverts_1233 (i : SolmateVault.Immutables) :
    FailureReverts (SolmateVault.runtimeCodeWith i) 1233 := by
  apply failureReverts_of_fails
  intro rest
  fails_steps

theorem vault_failureReverts_3439 (i : SolmateVault.Immutables) :
    FailureReverts (SolmateVault.runtimeCodeWith i) 3439 := by
  apply failureReverts_of_fails
  intro rest
  fails_steps

theorem vault_failureReverts_3957 (i : SolmateVault.Immutables) :
    FailureReverts (SolmateVault.runtimeCodeWith i) 3957 := by
  apply failureReverts_of_fails
  intro rest
  -- `SWAP2` first: a stack shorter than three items underflows.
  rcases rest with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact Fails.swap_underflow ⟨1, by decide⟩ (by pcode_fact) rfl
  · exact Fails.swap_underflow ⟨1, by decide⟩ (by pcode_fact) rfl
  fails_steps

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

theorem insns_asset (ia : SolmateAsset.Immutables) :
    insns (SolmateAsset.runtimeCodeWith ia) = insns SolmateAsset.runtimeCode := by
  kernel_decide

theorem asset_gasFeedsCall (ia : SolmateAsset.Immutables) :
    GasFeedsCall (SolmateAsset.runtimeCodeWith ia) 2838 := by
  rw [gasFeedsCall_iff, insns_asset]; kernel_decide

theorem asset_regionOk (ia : SolmateAsset.Immutables) :
    RegionOk (SolmateAsset.runtimeCodeWith ia) 2838 := by
  rw [regionOk_iff, insns_asset]; kernel_decide

/-- The asset's only call site returns to 1632 (`ecrecover` in `permit`). -/
theorem asset_callReturnPoints (ia : SolmateAsset.Immutables) :
    callReturnPoints (SolmateAsset.runtimeCodeWith ia) 2838 = [1632] := by
  rw [callReturnPoints_eq, insns_asset]; kernel_decide

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

end Verified.Solmate.ERC4626.LowGas

end

section

/-! ## `CallsFed`, and the code-level conditions `CodeOk` -/

namespace Verified.Solmate.ERC4626.LowGas

open EvmLean Verified.Solmate EvmLogic EvmLogic.GasMono EvmLogic.Solidity
open Verified.Solmate.Contracts

theorem vault_callsFed (i : SolmateVault.Immutables) :
    CallsFed (SolmateVault.runtimeCodeWith i) 5216 := by
  apply callsFed_of_scan
  rw [insns_vault]; kernel_decide

theorem asset_callsFed (ia : SolmateAsset.Immutables) :
    CallsFed (SolmateAsset.runtimeCodeWith ia) 2838 := by
  apply callsFed_of_scan
  rw [insns_asset]; kernel_decide

/-- The code-level conditions of the lockstep for the vault. -/
theorem vault_codeOk (i : SolmateVault.Immutables) :
    CodeOk (SolmateVault.runtimeCodeWith i) 5216 :=
  ⟨vault_gasFeedsCall i, vault_regionOk i, vault_callsFed i, vault_failureReverts i⟩

/-- The code-level conditions of the lockstep for the asset. -/
theorem asset_codeOk (ia : SolmateAsset.Immutables) :
    CodeOk (SolmateAsset.runtimeCodeWith ia) 2838 :=
  ⟨asset_gasFeedsCall ia, asset_regionOk ia, asset_callsFed ia, asset_failureReverts ia⟩

end Verified.Solmate.ERC4626.LowGas

end
