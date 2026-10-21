import Examples.Solmate.Contracts.SolmateVault
import Examples.Solmate.Contracts.SolmateAsset
import EvmLogic.AbsInt.Check
import EvmLogic.AbsInt.Domain
import EvmLogic.Tactic.KernelRfl

/-!
# Low gas: certificates of the abstract interpreter for the vault and asset

The certified abstract interpreter (`EvmLogic/AbsInt`) explores the vault and the asset in the
kernel (`vault_certify`, `asset_certify`) and its result is a certificate for all immutables
(`vault_cert`, `asset_cert`). Separate from `Targets.lean`, which uses them, so that the kernel
evaluation runs early in the build. See `docs/erc4626/details.md` §9.
-/

namespace Examples.Solmate.ERC4626.LowGas

open EvmLean EvmLogic EvmLogic.Program EvmLean.Interpreter EvmLogic.Solidity
open Examples.Solmate.Contracts
open EvmLogic.AbsInt

/-! ## Certificates -/

/-- The `PUSH32`s of the vault that push the `asset` immutable (immutable number `0`). -/
def vaultSyms : List (Nat × Nat) :=
  [(687, 0), (1169, 0), (2013, 0), (2168, 0), (2667, 0), (2994, 0)]

/-- The vault calls the asset (`sym 0`) or `ecrecover` (`1`). -/
def vaultTargets : AVal → Bool
  | .sym k => k == 0
  | .const n => n == 1
  | .top => false

/-- The asset calls `ecrecover` (`1`) only. -/
def assetTargets : AVal → Bool
  | .const n => n == 1
  | .sym _ => false
  | .top => false

def certFuel : Nat := 100000

theorem ascan_vault (i : SolmateVault.Immutables) :
    ascan (SolmateVault.runtimeCodeWith i) vaultSyms = ascan SolmateVault.runtimeCode vaultSyms := by
  kernel_decide

theorem ascan_asset (ia : SolmateAsset.Immutables) :
    ascan (SolmateAsset.runtimeCodeWith ia) [] = ascan SolmateAsset.runtimeCode [] := by
  kernel_decide

/-- **The vault's exploration succeeds** (kernel evaluation, ≈6600 abstract states). -/
theorem vault_certify :
    (certify vaultTargets SolmateVault.runtimeCode vaultSyms [] certFuel).isSome = true := by
  kernel_decide

/-- **The asset's exploration succeeds** (kernel evaluation, ≈3000 abstract states). -/
theorem asset_certify :
    (certify assetTargets SolmateAsset.runtimeCode [] [] certFuel).isSome = true := by
  kernel_decide

theorem vault_readBytes_asset (i : SolmateVault.Immutables) {o : Nat}
    (ho : o = 688 ∨ o = 1170 ∨ o = 2014 ∨ o = 2169 ∨ o = 2668 ∨ o = 2995) :
    readBytes (SolmateVault.runtimeCodeWith i) o 32 = Bytes.ofWord (Word.ofAddress i.asset) := by
  have hfit : ∀ o ∈ [688, 1170, 2014, 2169, 2668, 2995], o + 32 ≤ SolmateVault.runtimeCode.size := by
    rw [SolmateVault.size_runtimeCode]; decide
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
  · have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator)] ++
        (688, Word.ofAddress i.asset) :: [(1170, Word.ofAddress i.asset),
        (2014, Word.ofAddress i.asset), (2169, Word.ofAddress i.asset),
        (2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
    simp only [SolmateVault.runtimeCodeWith, hp]
    exact readBytes_patchWords_last _ _ _ _ _ (hfit _ (by decide)) (by simp)
  · have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
        (688, Word.ofAddress i.asset)] ++ (1170, Word.ofAddress i.asset) ::
        [(2014, Word.ofAddress i.asset), (2169, Word.ofAddress i.asset),
        (2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
    simp only [SolmateVault.runtimeCodeWith, hp]
    exact readBytes_patchWords_last _ _ _ _ _ (hfit _ (by decide)) (by simp)
  · have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
        (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset)] ++
        (2014, Word.ofAddress i.asset) :: [(2169, Word.ofAddress i.asset),
        (2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
    simp only [SolmateVault.runtimeCodeWith, hp]
    exact readBytes_patchWords_last _ _ _ _ _ (hfit _ (by decide)) (by simp)
  · have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
        (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset),
        (2014, Word.ofAddress i.asset)] ++ (2169, Word.ofAddress i.asset) ::
        [(2668, Word.ofAddress i.asset), (2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
    simp only [SolmateVault.runtimeCodeWith, hp]
    exact readBytes_patchWords_last _ _ _ _ _ (hfit _ (by decide)) (by simp)
  · have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
        (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset),
        (2014, Word.ofAddress i.asset), (2169, Word.ofAddress i.asset)] ++
        (2668, Word.ofAddress i.asset) :: [(2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl
    simp only [SolmateVault.runtimeCodeWith, hp]
    exact readBytes_patchWords_last _ _ _ _ _ (hfit _ (by decide)) (by simp)
  · have hp : i.patches = [(1831, i.initialChainId), (1879, i.initialDomainSeparator),
        (688, Word.ofAddress i.asset), (1170, Word.ofAddress i.asset),
        (2014, Word.ofAddress i.asset), (2169, Word.ofAddress i.asset),
        (2668, Word.ofAddress i.asset)] ++ (2995, Word.ofAddress i.asset) ::
        [(623, i.decimals)] := rfl
    simp only [SolmateVault.runtimeCodeWith, hp]
    exact readBytes_patchWords_last _ _ _ _ _ (hfit _ (by decide)) (by simp)

theorem vault_symOk (i : SolmateVault.Immutables) :
    SymOk (fun _ => i.asset) (SolmateVault.runtimeCodeWith i) vaultSyms := by
  intro q k h
  have hq : q + 1 = 688 ∨ q + 1 = 1170 ∨ q + 1 = 2014 ∨ q + 1 = 2169 ∨ q + 1 = 2668 ∨
      q + 1 = 2995 := by
    simp only [vaultSyms, symAt] at h
    split at h
    · simp_all
    split at h
    · simp_all
    split at h
    · simp_all
    split at h
    · simp_all
    split at h
    · simp_all
    split at h
    · simp_all
    cases h
  rw [vault_readBytes_asset i hq, Bytes.toWord_ofWord]

/-- **The vault's certificate**, for all immutables. -/
theorem vault_cert (i : SolmateVault.Immutables) :
    ∃ t, Cert (fun _ => i.asset) vaultTargets (SolmateVault.runtimeCodeWith i) [] t := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 vault_certify
  refine ⟨t, certify_sound (fuel := certFuel) ?_ (vault_symOk i)⟩
  unfold certify table at ht ⊢
  rw [ascan_vault]
  exact ht

/-- **The asset's certificate**, for all immutables. -/
theorem asset_cert (ia : SolmateAsset.Immutables) :
    ∃ t, Cert (fun _ => 0) assetTargets (SolmateAsset.runtimeCodeWith ia) [] t := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 asset_certify
  refine ⟨t, certify_sound (fuel := certFuel) (syms := []) ?_ (fun q k h => by cases h)⟩
  unfold certify table at ht ⊢
  rw [ascan_asset]
  exact ht

end Examples.Solmate.ERC4626.LowGas
