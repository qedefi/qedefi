import Verified.Solmate.Constructor.VaultInit
import Verified.Solmate.Constructor.Basic

/-!
# The code the `MockERC4626` constructor returns

The constructor copies the runtime code out of its init code (`CODECOPY` of bytes
`1226 … 6474`), stores the immutables into the copy (the asset at six offsets) and returns it.
`output_eq`: whatever the memory below, the returned bytes are `runtimeCodeWith` of the stored
words. The copied bytes are the runtime code with zero immutables
(`readBytes_initCode_runtime`, checked by the kernel on byte lists).
-/

namespace Verified.Solmate.Constructor.Vault
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity Verified.Solmate.Contracts
open Verified.Solmate.Constructor

/-- The runtime code with zero immutables. -/
theorem readBytes_initCode_runtime : readBytes SolmateVault.initCode 1226 5248 =
    SolmateVault.runtimeCodeWith ⟨0, 0, 0, 0⟩ := by
  rw [SolmateVault.initCode_eq, readBytes_append_of_le _ _ _ _
    (by rw [SolmateVault.size_creationCode]; omega)]
  apply eq_of_data_toList_eq
  rw [readBytes_toList _ _ _ (by rw [SolmateVault.size_creationCode]; omega)
    (by rw [SolmateVault.size_creationCode]; omega)]
  decide +kernel

/-- The stores of the immutables, in the order the constructor makes them. -/
def stores (cid ds : Word) (asset : Address) (dec : Word) : List (Nat × Word) :=
  [(688, Word.ofAddress asset), (1170, Word.ofAddress asset), (2014, Word.ofAddress asset),
    (2169, Word.ofAddress asset), (2668, Word.ofAddress asset), (2995, Word.ofAddress asset),
    (1879, ds), (1831, cid), (623, dec)]

theorem patches_eq (i : SolmateVault.Immutables) : i.patches =
    [(1831, i.initialChainId), (1879, i.initialDomainSeparator), (688, Word.ofAddress i.asset),
      (1170, Word.ofAddress i.asset), (2014, Word.ofAddress i.asset),
      (2169, Word.ofAddress i.asset), (2668, Word.ofAddress i.asset),
      (2995, Word.ofAddress i.asset), (623, i.decimals)] := rfl

theorem fits (i : SolmateVault.Immutables) :
    ∀ p ∈ i.patches, p.1 + 32 ≤ SolmateVault.runtimeCode.size := by
  rw [patches_eq, SolmateVault.size_runtimeCode]
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

set_option maxHeartbeats 1000000 in
/-- **The `RETURN`ed runtime code**: the copied code with the immutables stored. -/
theorem output_eq (M : Memory)
    (hM : ∀ j < 5248, Bytes.getD M.bytes j =
      Bytes.getD (readBytes SolmateVault.initCode 1226 5248) j)
    (cid ds : Word) (asset : Address) (dec : Word) :
    (storeWords M (stores cid ds asset dec)).read 0 5248 =
      SolmateVault.runtimeCodeWith ⟨cid, ds, asset, dec⟩ := by
  apply Bytes.ext_getD
  · rw [Memory.read, Bytes.size_readPadded, SolmateVault.runtimeCodeWith, size_patchWords,
      SolmateVault.size_runtimeCode]
  · intro j hj
    rw [Memory.read, Bytes.size_readPadded] at hj
    rw [Memory.read, Bytes.getD_readPadded]
    simp only [hj, ↓reduceIte, Nat.zero_add]
    rw [getD_storeWords,
      patchFn_congr _ (hM j hj), readBytes_initCode_runtime, SolmateVault.runtimeCodeWith,
      SolmateVault.runtimeCodeWith, getD_patchWords _ _ (fits _),
      patchFn_congr _ (getD_patchWords _ _ (fits ⟨0, 0, 0, 0⟩) j), patches_eq, patches_eq]
    simp only [stores, patchFn]
    have h0 : ∀ k, Bytes.getD (Bytes.ofWord (Word.ofAddress 0)) k = 0 := fun k => by
      rw [show Word.ofAddress 0 = 0 by decide]; exact Memory.getD_ofWord_zero k
    by_cases h1 : 688 ≤ j ∧ j < 688 + 32 <;> by_cases h2 : 1170 ≤ j ∧ j < 1170 + 32 <;>
      by_cases h3 : 2014 ≤ j ∧ j < 2014 + 32 <;> by_cases h4 : 2169 ≤ j ∧ j < 2169 + 32 <;>
      by_cases h5 : 2668 ≤ j ∧ j < 2668 + 32 <;> by_cases h6 : 2995 ≤ j ∧ j < 2995 + 32 <;>
      by_cases h7 : 1879 ≤ j ∧ j < 1879 + 32 <;> by_cases h8 : 1831 ≤ j ∧ j < 1831 + 32 <;>
      by_cases h9 : 623 ≤ j ∧ j < 623 + 32 <;>
      (set_option linter.unusedSimpArgs false in
        simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, and_self, ↓reduceIte, h0,
          Memory.getD_ofWord_zero]) <;> omega

end Verified.Solmate.Constructor.Vault
