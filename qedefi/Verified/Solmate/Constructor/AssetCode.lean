import Verified.Solmate.Constructor.AssetInit
import Verified.Solmate.Constructor.Basic

/-!
# The code the `MockERC20` constructor returns

The constructor copies the runtime code out of its init code (`CODECOPY` of bytes
`1015 … 3885`), stores the three immutables into the copy and returns it. `output_eq`: whatever
the memory below, the returned bytes are `runtimeCodeWith` of the stored words. The copied
bytes are the canonical runtime code with zero immutables (`readBytes_initCode_runtime`,
checked by the kernel on byte lists).
-/

namespace Verified.Solmate.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity Verified.Solmate.Contracts

theorem readBytes_initCode_runtime : readBytes SolmateAsset.initCode 1015 2870 =
    patchWords SolmateAsset.runtimeCode [(1063, 0), (1116, 0), (345, 0)] := by
  rw [SolmateAsset.initCode_eq, readBytes_append_of_le _ _ _ _
    (by rw [SolmateAsset.size_creationCode]; omega)]
  apply eq_of_data_toList_eq
  rw [readBytes_toList _ _ _ (by rw [SolmateAsset.size_creationCode]; omega)
    (by rw [SolmateAsset.size_creationCode]; omega)]
  decide +kernel

/-- The `RETURN`ed runtime code: the copied code with the three immutables stored (the
memory `M` holds the copy, `getD_initCode_runtime`). -/
theorem output_eq (M : Memory)
    (hM : ∀ j < 2870, Bytes.getD M.bytes j = Bytes.getD (readBytes SolmateAsset.initCode 1015 2870) j)
    (cid ds dec : Word) :
    ((((((M.expand 1116 32).storeWord 1116 ds).expand 1063 32).storeWord 1063 cid).expand 345
      32).storeWord 345 dec).read 0 2870 = SolmateAsset.runtimeCodeWith ⟨cid, ds, dec⟩ := by
  apply Bytes.ext_getD
  · rw [Memory.read, Bytes.size_readPadded, SolmateAsset.runtimeCodeWith, size_patchWords,
      SolmateAsset.size_runtimeCode]
  · intro j hj
    rw [Memory.read, Bytes.size_readPadded] at hj
    have hp : (⟨cid, ds, dec⟩ : SolmateAsset.Immutables).patches =
      [(1063, cid), (1116, ds), (345, dec)] := rfl
    simp only [Memory.read, Bytes.getD_readPadded, hj, ↓reduceIte, Nat.zero_add, Memory.storeWord,
      Memory.getD_bytes_write, Memory.getD_bytes_expand, Bytes.size_ofWord,
      SolmateAsset.runtimeCodeWith, hp]
    have hrs := SolmateAsset.size_runtimeCode
    by_cases h345 : 345 ≤ j ∧ j < 345 + 32
    · simp only [h345, and_self, ↓reduceIte]
      rw [show [(1063, cid), (1116, ds), (345, dec)] = [(1063, cid), (1116, ds)] ++ (345, dec) :: []
        from rfl, getD_patch_in _ _ _ 345 dec (by omega) (by simp) j h345.1 h345.2]
    · by_cases h1063 : 1063 ≤ j ∧ j < 1063 + 32
      · simp only [h345, h1063, and_self, ↓reduceIte]
        rw [show [(1063, cid), (1116, ds), (345, dec)] = [] ++ (1063, cid) :: [(1116, ds), (345, dec)]
          from rfl, getD_patch_in _ _ _ 1063 cid (by omega) (by simp) j h1063.1 h1063.2]
      · by_cases h1116 : 1116 ≤ j ∧ j < 1116 + 32
        · simp only [h345, h1063, h1116, and_self, ↓reduceIte]
          rw [show [(1063, cid), (1116, ds), (345, dec)] = [(1063, cid)] ++ (1116, ds) :: [(345, dec)]
            from rfl, getD_patch_in _ _ _ 1116 ds (by omega) (by simp) j h1116.1 h1116.2]
        · simp only [h345, h1063, h1116, ↓reduceIte]
          rw [hM j hj, readBytes_initCode_runtime, getD_patch_out _ _ j (by simp; omega),
            getD_patch_out _ _ j (by simp; omega)]

/-- The copy of the runtime code in memory, byte by byte. -/
theorem getD_write_runtime (X : Memory) (j : Nat) (hj : j < 2870) :
    Bytes.getD (X.write 0 (readBytes SolmateAsset.initCode 1015 2870)).bytes j =
      Bytes.getD (readBytes SolmateAsset.initCode 1015 2870) j := by
  rw [Memory.getD_bytes_write, size_readBytes]
  simp only [show 0 ≤ j ∧ j < 0 + 2870 from ⟨Nat.zero_le _, by omega⟩, and_self, ↓reduceIte,
    Nat.sub_zero]

end Verified.Solmate.Constructor
