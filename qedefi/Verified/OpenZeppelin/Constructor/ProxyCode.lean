import Verified.OpenZeppelin.Constructor.ProxyInit
import Verified.Solmate.Constructor.Basic

/-!
# The code the `TransparentUpgradeableProxy` constructor returns

The constructor copies the runtime code out of its init code (`CODECOPY` of bytes
`1102 … 2107`), stores the immutable `_admin` at offset 16 of the copy and returns it.
`output_eq`: whatever the memory below, the returned bytes are `runtimeCodeWith ⟨admin⟩`. The
copied bytes are the runtime code with a zero admin (`readBytes_initCode_runtime`, checked by
the kernel on byte lists).
-/

namespace Verified.OpenZeppelin.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity Verified.OpenZeppelin.Contracts
open Verified.Solmate.Constructor

/-- The runtime code with a zero `_admin`, as the constructor copies it. -/
theorem readBytes_proxyInit_runtime : readBytes OzTransparentProxy.initCode 1102 1005 =
    patchWords OzTransparentProxy.runtimeCode [(16, 0)] := by
  rw [OzTransparentProxy.initCode_eq, readBytes_append_of_le _ _ _ _
    (by rw [OzTransparentProxy.size_creationCode]; omega)]
  apply eq_of_data_toList_eq
  rw [readBytes_toList _ _ _ (by rw [OzTransparentProxy.size_creationCode]; omega)
    (by rw [OzTransparentProxy.size_creationCode]; omega)]
  decide +kernel

/-- **The `RETURN`ed runtime code**: the copy (held by `M`) with the admin stored at 16. -/
theorem proxy_output_eq (M : Memory)
    (hM : ∀ j < 1005, Bytes.getD M.bytes j =
      Bytes.getD (readBytes OzTransparentProxy.initCode 1102 1005) j) (a : Address) :
    ((M.expand 16 32).storeWord 16 (Word.ofAddress a)).read 0 1005 =
      OzTransparentProxy.runtimeCodeWith ⟨a⟩ := by
  apply Bytes.ext_getD
  · rw [Memory.read, Bytes.size_readPadded, OzTransparentProxy.runtimeCodeWith, size_patchWords,
      OzTransparentProxy.size_runtimeCode]
  · intro j hj
    rw [Memory.read, Bytes.size_readPadded] at hj
    have hp : (⟨a⟩ : OzTransparentProxy.Immutables).patches = [(16, Word.ofAddress a)] := rfl
    simp only [Memory.read, Bytes.getD_readPadded, hj, ↓reduceIte, Nat.zero_add, Memory.storeWord,
      Memory.getD_bytes_write, Memory.getD_bytes_expand, Bytes.size_ofWord,
      OzTransparentProxy.runtimeCodeWith, hp]
    have hrs := OzTransparentProxy.size_runtimeCode
    by_cases h16 : 16 ≤ j ∧ j < 16 + 32
    · simp only [h16, and_self, ↓reduceIte]
      rw [show [(16, Word.ofAddress a)] = [] ++ (16, Word.ofAddress a) :: [] from rfl,
        getD_patch_in _ _ _ 16 _ (by omega) (by simp) j h16.1 h16.2]
    · simp only [h16, ↓reduceIte]
      rw [hM j hj, readBytes_proxyInit_runtime, getD_patch_out _ _ j (by simp; omega),
        getD_patch_out _ _ j (by simp; omega)]

/-- The copy of the runtime code in memory, byte by byte. -/
theorem getD_write_proxyRuntime (X : Memory) (j : Nat) (hj : j < 1005) :
    Bytes.getD (X.write 0 (readBytes OzTransparentProxy.initCode 1102 1005)).bytes j =
      Bytes.getD (readBytes OzTransparentProxy.initCode 1102 1005) j := by
  rw [Memory.getD_bytes_write, size_readBytes]
  simp only [show 0 ≤ j ∧ j < 0 + 1005 from ⟨Nat.zero_le _, by omega⟩, and_self, ↓reduceIte,
    Nat.sub_zero]

end Verified.OpenZeppelin.Constructor
