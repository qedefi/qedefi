import Verified.OpenZeppelin.Constructor.AdminInit
import Verified.Solmate.Constructor.Basic
import Verified.Solmate.Constructor.JumpDest

/-!
# The `ProxyAdmin` init code for any owner

`initCodeFor o = creationCode ++ abi.encode(o)` (`initCodeFor_eq`), its argument as the
constructor's `CODECOPY` reads it, and its jump destinations: those of the creation code,
whatever `o` (`jumpTable_initCodeFor`).
-/

namespace Verified.OpenZeppelin.Contracts.OzProxyAdmin
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity Verified.Solmate.Constructor

theorem size_constructorArgs : constructorArgs.size = 32 := by decide +kernel

theorem size_initCodeFor (o : Address) : (initCodeFor o).size = 1232 := by
  rw [initCodeFor, size_patchWords, size_initCode]

/-- **The init code of a `ProxyAdmin` owned by `o`.** -/
theorem initCodeFor_eq (o : Address) :
    initCodeFor o = creationCode ++ Bytes.ofWord (Word.ofAddress o) := by
  apply Bytes.ext_getD
  · rw [size_initCodeFor, ByteArray.size_append, size_creationCode, Bytes.size_ofWord]
  · intro j hj
    rw [size_initCodeFor] at hj
    rw [Bytes.getD_append, size_creationCode, initCodeFor]
    by_cases hw : 1200 ≤ j ∧ j < 1200 + 32
    · rw [show [(1200, Word.ofAddress o)] = [] ++ (1200, Word.ofAddress o) :: [] from rfl,
        getD_patch_in _ _ _ _ _ (by rw [size_initCode]; omega) (by simp) j hw.1 hw.2]
      simp only [show ¬ j < 1200 by omega, ↓reduceIte]
    · have ho : ∀ o' ∈ [(1200, Word.ofAddress o)].map Prod.fst, j < o' ∨ o' + 32 ≤ j := by
        simp only [List.map_cons, List.map_nil, List.mem_singleton, forall_eq]; omega
      rw [getD_patch_out _ _ j ho, initCode_eq, Bytes.getD_append, size_creationCode]
      simp only [show j < 1200 by omega, ↓reduceIte]

/-- The argument, as the constructor's `CODECOPY` reads it. -/
theorem readBytes_initCodeFor_arg (o : Address) :
    readBytes (initCodeFor o) 1200 32 = Bytes.ofWord (Word.ofAddress o) := by
  rw [initCodeFor_eq]
  have h := readBytes_append_right creationCode (Bytes.ofWord (Word.ofAddress o))
  rwa [size_creationCode, Bytes.size_ofWord] at h

/-- Every jump destination of the creation code is valid in the init code for any owner. -/
theorem jumpTable_initCodeFor {jd : Array Bool} {o : Address}
    (hj : EvmLogic.Program.JumpTable jd (initCodeFor o)) (d : Nat)
    (h : d ∈ jumpDestList (initCode.size + 1) initCode.data.toList 0) (hd : d < 1200) :
    isValidJumpDest jd d = true := by
  rw [hj]
  apply isValidJumpDest_of_mem
  rw [size_initCodeFor]
  rw [size_initCode, initCode_eq, ByteArray.data_append, Array.toList_append] at h
  rw [initCodeFor_eq, ByteArray.data_append, Array.toList_append]
  exact mem_jumpDestList_append_left (c := creationCode.data.toList)
    (a := constructorArgs.data.toList) (a' := (Bytes.ofWord (Word.ofAddress o)).data.toList) h
    (by rw [Array.length_toList]; exact Nat.lt_of_lt_of_eq hd size_creationCode.symm)

end Verified.OpenZeppelin.Contracts.OzProxyAdmin
