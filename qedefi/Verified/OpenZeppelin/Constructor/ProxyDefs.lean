import Verified.OpenZeppelin.Constructor.ProxyInit
import Verified.Solmate.Constructor.Basic
import Verified.Solmate.Constructor.JumpDest

/-!
# The `TransparentUpgradeableProxy` init code for any implementation and owner

`initCodeFor logic o = creationCode ++ constructorArgsFor logic o` (`initCodeFor_eq`), the
arguments as the constructor's `CODECOPY` reads them (`readBytes_initCodeFor_args`), and the
jump destinations: those of the creation code, whatever the arguments (`jumpTable_initCodeFor`).
-/

namespace Verified.OpenZeppelin.Contracts.OzTransparentProxy
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity Verified.Solmate.Constructor

theorem size_constructorArgs : constructorArgs.size = 192 := by decide +kernel

theorem size_constructorArgsFor (logic o : Address) : (constructorArgsFor logic o).size = 192 := by
  simp only [constructorArgsFor, ByteArray.size_append, Bytes.size_ofWord, ByteArray.size_extract,
    size_constructorArgs, Nat.min_self]

theorem size_initCodeFor (logic o : Address) : (initCodeFor logic o).size = 3531 := by
  rw [initCodeFor, size_patchWords, size_initCode]

/-- **The init code of a proxy to `logic` with owner `o`.** -/
theorem initCodeFor_eq (logic o : Address) :
    initCodeFor logic o = creationCode ++ constructorArgsFor logic o := by
  apply Bytes.ext_getD
  · rw [size_initCodeFor, ByteArray.size_append, size_creationCode, size_constructorArgsFor]
  · intro j hj
    rw [size_initCodeFor] at hj
    rw [Bytes.getD_append, size_creationCode, initCodeFor]
    by_cases h1 : 3339 ≤ j ∧ j < 3339 + 32
    · rw [show [(3339, Word.ofAddress logic), (3371, Word.ofAddress o)] =
          [] ++ (3339, Word.ofAddress logic) :: [(3371, Word.ofAddress o)] from rfl,
        getD_patch_in _ _ _ _ _ (by rw [size_initCode]; omega) (by simp) j h1.1 h1.2]
      simp only [show ¬ j < 3339 by omega, ↓reduceIte, constructorArgsFor, Bytes.getD_append,
        Bytes.size_ofWord, show j - 3339 < 32 by omega]
    · by_cases h2 : 3371 ≤ j ∧ j < 3371 + 32
      · rw [show [(3339, Word.ofAddress logic), (3371, Word.ofAddress o)] =
            [(3339, Word.ofAddress logic)] ++ (3371, Word.ofAddress o) :: [] from rfl,
          getD_patch_in _ _ _ _ _ (by rw [size_initCode]; omega) (by simp) j h2.1 h2.2]
        simp only [show ¬ j < 3339 by omega, ↓reduceIte, constructorArgsFor, Bytes.getD_append,
          Bytes.size_ofWord, show ¬ j - 3339 < 32 by omega,
          show j - 3339 - 32 = j - 3371 by omega, show j - 3371 < 32 by omega]
      · have ho : ∀ o' ∈ [(3339, Word.ofAddress logic), (3371, Word.ofAddress o)].map Prod.fst,
            j < o' ∨ o' + 32 ≤ j := by
          simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false,
            forall_eq_or_imp, forall_eq]; omega
        rw [getD_patch_out _ _ j ho, initCode_eq, Bytes.getD_append, size_creationCode]
        by_cases hc : j < 3339
        · simp only [hc, ↓reduceIte]
        · simp only [hc, ↓reduceIte, constructorArgsFor, Bytes.getD_append, Bytes.size_ofWord,
            show ¬ j - 3339 < 32 by omega, show ¬ j - 3339 - 32 < 32 by omega,
            Bytes.getD_extract, show 64 + (j - 3339 - 32 - 32) = j - 3339 by omega,
            show j - 3339 < 192 by omega, ↓reduceIte]

/-- The calldata of the canonical `set(1)` (selector, then the word 1), as two words. -/
def dataWord0 : Word :=
  43871307414348465119245428467174558819278178421933205617286227672654652899328#256

def dataWord1 : Word := 26959946667150639794667015087019630673637144422540572481103610249216#256

theorem constructorArgs_tail : constructorArgs.extract 64 192 =
    Bytes.ofWord 0x60#256 ++ (Bytes.ofWord 0x24#256 ++ (Bytes.ofWord dataWord0 ++
      Bytes.ofWord dataWord1)) :=
  eq_of_data_toList_eq (by decide +kernel)

/-- The constructor arguments, as the init code's `CODECOPY` reads them. -/
theorem readBytes_initCodeFor_args (logic o : Address) :
    readBytes (initCodeFor logic o) 3339 192 =
      Bytes.ofWord (Word.ofAddress logic) ++ (Bytes.ofWord (Word.ofAddress o) ++
        (Bytes.ofWord 0x60#256 ++ (Bytes.ofWord 0x24#256 ++ (Bytes.ofWord dataWord0 ++
          Bytes.ofWord dataWord1)))) := by
  rw [initCodeFor_eq]
  have h := readBytes_append_right creationCode (constructorArgsFor logic o)
  rw [size_creationCode, size_constructorArgsFor] at h
  rw [h, constructorArgsFor, constructorArgs_tail]

/-- Every jump destination of the creation code is valid in the init code for any arguments. -/
theorem jumpTable_initCodeFor {jd : Array Bool} {logic o : Address}
    (hj : EvmLogic.Program.JumpTable jd (initCodeFor logic o)) (d : Nat)
    (h : d ∈ jumpDestList (initCode.size + 1) initCode.data.toList 0) (hd : d < 3339) :
    isValidJumpDest jd d = true := by
  rw [hj]
  apply isValidJumpDest_of_mem
  rw [size_initCodeFor]
  rw [size_initCode, initCode_eq, ByteArray.data_append, Array.toList_append] at h
  rw [initCodeFor_eq, ByteArray.data_append, Array.toList_append]
  exact mem_jumpDestList_append_left (c := creationCode.data.toList)
    (a := constructorArgs.data.toList) (a' := (constructorArgsFor logic o).data.toList) h
    (by rw [Array.length_toList]; exact Nat.lt_of_lt_of_eq hd size_creationCode.symm)

end Verified.OpenZeppelin.Contracts.OzTransparentProxy

namespace Verified.OpenZeppelin.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity Verified.OpenZeppelin.Contracts
open Verified.OpenZeppelin.Contracts.OzTransparentProxy

/-- The memory after the `CODECOPY` of the arguments, as word stores. -/
theorem write_args {X : Memory} (hX : X.size = 352) (logic o : Address) :
    X.write 160 (readBytes (initCodeFor logic o) 3339 192) =
      (((((X.storeWord 160 (Word.ofAddress logic)).storeWord 192 (Word.ofAddress o)).storeWord 224
        0x60#256).storeWord 256 0x24#256).storeWord 288 dataWord0).storeWord 320 dataWord1 := by
  rw [readBytes_initCodeFor_args]
  repeat' rw [Memory.write_ofWord_append_of_le]
  all_goals first
    | (simp only [ByteArray.size_append, Bytes.size_ofWord, Memory.size_storeWord, hX] <;> omega)
    | simp only [Nat.reduceAdd, Memory.write_ofWord]

end Verified.OpenZeppelin.Constructor
