import Verified.Solmate.Constructor.VaultInit
import Verified.Solmate.Constructor.Basic
import Verified.Solmate.Constructor.JumpDest
import Verified.Solmate.Contracts.Deploy

/-!
# The `MockERC4626` constructor: arguments and checkpoints

The init code of a vault over `asset` (`initCodeFor asset = creationCode ++
constructorArgsFor asset`), its arguments as words (`readBytes_initCodeFor_args`), and the
values the constructor computes.
-/

namespace Verified.Solmate.Contracts.SolmateVault
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity

theorem size_creationCode' : creationCode.size = 6474 := size_creationCode

theorem size_constructorArgsFor (asset : Address) : (constructorArgsFor asset).size = 224 := by
  simp only [constructorArgsFor, ByteArray.size_append, Bytes.size_ofWord, ByteArray.size_extract,
    size_constructorArgs, Nat.min_self]

/-- **The init code of a vault over `asset`** is the creation code followed by the ABI encoding
of `(asset, "Solmate Vault", "svSAST")`. -/
theorem initCodeFor_eq (asset : Address) :
    initCodeFor asset = creationCode ++ constructorArgsFor asset := by
  apply Bytes.ext_getD
  · rw [initCodeFor, size_patchWords, size_initCode, ByteArray.size_append, size_creationCode,
      size_constructorArgsFor]
  · intro j hj
    rw [initCodeFor, size_patchWords, size_initCode] at hj
    rw [Bytes.getD_append, size_creationCode, initCodeFor]
    by_cases hw : 6474 ≤ j ∧ j < 6474 + 32
    · rw [show [(6474, Word.ofAddress asset)] = [] ++ (6474, Word.ofAddress asset) :: [] from rfl,
        Verified.Solmate.Constructor.getD_patch_in _ _ _ _ _
          (by rw [size_initCode]; omega) (by simp) j hw.1 hw.2]
      simp only [show ¬ j < 6474 by omega, ↓reduceIte, constructorArgsFor, Bytes.getD_append,
        Bytes.size_ofWord, show j - 6474 < 32 by omega]
    · have ho : ∀ o ∈ [(6474, Word.ofAddress asset)].map Prod.fst, j < o ∨ o + 32 ≤ j := by
        simp only [List.map_cons, List.map_nil, List.mem_singleton, forall_eq]; omega
      rw [Verified.Solmate.Constructor.getD_patch_out _ _ j ho, initCode_eq, Bytes.getD_append,
        size_creationCode]
      by_cases hc : j < 6474
      · simp only [hc, ↓reduceIte]
      · simp only [hc, ↓reduceIte, constructorArgsFor, Bytes.getD_append, Bytes.size_ofWord,
          show ¬ j - 6474 < 32 by omega, Bytes.getD_extract,
          show 32 + (j - 6474 - 32) = j - 6474 by omega, show j - 6474 < 224 by omega]

/-- `"Solmate Vault"`, left-aligned in a word. -/
def nameWord : Word :=
  37738834794104325423618568217867347572636789375017625764301338977616208592896#256

/-- `"svSAST"`, left-aligned in a word. -/
def symbolWord : Word :=
  52225040146838276799603043087864185790795666495381553142803607270290628804608#256

theorem constructorArgs_tail : constructorArgs.extract 32 224 =
    Bytes.ofWord 0x60#256 ++ (Bytes.ofWord 0xa0#256 ++ (Bytes.ofWord 0x0d#256 ++
      (Bytes.ofWord nameWord ++ (Bytes.ofWord 0x06#256 ++ Bytes.ofWord symbolWord)))) :=
  eq_of_data_toList_eq (by decide +kernel)

/-- The constructor arguments, as the init code's `CODECOPY` reads them. -/
theorem readBytes_initCodeFor_args (asset : Address) :
    readBytes (initCodeFor asset) 6474 224 =
      Bytes.ofWord (Word.ofAddress asset) ++ (Bytes.ofWord 0x60#256 ++ (Bytes.ofWord 0xa0#256 ++
        (Bytes.ofWord 0x0d#256 ++ (Bytes.ofWord nameWord ++ (Bytes.ofWord 0x06#256 ++
          Bytes.ofWord symbolWord))))) := by
  rw [initCodeFor_eq]
  have h := readBytes_append_right creationCode (constructorArgsFor asset)
  rw [size_creationCode, size_constructorArgsFor] at h
  rw [h, constructorArgsFor, constructorArgs_tail]

theorem size_initCodeFor (asset : Address) : (initCodeFor asset).size = 6698 := by
  rw [initCodeFor, size_patchWords, size_initCode]

/-- Every jump destination of the creation code is valid in the init code of a vault over any
`asset`. -/
theorem jumpDest_initCodeFor (asset : Address) (d : Nat)
    (h : d ∈ jumpDestList (initCode.size + 1) initCode.data.toList 0) (hd : d < 6474) :
    isValidJumpDest (validJumpDests (initCodeFor asset)) d = true := by
  apply isValidJumpDest_of_mem
  rw [size_initCodeFor]
  rw [size_initCode, initCode_eq, ByteArray.data_append, Array.toList_append] at h
  rw [initCodeFor_eq, ByteArray.data_append, Array.toList_append]
  exact mem_jumpDestList_append_left (c := creationCode.data.toList)
    (a := constructorArgs.data.toList) (a' := (constructorArgsFor asset).data.toList) h
    (by rw [Array.length_toList]; exact Nat.lt_of_lt_of_eq hd size_creationCode.symm)

theorem jumpTable_initCodeFor {jd : Array Bool} {asset : Address}
    (hj : EvmLogic.Program.JumpTable jd (initCodeFor asset)) (d : Nat)
    (h : d ∈ jumpDestList (initCode.size + 1) initCode.data.toList 0) (hd : d < 6474) :
    isValidJumpDest jd d = true := by
  rw [hj]; exact jumpDest_initCodeFor asset d h hd

end Verified.Solmate.Contracts.SolmateVault

namespace Verified.Solmate.Constructor.Vault
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity Verified.Solmate.Contracts
open Verified.Solmate.Contracts.SolmateVault

/-- The memory after the `CODECOPY` of the arguments, as word stores. -/
theorem write_args {X : Memory} (hX : X.size = 480) (asset : Address) :
    X.write 256 (readBytes (initCodeFor asset) 6474 224) =
      ((((((X.storeWord 256 (Word.ofAddress asset)).storeWord 288 0x60#256).storeWord 320
        0xa0#256).storeWord 352 0x0d#256).storeWord 384 nameWord).storeWord 416
        0x06#256).storeWord 448 symbolWord := by
  rw [readBytes_initCodeFor_args]
  repeat' rw [Memory.write_ofWord_append_of_le]
  all_goals first
    | (simp only [ByteArray.size_append, Bytes.size_ofWord, Memory.size_storeWord, hX] <;> omega)
    | simp only [Nat.reduceAdd, Memory.write_ofWord]

theorem toWord_name :
    Bytes.toWord ((Bytes.ofWord nameWord).extract 0 13 ++ Bytes.zeros 19) = nameWord := by
  decide +kernel

theorem toWord_symbol :
    Bytes.toWord ((Bytes.ofWord symbolWord).extract 0 6 ++ Bytes.zeros 26) = symbolWord := by
  decide +kernel

/-- The word solc stores to call `decimals()`: the selector `0x313ce567`, left-aligned. -/
def decimalsSelectorWord : Word :=
  22270923681254677845691103109158760375340177724800803888364822332811285364736#256

/-- Memory at `0x0068` (before the `GAS` of the call to `asset.decimals()`): the decoded name
and symbol, and the call's input at `0x260`. -/
def MemA (M : Memory) : Prop :=
  M.size = 640 ∧ M.loadWord 64 = 608#256 ∧ M.loadWord 480 = 0x0d#256 ∧
    M.loadWord 512 = nameWord ∧ M.loadWord 544 = 0x06#256 ∧ M.loadWord 576 = symbolWord ∧
    M.loadWord 608 = decimalsSelectorWord ∧
    M.read 608 4 = (Bytes.ofWord decimalsSelectorWord).extract 0 4

/-- The machine at `0x0068`, reached from `m`. -/
def At104 (asset : Address) (m m' : Machine) : Prop :=
  m'.frame.code = initCodeFor asset ∧ EvmLogic.Program.JumpTable m'.frame.jumpDests (initCodeFor asset) ∧
    m'.frame.pc = 104 ∧
    m'.frame.stack = [Word.ofAddress asset, 608#256, 4#256, 608#256, 32#256, 612#256,
      826074471#256, Word.ofAddress asset, 544#256, 480#256, 544#256, 480#256,
      Word.ofAddress asset, 544#256, 480#256, Word.ofAddress asset] ∧
    MemA m'.frame.memory ∧
    m'.world = (m.world.sstore m.frame.msg.currentTarget 6#256 0#256).sstore
      m.frame.msg.currentTarget 7#256 0#256 ∧
    m.frame.gasLeft ≤ m'.frame.gasLeft + 50000 ∧ m'.frame.gasLeft ≤ m.frame.gasLeft

/-- Slot 0 after the constructor: `"Solmate Vault"` in Solidity's short-string encoding. -/
def nameSlot : Word := 37738834794104325423618568217867347572636789375017625764301338977616208592922#256

/-- Slot 1 after the constructor: `"svSAST"` in Solidity's short-string encoding. -/
def symbolSlot : Word :=
  52225040146838276799603043087864185790795666495381553142803607270290628804620#256

/-- The `INITIAL_DOMAIN_SEPARATOR` the constructor computes at `self` on chain `chainId`. -/
def domainSeparator (crypto : Crypto) (chainId : Nat) (self : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord
      63076024560530113402979550242307453568063438748328787417531900361828837441551#256 ++
    (Bytes.ofWord (crypto.keccak256 ((Bytes.ofWord nameWord).extract 0 13)) ++
      (Bytes.ofWord
          90743482286830539503240959006302832933333810038750515972785732718729991261126#256 ++
        (Bytes.ofWord (ofNat chainId) ++ Bytes.ofWord (Word.ofAddress self)))))

/-- The immutables the constructor stores at `self` on chain `chainId`, over `asset` whose
`decimals()` returned `dec`. -/
def immutables (crypto : Crypto) (chainId : Nat) (self asset : Address) (dec : Word) :
    SolmateVault.Immutables where
  initialChainId := ofNat chainId
  initialDomainSeparator := domainSeparator crypto chainId self
  asset := asset
  decimals := dec

theorem selectorOf_decimals :
    Abi.selectorOf ((Bytes.ofWord decimalsSelectorWord).extract 0 4) = 0x313ce567 := by
  decide +kernel

end Verified.Solmate.Constructor.Vault
