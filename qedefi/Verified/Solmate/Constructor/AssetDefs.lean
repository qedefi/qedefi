import Verified.Solmate.Constructor.AssetInit
import Verified.Solmate.Constructor.Basic
import Verified.Solmate.Contracts.Deploy
import EvmLogic.Program.Summary
import EvmLogic.Solidity.Memory

/-!
# The `MockERC20` constructor: arguments and checkpoints

The canonical deployment's constructor arguments as words (`readBytes_initCode_args`,
`write_args`), and the machine states at which the proof of the constructor is split
(`At399`, …): the symbolic executor runs one segment per theorem.
-/

namespace Verified.Solmate.Constructor
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLogic.Tactic
open Verified.Solmate.Contracts

namespace Asset

/-- `"Solmate Asset"`, left-aligned in a word (the ABI encoding of the name's bytes). -/
def nameWord : Word := 0x536f6c6d61746520417373657400000000000000000000000000000000000000#256

/-- `"SAST"`, left-aligned in a word. -/
def symbolWord : Word := 0x5341535400000000000000000000000000000000000000000000000000000000#256

theorem size_constructorArgs : SolmateAsset.constructorArgs.size = 224 := by decide +kernel

theorem constructorArgs_eq : SolmateAsset.constructorArgs =
    Bytes.ofWord 0x60#256 ++ (Bytes.ofWord 0xa0#256 ++ (Bytes.ofWord 0x12#256 ++ (Bytes.ofWord 0x0d#256 ++
      (Bytes.ofWord nameWord ++ (Bytes.ofWord 0x04#256 ++ Bytes.ofWord symbolWord))))) :=
  eq_of_data_toList_eq (by decide +kernel)

/-- The constructor arguments, as the init code's `CODECOPY` reads them. -/
theorem readBytes_initCode_args : readBytes SolmateAsset.initCode 3885 224 =
    Bytes.ofWord 0x60#256 ++ (Bytes.ofWord 0xa0#256 ++ (Bytes.ofWord 0x12#256 ++ (Bytes.ofWord 0x0d#256 ++
      (Bytes.ofWord nameWord ++ (Bytes.ofWord 0x04#256 ++ Bytes.ofWord symbolWord))))) := by
  rw [SolmateAsset.initCode_eq, ← constructorArgs_eq]
  have h := readBytes_append_right SolmateAsset.creationCode SolmateAsset.constructorArgs
  rwa [SolmateAsset.size_creationCode, size_constructorArgs] at h

/-- The memory after the `CODECOPY` of the arguments, as word stores. -/
theorem write_args {X : Memory} (hX : X.size = 448) :
    X.write 224 (readBytes SolmateAsset.initCode 3885 224) =
      ((((((X.storeWord 224 0x60#256).storeWord 256 0xa0#256).storeWord 288 0x12#256).storeWord 320
        0x0d#256).storeWord 352 nameWord).storeWord 384 0x04#256).storeWord 416 symbolWord := by
  rw [readBytes_initCode_args]
  repeat' rw [Memory.write_ofWord_append_of_le]
  all_goals first
    | (simp only [ByteArray.size_append, Bytes.size_ofWord, Memory.size_storeWord, hX] <;> omega)
    | simp only [Nat.reduceAdd, Memory.write_ofWord]

theorem toWord_name :
    Bytes.toWord ((Bytes.ofWord nameWord).extract 0 13 ++ Bytes.zeros 19) = nameWord := by
  decide +kernel

theorem toWord_symbol :
    Bytes.toWord ((Bytes.ofWord symbolWord).extract 0 4 ++ Bytes.zeros 28) = symbolWord := by
  decide +kernel

/-- Slot 0 after the constructor: `"Solmate Asset"` in Solidity's short-string encoding. -/
def nameSlot : Word := 37738834794104325423105373015100533266455423366588237796686126512645985009690#256

/-- Slot 1 after the constructor: `"SAST"` in Solidity's short-string encoding. -/
def symbolSlot : Word :=
  37657386601204008873856919470099658630592694321674888489937959870363441561608#256

/-- `keccak256("EIP712Domain(…)")`, as the init code pushes it. -/
def domainTypehash : Word :=
  63076024560530113402979550242307453568063438748328787417531900361828837441551#256

/-- `keccak256("1")`, as the init code pushes it. -/
def versionHash : Word :=
  90743482286830539503240959006302832933333810038750515972785732718729991261126#256

/-- The `INITIAL_DOMAIN_SEPARATOR` the constructor computes at `self` on chain `chainId`. -/
def domainSeparator (crypto : Crypto) (chainId : Nat) (self : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord domainTypehash ++
    (Bytes.ofWord (crypto.keccak256 ((Bytes.ofWord nameWord).extract 0 13)) ++
      (Bytes.ofWord versionHash ++ (Bytes.ofWord (ofNat chainId) ++
        Bytes.ofWord (Word.ofAddress self)))))

/-- The immutables the constructor stores at `self` on chain `chainId`. -/
def immutables (crypto : Crypto) (chainId : Nat) (self : Address) : SolmateAsset.Immutables where
  initialChainId := ofNat chainId
  initialDomainSeparator := domainSeparator crypto chainId self
  decimals := 18#256

end Asset


/-- Memory at `0x018f` (before the `MCOPY` of the symbol): the decoded arguments and the name. -/
def MemA (M : Memory) : Prop :=
  M.size = 544 ∧ M.loadWord 64 = 576#256 ∧
    M.read 416 4 = (Bytes.ofWord Asset.symbolWord).extract 0 4 ∧ M.loadWord 288 = 0x12#256 ∧
    M.loadWord 448 = 0x0d#256 ∧ M.loadWord 480 = Asset.nameWord ∧ M.loadWord 512 = 4#256

/-- The machine at `0x018f`, reached from `m`. -/
def At399 (m m' : Machine) : Prop :=
  m'.frame.code = SolmateAsset.initCode ∧ JumpTable m'.frame.jumpDests SolmateAsset.initCode ∧
    m'.frame.pc = 399 ∧
    m'.frame.stack = [544#256, 416#256, 4#256, 512#256, 4#256, 0#256, 384#256, 448#256, 509#256,
      160#256, 0#256, 0#256, 448#256, 224#256, 448#256, 46#256] ∧
    MemA m'.frame.memory ∧ m'.world = m.world ∧ m.frame.gasLeft ≤ m'.frame.gasLeft + 3000 ∧
    m'.frame.gasLeft ≤ m.frame.gasLeft


end Verified.Solmate.Constructor
