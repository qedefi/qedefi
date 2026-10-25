import EvmTest.InterpreterUtil
import EvmLean.Crypto.Real
import EvmLogic.Solidity.Strings
import Verified.Solmate.Contracts.SolmateVaultData
import Verified.Solmate.Contracts.SolmateAssetData

/-!
# Tests for `string` storage and ABI encoding (`EvmLogic.Solidity.Strings`)

The compiled `name()`/`symbol()` getters, run with the real Keccak-256, return
`Abi.encodeString` of what `Str.decode` reads (short, empty and long strings) within
`Str.getterGas`, and revert on inconsistent slots.
-/

namespace QEDefiTest.Strings
open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity EvmTest EvmTest.InterpreterUtil
open Verified.Solmate Verified.Solmate.Contracts

-- The canonical deployment strings, in their short storage form.
#guard Str.shortWord "Solmate Vault".toUTF8 ==
  0x536f6c6d617465205661756c740000000000000000000000000000000000001a#256
#guard Str.shortWord "svSAST".toUTF8 ==
  0x737653415354000000000000000000000000000000000000000000000000000c#256
#guard Str.shortWord "Solmate Asset".toUTF8 ==
  0x536f6c6d6174652041737365740000000000000000000000000000000000001a#256
#guard Str.shortWord "SAST".toUTF8 ==
  0x5341535400000000000000000000000000000000000000000000000000000008#256

-- `Abi.encodeString`: offset, length, data padded to 32 bytes.
#guard Abi.encodeString "SAST".toUTF8 ==
  Bytes.ofWord 32 ++ Bytes.ofWord 4 ++
    Bytes.ofWord 0x5341535400000000000000000000000000000000000000000000000000000000#256
#guard (Abi.encodeString ByteArray.empty).size == 64
#guard (Abi.encodeString (Bytes.zeros 33)).size == 64 + 64

/-- A storage holding the given slots. -/
def storageOf (xs : List (Word × Word)) : Storage :=
  xs.foldl (fun s (k, v) => s.set k v) ∅

/-- A long string of `n` bytes (`0, 1, 2, …` modulo 256). -/
def longStr (n : Nat) : ByteArray := ⟨(List.range n).toArray.map (·.toUInt8)⟩

/-- The storage of `s` at slot `p` in the long form, for a given Keccak. -/
def longSlots (keccak : ByteArray → Word) (p : Word) (s : ByteArray) : List (Word × Word) :=
  (p, BitVec.ofNat 256 (2 * s.size + 1)) ::
    (List.range ((s.size + 31) / 32)).map fun j =>
      (keccak (Bytes.ofWord p) + BitVec.ofNat 256 j, Str.chunk s j)

/-- The test context with the real Keccak-256. -/
def ctxReal : Context := { crypto := Crypto.real }

/-- Run the getter with selector `sel` of `code` against `storage`. -/
def getter (code : ByteArray) (sel : Nat) (storage : Storage) (gas : Nat := 1000000) :
    Option MessageResult :=
  let w := (mkWorld code).insert contract { nonce := 1, balance := 1000, code, storage }
  runMsg w (callMsg contract code gas (data := Abi.encodeCall sel [])) ctxReal

/-- The getter returns `encodeString` of what `Str.decode` reads, within `Str.getterGas`. -/
def getterOk (code : ByteArray) (sel : Nat) (p : Word) (storage : Storage) : Bool :=
  let gas := 1000000
  match getter code sel storage gas, Str.decode Crypto.real storage.get p with
  | some r, some s =>
    r.success && r.output == Abi.encodeString s &&
      gas - r.gasLeft ≤ Str.getterGas (Str.slotLen (storage.get p))
  | some r, none => !r.success && r.reverted
  | none, _ => false

/-- The two storages used: `name` at slot 0, `symbol` at slot 1. -/
def namesShort : Storage :=
  storageOf [(0, Str.shortWord "Solmate Vault".toUTF8), (1, Str.shortWord "svSAST".toUTF8)]

/-- Long `name` (70 bytes) and `symbol` (32 bytes), data at the real Keccak of the slot. -/
def namesLong : Storage :=
  storageOf (longSlots Crypto.real.keccak256 0 (longStr 70) ++
    longSlots Crypto.real.keccak256 1 (longStr 32))

-- Decoding the storage forms.
#guard Str.decode Crypto.real namesShort.get 0 == some "Solmate Vault".toUTF8
#guard Str.decode Crypto.real namesShort.get 1 == some "svSAST".toUTF8
#guard Str.decode Crypto.real namesLong.get 0 == some (longStr 70)
#guard Str.decode Crypto.real namesLong.get 1 == some (longStr 32)
#guard Str.decode Crypto.real (storageOf []).get 0 == some ByteArray.empty
-- inconsistent: even word with length 40, odd word with length 3
#guard Str.decode Crypto.real (storageOf [(0, 80)]).get 0 == none
#guard Str.decode Crypto.real (storageOf [(0, 7)]).get 0 == none

-- The compiled getters (vault: `name()` `0x06fdde03`, `symbol()` `0x95d89b41`).
#guard getterOk SolmateVault.runtimeCode 0x06fdde03 0 namesShort
#guard getterOk SolmateVault.runtimeCode 0x95d89b41 1 namesShort
#guard getterOk SolmateVault.runtimeCode 0x06fdde03 0 namesLong
#guard getterOk SolmateVault.runtimeCode 0x95d89b41 1 namesLong
#guard getterOk SolmateVault.runtimeCode 0x06fdde03 0 (storageOf [])
#guard getterOk SolmateVault.runtimeCode 0x06fdde03 0 (storageOf [(0, 80)])
#guard getterOk SolmateVault.runtimeCode 0x06fdde03 0 (storageOf [(0, 7)])
#guard getterOk SolmateVault.runtimeCode 0x06fdde03 0
  (storageOf (longSlots Crypto.real.keccak256 0 (longStr 1000)))
-- and the asset's
#guard getterOk SolmateAsset.runtimeCode 0x06fdde03 0 namesShort
#guard getterOk SolmateAsset.runtimeCode 0x95d89b41 1 namesShort
#guard getterOk SolmateAsset.runtimeCode 0x06fdde03 0 namesLong
#guard getterOk SolmateAsset.runtimeCode 0x95d89b41 1 namesLong
#guard getterOk SolmateAsset.runtimeCode 0x06fdde03 0 (storageOf [(0, 80)])
-- the canonical outputs
#guard (getter SolmateVault.runtimeCode 0x06fdde03 namesShort).map (·.output) ==
  some (Abi.encodeString "Solmate Vault".toUTF8)
#guard (getter SolmateVault.runtimeCode 0x95d89b41 namesShort).map (·.output) ==
  some (Abi.encodeString "svSAST".toUTF8)

end QEDefiTest.Strings
