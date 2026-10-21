import EvmLean.Crypto.Real
import EvmLogic.Solidity.Abi
import EvmLogic.Solidity.Layout
import Examples.Solmate.Contracts.SolmateAssetData

/-!
# Tests for the Solidity layer

Selectors against the compiler's method identifiers, ABI encoding and decoding on concrete
calldata, and packed storage fields (`Field.get`/`Field.set`).
-/

namespace Examples.Tests.Solidity

open EvmLean EvmLean.Interpreter EvmLogic EvmLogic.Solidity Examples.Solmate

-- Every method identifier of the Solmate asset artifact is the selector of its signature.
#guard Examples.Solmate.Contracts.SolmateAsset.selectors.all fun (sig, sel) =>
  Abi.selector Crypto.real sig == sel.toNat

#guard Abi.selector Crypto.real "transfer(address,uint256)" == 0xa9059cbb

/-- Calldata of `transfer(0x…01, 5)`. -/
def cd : ByteArray := Abi.encodeCall 0xa9059cbb [Word.ofAddress 1, 5]

#guard cd.size == 68
#guard Abi.selectorOf cd == 0xa9059cbb
#guard Bytes.toWord (readBytes cd 4 32) == 1
#guard Bytes.toWord (readBytes cd 36 32) == 5
#guard Word.shr 224 (Bytes.toWord (readBytes cd 0 32)) == 0xa9059cbb
-- short calldata is zero-padded
#guard Abi.selectorOf ⟨#[0xa9, 0x05]⟩ == 0xa9050000

/-- `uint8 decimals` at offset 0, `bool paused` at offset 1, `address owner` at offset 2 of
slot 5. -/
def decimals : Field := ⟨5, 0, 1⟩
/-- `bool paused`. -/
def paused : Field := ⟨5, 1, 1⟩
/-- `address owner`. -/
def owner : Field := ⟨5, 2, 20⟩

/-- A slot word holding `decimals = 18`, `paused = true`, `owner = 0xabcd`. -/
def packed : Word := 0xabcd * 2 ^ 16 + 1 * 2 ^ 8 + 18

#guard decimals.get packed == 18
#guard paused.get packed == 1
#guard owner.get packed == 0xabcd
#guard decimals.get (decimals.set packed 6) == 6
#guard paused.get (decimals.set packed 6) == 1
#guard owner.get (decimals.set packed 6) == 0xabcd
-- values are truncated to the field's width
#guard decimals.get (decimals.set packed 0x1ff) == 0xff
#guard owner.get (paused.set packed 0) == 0xabcd
#guard decimals.set (decimals.set packed 6) 18 == packed

end Examples.Tests.Solidity
