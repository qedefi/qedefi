import EvmLean.Interpreter
import EvmLean.Crypto.Real

/-! Contract-address derivation with the real Keccak (interpreter tests use a stand-in hash). -/

namespace EvmLean.AddressRealTest

open Interpreter

-- `CREATE`: well-known examples for sender 0x6ac7…dbf0.
#guard createAddress Crypto.real.keccak256 0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0 0
  = 0xcd234a471b72ba2f1ccf0a70fcaba648a5eecd8d
#guard createAddress Crypto.real.keccak256 0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0 1
  = 0x343c43a37d37dff08ae8c4a11544c718abb4fcf8

-- `CREATE2`: EIP-1014 examples 0 and 1.
#guard create2Address Crypto.real.keccak256 0 0 ⟨#[0]⟩ = 0x4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38
#guard create2Address Crypto.real.keccak256 0xdeadbeef00000000000000000000000000000000 0 ⟨#[0]⟩
  = 0xb928f69bb1d91cd65274e3c79d8986362984fda3

end EvmLean.AddressRealTest
