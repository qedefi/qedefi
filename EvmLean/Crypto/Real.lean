import EvmLean.Machine.Types
import EvmLean.Crypto.Keccak
import EvmLean.Crypto.Sha256
import EvmLean.Crypto.Ripemd160
import EvmLean.Crypto.Blake2f
import EvmLean.Crypto.Secp256k1
import EvmLean.Crypto.Bn254
import EvmLean.Crypto.Kzg

/-!
# The real cryptography

`Crypto.real` bundles the pure-Lean implementations. The conformance tests run with it;
theorems should instead quantify over an arbitrary `Crypto`, so that hash functions stay
uninterpreted and collision-freedom is an explicit hypothesis rather than an axiom.
-/

namespace EvmLean

/-- The real cryptographic primitives (pure Lean, no FFI). -/
def Crypto.real : Crypto where
  keccak256 := Keccak.hash256
  sha256 := Sha256.hash
  ripemd160 := Ripemd160.hash
  blake2f := Blake2.compress
  ecrecover := Secp256k1.recover
  bn254Add := Bn254.add
  bn254Mul := Bn254.mul
  bn254Pairing := Bn254.pairingCheck
  kzgVerify := Kzg.verifyProof

end EvmLean
