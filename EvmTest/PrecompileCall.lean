import EvmLean.Crypto.Real
import EvmLogic.Program.PrecompileCallEcrecover

/-!
# Tests for `ECRECOVER` on four words (`EvmLeanProofs.Program.PrecompileCallEcrecover`)

With the executable cryptography (`Crypto.real`): `ecrecoverAddress?` recovers the signer of
the classic test vector (`0x7156…8c8a`), rejects bad `v`, `r`, `s`, and agrees with the
precompile (`Precompile.ecrecover`) on the encoded four-word input, as `ecrecover_words`
states for every `Crypto`.
-/

namespace EvmLeanTest.PrecompileCall

open EvmLean EvmLean.Program

/-- The digest of the test vector. -/
def hash : Word := 0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3#256
/-- `v`. -/
def v : Word := 28#256
/-- `r`. -/
def r : Word := 0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608#256
/-- `s`. -/
def s : Word := 0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada#256
/-- The signer. -/
def signer : Address := 0x7156526fbd7a3c72969b54f64e42c10fbb768c8a#160

/-- The four-word input. -/
def input (v : Word) : ByteArray :=
  Bytes.ofWord hash ++ (Bytes.ofWord v ++ (Bytes.ofWord r ++ Bytes.ofWord s))

#guard ecrecoverAddress? Crypto.real hash v r s == some signer
#guard ecrecoverAddress? Crypto.real hash 27#256 r s != some signer
#guard ecrecoverAddress? Crypto.real hash 0#256 r s == none
#guard ecrecoverAddress? Crypto.real hash v 0#256 s == none
#guard (Precompile.ecrecover Crypto.real (input v) 3000).output ==
  ecrecoverOutput Crypto.real hash v r s
#guard (Precompile.ecrecover Crypto.real (input 0#256) 5000).output ==
  ecrecoverOutput Crypto.real hash 0#256 r s
#guard (Precompile.ecrecover Crypto.real (input v) 5000).gasLeft == 2000
#guard (Precompile.run Crypto.real .cancun 1 (input v) 3000).output == Bytes.ofWord (Word.ofAddress signer)

end EvmLeanTest.PrecompileCall
