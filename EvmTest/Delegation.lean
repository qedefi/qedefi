import EvmTest.TxSupport

/-!
# Tests for EIP-7702 delegation

Designators, authority recovery (authorization from the execution-spec-tests fixture
`prague/eip7702_set_code_tx/test_set_code_to_sstore.json`), and `setDelegation` state changes.
-/

open EvmLean EvmLean.Interpreter EvmTest

namespace EvmTest.DelegationTest

/-! ## Designators -/

#guard isValidDelegation (delegationCode 0x1234)
#guard (delegationCode 0x1234).size = 23
#guard delegatedAddress? (delegationCode 0xd38e1d3546bb5deee2fce227faf3889e86f388b8) =
  some 0xd38e1d3546bb5deee2fce227faf3889e86f388b8
#guard !isValidDelegation (hx "0xef0100")
#guard !isValidDelegation (delegationCode 0x1234 ++ hx "0x00")
#guard !isValidDelegation (hx "0xef0200" ++ Bytes.ofAddress 0x1234)
#guard delegatedAddress? (hx "0x6000") = none

/-! ## Authority recovery (real secp256k1) -/

/-- The fixture's authorization: chain id 0, delegate `0xd38e…88b8`, nonce 0. -/
def auth : Authorization :=
  { chainId := 0, address := 0xd38e1d3546bb5deee2fce227faf3889e86f388b8, nonce := 0,
    yParity := 0,
    r := 0x784bc8ae7bae310c059da9810fbc2e8f00325bfafe1e697583693503f8f3f944,
    s := 0x0f7d36e30482b4a314b00484ed184a0c6a63be83103351fee1382de33e7364dd }

/-- The signer recorded in the fixture. -/
def signer : Address := 0xa43a3eae84c091674a012b4550867766629ccdec

#guard recoverAuthority Crypto.real auth = some signer
-- Malformed signatures are rejected before recovery.
#guard recoverAuthority Crypto.real { auth with yParity := 2 } = none
#guard recoverAuthority Crypto.real { auth with s := Secp256k1.n / 2 + 1 } = none
#guard recoverAuthority Crypto.real { auth with r := 0 } = none
-- A different message recovers a different authority.
#guard recoverAuthority Crypto.real { auth with nonce := 1 } ≠ some signer

/-! ## `validate_authorization` and `set_delegation` -/

#guard (validateAuthorization Crypto.real 1 ∅ ∅ auth).1 = some signer
#guard (validateAuthorization Crypto.real 1 ∅ ∅ auth).2.contains signer
-- Chain id must be 0 or the chain's; the nonce must match the authority's.
#guard (validateAuthorization Crypto.real 1 ∅ ∅ { auth with chainId := 2 }).1 = none
#guard (validateAuthorization Crypto.real 1 ((∅ : World).insert signer { nonce := 1 }) ∅ auth).1
  = none
-- An authority with non-designator code is rejected (but warmed).
#guard validateAuthorization Crypto.real 1 ((∅ : World).insert signer { code := hx "0x00" }) ∅
  auth = (none, (∅ : AddressSet).insert signer)
-- A designator is fine.
#guard (validateAuthorization Crypto.real 1
  ((∅ : World).insert signer { code := delegationCode 5 }) ∅ auth).1 = some signer

/-- `setDelegation` on `w` with the fixture authorization. -/
def applied (w : World) (auths : List Authorization := [auth]) : World × AddressSet × Int :=
  setDelegation Crypto.real 1 auths w ∅

-- A new authority: code set, nonce bumped, no refund.
#guard (applied ∅).1.account signer = { nonce := 1, code := delegationCode auth.address }
#guard (applied ∅).2.2 = 0
-- An existing authority earns 25000 - 12500.
#guard (applied ((∅ : World).insert signer { balance := 1 })).2.2 = 12500
-- The second (now stale-nonce) copy of the same authorization is skipped.
#guard (applied ∅ [auth, auth]).1.account signer = { nonce := 1, code := delegationCode auth.address }

/-- A stand-in crypto whose recovery always yields the zero public key, so that every
well-formed authorization is signed by `fakeAuthority` (`fakeKeccak` of 64 zero bytes). -/
def anySigner : Crypto := { fakeCrypto with ecrecover := fun _ _ _ _ => some (Bytes.zeros 64) }

def fakeAuthority : Address := 64

#guard recoverAuthority anySigner auth = some fakeAuthority
-- Delegating to the zero address clears the code; the account survives through its nonce.
#guard (setDelegation anySigner 1 [{ auth with address := 0, nonce := 3 }]
  ((∅ : World).insert fakeAuthority { nonce := 3, code := delegationCode 7 }) ∅).1.account
  fakeAuthority = { nonce := 4 }
-- Authorizations apply in order: the second sees the first's nonce bump.
#guard (setDelegation anySigner 1 [auth, { auth with nonce := 1, address := 9 }] ∅ ∅).1.account
  fakeAuthority = { nonce := 2, code := delegationCode 9 }

end EvmTest.DelegationTest
