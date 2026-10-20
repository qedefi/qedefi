import Defi.ERC20.Permit
import EvmLogic.Program.PrecompileCallEcrecover
import EvmLogic.Solidity.SharesExtraErc20
import EvmLogic.Solidity.ERC20

/-!
# EIP-2612 as the bytecode computes it

The specification side of the `permit` refinement: every value the compiled Solmate `ERC20`
(both the vault's share token and the asset) computes for `permit`, `DOMAIN_SEPARATOR()` and
`nonces(owner)`, as an explicit expression in the context's `Crypto` (`crypto.keccak256`,
`crypto.ecrecover`). Nothing here assumes anything about `Crypto`.

* `PERMIT_TYPEHASH`, `DOMAIN_TYPEHASH`, `VERSION_HASH`: the three `keccak256` constants that
  solc folded into the bytecode (`keccak256("Permit(address owner,…)")`,
  `keccak256("EIP712Domain(…)")`, `keccak256("1")`). They are literals of the code, *not*
  `crypto.keccak256` of the strings: for the real Keccak they agree (checked by
  `lake exe difftest`), for an arbitrary `Crypto` the code still uses these words.
* `structHash`, `digest`: `keccak256(abi.encode(PERMIT_TYPEHASH, owner, spender, value, nonce,
  deadline))` and `keccak256("\x19\x01" ‖ domainSeparator ‖ structHash)`.
* `SigOk`: the signature check of `permit`: `ECRECOVER` (`ecrecoverAddress?`, exactly what the
  precompile at `0x01` returns for the four words the code passes) recovers `owner`, and
  `owner ≠ 0`.
* `domainSeparator`: `DOMAIN_SEPARATOR()`: the immutable `INITIAL_DOMAIN_SEPARATOR` while
  `block.chainid` is the immutable `INITIAL_CHAIN_ID`, otherwise `computedDomainSeparator`,
  which hashes the token's `name` from storage slot 0. The recomputation is covered for names
  stored in Solidity's short-string form (`ShortString`: fewer than 32 bytes, as both canonical
  names are); a long name (more than 31 bytes, stored out of place) is not covered.
* `PermitValid`: when `permit` succeeds: `v < 256` (the ABI decoder of `uint8 v`), the deadline
  has not passed, and `SigOk` at the owner's current nonce.
* `nonceSlot`, `permitWorld`: the storage effect of a successful `permit` (the nonce
  increment, then the allowance write).
* `SigUnforgeable`: the cryptographic assumption under which `SigOk` means "the owner
  signed". It is **not** used by any theorem; see `PERMIT.md`.
-/

namespace EvmLeanSpecs.Refinement.Permit

open EvmLean EvmLean.Program EvmLean.Interpreter EvmLean.Solidity

/-! ## Constants of the bytecode -/

/-- `keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256
deadline)")`, as compiled into the code. -/
def PERMIT_TYPEHASH : Word :=
  0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9#256

/-- `keccak256("EIP712Domain(string name,string version,uint256 chainId,address
verifyingContract)")`, as compiled into the code. -/
def DOMAIN_TYPEHASH : Word :=
  0x8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f#256

/-- `keccak256("1")` (the EIP-712 version), as compiled into the code. -/
def VERSION_HASH : Word :=
  0xc89efdaa54c0f20c7adf612882df0950f5a951637e0307cdcb4c672f298b8bc6#256

/-- The two-byte EIP-191 prefix `"\x19\x01"` of an EIP-712 digest. -/
def eip712Prefix : ByteArray := ⟨#[0x19, 0x01]⟩

/-! ## The EIP-712 message -/

/-- `keccak256(abi.encode(PERMIT_TYPEHASH, owner, spender, value, nonce, deadline))`. -/
def structHash (crypto : Crypto) (owner spender : Address) (value nonce deadline : Word) : Word :=
  crypto.keccak256 (Bytes.ofWord PERMIT_TYPEHASH ++ (Bytes.ofWord (Word.ofAddress owner) ++
    (Bytes.ofWord (Word.ofAddress spender) ++ (Bytes.ofWord value ++ (Bytes.ofWord nonce ++
      Bytes.ofWord deadline)))))

/-- `keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash))`. -/
def digest (crypto : Crypto) (domainSep sh : Word) : Word :=
  crypto.keccak256 (eip712Prefix ++ (Bytes.ofWord domainSep ++ Bytes.ofWord sh))

/-- **The signature check of `permit`**: `owner ≠ 0` and `ecrecover(digest, v, r, s)` (the
precompile at `0x01`, for this `crypto`) recovers `owner`, where the digest is that of the
permit message at nonce `nonce` under the domain separator `domainSep`. -/
def SigOk (crypto : Crypto) (domainSep : Word) (owner spender : Address)
    (value nonce deadline v r s : Word) : Prop :=
  owner ≠ 0 ∧
    ecrecoverAddress? crypto (digest crypto domainSep (structHash crypto owner spender value nonce
      deadline)) v r s = some owner

/-! ## The domain separator -/

/-- The length field of a short string stored in slot word `slot` (`(slot >> 1) & 0x7f`). -/
def shortLength (slot : Word) : Word := Word.shr 1#256 slot &&& 127#256

/-- The storage word of a `string` holds it in Solidity's short form: the low bit is clear and
the length (`shortLength`, from the low byte) is below 32. -/
def ShortString (slot : Word) : Prop := slot &&& 1#256 = 0#256 ∧ (shortLength slot).toNat < 32

/-- The bytes of a short string, as the code copies them to memory (the slot word with its low
byte cleared, truncated to the length). -/
def shortStringBytes (slot : Word) : ByteArray :=
  (Bytes.ofWord (slot &&& ~~~255#256)).extract 0 (shortLength slot).toNat

/-- `computeDomainSeparator()` for a short `name` stored as `nameSlot`:
`keccak256(abi.encode(DOMAIN_TYPEHASH, keccak256(bytes(name)), VERSION_HASH, chainid,
address(this)))`. -/
def computedDomainSeparator (crypto : Crypto) (nameSlot chainId : Word) (self : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord DOMAIN_TYPEHASH ++
    (Bytes.ofWord (crypto.keccak256 (shortStringBytes nameSlot)) ++ (Bytes.ofWord VERSION_HASH ++
      (Bytes.ofWord chainId ++ Bytes.ofWord (Word.ofAddress self)))))

/-- **`DOMAIN_SEPARATOR()`**: the immutable separator on the deployment chain, else the
recomputed one (`chainId` is `block.chainid` as a word, `nameSlot` the word in slot 0). -/
def domainSeparator (crypto : Crypto) (initialChainId initialDomainSeparator chainId nameSlot : Word)
    (self : Address) : Word :=
  if chainId = initialChainId then initialDomainSeparator
  else computedDomainSeparator crypto nameSlot chainId self

/-- The cases of `DOMAIN_SEPARATOR()` the theorems cover: on the deployment chain (any name),
or a short name. -/
def DomainCase (initialChainId chainId nameSlot : Word) : Prop :=
  chainId = initialChainId ∨ ShortString nameSlot

/-! ## `permit` -/

/-- The slot of `nonces[a]` (slot 5 of Solmate's `ERC20`). -/
def nonceSlot (crypto : Crypto) (a : Address) : Word := mappingSlot crypto (Word.ofAddress a) 5#256

/-- **When `permit` succeeds**, at the owner's current nonce `nonce`: `v` is a `uint8` (the ABI
decoder reverts otherwise), the deadline is not before the block timestamp, and the signature
check `SigOk` passes. -/
def PermitValid (crypto : Crypto) (domainSep : Word) (timestamp : Nat) (owner spender : Address)
    (value deadline v r s nonce : Word) : Prop :=
  v.toNat < 256 ∧ (ofNat timestamp).toNat ≤ deadline.toNat ∧
    SigOk crypto domainSep owner spender value nonce deadline v r s

/-- The world after a successful `permit`, as the code writes it: `nonces[owner]++` (word
arithmetic), then `allowance[owner][spender] = value`. -/
def permitWorld (crypto : Crypto) (w : World) (token owner spender : Address) (value : Word) :
    World :=
  (w.sstore token (nonceSlot crypto owner) (w.sload token (nonceSlot crypto owner) + 1#256)).sstore
    token (Erc20.allowanceSlot crypto Erc20.Layout.solmate owner spender) value

/-- Calldata of `permit(owner, spender, value, deadline, v, r, s)`, described by what the ABI
decoder reads (so `Abi.encodeCall 0xd505accf [...]` and calldata assembled by a calling
contract both qualify; `permitCall_encodeCall`). -/
structure PermitCall (data : ByteArray) (owner spender : Address) (value deadline v r s : Word) :
    Prop where
  /-- The selector of `permit(address,address,uint256,uint256,uint8,bytes32,bytes32)`. -/
  selector : Abi.selectorOf data = 0xd505accf
  /-- Seven argument words. -/
  size : 228 ≤ data.size
  /-- `owner`. -/
  arg0 : Bytes.toWord (readBytes data 4 32) = Word.ofAddress owner
  /-- `spender`. -/
  arg1 : Bytes.toWord (readBytes data 36 32) = Word.ofAddress spender
  /-- `value`. -/
  arg2 : Bytes.toWord (readBytes data 68 32) = value
  /-- `deadline`. -/
  arg3 : Bytes.toWord (readBytes data 100 32) = deadline
  /-- `v` (a word; the decoder checks that it is a `uint8`). -/
  arg4 : Bytes.toWord (readBytes data 132 32) = v
  /-- `r`. -/
  arg5 : Bytes.toWord (readBytes data 164 32) = r
  /-- `s`. -/
  arg6 : Bytes.toWord (readBytes data 196 32) = s

/-- Calldata of `permit`. -/
def permitData (owner spender : Address) (value deadline v r s : Word) : ByteArray :=
  Abi.encodeCall 0xd505accf [Word.ofAddress owner, Word.ofAddress spender, value, deadline, v, r, s]

/-- ABI-encoded `permit` calldata is a `PermitCall`. -/
theorem permitCall_encodeCall (owner spender : Address) (value deadline v r s : Word) :
    PermitCall (permitData owner spender value deadline v r s) owner spender value deadline v r s :=
  ⟨by rw [permitData, Abi.selectorOf_encodeCall],
   by rw [permitData, Abi.size_encodeCall]; simp,
   Abi.calldataload_encodeCall _ _ 0 (by simp), Abi.calldataload_encodeCall _ _ 1 (by simp),
   Abi.calldataload_encodeCall _ _ 2 (by simp), Abi.calldataload_encodeCall _ _ 3 (by simp),
   Abi.calldataload_encodeCall _ _ 4 (by simp), Abi.calldataload_encodeCall _ _ 5 (by simp),
   Abi.calldataload_encodeCall _ _ 6 (by simp)⟩

/-! ## What is *not* assumed -/

/-- **Unforgeability of ECDSA signatures (documentation only).** For a given owner, nobody
without the owner's key can produce `(v, r, s)` that recover to the owner for a message the
owner did not sign. This is a computational assumption about secp256k1 and Keccak; it cannot be
stated as a property of a single `crypto` function without a model of adversaries and keys,
so this predicate fixes only its shape: a set `Signed owner hash` of the digests the owner
signed, and the claim that every signature recovering to `owner` is for such a digest. **No
theorem uses it**: the refinement theorems hold for every `Crypto` and say exactly *when*
`permit` succeeds (`SigOk`); a user who wants "only the owner can grant an allowance by
`permit`" adds `SigUnforgeable crypto Signed` as a hypothesis. -/
def SigUnforgeable (crypto : Crypto) (Signed : Address → Word → Prop) : Prop :=
  ∀ owner hash v r s, ecrecoverAddress? crypto hash v r s = some owner → Signed owner hash

/-- Under `SigUnforgeable`, a valid permit was signed by its owner (for the permit's digest). -/
theorem signed_of_sigOk {crypto : Crypto} {Signed : Address → Word → Prop}
    (hu : SigUnforgeable crypto Signed) {ds : Word} {owner spender : Address}
    {value nonce deadline v r s : Word}
    (h : SigOk crypto ds owner spender value nonce deadline v r s) :
    Signed owner (digest crypto ds (structHash crypto owner spender value nonce deadline)) :=
  hu _ _ _ _ _ h.2

end EvmLeanSpecs.Refinement.Permit
