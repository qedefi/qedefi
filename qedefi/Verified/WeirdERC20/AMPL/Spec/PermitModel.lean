import Verified.WeirdERC20.AMPL.Spec.PermitMem
import QEDefi.ERC4626.Logs

/-!
# AMPL's `permit` as its code computes it

`UFragments.permit(owner, spender, value, deadline, v, r, s)` (solc 0.7.6) requires
`block.timestamp ≤ deadline` and `owner == ecrecover(digest, v, r, s)`. It then increments
`_nonces[owner]` with `SafeMath`, sets the allowance and logs `Approval`. The digest is EIP-712
over `DOMAIN_SEPARATOR()`, which is **recomputed on every call** from `name()`: the string in
slot 51, copied as solc 0.7 copies a storage string.

* `nameLen07`: the length solc 0.7 reads from the slot word: `(S & 0xff) / 2` when even,
  `S / 2` when odd. There is no consistency check (solc 0.8's `Panic(0x22)`).
* `nameBytes07`: the bytes hashed. Empty for length `0`. Up to 31 bytes: the slot word with its
  low byte cleared, cut to the length. From 32 bytes: the data words at `keccak256(51) + i`, cut
  to the length (`Str.longData`).
* `amplDs`: `keccak256(abi.encode(EIP712_DOMAIN, keccak256(name), keccak256("1"), chainid,
  this))`, with the code's literal type hashes.
* `amplRec m n`: **the signature recovery of AMPL's `permit`** at nonce `n`: the address
  `ecrecover` returns for the digest of the frame's calldata (`v` masked to its low byte, as
  the decoder does), `0` when recovery fails. At the call-depth limit the `STATICCALL` to
  `0x01` fails and `permit` reverts whatever the owner, so `amplRec` is then an address other
  than the owner (`1` for the owner `0`, else `0`). AMPL compares the recovered address with the
  owner without rejecting `0`, so an invalid signature passes for the owner `0`.
-/

namespace Verified.WeirdERC20.AMPL.Spec.Malformed
open EvmLean EvmLogic EvmLogic.Program EvmLogic.Solidity EvmLean.Interpreter
open Verified.WeirdERC20.AMPL.Spec QEDefi.ERC4626

/-- `keccak256("Permit(…)")`, a literal of the code. -/
def PERMIT_TYPEHASH : Word :=
  0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9#256

/-- `keccak256("EIP712Domain(…)")`, a literal of the code. -/
def DOMAIN_TYPEHASH : Word :=
  0x8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f#256

/-- `keccak256("1")`, a literal of the code. -/
def VERSION_HASH : Word :=
  0xc89efdaa54c0f20c7adf612882df0950f5a951637e0307cdcb4c672f298b8bc6#256

/-- The length solc 0.7 reads from a string's slot word. -/
def nameLen07 (S : Word) : Nat := if S.toNat % 2 = 0 then S.toNat % 256 / 2 else S.toNat / 2

/-- The bytes of the string at slot 51 as solc 0.7's copy produces them. -/
def nameBytes07 (crypto : Crypto) (sl : Word → Word) : ByteArray :=
  let S := sl 51#256
  let L := nameLen07 S
  if L = 0 then ByteArray.empty
  else if L ≤ 31 then (Bytes.ofWord (BitVec.ofNat 256 (S.toNat / 256 * 256))).extract 0 L
  else Str.longData sl (crypto.keccak256 (Bytes.ofWord 51#256)) L

/-- `DOMAIN_SEPARATOR()` of the account `self` with storage `sl` on chain `chainId`. -/
def amplDs (crypto : Crypto) (sl : Word → Word) (chainId : Word) (self : Address) : Word :=
  crypto.keccak256 (Bytes.ofWord DOMAIN_TYPEHASH ++
    (Bytes.ofWord (crypto.keccak256 (nameBytes07 crypto sl)) ++ (Bytes.ofWord VERSION_HASH ++
      (Bytes.ofWord chainId ++ Bytes.ofWord (Word.ofAddress self)))))

/-- `keccak256(abi.encode(PERMIT_TYPEHASH, owner, spender, value, nonce, deadline))`. -/
def structHash (crypto : Crypto) (owner spender : Address) (value nonce deadline : Word) : Word :=
  crypto.keccak256 (Bytes.ofWord PERMIT_TYPEHASH ++ (Bytes.ofWord (Word.ofAddress owner) ++
    (Bytes.ofWord (Word.ofAddress spender) ++ (Bytes.ofWord value ++ (Bytes.ofWord nonce ++
      Bytes.ofWord deadline)))))

/-- `"\x19\x01"`. -/
def eip712Prefix : ByteArray := ⟨#[0x19, 0x01]⟩

/-- `keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash))`. -/
def digest (crypto : Crypto) (ds sh : Word) : Word :=
  crypto.keccak256 (eip712Prefix ++ (Bytes.ofWord ds ++ Bytes.ofWord sh))

/-- The `permit` arguments of the calldata `d`, as AMPL's decoder reads them. -/
def pOwner (d : ByteArray) : Address := Word.toAddress (argWord d 0)
def pSpender (d : ByteArray) : Address := Word.toAddress (argWord d 1)
def pV (d : ByteArray) : Word := argWord d 4 &&& 255#256

/-- The digest `permit` signs at nonce `n`, in the frame `m`. -/
def amplDigest (m : Machine) (n : Word) : Word :=
  let d := m.frame.msg.data
  digest m.ctx.crypto
    (amplDs m.ctx.crypto (m.world.sload m.frame.msg.currentTarget) (ofNat m.ctx.block.chainId)
      m.frame.msg.currentTarget)
    (structHash m.ctx.crypto (pOwner d) (pSpender d) (argWord d 2) n (argWord d 3))

/-- **AMPL's signature recovery** for the `permit` calldata of the frame `m`, at nonce `n`. -/
def amplRec (m : Machine) (n : ℕ) : Address :=
  let d := m.frame.msg.data
  if Gas.stackDepthLimit < m.frame.msg.depth + 1 then (if pOwner d = 0 then 1 else 0)
  else (ecrecoverAddress? m.ctx.crypto (amplDigest m (BitVec.ofNat 256 n)) (pV d) (argWord d 5)
    (argWord d 6)).getD 0

/-- The slot of `_nonces[a]`. -/
def nonceSlot (crypto : Crypto) (a : Address) : Word := mappingSlot crypto (Word.ofAddress a) 160#256

/-- The slot of `_allowedFragments[o][sp]`. -/
def allowSlot' (crypto : Crypto) (o sp : Address) : Word :=
  mappingSlot2 crypto (Word.ofAddress o) (Word.ofAddress sp) 159#256

/-- **When `permit` succeeds**: no value, not static, below the depth limit, the deadline not
passed, the signer recovered, the nonce below `2²⁵⁶ − 1`. -/
def PermitOk (m : Machine) : Prop :=
  let d := m.frame.msg.data
  let t := m.frame.msg.currentTarget
  let nonce := m.world.sload t (nonceSlot m.ctx.crypto (pOwner d))
  m.frame.msg.value = 0 ∧ m.frame.msg.isStatic = false ∧
    m.frame.msg.depth + 1 ≤ Gas.stackDepthLimit ∧
    (ofNat m.ctx.block.timestamp).toNat ≤ (argWord d 3).toNat ∧
    amplRec m nonce.toNat = pOwner d ∧ nonce.toNat + 1 < 2 ^ 256

/-- `permit`'s successful end: the nonce incremented, the allowance set, `Approval`. -/
def PermitDone (m mf : Machine) : Prop :=
  let d := m.frame.msg.data
  let t := m.frame.msg.currentTarget
  let nonce := m.world.sload t (nonceSlot m.ctx.crypto (pOwner d))
  mf.world = (m.world.sstore t (nonceSlot m.ctx.crypto (pOwner d)) (nonce + 1#256)).sstore t
      (allowSlot' m.ctx.crypto (pOwner d) (pSpender d)) (argWord d 2) ∧
    mf.transient = m.transient ∧ mf.createdAccounts = m.createdAccounts ∧
    mf.frame.sub.logs = m.frame.sub.logs.push
      (approvalLog t (pOwner d) (pSpender d) (argWord d 2))

/-- `permit`'s code-level end at any gas: a success is a `PermitOk` frame ending as
`PermitDone`. -/
def PermitLow (m : Machine) (mf : Machine) (o : Outcome) : Prop :=
  (∃ out, o = .success out) ∧ PermitOk m ∧ PermitDone m mf

end Verified.WeirdERC20.AMPL.Spec.Malformed
