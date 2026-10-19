import EvmLean.Crypto.Secp256k1
import EvmLean.Prelude.Rlp
import EvmLean.Interpreter.Monad

/-!
# EIP-7702 delegation (Prague)

Mirrors `prague/vm/eoa_delegation.py` in `ethereum/execution-specs`:

| Lean                       | execution-specs               |
|----------------------------|-------------------------------|
| `isValidDelegation`        | `is_valid_delegation`         |
| `delegatedAddress?`        | `get_delegated_code_address`  |
| `recoverAuthority`         | `recover_authority`           |
| `validateAuthorization`    | `validate_authorization`      |
| `setDelegation`            | `set_delegation`              |
| `accessDelegation`         | `access_delegation`           |
| `applyTopLevelDelegation`  | the delegation part of `process_message_call` |

An account delegates by holding the 23-byte *delegation designator* `0xef0100 ‖ address`.
Calling it runs the code of `address` in the context of the delegating account; the
precompile at `address`, if any, is not run (`Message.disablePrecompiles`). Delegation is
followed one level only: the delegate's own code is run even if it is a designator (which
then halts on the invalid `0xef` opcode).

Everything here is inert before Prague: the callers gate on the fork, so a Cancun account
whose code happens to start with `0xef0100` is executed as ordinary code.
-/

namespace EvmLean.Interpreter

/-- `EOA_DELEGATION_MARKER`: the prefix `0xef0100` of a delegation designator. -/
def eoaDelegationMarker : ByteArray := ⟨#[0xef, 0x01, 0x00]⟩

/-- `EOA_DELEGATED_CODE_LENGTH`: a designator is the marker plus a 20-byte address. -/
def eoaDelegatedCodeLength : Nat := 23

/-- `SET_CODE_TX_MAGIC`: the domain-separation byte of authorization signatures. -/
def setCodeTxMagic : UInt8 := 0x05

/-- `GasCosts.AUTH_PER_EMPTY_ACCOUNT`: intrinsic cost per authorization. -/
def authPerEmptyAccount : Nat := 25000

/-- `GasCosts.REFUND_AUTH_PER_EXISTING_ACCOUNT`. -/
def refundAuthPerExistingAccount : Nat := 12500

/-- Is `code` a delegation designator `0xef0100 ‖ address`? Mirrors `is_valid_delegation`. -/
def isValidDelegation (code : ByteArray) : Bool :=
  code.size == eoaDelegatedCodeLength && code.extract 0 3 == eoaDelegationMarker

/-- The address a delegation designator points to. Mirrors `get_delegated_code_address`. -/
def delegatedAddress? (code : ByteArray) : Option Address :=
  if isValidDelegation code then some (BitVec.ofNat 160 (Bytes.toNat (code.extract 3 23)))
  else none

/-- The designator delegating to `a`. -/
def delegationCode (a : Address) : ByteArray := eoaDelegationMarker ++ Bytes.ofAddress a

/-- The message an authority signs: `0x05 ‖ rlp([chainId, address, nonce])`. -/
def authorizationSigningMessage (auth : Authorization) : ByteArray :=
  ⟨#[setCodeTxMagic]⟩ ++
    (Rlp.list [.nat auth.chainId, .bytes (Bytes.ofAddress auth.address), .nat auth.nonce]).encode

/-- The signer of an authorization, if the signature is well-formed and recovery succeeds.
Mirrors `recover_authority`: y-parity 0 or 1, `0 < r < n`, `0 < s ≤ n/2` (EIP-2). -/
def recoverAuthority (crypto : Crypto) (auth : Authorization) : Option Address :=
  let n := Secp256k1.n
  if auth.yParity > 1 then none
  else if auth.r = 0 ∨ auth.r ≥ n then none
  else if auth.s = 0 ∨ auth.s > n / 2 then none
  else
    let hash := Bytes.ofWord (crypto.keccak256 (authorizationSigningMessage auth))
    match crypto.ecrecover hash auth.yParity auth.r auth.s with
    | some pub => some (Word.toAddress (crypto.keccak256 pub))
    | none => none

/-- Check one authorization against the current state. Returns the authority if it is valid,
and the warm address set (the authority is warmed as soon as its signature recovers, even if
a later check fails). Mirrors `validate_authorization`. -/
def validateAuthorization (crypto : Crypto) (chainId : Nat) (w : World) (warm : AddressSet)
    (auth : Authorization) : Option Address × AddressSet :=
  if auth.chainId ≠ chainId ∧ auth.chainId ≠ 0 then (none, warm)
  else if auth.nonce ≥ 2 ^ 64 - 1 then (none, warm)
  else
    match recoverAuthority crypto auth with
    | none => (none, warm)
    | some authority =>
      let warm := warm.insert authority
      let acc := w.account authority
      if acc.code.size ≠ 0 && !isValidDelegation acc.code then (none, warm)
      else if acc.nonce ≠ auth.nonce then (none, warm)
      else (some authority, warm)

/-- Apply the authorizations in order: for each valid one, set the authority's code to the
designator (or clear it for the zero address) and increment its nonce; an authority that
already exists earns a refund of `25000 − 12500`. Returns the world, the warm set and the
refund. Mirrors `set_delegation` (without the final code refresh, done by the caller). -/
def setDelegation (crypto : Crypto) (chainId : Nat) (auths : List Authorization)
    (w : World) (warm : AddressSet) : World × AddressSet × Int :=
  auths.foldl (fun (w, warm, refund) auth =>
    match validateAuthorization crypto chainId w warm auth with
    | (none, warm) => (w, warm, refund)
    | (some authority, warm) =>
      let refund :=
        if w.exists authority then
          refund + ((authPerEmptyAccount - refundAuthPerExistingAccount : Nat) : Int)
        else refund
      let code := if auth.address = 0 then .empty else delegationCode auth.address
      let w := incrementNonce (setCode w authority code) authority
      (w, warm, refund)) (w, warm, 0)

/-- The code a delegation to `d` runs: none for a precompile address, whose precompile is
disabled under delegation (`disable_precompiles`), else the code of `d`. -/
def delegateCode (isPrecompile : Address → Bool) (w : World) (d : Address) : ByteArray :=
  if isPrecompile d then .empty else w.code d

/-- The delegation steps of `process_message_call` for a top-level call (Prague onward):
apply the transaction's authorizations, refresh the code, and if the target's code is a
designator, run the delegate's code with precompiles disabled and the delegate warm.
Returns the world, the message to run and the authorization refund (which is kept even if
the message fails). Creations and pre-Prague forks are unchanged. -/
def applyTopLevelDelegation (ctx : Context) (isPrecompile : Address → Bool) (w : World)
    (msg : Message) : World × Message × Int :=
  if ctx.fork < .prague then (w, msg, 0)
  else
    match msg.target, msg.codeAddress with
    | none, _ => (w, msg, 0)
    | some _, none => (w, msg, 0)
    | some _, some codeAddress =>
      let (w, warm, refund, code) :=
        if ctx.tx.authorizations.isEmpty then (w, msg.accessedAddresses, 0, msg.code)
        else
          let (w, warm, refund) := setDelegation ctx.crypto ctx.block.chainId
            ctx.tx.authorizations w msg.accessedAddresses
          (w, warm, refund, w.code codeAddress)
      match delegatedAddress? code with
      | none => (w, { msg with code, accessedAddresses := warm }, refund)
      | some d =>
        (w, { msg with code := delegateCode isPrecompile w d, codeAddress := some d,
                       disablePrecompiles := true, accessedAddresses := warm.insert d },
         refund)

/-- Resolve the code a `CALL*` to `a` runs. Before Prague, or if `a` holds no designator:
`a`'s code, no extra cost. Otherwise the delegate `d` is warmed, its access cost (warm 100,
cold 2600) is returned, and precompiles are disabled. Returns
`(disablePrecompiles, codeAddress, code, extraAccessCost)`. Mirrors `access_delegation`. -/
def accessDelegation (a : Address) : M (Bool × Address × ByteArray × Nat) := do
  let m ← get
  let code := m.world.code a
  if m.ctx.fork < .prague then return (false, a, code, 0)
  match delegatedAddress? code with
  | none => return (false, a, code, 0)
  | some d =>
    let warm ← accessAddress d
    return (true, d, delegateCode m.precompiles.isPrecompile m.world d, Gas.accessCost warm)

end EvmLean.Interpreter
