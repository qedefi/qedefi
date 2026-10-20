import EvmLean.Crypto.Secp256k1
import EvmLean.Prelude.Rlp
import EvmLean.Interpreter.Monad

/-!
# EIP-7702 delegation (Prague)

Mirrors `prague/vm/eoa_delegation.py`. An account delegates by holding the designator
`0xef0100 ‖ address`; calling it runs `address`'s code (never its precompile), one level deep.
Inert before Prague: callers gate on the fork.
-/

namespace EvmLean.Interpreter

/-- `EOA_DELEGATION_MARKER`: the designator prefix `0xef0100`. -/
def eoaDelegationMarker : ByteArray := ⟨#[0xef, 0x01, 0x00]⟩

/-- `EOA_DELEGATED_CODE_LENGTH`: marker plus a 20-byte address. -/
def eoaDelegatedCodeLength : Nat := 23

/-- `SET_CODE_TX_MAGIC`: domain-separation byte of authorization signatures. -/
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

/-- The authorization's signer, if y-parity ≤ 1, `0 < r < n` and `0 < s ≤ n/2` (EIP-2). -/
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

/-- The authority if valid, plus the warm set (warmed once recovered, even if later checks fail).
Mirrors `validate_authorization`. -/
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

/-- Apply authorizations in order, returning world, warm set and refund. Mirrors `set_delegation`
minus the final code refresh. -/
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

/-- The code a delegation to `d` runs: empty for a precompile address (precompiles disabled). -/
def delegateCode (isPrecompile : Address → Bool) (w : World) (d : Address) : ByteArray :=
  if isPrecompile d then .empty else w.code d

/-- The delegation part of `process_message_call` for a top-level call: returns world, message
and authorization refund. -/
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

/-- `(disablePrecompiles, codeAddress, code, extraAccessCost)` for a `CALL*` to `a`, warming the
delegate. Mirrors `access_delegation`. -/
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
